//! Codebase Synchronization
//!
//! Handles syncing codebases between local and remote locations.

use crate::hash::Hash;
use crate::names::Name;
use crate::{Codebase, DefKind, UcmError, UcmResult};

/// A remote codebase location.
#[derive(Debug, Clone)]
pub struct Remote {
    /// Remote name (e.g., "origin")
    pub name: String,
    /// Remote URL
    pub url: String,
}

impl Remote {
    /// Creates a new remote.
    pub fn new(name: impl Into<String>, url: impl Into<String>) -> Self {
        Self {
            name: name.into(),
            url: url.into(),
        }
    }
}

/// A sync operation to perform.
#[derive(Debug, Clone)]
pub enum SyncOp {
    /// Add a definition locally
    AddLocal(Name, String, DefKind),
    /// Add a definition remotely
    AddRemote(Name, String, DefKind),
    /// Remove a definition locally
    RemoveLocal(Hash),
    /// Remove a definition remotely
    RemoveRemote(Hash),
    /// Conflict that needs resolution
    Conflict {
        name: Name,
        local_hash: Hash,
        remote_hash: Hash,
    },
}

/// Result of comparing two codebases.
#[derive(Debug, Clone, Default)]
pub struct SyncPlan {
    /// Operations to perform
    pub operations: Vec<SyncOp>,
    /// Whether there are conflicts
    pub has_conflicts: bool,
}

impl SyncPlan {
    /// Creates an empty sync plan.
    pub fn new() -> Self {
        Self::default()
    }

    /// Adds an operation to the plan.
    pub fn add(&mut self, op: SyncOp) {
        if matches!(op, SyncOp::Conflict { .. }) {
            self.has_conflicts = true;
        }
        self.operations.push(op);
    }

    /// Returns true if the plan is empty.
    pub fn is_empty(&self) -> bool {
        self.operations.is_empty()
    }

    /// Returns the number of operations.
    pub fn len(&self) -> usize {
        self.operations.len()
    }
}

/// Synchronization engine.
pub struct SyncEngine<'a> {
    local: &'a mut Codebase,
}

impl<'a> SyncEngine<'a> {
    /// Creates a new sync engine for the given codebase.
    pub fn new(local: &'a mut Codebase) -> Self {
        Self { local }
    }

    /// Computes the sync plan between local and a remote export file.
    ///
    /// For file-based remotes (file:// URLs), reads the remote export and compares.
    pub fn plan(&self, remote: &Remote) -> UcmResult<SyncPlan> {
        let mut plan = SyncPlan::new();

        // Load remote data if it's a file-based remote
        if remote.url.starts_with("file://") {
            let remote_path = std::path::Path::new(&remote.url[7..]);
            if remote_path.exists() {
                let remote_data = self.load_remote_data(remote_path)?;
                self.compute_plan_from_data(&remote_data, &mut plan)?;
            }
        }
        // HTTP remotes would fetch from URL here

        Ok(plan)
    }

    /// Loads remote export data from a file path.
    fn load_remote_data(&self, path: &std::path::Path) -> UcmResult<ExportData> {
        let format = if path.extension().map_or(false, |e| e == "json") {
            ExportFormat::Json
        } else {
            ExportFormat::Binary
        };

        let file = std::fs::File::open(path)?;
        let data: ExportData = match format {
            ExportFormat::Json => {
                serde_json::from_reader(file)
                    .map_err(|e| UcmError::Storage(crate::storage::StorageError::Other(e.to_string())))?
            }
            ExportFormat::Binary => {
                bincode::deserialize_from(file)
                    .map_err(|e| UcmError::Storage(crate::storage::StorageError::Other(e.to_string())))?
            }
        };

        Ok(data)
    }

    /// Computes sync operations by comparing local state with remote data.
    fn compute_plan_from_data(&self, remote_data: &ExportData, plan: &mut SyncPlan) -> UcmResult<()> {
        // Build sets of remote definitions and names
        let remote_hashes: std::collections::HashSet<String> = remote_data.definitions
            .iter()
            .map(|(h, _, _)| h.clone())
            .collect();

        let remote_names: std::collections::HashMap<String, String> = remote_data.names
            .iter()
            .cloned()
            .collect();

        // Get local names and check what's missing from remote
        let local_names = self.local.list_names(None)?;
        for (name, hash) in &local_names {
            let hash_str = hash.to_string();

            // Check if remote has this hash
            if !remote_hashes.contains(&hash_str) {
                // Remote doesn't have this definition - need to push
                if let Some(info) = self.local.find(&crate::DefRef::Hash(hash.clone()))? {
                    plan.add(SyncOp::AddRemote(
                        name.clone(),
                        info.source.clone(),
                        info.kind,
                    ));
                }
            } else {
                // Check if name mapping differs
                let name_str = name.to_string();
                if let Some(remote_hash) = remote_names.get(&name_str) {
                    if remote_hash != &hash_str {
                        // Same name points to different hash - conflict
                        let remote_hash_parsed: Hash = remote_hash.parse()
                            .map_err(|_| UcmError::ParseError(format!("Invalid hash: {}", remote_hash)))?;
                        plan.add(SyncOp::Conflict {
                            name: name.clone(),
                            local_hash: hash.clone(),
                            remote_hash: remote_hash_parsed,
                        });
                    }
                }
            }
        }

        // Check what remote has that local doesn't
        for (name_str, hash_str) in &remote_names {
            let name = Name::new(name_str);
            if self.local.resolve(&name)?.is_none() {
                // Local doesn't have this name - need to pull
                if let Some((_, kind_str, source)) = remote_data.definitions
                    .iter()
                    .find(|(h, _, _)| h == hash_str)
                {
                    let kind = DefKind::from_str(kind_str);
                    plan.add(SyncOp::AddLocal(name, source.clone(), kind));
                }
            }
        }

        Ok(())
    }

    /// Executes a sync plan, applying all operations.
    pub fn execute(&mut self, plan: &SyncPlan) -> UcmResult<()> {
        for op in &plan.operations {
            match op {
                SyncOp::AddLocal(name, source, kind) => {
                    let hash = match kind {
                        DefKind::Term => self.local.add_term(source)?,
                        DefKind::Type => self.local.add_type(source)?,
                        DefKind::Effect => self.local.add_effect(source)?,
                        DefKind::Handler => self.local.add_handler(source)?,
                        DefKind::Test => self.local.add_test(source)?,
                        DefKind::Doc => self.local.add_term(source)?, // Treat docs as terms
                    };
                    self.local.add_name(name.clone(), hash)?;
                }
                SyncOp::AddRemote(_name, _source, _kind) => {
                    // Remote operations are handled by push()
                }
                SyncOp::RemoveLocal(hash) => {
                    // Find and remove names pointing to this hash
                    let names = self.local.list_names(None)?;
                    for (name, h) in names {
                        if &h == hash {
                            self.local.remove_name(&name)?;
                        }
                    }
                }
                SyncOp::RemoveRemote(_hash) => {
                    // Remote operations are handled by push()
                }
                SyncOp::Conflict { .. } => {
                    // Conflicts require manual resolution
                }
            }
        }
        Ok(())
    }

    /// Pushes local changes to remote.
    ///
    /// For file-based remotes, exports local codebase to the remote path.
    /// For HTTP remotes, would POST data to the URL.
    pub fn push(&mut self, remote: &Remote) -> UcmResult<PushResult> {
        let plan = self.plan(remote)?;

        // Count operations that would push to remote
        let push_ops: Vec<_> = plan.operations.iter()
            .filter(|op| matches!(op, SyncOp::AddRemote(_, _, _)))
            .collect();
        let pushed = push_ops.len();

        if remote.url.starts_with("file://") {
            let remote_path = std::path::Path::new(&remote.url[7..]);

            // Export current state to remote
            let format = if remote_path.extension().map_or(false, |e| e == "json") {
                ExportFormat::Json
            } else {
                ExportFormat::Binary
            };

            export_codebase(self.local, remote_path, format)?;
        }
        // HTTP push would POST to URL here

        Ok(PushResult {
            pushed,
            remote: remote.clone(),
        })
    }

    /// Pulls remote changes to local.
    ///
    /// For file-based remotes, imports from the remote path.
    /// For HTTP remotes, would GET data from the URL.
    pub fn pull(&mut self, remote: &Remote) -> UcmResult<PullResult> {
        let plan = self.plan(remote)?;

        // Execute only the local additions (pull operations)
        let mut pulled = 0;
        for op in &plan.operations {
            if let SyncOp::AddLocal(name, source, kind) = op {
                let hash = match kind {
                    DefKind::Term => self.local.add_term(source)?,
                    DefKind::Type => self.local.add_type(source)?,
                    DefKind::Effect => self.local.add_effect(source)?,
                    DefKind::Handler => self.local.add_handler(source)?,
                    DefKind::Test => self.local.add_test(source)?,
                    DefKind::Doc => self.local.add_term(source)?,
                };
                self.local.add_name(name.clone(), hash)?;
                pulled += 1;
            }
        }

        Ok(PullResult {
            pulled,
            remote: remote.clone(),
        })
    }
}

/// Result of a push operation.
#[derive(Debug)]
pub struct PushResult {
    /// Number of definitions pushed
    pub pushed: usize,
    /// Remote that was pushed to
    pub remote: Remote,
}

/// Result of a pull operation.
#[derive(Debug)]
pub struct PullResult {
    /// Number of definitions pulled
    pub pulled: usize,
    /// Remote that was pulled from
    pub remote: Remote,
}

/// Conflict resolution strategies.
#[derive(Debug, Clone, Copy)]
pub enum ConflictResolution {
    /// Keep the local version
    KeepLocal,
    /// Keep the remote version
    KeepRemote,
    /// Keep both (with different names)
    KeepBoth,
    /// Skip this conflict
    Skip,
}

/// Resolves a conflict using the given strategy.
pub fn resolve_conflict(
    _name: &Name,
    _local_hash: &Hash,
    _remote_hash: &Hash,
    resolution: ConflictResolution,
) -> Option<SyncOp> {
    match resolution {
        ConflictResolution::KeepLocal => None, // No-op, already have local
        ConflictResolution::KeepRemote => {
            // TODO: Return operation to update local with remote
            None
        }
        ConflictResolution::KeepBoth => {
            // TODO: Rename one and keep both
            None
        }
        ConflictResolution::Skip => None,
    }
}

/// Format for exporting/importing codebase data.
#[derive(Debug, Clone, Copy)]
pub enum ExportFormat {
    /// JSON format
    Json,
    /// Binary format (more compact)
    Binary,
}

/// Exported codebase data for sync.
#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ExportData {
    /// Version of the export format
    pub version: u32,
    /// Definitions: (hash_hex, kind_str, source)
    pub definitions: Vec<(String, String, String)>,
    /// Names: (name, hash_hex)
    pub names: Vec<(String, String)>,
}

impl ExportData {
    /// Create a new export data container.
    pub fn new() -> Self {
        Self {
            version: 1,
            definitions: Vec::new(),
            names: Vec::new(),
        }
    }
}

impl Default for ExportData {
    fn default() -> Self {
        Self::new()
    }
}

/// Exports a codebase to a file.
pub fn export_codebase(
    codebase: &Codebase,
    path: &std::path::Path,
    format: ExportFormat,
) -> UcmResult<()> {
    // Collect all definitions and names
    let mut export_data = ExportData::new();

    // Get all names and their hashes
    let names = codebase.list_names(None)?;
    for (name, hash) in &names {
        export_data.names.push((name.to_string(), hash.to_string()));

        // Get the definition for this hash
        if let Some(info) = codebase.find(&crate::DefRef::Hash(hash.clone()))? {
            // Check if we already have this definition
            if !export_data.definitions.iter().any(|(h, _, _)| h == &hash.to_string()) {
                export_data.definitions.push((
                    hash.to_string(),
                    info.kind.as_str().to_string(),
                    info.source.clone(),
                ));
            }
        }
    }

    // Write to file
    let file = std::fs::File::create(path)?;
    match format {
        ExportFormat::Json => {
            serde_json::to_writer_pretty(file, &export_data)
                .map_err(|e| UcmError::Storage(crate::storage::StorageError::Other(e.to_string())))?;
        }
        ExportFormat::Binary => {
            bincode::serialize_into(file, &export_data)
                .map_err(|e| UcmError::Storage(crate::storage::StorageError::Other(e.to_string())))?;
        }
    }

    Ok(())
}

/// Imports a codebase from a file.
pub fn import_codebase(
    codebase: &mut Codebase,
    path: &std::path::Path,
    format: ExportFormat,
) -> UcmResult<usize> {
    // Read from file
    let file = std::fs::File::open(path)?;
    let export_data: ExportData = match format {
        ExportFormat::Json => {
            serde_json::from_reader(file)
                .map_err(|e| UcmError::Storage(crate::storage::StorageError::Other(e.to_string())))?
        }
        ExportFormat::Binary => {
            bincode::deserialize_from(file)
                .map_err(|e| UcmError::Storage(crate::storage::StorageError::Other(e.to_string())))?
        }
    };

    let mut imported = 0;

    // Import definitions
    for (_hash_str, kind_str, source) in &export_data.definitions {
        let _hash = match kind_str.as_str() {
            "term" => codebase.add_term(source)?,
            "type" => codebase.add_type(source)?,
            "effect" => codebase.add_effect(source)?,
            "handler" => codebase.add_handler(source)?,
            "test" => codebase.add_test(source)?,
            other => return Err(UcmError::ParseError(
                format!("Unknown definition kind '{}' in import data", other)
            )),
        };
        imported += 1;
    }

    // Import names
    for (name_str, hash_str) in &export_data.names {
        let name = Name::new(name_str);
        let hash: Hash = hash_str.parse()
            .map_err(|_| UcmError::ParseError(format!("Invalid hash: {}", hash_str)))?;
        // Only add if name doesn't already exist
        if codebase.resolve(&name)?.is_none() {
            codebase.add_name(name, hash)?;
        }
    }

    Ok(imported)
}
