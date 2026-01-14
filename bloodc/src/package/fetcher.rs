//! Package fetching from various sources.
//!
//! This module handles downloading packages from:
//! - Registry (blood-lang.org/packages)
//! - Git repositories
//! - Local paths
//!
//! ## Fetching Process
//!
//! ```text
//! Source          Download        Verify          Extract
//!   │                │               │               │
//!   ├─ Registry ────>│ GET tarball ──┼─ checksum ───>│ untar
//!   │                │               │               │
//!   ├─ Git ─────────>│ clone/fetch ──┼─ ref check ──>│ checkout
//!   │                │               │               │
//!   └─ Path ────────>│ (no-op) ──────┼─ exists ─────>│ (symlink)
//! ```

use std::fs;
use std::io;
use std::path::{Path, PathBuf};

use thiserror::Error;

use super::cache::PackageCache;
use super::resolver::{PackageId, ResolvedSource};
use super::version::Version;

/// Package fetcher for downloading packages from various sources.
#[derive(Debug)]
#[allow(dead_code)] // Infrastructure for package registry
pub struct Fetcher {
    /// Package cache for storing downloaded packages.
    cache: PackageCache,
    /// Registry URL.
    registry_url: String,
}

impl Fetcher {
    /// Create a new fetcher with a package cache.
    pub fn new(cache: PackageCache) -> Self {
        Fetcher {
            cache,
            registry_url: "https://blood-lang.org/packages".to_string(),
        }
    }

    /// Create a fetcher with a custom registry URL.
    pub fn with_registry(cache: PackageCache, registry_url: String) -> Self {
        Fetcher { cache, registry_url }
    }

    /// Fetch a package from its source.
    pub fn fetch(
        &self,
        id: &PackageId,
        source: &ResolvedSource,
    ) -> Result<PathBuf, FetchError> {
        match source {
            ResolvedSource::Registry { url, checksum } => {
                self.fetch_from_registry(id, url, checksum.as_deref())
            }
            ResolvedSource::Git {
                url,
                reference,
                revision,
            } => self.fetch_from_git(id, url, reference.as_deref(), revision),
            ResolvedSource::Path { path } => self.fetch_from_path(id, path),
        }
    }

    /// Fetch a package from the registry.
    fn fetch_from_registry(
        &self,
        id: &PackageId,
        registry_url: &str,
        checksum: Option<&str>,
    ) -> Result<PathBuf, FetchError> {
        // Check if already cached
        if let Some(path) = self.cache.get_cached(&id.name, &id.version) {
            // Verify checksum if provided
            if let Some(expected) = checksum {
                self.verify_checksum(&path, expected)?;
            }
            return Ok(path);
        }

        // Download URL format: {registry}/api/v1/packages/{name}/{version}/download
        let download_url = format!(
            "{}/api/v1/packages/{}/{}/download",
            registry_url, id.name, id.version
        );

        // In a real implementation, this would:
        // 1. Make HTTP request to download_url
        // 2. Save tarball to temp location
        // 3. Verify checksum
        // 4. Extract to cache directory
        // 5. Return path to extracted package

        // For now, return an error indicating fetching is not yet implemented
        Err(FetchError::NotImplemented(format!(
            "registry download from {} for {} v{}",
            download_url, id.name, id.version
        )))
    }

    /// Fetch a package from a git repository.
    fn fetch_from_git(
        &self,
        id: &PackageId,
        url: &str,
        reference: Option<&str>,
        revision: &str,
    ) -> Result<PathBuf, FetchError> {
        // Check if already cached
        if let Some(path) = self.cache.get_git_cached(&id.name, revision) {
            return Ok(path);
        }

        // In a real implementation, this would:
        // 1. Clone or fetch the repository
        // 2. Checkout the specified revision
        // 3. Cache the result
        // 4. Return path to the checkout

        // Build git reference for error message
        let ref_info = match reference {
            Some(r) => format!("{} at {}", r, revision),
            None => revision.to_string(),
        };

        Err(FetchError::NotImplemented(format!(
            "git clone from {} ({}) for {}",
            url, ref_info, id.name
        )))
    }

    /// "Fetch" a package from a local path (just validate it exists).
    fn fetch_from_path(&self, id: &PackageId, path: &Path) -> Result<PathBuf, FetchError> {
        if !path.exists() {
            return Err(FetchError::PathNotFound {
                package: id.name.clone(),
                path: path.to_path_buf(),
            });
        }

        // Verify it's a valid Blood package (has Blood.toml)
        let manifest_path = path.join("Blood.toml");
        if !manifest_path.exists() {
            return Err(FetchError::InvalidPackage {
                package: id.name.clone(),
                reason: format!("no Blood.toml found at {}", path.display()),
            });
        }

        Ok(path.to_path_buf())
    }

    /// Verify a package checksum.
    fn verify_checksum(&self, path: &Path, expected: &str) -> Result<(), FetchError> {
        // Parse expected checksum format (sha256:...)
        let (algo, hash) = expected.split_once(':').ok_or_else(|| {
            FetchError::InvalidChecksum {
                expected: expected.to_string(),
                actual: "invalid format".to_string(),
            }
        })?;

        if algo != "sha256" {
            return Err(FetchError::UnsupportedChecksum {
                algorithm: algo.to_string(),
            });
        }

        // Compute actual checksum
        let actual = compute_dir_hash(path)?;

        if actual != hash {
            return Err(FetchError::InvalidChecksum {
                expected: hash.to_string(),
                actual,
            });
        }

        Ok(())
    }

    /// Get the package cache.
    pub fn cache(&self) -> &PackageCache {
        &self.cache
    }
}

/// Compute a hash of a directory's contents.
fn compute_dir_hash(path: &Path) -> Result<String, FetchError> {
    use sha2::{Sha256, Digest};

    let mut hasher = Sha256::new();

    // Get all files sorted by path for deterministic hashing
    let mut files: Vec<PathBuf> = Vec::new();
    collect_files(path, &mut files)?;
    files.sort();

    for file in files {
        // Include relative path in hash
        if let Ok(rel) = file.strip_prefix(path) {
            hasher.update(rel.to_string_lossy().as_bytes());
        }

        // Include file contents
        let contents = fs::read(&file).map_err(|e| FetchError::Io(e))?;
        hasher.update(&contents);
    }

    let result = hasher.finalize();
    Ok(hex::encode(result))
}

/// Recursively collect all files in a directory.
fn collect_files(dir: &Path, files: &mut Vec<PathBuf>) -> Result<(), FetchError> {
    if !dir.is_dir() {
        return Ok(());
    }

    for entry in fs::read_dir(dir).map_err(FetchError::Io)? {
        let entry = entry.map_err(FetchError::Io)?;
        let path = entry.path();

        if path.is_file() {
            files.push(path);
        } else if path.is_dir() {
            // Skip hidden directories and common ignores
            if let Some(name) = path.file_name().and_then(|n| n.to_str()) {
                if !name.starts_with('.') && name != "target" && name != "node_modules" {
                    collect_files(&path, files)?;
                }
            }
        }
    }

    Ok(())
}

/// Source to fetch a package from.
#[derive(Debug, Clone)]
pub enum FetchSource {
    /// Fetch from the default registry.
    Registry,
    /// Fetch from a custom registry.
    CustomRegistry(String),
    /// Fetch from a git repository.
    Git {
        /// Repository URL.
        url: String,
        /// Branch name.
        branch: Option<String>,
        /// Tag name.
        tag: Option<String>,
        /// Commit revision.
        rev: Option<String>,
    },
    /// Use a local path.
    Path(PathBuf),
}

/// Errors that can occur during package fetching.
#[derive(Debug, Error)]
pub enum FetchError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),

    #[error("path not found for package '{package}': {path}")]
    PathNotFound { package: String, path: PathBuf },

    #[error("invalid package '{package}': {reason}")]
    InvalidPackage { package: String, reason: String },

    #[error("checksum mismatch: expected {expected}, got {actual}")]
    InvalidChecksum { expected: String, actual: String },

    #[error("unsupported checksum algorithm: {algorithm}")]
    UnsupportedChecksum { algorithm: String },

    #[error("network error: {0}")]
    Network(String),

    #[error("git error: {0}")]
    Git(String),

    #[error("not yet implemented: {0}")]
    NotImplemented(String),

    #[error("package not found: {name} v{version}")]
    NotFound { name: String, version: Version },
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn test_fetcher_new() {
        let temp = TempDir::new().unwrap();
        let cache = PackageCache::new(temp.path().to_path_buf());
        let fetcher = Fetcher::new(cache);
        assert_eq!(fetcher.registry_url, "https://blood-lang.org/packages");
    }

    #[test]
    fn test_fetch_from_path_exists() {
        let temp = TempDir::new().unwrap();
        let cache = PackageCache::new(temp.path().join("cache"));
        let fetcher = Fetcher::new(cache);

        // Create a valid package directory
        let pkg_dir = temp.path().join("my-package");
        fs::create_dir(&pkg_dir).unwrap();
        fs::write(
            pkg_dir.join("Blood.toml"),
            "[package]\nname = \"test\"\nversion = \"1.0.0\"",
        )
        .unwrap();

        let id = PackageId::new("test".to_string(), Version::parse("1.0.0").unwrap());
        let result = fetcher.fetch_from_path(&id, &pkg_dir);

        assert!(result.is_ok());
        assert_eq!(result.unwrap(), pkg_dir);
    }

    #[test]
    fn test_fetch_from_path_missing() {
        let temp = TempDir::new().unwrap();
        let cache = PackageCache::new(temp.path().join("cache"));
        let fetcher = Fetcher::new(cache);

        let id = PackageId::new("test".to_string(), Version::parse("1.0.0").unwrap());
        let result = fetcher.fetch_from_path(&id, &temp.path().join("nonexistent"));

        assert!(matches!(result, Err(FetchError::PathNotFound { .. })));
    }

    #[test]
    fn test_fetch_from_path_no_manifest() {
        let temp = TempDir::new().unwrap();
        let cache = PackageCache::new(temp.path().join("cache"));
        let fetcher = Fetcher::new(cache);

        // Create directory without Blood.toml
        let pkg_dir = temp.path().join("my-package");
        fs::create_dir(&pkg_dir).unwrap();

        let id = PackageId::new("test".to_string(), Version::parse("1.0.0").unwrap());
        let result = fetcher.fetch_from_path(&id, &pkg_dir);

        assert!(matches!(result, Err(FetchError::InvalidPackage { .. })));
    }

    #[test]
    fn test_fetch_from_registry_not_implemented() {
        let temp = TempDir::new().unwrap();
        let cache = PackageCache::new(temp.path().to_path_buf());
        let fetcher = Fetcher::new(cache);

        let id = PackageId::new("test".to_string(), Version::parse("1.0.0").unwrap());
        let result = fetcher.fetch_from_registry(&id, "https://example.com", None);

        assert!(matches!(result, Err(FetchError::NotImplemented(_))));
    }

    #[test]
    fn test_fetch_from_git_not_implemented() {
        let temp = TempDir::new().unwrap();
        let cache = PackageCache::new(temp.path().to_path_buf());
        let fetcher = Fetcher::new(cache);

        let id = PackageId::new("test".to_string(), Version::parse("1.0.0").unwrap());
        let result = fetcher.fetch_from_git(&id, "https://github.com/test/test", None, "abc123");

        assert!(matches!(result, Err(FetchError::NotImplemented(_))));
    }

    #[test]
    fn test_compute_dir_hash() {
        let temp = TempDir::new().unwrap();

        // Create some files
        fs::write(temp.path().join("a.txt"), "hello").unwrap();
        fs::write(temp.path().join("b.txt"), "world").unwrap();

        let hash1 = compute_dir_hash(temp.path()).unwrap();

        // Hash should be deterministic
        let hash2 = compute_dir_hash(temp.path()).unwrap();
        assert_eq!(hash1, hash2);

        // Modifying content should change hash
        fs::write(temp.path().join("a.txt"), "changed").unwrap();
        let hash3 = compute_dir_hash(temp.path()).unwrap();
        assert_ne!(hash1, hash3);
    }
}
