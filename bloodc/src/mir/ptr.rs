//! # 128-bit Generational Pointers
//!
//! This module implements Blood's 128-bit generational pointer representation
//! as specified in [MEMORY_MODEL.md](../../MEMORY_MODEL.md).
//!
//! ## Pointer Layout
//!
//! ```text
//! ┌────────────────────────────────────────────────────────────────────────────┐
//! │                           128-bit Blood Pointer                             │
//! ├────────────────────────────────────────────────────────────────────────────┤
//! │ 127                           64 63                 32 31                 0 │
//! │ ├──────────────────────────────┤├───────────────────┤├───────────────────┤ │
//! │ │         ADDRESS (64)         ││   GENERATION (32) ││   METADATA (32)   │ │
//! │ └──────────────────────────────┘└───────────────────┘└───────────────────┘ │
//! └────────────────────────────────────────────────────────────────────────────┘
//! ```
//!
//! ## Design References
//!
//! - [Vale's Generational References](https://verdagon.dev/blog/generational-references)
//! - Blood MEMORY_MODEL.md §2: Pointer Representation

use std::fmt;

// ============================================================================
// Blood Pointer
// ============================================================================

/// A 128-bit generational pointer.
///
/// This is Blood's primary heap pointer type. It contains:
/// - 64-bit address
/// - 32-bit generation counter
/// - 32-bit metadata (tier, flags, type fingerprint)
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(C, align(16))]
pub struct BloodPtr {
    /// The virtual address of the pointed-to value.
    pub address: u64,
    /// The expected generation counter.
    pub generation: u32,
    /// Metadata: tier (4 bits), flags (4 bits), type fingerprint (24 bits).
    pub metadata: u32,
}

impl BloodPtr {
    /// Null pointer constant.
    pub const NULL: BloodPtr = BloodPtr {
        address: 0,
        generation: 0,
        metadata: PtrFlags::NULLABLE.bits() as u32,
    };

    /// Create a new BloodPtr.
    pub const fn new(address: u64, generation: u32, metadata: PtrMetadata) -> Self {
        Self {
            address,
            generation,
            metadata: metadata.to_u32(),
        }
    }

    /// Create a null pointer.
    pub const fn null() -> Self {
        Self::NULL
    }

    /// Check if this pointer is null.
    pub fn is_null(&self) -> bool {
        self.address == 0
    }

    /// Get the memory tier.
    pub fn tier(&self) -> MemoryTier {
        MemoryTier::from_bits((self.metadata >> 28) & 0xF)
    }

    /// Get the flags.
    pub fn flags(&self) -> PtrFlags {
        PtrFlags::from_bits_truncate(((self.metadata >> 24) & 0xF) as u8)
    }

    /// Get the type fingerprint.
    pub fn type_fingerprint(&self) -> u32 {
        self.metadata & 0x00FF_FFFF
    }

    /// Get the parsed metadata.
    pub fn parsed_metadata(&self) -> PtrMetadata {
        PtrMetadata::from_u32(self.metadata)
    }

    /// Check if this is a mutable reference.
    pub fn is_mutable(&self) -> bool {
        self.flags().contains(PtrFlags::MUT)
    }

    /// Check if this has linear ownership.
    pub fn is_linear(&self) -> bool {
        self.flags().contains(PtrFlags::LINEAR)
    }

    /// Check if this is frozen (deeply immutable).
    pub fn is_frozen(&self) -> bool {
        self.flags().contains(PtrFlags::FROZEN)
    }

    /// Check if this pointer may be null.
    pub fn is_nullable(&self) -> bool {
        self.flags().contains(PtrFlags::NULLABLE)
    }

    /// Create a new pointer with updated generation.
    pub fn with_generation(self, gen: u32) -> Self {
        Self {
            generation: gen,
            ..self
        }
    }

    /// Create a new pointer with updated metadata.
    pub fn with_metadata(self, metadata: PtrMetadata) -> Self {
        Self {
            metadata: metadata.to_u32(),
            ..self
        }
    }

    /// Validate this pointer against a slot's generation.
    ///
    /// Returns `Ok(())` if generations match, `Err` otherwise.
    pub fn validate(&self, slot_generation: u32) -> Result<(), StaleReferenceError> {
        // Handle special generations
        if self.generation == PERSISTENT_MARKER {
            // Persistent pointers are always valid
            return Ok(());
        }

        if self.generation == slot_generation {
            Ok(())
        } else {
            Err(StaleReferenceError {
                expected: self.generation,
                actual: slot_generation,
                address: self.address,
            })
        }
    }

    /// Convert to raw bytes (for serialization/FFI).
    pub fn to_bytes(&self) -> [u8; 16] {
        let mut bytes = [0u8; 16];
        bytes[0..8].copy_from_slice(&self.address.to_le_bytes());
        bytes[8..12].copy_from_slice(&self.generation.to_le_bytes());
        bytes[12..16].copy_from_slice(&self.metadata.to_le_bytes());
        bytes
    }

    /// Create from raw bytes.
    pub fn from_bytes(bytes: [u8; 16]) -> Self {
        Self {
            address: u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            generation: u32::from_le_bytes(bytes[8..12].try_into().unwrap()),
            metadata: u32::from_le_bytes(bytes[12..16].try_into().unwrap()),
        }
    }
}

impl Default for BloodPtr {
    fn default() -> Self {
        Self::null()
    }
}

impl fmt::Debug for BloodPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BloodPtr")
            .field("address", &format_args!("{:#x}", self.address))
            .field("generation", &self.generation)
            .field("tier", &self.tier())
            .field("flags", &self.flags())
            .field("type_fp", &format_args!("{:#x}", self.type_fingerprint()))
            .finish()
    }
}

impl fmt::Display for BloodPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.is_null() {
            write!(f, "null")
        } else {
            write!(f, "ptr@{:#x}:g{}", self.address, self.generation)
        }
    }
}

// ============================================================================
// Reserved Generation Values
// ============================================================================

/// Marker for persistent (reference-counted) allocations.
///
/// From MEMORY_MODEL.md §4.5:
/// "Generation 0xFFFF_FFFF indicates a persistent allocation that should
/// not be generation-checked."
pub const PERSISTENT_MARKER: u32 = 0xFFFF_FFFF;

/// Initial generation value for new allocations.
pub const INITIAL_GENERATION: u32 = 1;

/// Generation value indicating freed memory.
pub const FREED_GENERATION: u32 = 0;

// ============================================================================
// Memory Tiers
// ============================================================================

/// Memory tier for a pointer.
///
/// From MEMORY_MODEL.md §3:
/// | Tier | Name | Lifecycle | Safety Mechanism |
/// |------|------|-----------|------------------|
/// | 0 | Stack | Lexical scope | Compile-time proof |
/// | 1 | Region | Explicit scope | Generational check |
/// | 2 | Persistent | Reference-counted | Deferred RC |
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
#[repr(u8)]
pub enum MemoryTier {
    /// Stack allocation (thin pointers, no runtime check).
    Stack = 0,
    /// Region allocation (generational check).
    #[default]
    Region = 1,
    /// Persistent allocation (reference counted).
    Persistent = 2,
    /// Reserved for future use.
    Reserved = 3,
}

impl MemoryTier {
    /// Create from the 4-bit tier field.
    pub fn from_bits(bits: u32) -> Self {
        match bits {
            0 => MemoryTier::Stack,
            1 => MemoryTier::Region,
            2 => MemoryTier::Persistent,
            _ => MemoryTier::Reserved,
        }
    }

    /// Convert to 4-bit field.
    pub fn to_bits(self) -> u32 {
        self as u32
    }

    /// Check if this tier requires generation checks.
    pub fn needs_generation_check(self) -> bool {
        matches!(self, MemoryTier::Region)
    }

    /// Check if this tier uses reference counting.
    pub fn is_ref_counted(self) -> bool {
        matches!(self, MemoryTier::Persistent)
    }
}


// ============================================================================
// Pointer Flags
// ============================================================================

bitflags::bitflags! {
    /// Flags for pointer properties.
    ///
    /// From MEMORY_MODEL.md §2.2:
    /// | Bit | Name | Meaning |
    /// |-----|------|---------|
    /// | 27 | MUT | Mutable reference |
    /// | 26 | LINEAR | Linear ownership |
    /// | 25 | FROZEN | Deeply immutable |
    /// | 24 | NULLABLE | May be null |
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
    pub struct PtrFlags: u8 {
        /// Mutable reference (1) or immutable (0).
        const MUT = 0b1000;
        /// Linear ownership (1) or unrestricted (0).
        const LINEAR = 0b0100;
        /// Deeply immutable, shareable across fibers.
        const FROZEN = 0b0010;
        /// May be null (0 address valid).
        const NULLABLE = 0b0001;
    }
}

impl Default for PtrFlags {
    fn default() -> Self {
        PtrFlags::empty()
    }
}

// ============================================================================
// Pointer Metadata
// ============================================================================

/// Parsed metadata from a BloodPtr.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PtrMetadata {
    /// Memory tier (4 bits).
    pub tier: MemoryTier,
    /// Pointer flags (4 bits).
    pub flags: PtrFlags,
    /// Type fingerprint for dispatch optimization (24 bits).
    pub type_fingerprint: u32,
}

impl PtrMetadata {
    /// Create new metadata.
    pub const fn new(tier: MemoryTier, flags: PtrFlags, type_fingerprint: u32) -> Self {
        Self {
            tier,
            flags,
            type_fingerprint: type_fingerprint & 0x00FF_FFFF,
        }
    }

    /// Create default metadata for region-allocated values.
    pub const fn region() -> Self {
        Self {
            tier: MemoryTier::Region,
            flags: PtrFlags::empty(),
            type_fingerprint: 0,
        }
    }

    /// Create metadata for stack pointers.
    pub const fn stack() -> Self {
        Self {
            tier: MemoryTier::Stack,
            flags: PtrFlags::empty(),
            type_fingerprint: 0,
        }
    }

    /// Create metadata for persistent pointers.
    pub const fn persistent() -> Self {
        Self {
            tier: MemoryTier::Persistent,
            flags: PtrFlags::empty(),
            type_fingerprint: 0,
        }
    }

    /// Pack into u32.
    pub const fn to_u32(&self) -> u32 {
        ((self.tier as u32) << 28)
            | ((self.flags.bits() as u32) << 24)
            | (self.type_fingerprint & 0x00FF_FFFF)
    }

    /// Unpack from u32.
    pub fn from_u32(value: u32) -> Self {
        Self {
            tier: MemoryTier::from_bits((value >> 28) & 0xF),
            flags: PtrFlags::from_bits_truncate(((value >> 24) & 0xF) as u8),
            type_fingerprint: value & 0x00FF_FFFF,
        }
    }

    /// Set the mutable flag.
    pub fn with_mut(mut self, mutable: bool) -> Self {
        if mutable {
            self.flags.insert(PtrFlags::MUT);
        } else {
            self.flags.remove(PtrFlags::MUT);
        }
        self
    }

    /// Set the linear flag.
    pub fn with_linear(mut self, linear: bool) -> Self {
        if linear {
            self.flags.insert(PtrFlags::LINEAR);
        } else {
            self.flags.remove(PtrFlags::LINEAR);
        }
        self
    }

    /// Set the frozen flag.
    pub fn with_frozen(mut self, frozen: bool) -> Self {
        if frozen {
            self.flags.insert(PtrFlags::FROZEN);
        } else {
            self.flags.remove(PtrFlags::FROZEN);
        }
        self
    }

    /// Set the type fingerprint.
    pub fn with_type_fingerprint(mut self, fp: u32) -> Self {
        self.type_fingerprint = fp & 0x00FF_FFFF;
        self
    }
}

impl Default for PtrMetadata {
    fn default() -> Self {
        Self::region()
    }
}

// ============================================================================
// Stale Reference Error
// ============================================================================

/// Error raised when a stale pointer is dereferenced.
///
/// This corresponds to Blood's `StaleReference` effect.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaleReferenceError {
    /// The generation the pointer expected.
    pub expected: u32,
    /// The actual generation found in the slot.
    pub actual: u32,
    /// The address of the stale pointer.
    pub address: u64,
}

impl fmt::Display for StaleReferenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "stale reference at {:#x}: expected generation {}, found {}",
            self.address, self.expected, self.actual
        )
    }
}

impl std::error::Error for StaleReferenceError {}

// ============================================================================
// Type Fingerprint
// ============================================================================

/// Compute a 24-bit type fingerprint.
///
/// This is used for fast type checks in multiple dispatch and debug assertions.
/// Collision probability: ~1/16M for type pairs.
pub fn compute_type_fingerprint(type_name: &str) -> u32 {
    // Simple FNV-1a hash truncated to 24 bits
    let mut hash: u32 = 0x811c_9dc5;
    for byte in type_name.bytes() {
        hash ^= byte as u32;
        hash = hash.wrapping_mul(0x0100_0193);
    }
    hash & 0x00FF_FFFF
}

// ============================================================================
// Memory Slot
// ============================================================================

/// A memory slot that holds a value with its generation.
///
/// From MEMORY_MODEL.md §1.3:
/// "Every heap allocation carries a generation counter. Pointers store both
/// the address and the expected generation. On dereference, these must match."
#[derive(Debug, Clone)]
pub struct MemorySlot<T> {
    /// The actual value.
    pub value: T,
    /// Current generation counter.
    pub generation: u32,
    /// Metadata about this slot.
    pub metadata: SlotMetadata,
}

impl<T> MemorySlot<T> {
    /// Create a new slot with initial generation.
    pub fn new(value: T) -> Self {
        Self {
            value,
            generation: INITIAL_GENERATION,
            metadata: SlotMetadata::default(),
        }
    }

    /// Increment the generation (for deallocation).
    pub fn increment_generation(&mut self) {
        if self.generation != PERSISTENT_MARKER {
            self.generation = self.generation.wrapping_add(1);
            // Skip 0 (freed marker) and PERSISTENT_MARKER
            if self.generation == FREED_GENERATION || self.generation == PERSISTENT_MARKER {
                self.generation = INITIAL_GENERATION;
            }
        }
    }

    /// Mark as freed.
    pub fn mark_freed(&mut self) {
        self.generation = FREED_GENERATION;
    }

    /// Create a pointer to this slot.
    pub fn make_ptr(&self, address: u64, tier: MemoryTier) -> BloodPtr {
        BloodPtr::new(
            address,
            self.generation,
            PtrMetadata::new(tier, PtrFlags::empty(), 0),
        )
    }
}

/// Metadata for a memory slot.
#[derive(Debug, Clone, Default)]
pub struct SlotMetadata {
    /// Type ID for runtime type checks.
    pub type_id: u32,
    /// Reference count (for Tier 2).
    pub ref_count: u32,
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_blood_ptr_null() {
        let ptr = BloodPtr::null();
        assert!(ptr.is_null());
        assert_eq!(ptr.address, 0);
    }

    #[test]
    fn test_blood_ptr_new() {
        let meta = PtrMetadata::new(MemoryTier::Region, PtrFlags::MUT, 0x123456);
        let ptr = BloodPtr::new(0xDEAD_BEEF, 42, meta);

        assert!(!ptr.is_null());
        assert_eq!(ptr.address, 0xDEAD_BEEF);
        assert_eq!(ptr.generation, 42);
        assert_eq!(ptr.tier(), MemoryTier::Region);
        assert!(ptr.is_mutable());
        assert_eq!(ptr.type_fingerprint(), 0x123456);
    }

    #[test]
    fn test_blood_ptr_validate() {
        let meta = PtrMetadata::region();
        let ptr = BloodPtr::new(0x1000, 42, meta);

        assert!(ptr.validate(42).is_ok());
        assert!(ptr.validate(43).is_err());

        let err = ptr.validate(43).unwrap_err();
        assert_eq!(err.expected, 42);
        assert_eq!(err.actual, 43);
    }

    #[test]
    fn test_blood_ptr_persistent_always_valid() {
        let meta = PtrMetadata::persistent();
        let ptr = BloodPtr::new(0x1000, PERSISTENT_MARKER, meta);

        // Persistent pointers should validate against any generation
        assert!(ptr.validate(1).is_ok());
        assert!(ptr.validate(999).is_ok());
        assert!(ptr.validate(FREED_GENERATION).is_ok());
    }

    #[test]
    fn test_blood_ptr_serialization() {
        let meta = PtrMetadata::new(MemoryTier::Region, PtrFlags::MUT | PtrFlags::LINEAR, 0xABCDEF);
        let ptr = BloodPtr::new(0x1234_5678_9ABC_DEF0, 0xCAFE_BABE, meta);

        let bytes = ptr.to_bytes();
        let restored = BloodPtr::from_bytes(bytes);

        assert_eq!(ptr, restored);
    }

    #[test]
    fn test_memory_tier_needs_check() {
        assert!(!MemoryTier::Stack.needs_generation_check());
        assert!(MemoryTier::Region.needs_generation_check());
        assert!(!MemoryTier::Persistent.needs_generation_check());
    }

    #[test]
    fn test_ptr_metadata_packing() {
        let meta = PtrMetadata::new(MemoryTier::Region, PtrFlags::MUT | PtrFlags::FROZEN, 0x123456);
        let packed = meta.to_u32();
        let unpacked = PtrMetadata::from_u32(packed);

        assert_eq!(meta.tier, unpacked.tier);
        assert_eq!(meta.flags, unpacked.flags);
        assert_eq!(meta.type_fingerprint, unpacked.type_fingerprint);
    }

    #[test]
    fn test_ptr_flags() {
        let flags = PtrFlags::MUT | PtrFlags::LINEAR;
        assert!(flags.contains(PtrFlags::MUT));
        assert!(flags.contains(PtrFlags::LINEAR));
        assert!(!flags.contains(PtrFlags::FROZEN));
        assert!(!flags.contains(PtrFlags::NULLABLE));
    }

    #[test]
    fn test_type_fingerprint() {
        let fp1 = compute_type_fingerprint("i32");
        let fp2 = compute_type_fingerprint("String");
        let fp3 = compute_type_fingerprint("i32");

        // Same type should produce same fingerprint
        assert_eq!(fp1, fp3);
        // Different types should (very likely) produce different fingerprints
        assert_ne!(fp1, fp2);
        // Should be 24 bits max
        assert!(fp1 <= 0x00FF_FFFF);
        assert!(fp2 <= 0x00FF_FFFF);
    }

    #[test]
    fn test_memory_slot() {
        let mut slot: MemorySlot<i32> = MemorySlot::new(42);

        assert_eq!(slot.value, 42);
        assert_eq!(slot.generation, INITIAL_GENERATION);

        // Simulate deallocation
        slot.increment_generation();
        assert_eq!(slot.generation, 2);

        // Test generation wraparound
        slot.generation = u32::MAX - 1;
        slot.increment_generation();
        // Should skip PERSISTENT_MARKER
        assert_eq!(slot.generation, INITIAL_GENERATION);
    }

    #[test]
    fn test_memory_slot_make_ptr() {
        let slot: MemorySlot<i32> = MemorySlot::new(42);
        let ptr = slot.make_ptr(0x1000, MemoryTier::Region);

        assert_eq!(ptr.address, 0x1000);
        assert_eq!(ptr.generation, slot.generation);
        assert_eq!(ptr.tier(), MemoryTier::Region);
    }

    #[test]
    fn test_ptr_metadata_builders() {
        let meta = PtrMetadata::region()
            .with_mut(true)
            .with_linear(true)
            .with_frozen(false)
            .with_type_fingerprint(0xABCDEF);

        assert_eq!(meta.tier, MemoryTier::Region);
        assert!(meta.flags.contains(PtrFlags::MUT));
        assert!(meta.flags.contains(PtrFlags::LINEAR));
        assert!(!meta.flags.contains(PtrFlags::FROZEN));
        assert_eq!(meta.type_fingerprint, 0xABCDEF);
    }

    #[test]
    fn test_stale_reference_error_display() {
        let err = StaleReferenceError {
            expected: 42,
            actual: 43,
            address: 0x1000,
        };
        let msg = format!("{}", err);
        assert!(msg.contains("42"));
        assert!(msg.contains("43"));
        assert!(msg.contains("0x1000"));
    }

    #[test]
    fn test_blood_ptr_display() {
        let ptr = BloodPtr::null();
        assert_eq!(format!("{}", ptr), "null");

        let ptr2 = BloodPtr::new(0x1000, 42, PtrMetadata::region());
        let display = format!("{}", ptr2);
        assert!(display.contains("0x1000"));
        assert!(display.contains("g42"));
    }
}
