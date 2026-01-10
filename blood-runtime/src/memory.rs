//! # Memory Management
//!
//! Memory allocation and management for the Blood runtime.
//!
//! ## Design
//!
//! Based on the Blood memory model (MEMORY_MODEL.md):
//! - Tier 0: Stack allocation (fastest)
//! - Tier 1: Region allocation (scoped)
//! - Tier 2: Persistent heap (longest-lived)
//! - Generational references for safety
//!
//! ## Technical References
//!
//! - [MEMORY_MODEL.md](../../../MEMORY_MODEL.md)
//! - [Generational References](https://floooh.github.io/2018/06/17/handles-vs-pointers.html)

use std::alloc::{self, Layout};
use std::cell::UnsafeCell;
use std::fmt;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};

/// Generation counter for detecting stale references.
pub type Generation = u32;

/// Reserved generation values.
pub mod generation {
    use super::Generation;

    /// Uninitialized slot.
    pub const UNINITIALIZED: Generation = 0;
    /// First valid generation.
    pub const FIRST: Generation = 1;
    /// Overflow guard value (triggers tier promotion).
    pub const OVERFLOW_GUARD: Generation = u32::MAX - 1;
    /// Persistent marker (never collected).
    pub const PERSISTENT: Generation = u32::MAX;
}

/// Error when accessing a stale reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct StaleReferenceError {
    /// Expected generation.
    pub expected: Generation,
    /// Actual generation.
    pub actual: Generation,
}

impl fmt::Display for StaleReferenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "stale reference: expected generation {}, found {}",
            self.expected, self.actual
        )
    }
}

impl std::error::Error for StaleReferenceError {}

/// Pointer metadata flags.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PointerMetadata(u32);

impl PointerMetadata {
    /// No special flags.
    pub const NONE: Self = Self(0);
    /// Pointer is to stack memory.
    pub const STACK: Self = Self(1 << 0);
    /// Pointer is to region memory.
    pub const REGION: Self = Self(1 << 1);
    /// Pointer is to heap memory.
    pub const HEAP: Self = Self(1 << 2);
    /// Pointer is linear (must be used exactly once).
    pub const LINEAR: Self = Self(1 << 3);
    /// Pointer is weak (may become null).
    pub const WEAK: Self = Self(1 << 4);

    /// Create from raw bits.
    pub const fn from_bits(bits: u32) -> Self {
        Self(bits)
    }

    /// Get raw bits.
    pub const fn bits(&self) -> u32 {
        self.0
    }

    /// Union of two metadata values.
    pub const fn union(self, other: Self) -> Self {
        Self(self.0 | other.0)
    }

    /// Check if a flag is set.
    pub const fn contains(&self, other: Self) -> bool {
        (self.0 & other.0) == other.0
    }
}

/// A 128-bit generational pointer (BloodPtr).
///
/// Layout:
/// - Bits 0-63: Address
/// - Bits 64-95: Generation (32 bits)
/// - Bits 96-127: Metadata (32 bits)
#[repr(C, align(16))]
#[derive(Clone, Copy)]
pub struct BloodPtr {
    /// Raw address.
    address: usize,
    /// Generation counter.
    generation: Generation,
    /// Pointer metadata.
    metadata: PointerMetadata,
}

impl BloodPtr {
    /// Create a null pointer.
    pub const fn null() -> Self {
        Self {
            address: 0,
            generation: generation::UNINITIALIZED,
            metadata: PointerMetadata::NONE,
        }
    }

    /// Create a new pointer.
    pub const fn new(address: usize, generation: Generation, metadata: PointerMetadata) -> Self {
        Self {
            address,
            generation,
            metadata,
        }
    }

    /// Check if the pointer is null.
    pub const fn is_null(&self) -> bool {
        self.address == 0
    }

    /// Get the raw address.
    pub const fn address(&self) -> usize {
        self.address
    }

    /// Get the generation.
    pub const fn generation(&self) -> Generation {
        self.generation
    }

    /// Get the metadata.
    pub const fn metadata(&self) -> PointerMetadata {
        self.metadata
    }

    /// Check if this is a stack pointer.
    pub const fn is_stack(&self) -> bool {
        self.metadata.contains(PointerMetadata::STACK)
    }

    /// Check if this is a region pointer.
    pub const fn is_region(&self) -> bool {
        self.metadata.contains(PointerMetadata::REGION)
    }

    /// Check if this is a heap pointer.
    pub const fn is_heap(&self) -> bool {
        self.metadata.contains(PointerMetadata::HEAP)
    }

    /// Check if this is a linear pointer.
    pub const fn is_linear(&self) -> bool {
        self.metadata.contains(PointerMetadata::LINEAR)
    }

    /// Check if this is a weak pointer.
    pub const fn is_weak(&self) -> bool {
        self.metadata.contains(PointerMetadata::WEAK)
    }
}

impl fmt::Debug for BloodPtr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("BloodPtr")
            .field("address", &format_args!("{:#x}", self.address))
            .field("generation", &self.generation)
            .field("metadata", &self.metadata)
            .finish()
    }
}

impl PartialEq for BloodPtr {
    fn eq(&self, other: &Self) -> bool {
        self.address == other.address && self.generation == other.generation
    }
}

impl Eq for BloodPtr {}

/// A memory slot with generation tracking.
pub struct Slot {
    /// Current generation (incremented on each reuse).
    generation: AtomicU32,
    /// Whether the slot is occupied.
    occupied: AtomicU32,
    /// Pointer to the actual data.
    data: UnsafeCell<*mut u8>,
    /// Size of the allocated data.
    size: AtomicUsize,
}

impl Slot {
    /// Create a new empty slot.
    pub fn new() -> Self {
        Self {
            generation: AtomicU32::new(generation::FIRST),
            occupied: AtomicU32::new(0),
            data: UnsafeCell::new(std::ptr::null_mut()),
            size: AtomicUsize::new(0),
        }
    }

    /// Get the current generation.
    pub fn generation(&self) -> Generation {
        self.generation.load(Ordering::Acquire)
    }

    /// Check if the slot is occupied.
    pub fn is_occupied(&self) -> bool {
        self.occupied.load(Ordering::Acquire) != 0
    }

    /// Allocate data in this slot.
    ///
    /// # Safety
    ///
    /// The slot must not be currently occupied.
    pub unsafe fn allocate(&self, layout: Layout) -> *mut u8 {
        debug_assert!(!self.is_occupied());

        let ptr = alloc::alloc(layout);
        if ptr.is_null() {
            return ptr;
        }

        *self.data.get() = ptr;
        self.size.store(layout.size(), Ordering::Release);
        self.occupied.store(1, Ordering::Release);

        ptr
    }

    /// Deallocate the data in this slot.
    ///
    /// # Safety
    ///
    /// The slot must be currently occupied.
    pub unsafe fn deallocate(&self) {
        debug_assert!(self.is_occupied());

        let ptr = *self.data.get();
        let size = self.size.load(Ordering::Acquire);

        if !ptr.is_null() && size > 0 {
            let layout = Layout::from_size_align_unchecked(size, 1);
            alloc::dealloc(ptr, layout);
        }

        *self.data.get() = std::ptr::null_mut();
        self.size.store(0, Ordering::Release);
        self.occupied.store(0, Ordering::Release);

        // Increment generation for next use
        let mut gen = self.generation.load(Ordering::Acquire);
        if gen >= generation::OVERFLOW_GUARD {
            // Would overflow, mark as needing tier promotion
            gen = generation::OVERFLOW_GUARD;
        } else {
            gen += 1;
        }
        self.generation.store(gen, Ordering::Release);
    }

    /// Validate a generation matches.
    pub fn validate(&self, expected_gen: Generation) -> Result<(), StaleReferenceError> {
        let actual = self.generation.load(Ordering::Acquire);
        if actual != expected_gen {
            Err(StaleReferenceError {
                expected: expected_gen,
                actual,
            })
        } else {
            Ok(())
        }
    }
}

impl Default for Slot {
    fn default() -> Self {
        Self::new()
    }
}

// Safety: Slot uses atomic operations for thread safety.
unsafe impl Send for Slot {}
unsafe impl Sync for Slot {}

/// Memory tier for allocation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MemoryTier {
    /// Stack allocation (Tier 0).
    Stack,
    /// Region allocation (Tier 1).
    Region,
    /// Heap allocation (Tier 2).
    Heap,
}

/// Region identifier.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct RegionId(pub u64);

impl RegionId {
    /// Get the raw ID value.
    pub fn as_u64(&self) -> u64 {
        self.0
    }
}

/// Global region ID counter.
static NEXT_REGION_ID: AtomicU64 = AtomicU64::new(1);

/// Generate a new unique region ID.
pub fn next_region_id() -> RegionId {
    RegionId(NEXT_REGION_ID.fetch_add(1, Ordering::Relaxed))
}

/// A memory region for scoped allocation.
pub struct Region {
    /// Region ID.
    id: RegionId,
    /// Memory buffer.
    buffer: Vec<u8>,
    /// Current allocation offset.
    offset: AtomicUsize,
    /// Maximum size.
    max_size: usize,
    /// Whether the region is closed for new allocations.
    closed: AtomicU32,
}

impl Region {
    /// Create a new region with the given initial and maximum sizes.
    pub fn new(initial_size: usize, max_size: usize) -> Self {
        Self {
            id: next_region_id(),
            buffer: vec![0u8; initial_size],
            offset: AtomicUsize::new(0),
            max_size,
            closed: AtomicU32::new(0),
        }
    }

    /// Get the region ID.
    pub fn id(&self) -> RegionId {
        self.id
    }

    /// Get the current used size.
    pub fn used(&self) -> usize {
        self.offset.load(Ordering::Acquire)
    }

    /// Get the current capacity.
    pub fn capacity(&self) -> usize {
        self.buffer.len()
    }

    /// Get the maximum size.
    pub fn max_size(&self) -> usize {
        self.max_size
    }

    /// Check if the region is closed.
    pub fn is_closed(&self) -> bool {
        self.closed.load(Ordering::Acquire) != 0
    }

    /// Close the region for new allocations.
    pub fn close(&self) {
        self.closed.store(1, Ordering::Release);
    }

    /// Allocate memory from the region.
    pub fn allocate(&mut self, size: usize, align: usize) -> Option<*mut u8> {
        if self.is_closed() {
            return None;
        }

        let offset = self.offset.load(Ordering::Acquire);
        let aligned_offset = (offset + align - 1) & !(align - 1);
        let new_offset = aligned_offset + size;

        if new_offset > self.buffer.len() {
            // Try to grow
            if new_offset > self.max_size {
                return None;
            }
            let new_capacity = (new_offset * 2).min(self.max_size);
            self.buffer.resize(new_capacity, 0);
        }

        self.offset.store(new_offset, Ordering::Release);
        Some(unsafe { self.buffer.as_mut_ptr().add(aligned_offset) })
    }

    /// Reset the region, freeing all allocations.
    pub fn reset(&mut self) {
        self.offset.store(0, Ordering::Release);
        self.closed.store(0, Ordering::Release);
    }
}

impl fmt::Debug for Region {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Region")
            .field("id", &self.id)
            .field("used", &self.used())
            .field("capacity", &self.capacity())
            .field("max_size", &self.max_size)
            .field("closed", &self.is_closed())
            .finish()
    }
}

/// Generation snapshot for continuation capture.
#[derive(Debug, Clone)]
pub struct GenerationSnapshot {
    /// Captured (address, generation) pairs.
    entries: Vec<(usize, Generation)>,
}

impl GenerationSnapshot {
    /// Create a new empty snapshot.
    pub fn new() -> Self {
        Self { entries: Vec::new() }
    }

    /// Create a snapshot from a list of pointers.
    pub fn capture(pointers: &[BloodPtr]) -> Self {
        let entries = pointers
            .iter()
            .filter(|p| !p.is_null())
            .map(|p| (p.address(), p.generation()))
            .collect();
        Self { entries }
    }

    /// Add a pointer to the snapshot.
    pub fn add(&mut self, ptr: &BloodPtr) {
        if !ptr.is_null() {
            self.entries.push((ptr.address(), ptr.generation()));
        }
    }

    /// Get the number of entries.
    pub fn len(&self) -> usize {
        self.entries.len()
    }

    /// Check if the snapshot is empty.
    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// Validate all references in the snapshot.
    ///
    /// Returns the first stale reference error, if any.
    pub fn validate<F>(&self, get_slot: F) -> Result<(), StaleReferenceError>
    where
        F: Fn(usize) -> Option<Generation>,
    {
        for (addr, expected_gen) in &self.entries {
            if let Some(actual_gen) = get_slot(*addr) {
                if actual_gen != *expected_gen {
                    return Err(StaleReferenceError {
                        expected: *expected_gen,
                        actual: actual_gen,
                    });
                }
            } else {
                // Slot no longer exists
                return Err(StaleReferenceError {
                    expected: *expected_gen,
                    actual: generation::UNINITIALIZED,
                });
            }
        }
        Ok(())
    }

    /// Get the entries.
    pub fn entries(&self) -> &[(usize, Generation)] {
        &self.entries
    }
}

impl Default for GenerationSnapshot {
    fn default() -> Self {
        Self::new()
    }
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
        assert_eq!(ptr.address(), 0);
        assert_eq!(ptr.generation(), generation::UNINITIALIZED);
    }

    #[test]
    fn test_blood_ptr_new() {
        let ptr = BloodPtr::new(0x1000, 42, PointerMetadata::HEAP);
        assert!(!ptr.is_null());
        assert_eq!(ptr.address(), 0x1000);
        assert_eq!(ptr.generation(), 42);
        assert!(ptr.is_heap());
        assert!(!ptr.is_stack());
    }

    #[test]
    fn test_pointer_metadata() {
        let meta = PointerMetadata::STACK.union(PointerMetadata::LINEAR);
        assert!(meta.contains(PointerMetadata::STACK));
        assert!(meta.contains(PointerMetadata::LINEAR));
        assert!(!meta.contains(PointerMetadata::HEAP));
    }

    #[test]
    fn test_slot_lifecycle() {
        let slot = Slot::new();
        assert_eq!(slot.generation(), generation::FIRST);
        assert!(!slot.is_occupied());

        unsafe {
            let layout = Layout::from_size_align(64, 8).unwrap();
            let ptr = slot.allocate(layout);
            assert!(!ptr.is_null());
            assert!(slot.is_occupied());

            slot.deallocate();
            assert!(!slot.is_occupied());
            assert_eq!(slot.generation(), generation::FIRST + 1);
        }
    }

    #[test]
    fn test_slot_validation() {
        let slot = Slot::new();
        assert!(slot.validate(generation::FIRST).is_ok());
        assert!(slot.validate(generation::FIRST + 1).is_err());
    }

    #[test]
    fn test_region_allocation() {
        let mut region = Region::new(1024, 4096);
        assert_eq!(region.used(), 0);

        let ptr1 = region.allocate(100, 8).unwrap();
        assert!(!ptr1.is_null());
        assert!(region.used() >= 100);

        let ptr2 = region.allocate(200, 8).unwrap();
        assert!(!ptr2.is_null());
        assert!(region.used() >= 300);
    }

    #[test]
    fn test_region_reset() {
        let mut region = Region::new(1024, 4096);
        region.allocate(500, 8).unwrap();
        assert!(region.used() >= 500);

        region.reset();
        assert_eq!(region.used(), 0);
    }

    #[test]
    fn test_region_close() {
        let mut region = Region::new(1024, 4096);
        assert!(!region.is_closed());

        region.close();
        assert!(region.is_closed());
        assert!(region.allocate(100, 8).is_none());
    }

    #[test]
    fn test_generation_snapshot() {
        let ptrs = vec![
            BloodPtr::new(0x1000, 1, PointerMetadata::HEAP),
            BloodPtr::new(0x2000, 2, PointerMetadata::HEAP),
            BloodPtr::null(),
        ];

        let snapshot = GenerationSnapshot::capture(&ptrs);
        assert_eq!(snapshot.len(), 2); // Null is excluded

        // Validate with matching generations
        let result = snapshot.validate(|addr| {
            match addr {
                0x1000 => Some(1),
                0x2000 => Some(2),
                _ => None,
            }
        });
        assert!(result.is_ok());

        // Validate with mismatched generation
        let result = snapshot.validate(|addr| {
            match addr {
                0x1000 => Some(1),
                0x2000 => Some(99), // Wrong generation
                _ => None,
            }
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_stale_reference_error() {
        let err = StaleReferenceError {
            expected: 5,
            actual: 10,
        };
        let msg = err.to_string();
        assert!(msg.contains("5"));
        assert!(msg.contains("10"));
    }

    #[test]
    fn test_region_id() {
        let id1 = next_region_id();
        let id2 = next_region_id();
        assert_ne!(id1, id2);
    }
}
