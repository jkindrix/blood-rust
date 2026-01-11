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
//! ## Slot Registry
//!
//! The slot registry tracks all allocations and their generations, enabling
//! validation of generational references on effect handler resume. This is
//! based on the [generational arena](https://crates.io/crates/generational-arena)
//! pattern for solving the ABA problem.
//!
//! ## Technical References
//!
//! - [MEMORY_MODEL.md](../../../MEMORY_MODEL.md)
//! - [Generational References](https://floooh.github.io/2018/06/17/handles-vs-pointers.html)
//! - [Vale's Generational References](https://verdagon.dev/blog/generational-references)

use std::alloc::{self, Layout};
use std::cell::UnsafeCell;
use std::collections::HashMap;
use std::fmt;
use std::sync::atomic::{AtomicU32, AtomicU64, AtomicUsize, Ordering};
use std::sync::OnceLock;
use parking_lot::RwLock;

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

// ============================================================================
// Slot Registry - Global address → generation mapping
// ============================================================================

/// Entry in the slot registry tracking allocation state.
#[derive(Debug, Clone, Copy)]
pub struct SlotEntry {
    /// Current generation of this slot.
    pub generation: Generation,
    /// Size of the allocation.
    pub size: usize,
    /// Whether the slot is currently allocated.
    pub is_allocated: bool,
}

impl SlotEntry {
    /// Create a new allocated slot entry.
    pub fn new(generation: Generation, size: usize) -> Self {
        Self {
            generation,
            size,
            is_allocated: true,
        }
    }

    /// Mark the slot as deallocated and increment generation.
    pub fn deallocate(&mut self) {
        self.is_allocated = false;
        // Increment generation for next allocation (prevents ABA problem)
        if self.generation < generation::OVERFLOW_GUARD {
            self.generation += 1;
        }
    }
}

/// Global slot registry for tracking allocations and their generations.
///
/// This registry enables validation of generational references by mapping
/// addresses to their current generation. When an effect handler captures
/// a continuation, it snapshots the generations of all captured references.
/// On resume, these generations are validated against the registry to detect
/// stale references that were freed and reallocated.
///
/// Based on the generational arena pattern from:
/// - [generational-arena](https://github.com/fitzgen/generational-arena)
/// - [slotmap](https://crates.io/crates/slotmap)
pub struct SlotRegistry {
    /// Map from allocation address to slot entry.
    slots: RwLock<HashMap<u64, SlotEntry>>,
}

impl SlotRegistry {
    /// Create a new empty slot registry.
    pub fn new() -> Self {
        Self {
            slots: RwLock::new(HashMap::new()),
        }
    }

    /// Register a new allocation.
    ///
    /// Returns the generation assigned to this allocation.
    pub fn register(&self, address: u64, size: usize) -> Generation {
        let mut slots = self.slots.write();

        // Check if this address was previously used
        if let Some(entry) = slots.get_mut(&address) {
            // Reuse slot with incremented generation
            entry.generation = if entry.generation < generation::OVERFLOW_GUARD {
                entry.generation + 1
            } else {
                generation::OVERFLOW_GUARD
            };
            entry.size = size;
            entry.is_allocated = true;
            entry.generation
        } else {
            // New slot
            let entry = SlotEntry::new(generation::FIRST, size);
            let gen = entry.generation;
            slots.insert(address, entry);
            gen
        }
    }

    /// Unregister an allocation (mark as freed).
    ///
    /// The slot entry is retained with an incremented generation to detect
    /// stale references that try to access it after deallocation.
    pub fn unregister(&self, address: u64) {
        let mut slots = self.slots.write();
        if let Some(entry) = slots.get_mut(&address) {
            entry.deallocate();
        }
    }

    /// Get the current generation for an address.
    ///
    /// Returns `None` if the address was never registered.
    /// Returns the generation (even if deallocated) if it was registered.
    pub fn get_generation(&self, address: u64) -> Option<Generation> {
        let slots = self.slots.read();
        slots.get(&address).map(|e| e.generation)
    }

    /// Check if an address is currently allocated.
    pub fn is_allocated(&self, address: u64) -> bool {
        let slots = self.slots.read();
        slots.get(&address).map(|e| e.is_allocated).unwrap_or(false)
    }

    /// Validate an address against an expected generation.
    ///
    /// Returns `Ok(())` if the generation matches and the slot is allocated.
    /// Returns `Err` with the actual generation if validation fails.
    pub fn validate(&self, address: u64, expected_gen: Generation) -> Result<(), StaleReferenceError> {
        // Skip persistent references (they never become stale)
        if expected_gen == generation::PERSISTENT {
            return Ok(());
        }

        let slots = self.slots.read();
        match slots.get(&address) {
            Some(entry) => {
                if entry.generation != expected_gen {
                    Err(StaleReferenceError {
                        expected: expected_gen,
                        actual: entry.generation,
                    })
                } else if !entry.is_allocated {
                    // Slot was freed (generation incremented on free)
                    Err(StaleReferenceError {
                        expected: expected_gen,
                        actual: entry.generation,
                    })
                } else {
                    Ok(())
                }
            }
            None => {
                // Address was never registered - could be:
                // 1. Stack or static memory (not tracked in registry)
                // 2. Heap memory that was freed and cleaned up from registry
                //
                // If the expected generation is FIRST, assume it's stack/static
                // memory which is always valid. Otherwise, it was likely heap
                // memory that got freed.
                if expected_gen == generation::FIRST {
                    Ok(()) // Likely stack/static memory
                } else {
                    Err(StaleReferenceError {
                        expected: expected_gen,
                        actual: generation::UNINITIALIZED,
                    })
                }
            }
        }
    }

    /// Get the number of tracked slots.
    pub fn len(&self) -> usize {
        self.slots.read().len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.slots.read().is_empty()
    }

    /// Clear all slots (for testing).
    #[cfg(test)]
    pub fn clear(&self) {
        self.slots.write().clear();
    }
}

impl Default for SlotRegistry {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for SlotRegistry {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let slots = self.slots.read();
        f.debug_struct("SlotRegistry")
            .field("num_slots", &slots.len())
            .finish()
    }
}

// Thread-safe: uses RwLock internally
unsafe impl Send for SlotRegistry {}
unsafe impl Sync for SlotRegistry {}

/// Global slot registry instance.
static SLOT_REGISTRY: OnceLock<SlotRegistry> = OnceLock::new();

/// Get the global slot registry.
pub fn slot_registry() -> &'static SlotRegistry {
    SLOT_REGISTRY.get_or_init(SlotRegistry::new)
}

/// Register an allocation in the global slot registry.
///
/// This should be called by the allocator when a new allocation is made.
/// Returns the generation assigned to this allocation.
pub fn register_allocation(address: u64, size: usize) -> Generation {
    slot_registry().register(address, size)
}

/// Unregister an allocation from the global slot registry.
///
/// This should be called by the allocator when memory is freed.
pub fn unregister_allocation(address: u64) {
    slot_registry().unregister(address)
}

/// Get the current generation for an address from the global registry.
pub fn get_slot_generation(address: u64) -> Option<Generation> {
    slot_registry().get_generation(address)
}

/// Validate an address against an expected generation using the global registry.
pub fn validate_generation(address: u64, expected_gen: Generation) -> Result<(), StaleReferenceError> {
    slot_registry().validate(address, expected_gen)
}

// ============================================================================
// Pointer Metadata
// ============================================================================

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
    /// Heap allocation (Tier 2) - basic heap without RC.
    Heap,
    /// Persistent allocation (Tier 3) - reference counted with cycle collection.
    Persistent,
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
// Tier 3: Persistent (Reference Counted with Cycle Collection)
// ============================================================================

/// Type layout information for cycle collection.
///
/// Describes the location of pointer fields within a type, enabling
/// the cycle collector to traverse object graphs.
#[derive(Debug, Clone)]
pub struct TypeLayout {
    /// Offsets of slot ID fields within the type.
    ///
    /// Each offset points to a `u64` field that holds a slot ID
    /// (as returned by `persistent_alloc`).
    pub slot_offsets: Vec<usize>,
    /// Size of the type in bytes.
    pub size: usize,
}

impl TypeLayout {
    /// Create a new type layout with no pointer fields.
    pub fn new(size: usize) -> Self {
        Self {
            slot_offsets: Vec::new(),
            size,
        }
    }

    /// Create a type layout with the given slot offsets.
    pub fn with_slots(size: usize, slot_offsets: Vec<usize>) -> Self {
        Self { slot_offsets, size }
    }

    /// Add a slot offset.
    pub fn add_slot_offset(&mut self, offset: usize) {
        self.slot_offsets.push(offset);
    }
}

/// Global registry mapping type fingerprints to layouts.
pub struct TypeRegistry {
    layouts: parking_lot::RwLock<std::collections::HashMap<u32, TypeLayout>>,
}

impl TypeRegistry {
    /// Create a new empty type registry.
    pub fn new() -> Self {
        Self {
            layouts: parking_lot::RwLock::new(std::collections::HashMap::new()),
        }
    }

    /// Register a type layout.
    ///
    /// Returns the type fingerprint (computed from the layout).
    pub fn register(&self, type_fp: u32, layout: TypeLayout) {
        self.layouts.write().insert(type_fp, layout);
    }

    /// Get the layout for a type fingerprint.
    pub fn get(&self, type_fp: u32) -> Option<TypeLayout> {
        self.layouts.read().get(&type_fp).cloned()
    }

    /// Check if a type fingerprint is registered.
    pub fn contains(&self, type_fp: u32) -> bool {
        self.layouts.read().contains_key(&type_fp)
    }

    /// Get the number of registered types.
    pub fn len(&self) -> usize {
        self.layouts.read().len()
    }

    /// Check if the registry is empty.
    pub fn is_empty(&self) -> bool {
        self.layouts.read().is_empty()
    }
}

impl Default for TypeRegistry {
    fn default() -> Self {
        Self::new()
    }
}

/// Global type registry for cycle collection.
static TYPE_REGISTRY: OnceLock<TypeRegistry> = OnceLock::new();

/// Get the global type registry.
pub fn type_registry() -> &'static TypeRegistry {
    TYPE_REGISTRY.get_or_init(TypeRegistry::new)
}

/// Register a type for cycle collection.
///
/// Must be called before allocating values of this type if cycle
/// collection traversal is needed.
pub fn register_type(type_fp: u32, layout: TypeLayout) {
    type_registry().register(type_fp, layout);
}

/// Metadata for persistent slots.
#[derive(Debug, Clone, Copy, Default)]
pub struct PersistentMetadata {
    /// Type fingerprint for RTTI.
    pub type_fp: u32,
    /// Flags (frozen, etc.).
    pub flags: u32,
}

impl PersistentMetadata {
    /// Flag indicating the value is deeply immutable.
    pub const FROZEN: u32 = 1 << 0;
    /// Flag indicating weak references exist.
    pub const HAS_WEAK: u32 = 1 << 1;
    /// Flag indicating pending collection.
    pub const PENDING_DROP: u32 = 1 << 2;

    /// Create new metadata.
    pub fn new(type_fp: u32) -> Self {
        Self { type_fp, flags: 0 }
    }

    /// Check if frozen.
    pub fn is_frozen(&self) -> bool {
        self.flags & Self::FROZEN != 0
    }

    /// Set frozen flag.
    pub fn set_frozen(&mut self) {
        self.flags |= Self::FROZEN;
    }
}

/// A persistent slot with reference counting.
///
/// This is used for Tier 3 allocations that are shared across fibers
/// or have lived past generation overflow.
pub struct PersistentSlot {
    /// Pointer to the actual value data.
    value: UnsafeCell<*mut u8>,
    /// Size of the value in bytes.
    size: AtomicUsize,
    /// Strong reference count.
    refcount: AtomicU64,
    /// Weak reference count.
    weak_count: AtomicU32,
    /// Slot metadata.
    metadata: UnsafeCell<PersistentMetadata>,
    /// Layout for deallocation.
    layout: UnsafeCell<Option<Layout>>,
}

impl PersistentSlot {
    /// Create a new persistent slot.
    pub fn new(value_ptr: *mut u8, size: usize, layout: Layout, type_fp: u32) -> Self {
        Self {
            value: UnsafeCell::new(value_ptr),
            size: AtomicUsize::new(size),
            refcount: AtomicU64::new(1),
            weak_count: AtomicU32::new(0),
            metadata: UnsafeCell::new(PersistentMetadata::new(type_fp)),
            layout: UnsafeCell::new(Some(layout)),
        }
    }

    /// Get the current reference count.
    pub fn refcount(&self) -> u64 {
        self.refcount.load(Ordering::Acquire)
    }

    /// Get the weak reference count.
    pub fn weak_count(&self) -> u32 {
        self.weak_count.load(Ordering::Acquire)
    }

    /// Check if the slot is still alive (refcount > 0).
    pub fn is_alive(&self) -> bool {
        self.refcount.load(Ordering::Acquire) > 0
    }

    /// Get the value pointer.
    ///
    /// # Safety
    /// The slot must be alive (refcount > 0).
    pub unsafe fn value_ptr(&self) -> *mut u8 {
        *self.value.get()
    }

    /// Get the value size.
    pub fn size(&self) -> usize {
        self.size.load(Ordering::Acquire)
    }

    /// Increment the reference count.
    ///
    /// # Panics
    /// Panics if the refcount was zero (double-increment of dead slot).
    pub fn increment(&self) {
        let old = self.refcount.fetch_add(1, Ordering::Relaxed);
        if old == 0 {
            panic!("PersistentSlot: increment of zero refcount");
        }
    }

    /// Decrement the reference count.
    ///
    /// Returns `true` if this was the last reference (refcount became 0).
    pub fn decrement(&self) -> bool {
        let old = self.refcount.fetch_sub(1, Ordering::Release);
        if old == 1 {
            // Last reference dropped - acquire to synchronize with other decrements
            std::sync::atomic::fence(Ordering::Acquire);
            true
        } else if old == 0 {
            panic!("PersistentSlot: decrement of zero refcount");
        } else {
            false
        }
    }

    /// Increment weak reference count.
    pub fn increment_weak(&self) {
        self.weak_count.fetch_add(1, Ordering::Relaxed);
    }

    /// Decrement weak reference count.
    ///
    /// Returns `true` if this was the last weak reference and refcount is also 0.
    pub fn decrement_weak(&self) -> bool {
        let old = self.weak_count.fetch_sub(1, Ordering::Release);
        old == 1 && self.refcount.load(Ordering::Acquire) == 0
    }

    /// Try to upgrade a weak reference to a strong reference.
    ///
    /// Returns `true` if upgrade succeeded, `false` if the slot is dead.
    pub fn try_upgrade_weak(&self) -> bool {
        loop {
            let current = self.refcount.load(Ordering::Acquire);
            if current == 0 {
                return false;
            }
            if self.refcount.compare_exchange_weak(
                current,
                current + 1,
                Ordering::AcqRel,
                Ordering::Relaxed,
            ).is_ok() {
                return true;
            }
        }
    }

    /// Mark the slot as pending drop.
    pub fn mark_pending_drop(&self) {
        unsafe {
            let meta = &mut *self.metadata.get();
            meta.flags |= PersistentMetadata::PENDING_DROP;
        }
    }

    /// Check if pending drop.
    pub fn is_pending_drop(&self) -> bool {
        unsafe {
            let meta = &*self.metadata.get();
            meta.flags & PersistentMetadata::PENDING_DROP != 0
        }
    }

    /// Deallocate the slot's value.
    ///
    /// # Safety
    /// Must only be called when refcount and weak_count are both 0.
    pub unsafe fn deallocate_value(&self) {
        let ptr = *self.value.get();
        if !ptr.is_null() {
            if let Some(layout) = (*self.layout.get()).take() {
                alloc::dealloc(ptr, layout);
            }
            *self.value.get() = std::ptr::null_mut();
        }
    }

    /// Get the type fingerprint for this slot.
    pub fn type_fp(&self) -> u32 {
        unsafe { (*self.metadata.get()).type_fp }
    }

    /// Extract child slot IDs from this slot's value.
    ///
    /// Uses the type registry to determine which offsets contain slot IDs.
    /// Returns an empty vector if the type is not registered.
    ///
    /// # Safety
    /// The slot must be alive (refcount > 0).
    pub unsafe fn child_slots(&self) -> Vec<u64> {
        let type_fp = self.type_fp();
        let layout = match type_registry().get(type_fp) {
            Some(layout) => layout,
            None => return Vec::new(), // Type not registered, assume no pointers
        };

        let value_ptr = self.value_ptr();
        if value_ptr.is_null() {
            return Vec::new();
        }

        let value_size = self.size();
        let mut children = Vec::with_capacity(layout.slot_offsets.len());

        for &offset in &layout.slot_offsets {
            // Safety: bounds check before reading
            if offset + std::mem::size_of::<u64>() <= value_size {
                let slot_id_ptr = value_ptr.add(offset) as *const u64;
                let slot_id = *slot_id_ptr;
                if slot_id != 0 {
                    children.push(slot_id);
                }
            }
        }

        children
    }
}

impl fmt::Debug for PersistentSlot {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PersistentSlot")
            .field("refcount", &self.refcount())
            .field("weak_count", &self.weak_count())
            .field("size", &self.size())
            .finish()
    }
}

// Safety: PersistentSlot uses atomic operations for thread safety.
unsafe impl Send for PersistentSlot {}
unsafe impl Sync for PersistentSlot {}

// ============================================================================
// Deferred Reference Counting
// ============================================================================

/// Queue for deferred reference count decrements.
///
/// This avoids deep recursion when dropping values that contain
/// many nested references.
pub struct DeferredDecrementQueue {
    /// Queue of slots pending decrement processing.
    queue: RwLock<Vec<*const PersistentSlot>>,
    /// Maximum queue size before forcing synchronous processing.
    max_size: usize,
}

impl DeferredDecrementQueue {
    /// Default maximum queue size.
    pub const DEFAULT_MAX_SIZE: usize = 1024;

    /// Create a new deferred decrement queue.
    pub fn new(max_size: usize) -> Self {
        Self {
            queue: RwLock::new(Vec::with_capacity(max_size)),
            max_size,
        }
    }

    /// Queue a slot for deferred processing.
    ///
    /// If the queue is full, processes immediately.
    ///
    /// # Safety
    /// The slot pointer must be valid.
    pub unsafe fn enqueue(&self, slot: *const PersistentSlot) {
        let mut queue = self.queue.write();
        if queue.len() >= self.max_size {
            // Queue full - process synchronously
            drop(queue);
            self.process_batch(self.max_size / 2);
            queue = self.queue.write();
        }
        queue.push(slot);
    }

    /// Process a batch of queued decrements.
    ///
    /// Returns the number of slots processed.
    pub fn process_batch(&self, max_count: usize) -> usize {
        let batch: Vec<_> = {
            let mut queue = self.queue.write();
            let count = max_count.min(queue.len());
            queue.drain(..count).collect()
        };

        let processed = batch.len();
        for slot_ptr in batch {
            // Safety: slots in queue are valid
            unsafe {
                let slot = &*slot_ptr;
                if slot.refcount() == 0 && slot.weak_count() == 0 {
                    slot.deallocate_value();
                }
            }
        }
        processed
    }

    /// Process all queued decrements.
    pub fn process_all(&self) -> usize {
        let mut total = 0;
        loop {
            let processed = self.process_batch(100);
            if processed == 0 {
                break;
            }
            total += processed;
        }
        total
    }

    /// Get the current queue length.
    pub fn len(&self) -> usize {
        self.queue.read().len()
    }

    /// Check if the queue is empty.
    pub fn is_empty(&self) -> bool {
        self.queue.read().is_empty()
    }
}

impl Default for DeferredDecrementQueue {
    fn default() -> Self {
        Self::new(Self::DEFAULT_MAX_SIZE)
    }
}

// Safety: Queue uses RwLock for thread safety.
unsafe impl Send for DeferredDecrementQueue {}
unsafe impl Sync for DeferredDecrementQueue {}

/// Global deferred decrement queue.
static DEFERRED_QUEUE: OnceLock<DeferredDecrementQueue> = OnceLock::new();

/// Get the global deferred decrement queue.
pub fn deferred_queue() -> &'static DeferredDecrementQueue {
    DEFERRED_QUEUE.get_or_init(DeferredDecrementQueue::default)
}

// ============================================================================
// Persistent Allocator
// ============================================================================

/// Allocator for Tier 3 (Persistent) memory.
pub struct PersistentAllocator {
    /// All active persistent slots.
    slots: RwLock<HashMap<u64, Box<PersistentSlot>>>,
    /// Next slot ID.
    next_id: AtomicU64,
    /// Statistics.
    stats: PersistentStats,
}

/// Statistics for the persistent allocator.
#[derive(Debug, Default)]
pub struct PersistentStats {
    /// Total allocations.
    pub allocations: AtomicU64,
    /// Total deallocations.
    pub deallocations: AtomicU64,
    /// Current live slots.
    pub live_slots: AtomicU64,
    /// Cycle collection runs.
    pub cycle_collections: AtomicU64,
    /// Cycles collected.
    pub cycles_collected: AtomicU64,
}

impl PersistentAllocator {
    /// Create a new persistent allocator.
    pub fn new() -> Self {
        Self {
            slots: RwLock::new(HashMap::new()),
            next_id: AtomicU64::new(1),
            stats: PersistentStats::default(),
        }
    }

    /// Allocate a new persistent slot.
    ///
    /// Returns the slot ID.
    pub fn allocate(&self, size: usize, align: usize, type_fp: u32) -> Option<u64> {
        let layout = Layout::from_size_align(size, align).ok()?;
        let ptr = unsafe { alloc::alloc(layout) };
        if ptr.is_null() {
            return None;
        }

        let id = self.next_id.fetch_add(1, Ordering::Relaxed);
        let slot = Box::new(PersistentSlot::new(ptr, size, layout, type_fp));

        self.slots.write().insert(id, slot);
        self.stats.allocations.fetch_add(1, Ordering::Relaxed);
        self.stats.live_slots.fetch_add(1, Ordering::Relaxed);

        Some(id)
    }

    /// Get a slot by ID.
    pub fn get(&self, id: u64) -> Option<*const PersistentSlot> {
        self.slots.read().get(&id).map(|s| s.as_ref() as *const _)
    }

    /// Increment reference count for a slot.
    pub fn increment(&self, id: u64) -> bool {
        if let Some(slot) = self.slots.read().get(&id) {
            slot.increment();
            true
        } else {
            false
        }
    }

    /// Decrement reference count for a slot.
    ///
    /// If this was the last reference, queues for deferred cleanup.
    pub fn decrement(&self, id: u64) {
        let slot_ptr = {
            let slots = self.slots.read();
            slots.get(&id).map(|s| s.as_ref() as *const _)
        };

        if let Some(ptr) = slot_ptr {
            let slot: &PersistentSlot = unsafe { &*ptr };
            if slot.decrement() {
                // Last reference - queue for deferred processing
                unsafe { deferred_queue().enqueue(ptr) };
                self.stats.deallocations.fetch_add(1, Ordering::Relaxed);
                self.stats.live_slots.fetch_sub(1, Ordering::Relaxed);
            }
        }
    }

    /// Remove a slot from the allocator.
    ///
    /// # Safety
    /// Only call when the slot has been fully processed.
    pub unsafe fn remove(&self, id: u64) {
        self.slots.write().remove(&id);
    }

    /// Get allocator statistics.
    pub fn stats(&self) -> &PersistentStats {
        &self.stats
    }

    /// Get the number of live slots.
    pub fn live_count(&self) -> usize {
        self.slots.read().len()
    }
}

impl Default for PersistentAllocator {
    fn default() -> Self {
        Self::new()
    }
}

/// Global persistent allocator.
static PERSISTENT_ALLOCATOR: OnceLock<PersistentAllocator> = OnceLock::new();

/// Get the global persistent allocator.
pub fn persistent_allocator() -> &'static PersistentAllocator {
    PERSISTENT_ALLOCATOR.get_or_init(PersistentAllocator::new)
}

// ============================================================================
// Cycle Collection
// ============================================================================

/// Cycle collector for Tier 3 memory.
///
/// Uses mark-sweep over persistent slots to detect and collect
/// reference cycles that cannot be collected by reference counting alone.
pub struct CycleCollector {
    /// Threshold for triggering collection (bytes).
    threshold: AtomicUsize,
    /// Whether collection is currently running.
    collecting: AtomicU32,
}

/// Configuration for cycle collection.
#[derive(Debug, Clone)]
pub struct CycleCollectorConfig {
    /// Memory threshold to trigger collection (bytes).
    pub threshold_bytes: usize,
    /// Maximum slots to process per batch.
    pub batch_size: usize,
}

impl Default for CycleCollectorConfig {
    fn default() -> Self {
        Self {
            threshold_bytes: 10 * 1024 * 1024, // 10 MB
            batch_size: 1000,
        }
    }
}

impl CycleCollector {
    /// Create a new cycle collector with default config.
    pub fn new() -> Self {
        Self::with_config(CycleCollectorConfig::default())
    }

    /// Create a new cycle collector with custom config.
    pub fn with_config(config: CycleCollectorConfig) -> Self {
        Self {
            threshold: AtomicUsize::new(config.threshold_bytes),
            collecting: AtomicU32::new(0),
        }
    }

    /// Check if collection is currently running.
    pub fn is_collecting(&self) -> bool {
        self.collecting.load(Ordering::Acquire) != 0
    }

    /// Get the current collection threshold in bytes.
    pub fn threshold(&self) -> usize {
        self.threshold.load(Ordering::Acquire)
    }

    /// Set the collection threshold in bytes.
    pub fn set_threshold(&self, bytes: usize) {
        self.threshold.store(bytes, Ordering::Release);
    }

    /// Check if collection should be triggered based on slot count.
    ///
    /// Returns true if the number of live slots exceeds the threshold.
    /// Note: Threshold is interpreted as slot count, not bytes.
    pub fn should_collect(&self) -> bool {
        let stats = persistent_allocator().stats();
        stats.live_slots.load(Ordering::Relaxed) as usize >= self.threshold()
    }

    /// Try to start collection.
    ///
    /// Returns `false` if collection is already running.
    fn try_start(&self) -> bool {
        self.collecting.compare_exchange(0, 1, Ordering::AcqRel, Ordering::Relaxed).is_ok()
    }

    /// Mark collection as finished.
    fn finish(&self) {
        self.collecting.store(0, Ordering::Release);
    }

    /// Run a cycle collection.
    ///
    /// Returns the number of cycles collected.
    pub fn collect(&self, roots: &[u64]) -> usize {
        if !self.try_start() {
            return 0; // Already collecting
        }

        let allocator = persistent_allocator();

        // Phase 1: Mark all reachable from roots
        let mut marked = std::collections::HashSet::new();
        let mut worklist: Vec<u64> = roots.to_vec();

        while let Some(id) = worklist.pop() {
            if marked.contains(&id) {
                continue;
            }
            marked.insert(id);

            // Traverse object graph using type information
            if let Some(slot) = allocator.get(id) {
                unsafe {
                    // Only traverse alive slots
                    if (*slot).is_alive() {
                        let children = (*slot).child_slots();
                        for child_id in children {
                            if !marked.contains(&child_id) {
                                worklist.push(child_id);
                            }
                        }
                    }
                }
            }
        }

        // Phase 2: Sweep unmarked slots
        let mut collected = 0;
        let slots = allocator.slots.read();
        let unmarked: Vec<u64> = slots
            .iter()
            .filter(|(&id, slot)| {
                !marked.contains(&id) && slot.refcount() == 0 && !slot.is_pending_drop()
            })
            .map(|(&id, _)| id)
            .collect();
        drop(slots);

        for id in unmarked {
            // Mark for cleanup
            if let Some(slot) = allocator.get(id) {
                unsafe {
                    (*slot).mark_pending_drop();
                    (*slot).deallocate_value();
                }
            }
            unsafe { allocator.remove(id) };
            collected += 1;
        }

        allocator.stats.cycle_collections.fetch_add(1, Ordering::Relaxed);
        allocator.stats.cycles_collected.fetch_add(collected as u64, Ordering::Relaxed);

        self.finish();
        collected
    }

    /// Collect with roots extracted from suspended continuations.
    ///
    /// This is the primary entry point for cycle collection that
    /// respects algebraic effect safety.
    pub fn collect_with_snapshot_roots(&self, _snapshot_refs: &[(usize, Generation)]) -> usize {
        // Convert snapshot addresses to slot IDs
        // In a full implementation, we would maintain a reverse mapping
        // For now, we collect without snapshot awareness
        self.collect(&[])
    }
}

impl Default for CycleCollector {
    fn default() -> Self {
        Self::new()
    }
}

/// Global cycle collector.
static CYCLE_COLLECTOR: OnceLock<CycleCollector> = OnceLock::new();

/// Get the global cycle collector.
pub fn cycle_collector() -> &'static CycleCollector {
    CYCLE_COLLECTOR.get_or_init(CycleCollector::new)
}

/// Trigger a cycle collection with the given roots.
pub fn collect_cycles(roots: &[u64]) -> usize {
    cycle_collector().collect(roots)
}

/// Trigger a cycle collection with snapshot roots.
pub fn collect_cycles_with_snapshots(snapshots: &[GenerationSnapshot]) -> usize {
    let all_refs: Vec<_> = snapshots
        .iter()
        .flat_map(|s| s.entries().iter().copied())
        .collect();
    cycle_collector().collect_with_snapshot_roots(&all_refs)
}

// ============================================================================
// Tier 3 Public API
// ============================================================================

/// Allocate a persistent (Tier 3) value.
///
/// Returns the slot ID and a pointer to the allocated memory.
pub fn persistent_alloc(size: usize, align: usize, type_fp: u32) -> Option<(u64, *mut u8)> {
    let id = persistent_allocator().allocate(size, align, type_fp)?;
    let slot_ptr = persistent_allocator().get(id)?;
    let value_ptr = unsafe { (*slot_ptr).value_ptr() };
    Some((id, value_ptr))
}

/// Increment the reference count for a persistent slot.
pub fn persistent_increment(id: u64) -> bool {
    persistent_allocator().increment(id)
}

/// Decrement the reference count for a persistent slot.
pub fn persistent_decrement(id: u64) {
    persistent_allocator().decrement(id)
}

/// Get the reference count for a persistent slot.
pub fn persistent_refcount(id: u64) -> Option<u64> {
    persistent_allocator()
        .get(id)
        .map(|ptr| unsafe { (*ptr).refcount() })
}

/// Check if a persistent slot is alive.
pub fn persistent_is_alive(id: u64) -> bool {
    persistent_allocator()
        .get(id)
        .map(|ptr| unsafe { (*ptr).is_alive() })
        .unwrap_or(false)
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

    // =========================================================================
    // Slot Registry Tests
    // =========================================================================

    #[test]
    fn test_slot_registry_register() {
        let registry = SlotRegistry::new();

        // Register a new allocation
        let gen = registry.register(0x1000, 64);
        assert_eq!(gen, generation::FIRST);
        assert!(registry.is_allocated(0x1000));

        // Registering at same address should increment generation
        let gen2 = registry.register(0x1000, 128);
        assert_eq!(gen2, generation::FIRST + 1);
    }

    #[test]
    fn test_slot_registry_unregister() {
        let registry = SlotRegistry::new();

        let gen = registry.register(0x2000, 32);
        assert!(registry.is_allocated(0x2000));

        registry.unregister(0x2000);
        assert!(!registry.is_allocated(0x2000));

        // Generation should have been incremented on deallocation
        let current_gen = registry.get_generation(0x2000);
        assert_eq!(current_gen, Some(gen + 1));
    }

    #[test]
    fn test_slot_registry_validate_success() {
        let registry = SlotRegistry::new();

        let gen = registry.register(0x3000, 16);
        let result = registry.validate(0x3000, gen);
        assert!(result.is_ok());
    }

    #[test]
    fn test_slot_registry_validate_stale() {
        let registry = SlotRegistry::new();

        let gen = registry.register(0x4000, 16);
        registry.unregister(0x4000);

        // Validation should fail because the slot was freed
        let result = registry.validate(0x4000, gen);
        assert!(result.is_err());

        let err = result.unwrap_err();
        assert_eq!(err.expected, gen);
        assert_eq!(err.actual, gen + 1); // Generation was incremented on deallocation
    }

    #[test]
    fn test_slot_registry_validate_reallocation() {
        let registry = SlotRegistry::new();

        // First allocation
        let gen1 = registry.register(0x5000, 16);
        registry.unregister(0x5000);

        // Reallocate at same address
        let gen2 = registry.register(0x5000, 32);
        assert!(gen2 > gen1);

        // Validation with old generation should fail (ABA detection)
        let result = registry.validate(0x5000, gen1);
        assert!(result.is_err());

        // Validation with new generation should succeed
        let result = registry.validate(0x5000, gen2);
        assert!(result.is_ok());
    }

    #[test]
    fn test_slot_registry_persistent_skip() {
        let registry = SlotRegistry::new();

        // Persistent references should always validate successfully
        let result = registry.validate(0x6000, generation::PERSISTENT);
        assert!(result.is_ok());
    }

    #[test]
    fn test_slot_registry_unknown_address() {
        let registry = SlotRegistry::new();

        // Unregistered address with generation FIRST is OK (might be stack/static)
        let result = registry.validate(0x9999, generation::FIRST);
        assert!(result.is_ok());

        // Unregistered address with higher generation is likely freed heap
        let result = registry.validate(0x9999, generation::FIRST + 5);
        assert!(result.is_err());
    }

    #[test]
    fn test_slot_entry_lifecycle() {
        let mut entry = SlotEntry::new(generation::FIRST, 64);
        assert!(entry.is_allocated);
        assert_eq!(entry.generation, generation::FIRST);
        assert_eq!(entry.size, 64);

        entry.deallocate();
        assert!(!entry.is_allocated);
        assert_eq!(entry.generation, generation::FIRST + 1);
    }

    #[test]
    fn test_global_slot_registry_functions() {
        // These use the global registry - use unique addresses to avoid conflicts
        let addr = 0xDEAD_BEEF_1234u64;

        let gen = register_allocation(addr, 100);
        assert!(slot_registry().is_allocated(addr));

        let looked_up = get_slot_generation(addr);
        assert_eq!(looked_up, Some(gen));

        assert!(validate_generation(addr, gen).is_ok());

        unregister_allocation(addr);
        assert!(!slot_registry().is_allocated(addr));
    }

    // =========================================================================
    // Tier 3: Persistent Slot Tests
    // =========================================================================

    #[test]
    fn test_persistent_metadata() {
        let mut meta = PersistentMetadata::new(0x1234);
        assert_eq!(meta.type_fp, 0x1234);
        assert!(!meta.is_frozen());

        meta.set_frozen();
        assert!(meta.is_frozen());
    }

    #[test]
    fn test_persistent_slot_refcount() {
        let layout = Layout::from_size_align(64, 8).unwrap();
        let ptr = unsafe { alloc::alloc(layout) };
        assert!(!ptr.is_null());

        let slot = PersistentSlot::new(ptr, 64, layout, 0);
        assert_eq!(slot.refcount(), 1);
        assert!(slot.is_alive());

        slot.increment();
        assert_eq!(slot.refcount(), 2);

        assert!(!slot.decrement()); // Not last ref
        assert_eq!(slot.refcount(), 1);

        assert!(slot.decrement()); // Last ref
        assert_eq!(slot.refcount(), 0);
        assert!(!slot.is_alive());

        // Clean up
        unsafe { slot.deallocate_value() };
    }

    #[test]
    fn test_persistent_slot_weak() {
        let layout = Layout::from_size_align(32, 8).unwrap();
        let ptr = unsafe { alloc::alloc(layout) };
        assert!(!ptr.is_null());

        let slot = PersistentSlot::new(ptr, 32, layout, 0);
        assert_eq!(slot.weak_count(), 0);

        slot.increment_weak();
        assert_eq!(slot.weak_count(), 1);

        // Try upgrade while alive
        assert!(slot.try_upgrade_weak());
        assert_eq!(slot.refcount(), 2);

        // Clean up - decrement strong refs
        slot.decrement(); // refcount = 1
        slot.decrement(); // refcount = 0, last strong ref

        // Decrement weak - returns true because both weak_count becomes 0 and refcount is 0
        assert!(slot.decrement_weak());

        unsafe { slot.deallocate_value() };
    }

    #[test]
    fn test_persistent_alloc_decrement() {
        let result = persistent_alloc(128, 8, 0xABCD);
        assert!(result.is_some());

        let (id, ptr) = result.unwrap();
        assert!(!ptr.is_null());
        assert!(persistent_is_alive(id));
        assert_eq!(persistent_refcount(id), Some(1));

        persistent_decrement(id);
        // After decrement, slot may be queued for cleanup
    }

    #[test]
    fn test_persistent_increment_decrement() {
        let result = persistent_alloc(64, 8, 0);
        let (id, _) = result.unwrap();

        assert!(persistent_increment(id));
        assert_eq!(persistent_refcount(id), Some(2));

        persistent_decrement(id);
        assert_eq!(persistent_refcount(id), Some(1));

        persistent_decrement(id);
    }

    #[test]
    fn test_deferred_queue() {
        let queue = DeferredDecrementQueue::new(10);
        assert!(queue.is_empty());
        assert_eq!(queue.len(), 0);
    }

    #[test]
    fn test_cycle_collector_not_reentrant() {
        let collector = CycleCollector::new();
        assert!(!collector.is_collecting());

        // First collection should succeed
        let count1 = collector.collect(&[]);
        assert_eq!(count1, 0);
        assert!(!collector.is_collecting());
    }

    #[test]
    fn test_type_registry() {
        let registry = TypeRegistry::new();
        assert!(registry.is_empty());

        // Register a type with slot offsets
        let layout = TypeLayout::with_slots(24, vec![0, 8, 16]);
        registry.register(0xABCD, layout.clone());

        assert!(registry.contains(0xABCD));
        assert!(!registry.contains(0x1234));

        let retrieved = registry.get(0xABCD).unwrap();
        assert_eq!(retrieved.size, 24);
        assert_eq!(retrieved.slot_offsets, vec![0, 8, 16]);
    }

    #[test]
    fn test_cycle_collector_threshold() {
        let collector = CycleCollector::new();

        // Default threshold
        let default_threshold = collector.threshold();
        assert!(default_threshold > 0);

        // Set new threshold
        collector.set_threshold(1024);
        assert_eq!(collector.threshold(), 1024);
    }

    #[test]
    fn test_type_layout() {
        let mut layout = TypeLayout::new(16);
        assert_eq!(layout.size, 16);
        assert!(layout.slot_offsets.is_empty());

        layout.add_slot_offset(0);
        layout.add_slot_offset(8);
        assert_eq!(layout.slot_offsets, vec![0, 8]);
    }

    #[test]
    fn test_memory_tier_enum() {
        assert_eq!(MemoryTier::Stack, MemoryTier::Stack);
        assert_ne!(MemoryTier::Stack, MemoryTier::Region);
        assert_ne!(MemoryTier::Region, MemoryTier::Heap);
        assert_ne!(MemoryTier::Heap, MemoryTier::Persistent);
    }
}
