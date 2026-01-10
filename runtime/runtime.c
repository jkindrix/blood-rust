// Blood Runtime Library - C Implementation
// Compile with: cc -c runtime.c -o runtime.o
//
// For full runtime features (fibers, channels, effects), use the Rust
// blood-runtime crate:
//   cargo build --release -p blood-runtime
//   Link with: -lblood_runtime

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

// ============================================================================
// I/O Functions
// ============================================================================

void print_int(int32_t n) {
    printf("%d", n);
    fflush(stdout);
}

void println_int(int32_t n) {
    printf("%d\n", n);
}

void print_i64(int64_t n) {
    printf("%ld", n);
    fflush(stdout);
}

void println_i64(int64_t n) {
    printf("%ld\n", n);
}

void print_str(const char* s) {
    if (s) printf("%s", s);
    fflush(stdout);
}

void println_str(const char* s) {
    if (s) printf("%s\n", s);
}

void print_char(int32_t c) {
    printf("%c", (char)c);
    fflush(stdout);
}

void println(void) {
    printf("\n");
}

// ============================================================================
// Memory Management (with generational reference support)
// ============================================================================

int blood_alloc(size_t size, uint64_t* out_addr, uint64_t* out_gen_meta) {
    if (!out_addr || !out_gen_meta) return -1;
    void* ptr = malloc(size);
    if (!ptr) {
        fprintf(stderr, "blood: out of memory\n");
        return -3;
    }
    *out_addr = (uint64_t)ptr;
    *out_gen_meta = ((uint64_t)1 << 32) | 2; // gen=1, metadata=REGION
    return 0;
}

// Simple allocation returning pointer directly (for backward compatibility)
void* blood_alloc_simple(size_t size) {
    void* ptr = malloc(size);
    if (ptr == NULL) {
        fprintf(stderr, "blood: out of memory\n");
        exit(1);
    }
    return ptr;
}

void* blood_realloc(void* ptr, size_t size) {
    void* new_ptr = realloc(ptr, size);
    if (new_ptr == NULL && size > 0) {
        fprintf(stderr, "blood: out of memory\n");
        exit(1);
    }
    return new_ptr;
}

void blood_free(uint64_t addr, size_t size) {
    (void)size; // unused in simple implementation
    if (addr) free((void*)addr);
}

// Simple free for backward compatibility
void blood_free_simple(void* ptr) {
    free(ptr);
}

int blood_check_generation(uint32_t expected, uint32_t actual) {
    if (expected == UINT32_MAX) return 1; // PERSISTENT always valid
    return expected == actual ? 1 : 0;
}

uint32_t blood_get_generation(uint64_t addr) {
    (void)addr;
    return 1; // Simple: always return first generation
}

// ============================================================================
// String Functions
// ============================================================================

// Concatenate two strings, returning a newly allocated string
char* blood_str_concat(const char* a, const char* b) {
    size_t len_a = strlen(a);
    size_t len_b = strlen(b);
    char* result = (char*)blood_alloc_simple(len_a + len_b + 1);
    memcpy(result, a, len_a);
    memcpy(result + len_a, b, len_b + 1);
    return result;
}

// Convert integer to string
char* blood_int_to_str(int32_t n) {
    char buffer[32];
    snprintf(buffer, sizeof(buffer), "%d", n);
    char* result = (char*)blood_alloc_simple(strlen(buffer) + 1);
    strcpy(result, buffer);
    return result;
}

// ============================================================================
// Effect Runtime
// ============================================================================

// Handler operation function pointer type
typedef int64_t (*EffectOpFn)(void* evidence, int64_t* args, size_t arg_count);

// Handler entry structure
typedef struct {
    uint64_t effect_id;      // Effect type identifier
    uint64_t handler_id;     // Unique handler instance ID
    EffectOpFn* operations;  // Array of operation function pointers
    size_t op_count;         // Number of operations
    void* state;             // Handler state (for stateful handlers)
} HandlerEntry;

// Evidence vector structure (stack-like)
typedef struct {
    HandlerEntry* handlers;  // Stack of handler entries
    size_t len;
    size_t capacity;
} EvidenceVector;

// Global evidence vector for current thread (thread-local in production)
static EvidenceVector* g_current_evidence = NULL;

void* blood_evidence_create(void) {
    EvidenceVector* ev = (EvidenceVector*)malloc(sizeof(EvidenceVector));
    if (!ev) return NULL;
    ev->handlers = (HandlerEntry*)malloc(16 * sizeof(HandlerEntry));
    if (!ev->handlers) {
        free(ev);
        return NULL;
    }
    ev->len = 0;
    ev->capacity = 16;
    // Set as current evidence
    g_current_evidence = ev;
    return ev;
}

void blood_evidence_destroy(void* handle) {
    if (!handle) return;
    EvidenceVector* ev = (EvidenceVector*)handle;
    // Clean up handler entries
    for (size_t i = 0; i < ev->len; i++) {
        if (ev->handlers[i].operations) {
            free(ev->handlers[i].operations);
        }
    }
    free(ev->handlers);
    free(ev);
    if (g_current_evidence == ev) {
        g_current_evidence = NULL;
    }
}

void blood_evidence_push(void* handle, uint64_t handler_id) {
    if (!handle) return;
    EvidenceVector* ev = (EvidenceVector*)handle;
    if (ev->len >= ev->capacity) {
        size_t new_cap = ev->capacity * 2;
        HandlerEntry* new_handlers = (HandlerEntry*)realloc(
            ev->handlers, new_cap * sizeof(HandlerEntry)
        );
        if (!new_handlers) return;
        ev->handlers = new_handlers;
        ev->capacity = new_cap;
    }
    // Initialize handler entry
    HandlerEntry* entry = &ev->handlers[ev->len++];
    entry->effect_id = 0;  // Will be set by blood_evidence_register
    entry->handler_id = handler_id;
    entry->operations = NULL;
    entry->op_count = 0;
    entry->state = NULL;
}

uint64_t blood_evidence_pop(void* handle) {
    if (!handle) return 0;
    EvidenceVector* ev = (EvidenceVector*)handle;
    if (ev->len == 0) return 0;
    HandlerEntry* entry = &ev->handlers[--ev->len];
    if (entry->operations) {
        free(entry->operations);
        entry->operations = NULL;
    }
    return entry->handler_id;
}

uint64_t blood_evidence_get(void* handle, size_t index) {
    if (!handle) return 0;
    EvidenceVector* ev = (EvidenceVector*)handle;
    if (index >= ev->len) return 0;
    return ev->handlers[index].handler_id;
}

// Register handler operations for an effect
void blood_evidence_register(void* handle, uint64_t effect_id,
                             EffectOpFn* operations, size_t op_count) {
    if (!handle) return;
    EvidenceVector* ev = (EvidenceVector*)handle;
    if (ev->len == 0) return;

    HandlerEntry* entry = &ev->handlers[ev->len - 1];
    entry->effect_id = effect_id;
    entry->operations = (EffectOpFn*)malloc(op_count * sizeof(EffectOpFn));
    if (entry->operations) {
        for (size_t i = 0; i < op_count; i++) {
            entry->operations[i] = operations[i];
        }
        entry->op_count = op_count;
    }
}

// Set handler state
void blood_evidence_set_state(void* handle, void* state) {
    if (!handle) return;
    EvidenceVector* ev = (EvidenceVector*)handle;
    if (ev->len == 0) return;
    ev->handlers[ev->len - 1].state = state;
}

// Get handler state
void* blood_evidence_get_state(void* handle, size_t index) {
    if (!handle) return NULL;
    EvidenceVector* ev = (EvidenceVector*)handle;
    if (index >= ev->len) return NULL;
    return ev->handlers[index].state;
}

// Get current evidence vector (for perform operations)
void* blood_evidence_current(void) {
    return g_current_evidence;
}

// Find handler for effect and perform operation
// Returns 0 on success, -1 if handler not found
int64_t blood_perform(uint64_t effect_id, uint32_t op_index,
                      int64_t* args, size_t arg_count) {
    if (!g_current_evidence) {
        fprintf(stderr, "BLOOD RUNTIME ERROR: No evidence vector for perform\n");
        return -1;
    }

    EvidenceVector* ev = g_current_evidence;

    // Search from top of stack (most recent handler first)
    for (size_t i = ev->len; i > 0; i--) {
        HandlerEntry* entry = &ev->handlers[i - 1];
        if (entry->effect_id == effect_id) {
            if (op_index < entry->op_count && entry->operations[op_index]) {
                return entry->operations[op_index](entry, args, arg_count);
            }
            fprintf(stderr, "BLOOD RUNTIME ERROR: Operation %u not found for effect %lu\n",
                    op_index, effect_id);
            return -1;
        }
    }

    fprintf(stderr, "BLOOD RUNTIME ERROR: Handler not found for effect %lu\n", effect_id);
    return -1;
}

// Get handler depth for effect (for tail-resumptive optimization)
size_t blood_handler_depth(uint64_t effect_id) {
    if (!g_current_evidence) return 0;

    EvidenceVector* ev = g_current_evidence;
    for (size_t i = ev->len; i > 0; i--) {
        if (ev->handlers[i - 1].effect_id == effect_id) {
            return i - 1;
        }
    }
    return 0;
}

// ============================================================================
// Multiple Dispatch Runtime
// ============================================================================

// Simple dispatch table implementation.
// In production, this would use a hash table for O(1) lookup.
// For now, we use a linear search through registered entries.

typedef struct {
    uint64_t method_slot;
    uint64_t type_tag;
    void* impl_ptr;
} DispatchEntry;

#define MAX_DISPATCH_ENTRIES 1024
static DispatchEntry g_dispatch_table[MAX_DISPATCH_ENTRIES];
static size_t g_dispatch_count = 0;

// Register an implementation for a method/type combination
void blood_dispatch_register(uint64_t method_slot, uint64_t type_tag, void* impl_ptr) {
    if (g_dispatch_count >= MAX_DISPATCH_ENTRIES) {
        fprintf(stderr, "BLOOD RUNTIME ERROR: Dispatch table full\n");
        abort();
    }
    g_dispatch_table[g_dispatch_count].method_slot = method_slot;
    g_dispatch_table[g_dispatch_count].type_tag = type_tag;
    g_dispatch_table[g_dispatch_count].impl_ptr = impl_ptr;
    g_dispatch_count++;
}

// Look up an implementation for a method given the receiver's type
void* blood_dispatch_lookup(uint64_t method_slot, uint64_t type_tag) {
    // Linear search - in production, use a hash table
    for (size_t i = 0; i < g_dispatch_count; i++) {
        if (g_dispatch_table[i].method_slot == method_slot &&
            g_dispatch_table[i].type_tag == type_tag) {
            return g_dispatch_table[i].impl_ptr;
        }
    }
    fprintf(stderr, "BLOOD RUNTIME ERROR: No implementation found for method %lu with type %lu\n",
            (unsigned long)method_slot, (unsigned long)type_tag);
    abort();
    return NULL;
}

// Get the runtime type tag from an object's header.
// Objects with RTTI have a type tag in their first 8 bytes.
// For simple types without headers, returns 0.
uint64_t blood_get_type_tag(void* obj) {
    if (obj == NULL) return 0;
    // In a full implementation, this would read from the object's header.
    // For now, return the pointer cast as the "type" - callers should
    // use proper type tags when registering implementations.
    return (uint64_t)(uintptr_t)obj;
}

// ============================================================================
// Fiber Support (Stubs - not supported in minimal runtime)
// ============================================================================

uint64_t blood_fiber_create(void) {
    static uint64_t next_id = 1;
    return next_id++;
}

uint64_t blood_fiber_suspend(void) {
    return 0;
}

void blood_fiber_resume(uint64_t fiber, uint64_t value) {
    (void)fiber; (void)value;
}

// ============================================================================
// Error Handling
// ============================================================================

void blood_stale_reference_panic(uint32_t expected, uint32_t actual) {
    fprintf(stderr, "BLOOD RUNTIME ERROR: Stale reference detected!\n");
    fprintf(stderr, "Expected generation: %u, Actual: %u\n", expected, actual);
    fprintf(stderr, "This indicates use-after-free. Aborting.\n");
    abort();
}

void blood_panic(const char* msg) {
    fprintf(stderr, "BLOOD RUNTIME PANIC: %s\n", msg ? msg : "unknown error");
    abort();
}

// ============================================================================
// Runtime Lifecycle
// ============================================================================

int blood_runtime_init(void) {
    return 0;
}

void blood_runtime_shutdown(void) {
    // Nothing to do in minimal runtime
}

// ============================================================================
// Entry Point
// ============================================================================

// The Blood main function
extern void blood_main(void);

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
    blood_runtime_init();
    blood_main();
    blood_runtime_shutdown();
    return 0;
}
