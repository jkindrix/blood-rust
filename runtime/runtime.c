// Blood Runtime Library - Phase 1
// Provides basic I/O and memory functions for Blood programs
//
// Compile with: cc -c runtime.c -o runtime.o
// Link with Blood object files: cc blood_program.o runtime.o -o blood_program

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

// ============================================================
// I/O Functions
// ============================================================

void print_int(int32_t n) {
    printf("%d", n);
}

void println_int(int32_t n) {
    printf("%d\n", n);
}

void print_str(const char* s) {
    printf("%s", s);
}

void println_str(const char* s) {
    printf("%s\n", s);
}

void print_char(int32_t c) {
    printf("%c", (char)c);
}

void println(void) {
    printf("\n");
}

// ============================================================
// Memory Functions
// ============================================================

void* blood_alloc(size_t size) {
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

void blood_free(void* ptr) {
    free(ptr);
}

// ============================================================
// String Functions
// ============================================================

// Concatenate two strings, returning a newly allocated string
char* blood_str_concat(const char* a, const char* b) {
    size_t len_a = strlen(a);
    size_t len_b = strlen(b);
    char* result = (char*)blood_alloc(len_a + len_b + 1);
    memcpy(result, a, len_a);
    memcpy(result + len_a, b, len_b + 1);
    return result;
}

// Convert integer to string
char* blood_int_to_str(int32_t n) {
    char buffer[32];
    snprintf(buffer, sizeof(buffer), "%d", n);
    char* result = (char*)blood_alloc(strlen(buffer) + 1);
    strcpy(result, buffer);
    return result;
}

// ============================================================
// Entry Point
// ============================================================

// The Blood main function
extern void blood_main(void);

int main(int argc, char** argv) {
    (void)argc;
    (void)argv;
    blood_main();
    return 0;
}
