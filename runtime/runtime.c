// Minimal C runtime stub - real runtime provided by Rust blood-runtime
#include <stdio.h>
#include <stdlib.h>

// Forward declaration - provided by compiled Blood code
extern int blood_main(void);

int main(void) {
    return blood_main();
}
