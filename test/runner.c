/* SPDX-License-Identifier: GPL-3.0-or-later
 *
 * wots+fv - WOTS+ (RFC 8391) with formal verification.
 * Copyright (C) 2026 wots+fv contributors.
 */

/* Test harness for wots+fv.

   Reads N vectors from stdin (produced by test/gen_vectors), re-runs
   each with src/wots.c, and byte-compares pk + sig against the
   upstream xmss-reference output.  Also runs SHA-256 KATs (including
   NIST CAVS vectors from test/vectors/) and WOTS+ self-consistency /
   tamper checks.

   Section drivers live in test/sha256.c and test/wots.c;
   shared helpers in test/common.c. */

#include "wots.h"

#include <stdio.h>

/* Section drivers, defined in their respective TUs. */
int run_sha256_tests(void);
int run_wots_tests(void);
int run_wots_vector_xcheck(void);

int main(void) {
    (void)printf("wots+fv v%d.%d.%d (XMSS OID 0x%08x)\n",
                 WOTSFV_VERSION_MAJOR, WOTSFV_VERSION_MINOR, WOTSFV_VERSION_PATCH,
                 (unsigned)WOTSFV_OID);

    int failures = 0;
    failures += run_sha256_tests();
    failures += run_wots_tests();
    failures += run_wots_vector_xcheck();

    if (failures) {
        (void)printf("%d test(s) FAILED\n", failures);
        return 1;
    }
    (void)printf("all tests passed\n");
    return 0;
}
