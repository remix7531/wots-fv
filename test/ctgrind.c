/* SPDX-License-Identifier: GPL-3.0-or-later
 *
 * wots+fv - WOTS+ (RFC 8391) with formal verification.
 * Copyright (C) 2026 wots+fv contributors.
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program.  If not, see <https://www.gnu.org/licenses/>.
 */

/* Constant-time check for the secret-consuming WOTS+ entry points
   (wotsfv_pkgen and wotsfv_sign) via the ctgrind technique
   (https://github.com/agl/ctgrind).  These are the only API functions
   that read sk_seed; pk_from_sig and verify see only public inputs.

   sk_seed is initialized to a real value, then marked "undefined"
   for valgrind's memcheck.  Any branch or memory address computed
   from those bytes will trip a "Conditional jump or move depends
   on uninitialised value" error, which --error-exitcode=1 promotes
   to a non-zero exit. */

#include <stdint.h>
#include <stdio.h>
#include <string.h>

#include <memcheck.h>

#include "wots.h"

int main(void) {
    uint8_t  sk_seed[WOTSFV_SK_SEED_BYTES];
    uint8_t  pub_seed[WOTSFV_PUB_SEED_BYTES];
    uint8_t  msg[WOTSFV_MSG_BYTES];
    uint8_t  sig[WOTSFV_SIG_BYTES];
    uint8_t  pk[WOTSFV_PK_BYTES];
    uint32_t addr[8];

    memset(pub_seed, 0xA5, sizeof pub_seed);
    memset(msg,      0x5A, sizeof msg);
    memset(sk_seed,  0x42, sizeof sk_seed);

    VALGRIND_MAKE_MEM_UNDEFINED(sk_seed, sizeof sk_seed);

    /* wotsfv_pkgen reads sk_seed. */
    memset(addr, 0, sizeof addr);
    wotsfv_pkgen(pk, sk_seed, pub_seed, addr);

    /* wotsfv_sign reads sk_seed. */
    memset(addr, 0, sizeof addr);
    wotsfv_sign(sig, msg, sk_seed, pub_seed, addr);

    /* Outputs are secret-derived; mark them defined so the sink below
       doesn't itself trigger a use-of-uninit report. */
    VALGRIND_MAKE_MEM_DEFINED(pk,  sizeof pk);
    VALGRIND_MAKE_MEM_DEFINED(sig, sizeof sig);

    /* Keep the calls from being optimized away. */
    volatile uint8_t sink = 0;
    for (size_t i = 0; i < sizeof pk;  i++) sink ^= pk[i];
    for (size_t i = 0; i < sizeof sig; i++) sink ^= sig[i];
    (void)sink;

    return 0;
}
