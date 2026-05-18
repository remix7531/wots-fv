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

#ifndef WOTSFV_H
#define WOTSFV_H

#include <stdint.h>

/* WOTS+ (RFC 8391 §3.1), parameter set XMSS-SHA2_10_256
   (XMSS OID 0x00000001).  See SECURITY.md for the threat model.

   WOTS+ is a one-time signature scheme: every (sk_seed, pub_seed,
   addr) triple may sign at most one message. */

#define WOTSFV_VERSION_MAJOR  0
#define WOTSFV_VERSION_MINOR  2
#define WOTSFV_VERSION_PATCH  0

#define WOTSFV_OID            0x00000001u

#define WOTSFV_SK_SEED_BYTES   32
#define WOTSFV_PUB_SEED_BYTES  32
#define WOTSFV_MSG_BYTES       32
#define WOTSFV_PK_BYTES        2144   /* 67 * 32 */
#define WOTSFV_SIG_BYTES       2144   /* 67 * 32 */

/* RFC 8391 §2.5 ADRS: 8 big-endian 32-bit words.  The chain,
   hash and key-and-mask slots (indices 5..7) are scratch and
   are clobbered by every API call below.

   Spelled as a raw [restrict 8] in the function signatures (rather
   than via this typedef) so the no-alias guarantee actually binds
   to the parameter. */
typedef uint32_t wotsfv_addr[8];

enum wotsfv_result {
    WOTSFV_OK            =  0,
    WOTSFV_VERIFY_FAILED = -1,
};

/* Common preconditions for all four functions:
     - all pointers non-NULL,
     - each buffer is at least the byte count shown in its trailing
       parameter comment,
     - input/output buffers do not overlap,
     - addr's slots 5..7 are clobbered. */

/* RFC 8391 Algorithm 4 (WOTS_genPK). */
void wotsfv_pkgen(uint8_t        *restrict pk        /* WOTSFV_PK_BYTES        */,
                  const uint8_t  *restrict sk_seed   /* WOTSFV_SK_SEED_BYTES   */,
                  const uint8_t  *restrict pub_seed  /* WOTSFV_PUB_SEED_BYTES  */,
                  uint32_t                 addr[restrict 8]);

/* RFC 8391 Algorithm 5 (WOTS_sign). */
void wotsfv_sign(uint8_t        *restrict sig        /* WOTSFV_SIG_BYTES       */,
                 const uint8_t  *restrict msg        /* WOTSFV_MSG_BYTES       */,
                 const uint8_t  *restrict sk_seed    /* WOTSFV_SK_SEED_BYTES   */,
                 const uint8_t  *restrict pub_seed   /* WOTSFV_PUB_SEED_BYTES  */,
                 uint32_t                 addr[restrict 8]);

/* RFC 8391 Algorithm 6 (WOTS_pkFromSig).  Prefer wotsfv_verify for
   verification: it returns a single ok/fail rather than a buffer. */
void wotsfv_pk_from_sig(uint8_t        *restrict pk_cand   /* WOTSFV_PK_BYTES       */,
                        const uint8_t  *restrict sig       /* WOTSFV_SIG_BYTES      */,
                        const uint8_t  *restrict msg       /* WOTSFV_MSG_BYTES      */,
                        const uint8_t  *restrict pub_seed  /* WOTSFV_PUB_SEED_BYTES */,
                        uint32_t                 addr[restrict 8]);

/* WOTS+ signature verification.
   Returns WOTSFV_OK or WOTSFV_VERIFY_FAILED. */
int wotsfv_verify(const uint8_t  *restrict pk        /* WOTSFV_PK_BYTES        */,
                  const uint8_t  *restrict sig       /* WOTSFV_SIG_BYTES       */,
                  const uint8_t  *restrict msg       /* WOTSFV_MSG_BYTES       */,
                  const uint8_t  *restrict pub_seed  /* WOTSFV_PUB_SEED_BYTES  */,
                  uint32_t                 addr[restrict 8]);

#endif
