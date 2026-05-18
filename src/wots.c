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

/* RFC 8391 WOTS+ with XMSS-SHA2_10_256 parameters.
   Public API in wots.h, threat model in SECURITY.md. */

#include "wots.h"
#include "sha256.h"
#include "util.h"

/* RFC 8391 §3.1.1 / §5.3 parameters. */
#define N           32
#define W           16
#define LEN1        64
#define LEN2        3
#define LEN         67          /* LEN1 + LEN2 */
#define PAD         32          /* padding_len for SHA2-256 WOTS+ */
#define ADDR_BYTES  32          /* serialized ADRS length */

/* ADRS slot indices (RFC 8391 §2.5). */
#define ADRS_OTS_ADDR  4
#define ADRS_CHAIN     5
#define ADRS_HASH      6
#define ADRS_KEYMSK    7

_Static_assert(WOTSFV_SK_SEED_BYTES  == N,        "sk_seed == n");
_Static_assert(WOTSFV_PUB_SEED_BYTES == N,        "pub_seed == n");
_Static_assert(WOTSFV_MSG_BYTES      == N,        "msg == n");
_Static_assert(WOTSFV_PK_BYTES       == LEN * N,  "pk == len*n");
_Static_assert(WOTSFV_SIG_BYTES      == LEN * N,  "sig == len*n");

/* Serialize 8 big-endian uint32 ADRS words to 32 bytes. */
static void addr_bytes(uint8_t out[ADDR_BYTES], const uint32_t a[8]) {
    for (unsigned i = 0; i < 8; i++) {
        out[(4*i) + 0] = (uint8_t)(a[i] >> 24);
        out[(4*i) + 1] = (uint8_t)(a[i] >> 16);
        out[(4*i) + 2] = (uint8_t)(a[i] >>  8);
        out[(4*i) + 3] = (uint8_t)(a[i]);
    }
}

/* PRF(key, in) = SHA256(toByte(3, 32) || key || in).  RFC 8391 §5.1. */
static void prf(uint8_t out[N], const uint8_t in[ADDR_BYTES], const uint8_t key[N]) {
    uint8_t buf[PAD + N + ADDR_BYTES];
    wotsfv_memset(buf, 0, PAD);
    buf[PAD - 1] = 3;
    wotsfv_memcpy(buf + PAD,     key, N);
    wotsfv_memcpy(buf + PAD + N, in,  ADDR_BYTES);
    wotsfv_sha256(out, buf, sizeof buf);
}

/* PRF_keygen(key, in) = SHA256(toByte(4, 32) || key || in).
   RFC 8391 §10.1.1; in = pub_seed || ADRS. */
static void prf_keygen(uint8_t out[N],
                       const uint8_t in[N + ADDR_BYTES],
                       const uint8_t key[N]) {
    uint8_t buf[PAD + (2 * N) + ADDR_BYTES];
    wotsfv_memset(buf, 0, PAD);
    buf[PAD - 1] = 4;
    wotsfv_memcpy(buf + PAD,     key, N);
    wotsfv_memcpy(buf + PAD + N, in,  N + ADDR_BYTES);
    wotsfv_sha256(out, buf, sizeof buf);
}

/* Tweakable hash F(KEY, M) = SHA256(toByte(0, 32) || KEY || (M XOR mask)),
   with KEY = PRF(pub_seed, ADRS|keymask=0) and
        mask = PRF(pub_seed, ADRS|keymask=1).
   Reads addr[0..6]; writes addr[ADRS_KEYMSK]. */
static void thash_f(uint8_t out[N], const uint8_t in[N],
                    const uint8_t pub_seed[N], uint32_t addr[8]) {
    uint8_t buf[PAD + (2 * N)];
    uint8_t ab[ADDR_BYTES];
    uint8_t mask[N];

    wotsfv_memset(buf, 0, PAD);

    addr[ADRS_KEYMSK] = 0;
    addr_bytes(ab, addr);
    prf(buf + PAD, ab, pub_seed);

    addr[ADRS_KEYMSK] = 1;
    addr_bytes(ab, addr);
    prf(mask, ab, pub_seed);

    for (unsigned i = 0; i < N; i++) {
        buf[PAD + N + i] = in[i] ^ mask[i];
    }
    wotsfv_sha256(out, buf, sizeof buf);
}

/* sk_i = PRF_keygen(sk_seed, pub_seed || ADRS) with ADRS.chain = i.
   Reads addr[0..4]; writes addr[ADRS_CHAIN..ADRS_KEYMSK]. */
static void derive_sk(uint8_t out[N], unsigned chain_i,
                      const uint8_t sk_seed[N],
                      const uint8_t pub_seed[N],
                      uint32_t addr[8]) {
    addr[ADRS_CHAIN]  = (uint32_t)chain_i;
    addr[ADRS_HASH]   = 0;
    addr[ADRS_KEYMSK] = 0;
    uint8_t in[N + ADDR_BYTES];
    wotsfv_memcpy(in, pub_seed, N);
    addr_bytes(in + N, addr);
    prf_keygen(out, in, sk_seed);
}

/* RFC 8391 Algorithm 2 (chaining): F iterated `steps` times.
   Reads addr[0..ADRS_CHAIN]; writes addr[ADRS_HASH..ADRS_KEYMSK]. */
static void chain(uint8_t buf[N], unsigned start, unsigned steps,
                  const uint8_t pub_seed[N], uint32_t addr[8]) {
    for (unsigned i = 0; i < steps; i++) {
        addr[ADRS_HASH] = (uint32_t)(start + i);
        thash_f(buf, buf, pub_seed, addr);
    }
}

/* Expand msg into LEN base-w digits: 64 nibbles + 3-nibble checksum.
   csum <= LEN1 * (W-1) = 960 < 2^12, so it fits in LEN2 nibbles. */
static void expand_digits(uint8_t digits[LEN], const uint8_t msg[N]) {
    for (unsigned i = 0; i < N; i++) {
        digits[(2*i) + 0] = (uint8_t)(msg[i] >> 4);
        digits[(2*i) + 1] = (uint8_t)(msg[i] & 0x0f);
    }
    uint32_t csum = 0;
    for (unsigned i = 0; i < LEN1; i++) {
        csum += (uint32_t)(W - 1 - digits[i]);
    }
    digits[LEN1 + 0] = (uint8_t)((csum >> 8) & 0x0f);
    digits[LEN1 + 1] = (uint8_t)((csum >> 4) & 0x0f);
    digits[LEN1 + 2] = (uint8_t)((csum >> 0) & 0x0f);
}

void wotsfv_pkgen(uint8_t       *restrict pk,
                  const uint8_t *restrict sk_seed,
                  const uint8_t *restrict pub_seed,
                  uint32_t                addr[restrict 8]) {
    WOTSFV_ASSERT(pk);
    WOTSFV_ASSERT(sk_seed);
    WOTSFV_ASSERT(pub_seed);
    WOTSFV_ASSERT(addr);
    for (unsigned i = 0; i < LEN; i++) {
        derive_sk(pk + ((size_t)i * N), i, sk_seed, pub_seed, addr);
        chain(pk + ((size_t)i * N), 0, W - 1, pub_seed, addr);
    }
}

void wotsfv_sign(uint8_t       *restrict sig,
                 const uint8_t *restrict msg,
                 const uint8_t *restrict sk_seed,
                 const uint8_t *restrict pub_seed,
                 uint32_t                addr[restrict 8]) {
    WOTSFV_ASSERT(sig);
    WOTSFV_ASSERT(msg);
    WOTSFV_ASSERT(sk_seed);
    WOTSFV_ASSERT(pub_seed);
    WOTSFV_ASSERT(addr);
    uint8_t digits[LEN];
    expand_digits(digits, msg);
    for (unsigned i = 0; i < LEN; i++) {
        derive_sk(sig + ((size_t)i * N), i, sk_seed, pub_seed, addr);
        chain(sig + ((size_t)i * N), 0, digits[i], pub_seed, addr);
    }
}

void wotsfv_pk_from_sig(uint8_t       *restrict pk_cand,
                        const uint8_t *restrict sig,
                        const uint8_t *restrict msg,
                        const uint8_t *restrict pub_seed,
                        uint32_t                addr[restrict 8]) {
    WOTSFV_ASSERT(pk_cand);
    WOTSFV_ASSERT(sig);
    WOTSFV_ASSERT(msg);
    WOTSFV_ASSERT(pub_seed);
    WOTSFV_ASSERT(addr);
    uint8_t digits[LEN];
    expand_digits(digits, msg);
    for (unsigned i = 0; i < LEN; i++) {
        wotsfv_memcpy(pk_cand + ((size_t)i * N), sig + ((size_t)i * N), N);
        addr[ADRS_CHAIN]  = (uint32_t)i;
        addr[ADRS_HASH]   = 0;
        addr[ADRS_KEYMSK] = 0;
        chain(pk_cand + ((size_t)i * N), digits[i], W - 1 - digits[i], pub_seed, addr);
    }
}

int wotsfv_verify(const uint8_t *restrict pk,
                  const uint8_t *restrict sig,
                  const uint8_t *restrict msg,
                  const uint8_t *restrict pub_seed,
                  uint32_t                addr[restrict 8]) {
    WOTSFV_ASSERT(pk);
    WOTSFV_ASSERT(sig);
    WOTSFV_ASSERT(msg);
    WOTSFV_ASSERT(pub_seed);
    WOTSFV_ASSERT(addr);
    uint8_t pk_cand[WOTSFV_PK_BYTES];
    wotsfv_pk_from_sig(pk_cand, sig, msg, pub_seed, addr);
    return (wotsfv_ct_memcmp(pk_cand, pk, WOTSFV_PK_BYTES) == 0)
               ? WOTSFV_OK
               : WOTSFV_VERIFY_FAILED;
}
