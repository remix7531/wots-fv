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

/* WOTS+ test-vector generator.  Links against the upstream xmss-reference
   static library (packaged by .nix/xmss-reference.nix) and OpenSSL.

   Usage:  gen_vectors <N>
   Reads 128 * N random bytes from /dev/urandom, for each record
   (sk_seed[32] || pub_seed[32] || msg[32] || addr[32]) computes pk and
   sig with the reference WOTS+ implementation for OID 0x00000001
   (XMSS-SHA2_10_256), and writes the record + outputs to stdout:

       input[128] || pk[2144] || sig[2144]   per vector

   Total output = N * 4416 bytes.  Consumer is test/main (our impl). */

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#include <xmss-reference/params.h>
#include <xmss-reference/wots.h>

#define N_BYTES   32
#define WLEN      67
#define SIG_BYTES (WLEN * N_BYTES)
#define PK_BYTES  (WLEN * N_BYTES)

static int read_exact(FILE *f, void *buf, size_t n) {
    return fread(buf, 1, n, f) == n ? 0 : -1;
}
static int write_exact(FILE *f, const void *buf, size_t n) {
    return fwrite(buf, 1, n, f) == n ? 0 : -1;
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s <N>\n", argv[0]);
        return 2;
    }
    long n_vectors = strtol(argv[1], NULL, 10);
    if (n_vectors <= 0) {
        fprintf(stderr, "%s: N must be > 0\n", argv[0]);
        return 2;
    }

    xmss_params params;
    if (xmss_parse_oid(&params, 0x00000001u) != 0) {
        fprintf(stderr, "%s: xmss_parse_oid failed\n", argv[0]);
        return 3;
    }

    FILE *rng = fopen("/dev/urandom", "rb");
    if (!rng) { perror("/dev/urandom"); return 4; }

    unsigned char input[128];
    unsigned char pk[PK_BYTES], sig[SIG_BYTES];

    for (long i = 0; i < n_vectors; i++) {
        if (read_exact(rng, input, sizeof input)) {
            fprintf(stderr, "%s: /dev/urandom short read\n", argv[0]);
            fclose(rng); return 5;
        }

        const unsigned char *sk_seed  = input + 0;
        const unsigned char *pub_seed = input + 32;
        const unsigned char *msg      = input + 64;
        const unsigned char *addr_bytes = input + 96;

        uint32_t addr_pk[8], addr_sig[8];
        for (int k = 0; k < 8; k++) {
            uint32_t v =
                ((uint32_t)addr_bytes[4*k+0] << 24) |
                ((uint32_t)addr_bytes[4*k+1] << 16) |
                ((uint32_t)addr_bytes[4*k+2] <<  8) |
                ((uint32_t)addr_bytes[4*k+3]);
            addr_pk[k] = v;
            addr_sig[k] = v;
        }

        wots_pkgen(&params, pk,  sk_seed, pub_seed, addr_pk);
        wots_sign (&params, sig, msg, sk_seed, pub_seed, addr_sig);

        if (write_exact(stdout, input, sizeof input) ||
            write_exact(stdout, pk, sizeof pk)       ||
            write_exact(stdout, sig, sizeof sig)) {
            fprintf(stderr, "%s: stdout write failed\n", argv[0]);
            fclose(rng); return 6;
        }
    }

    fclose(rng);
    return 0;
}
