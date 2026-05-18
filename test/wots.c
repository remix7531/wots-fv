/* SPDX-License-Identifier: GPL-3.0-or-later
 *
 * wots+fv - WOTS+ (RFC 8391) with formal verification.
 * Copyright (C) 2026 wots+fv contributors.
 */

#include "common.h"
#include "wots.h"

#include <stdio.h>
#include <string.h>

/* ---------- Self-consistency ---------- */

static enum test_status test_wots_self_roundtrip(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    const uint8_t *sk_seed  = input +  0;
    const uint8_t *pub_seed = input + 32;
    const uint8_t *msg      = input + 64;

    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  sk_seed, pub_seed, a0);
    wotsfv_sign (sig, msg, sk_seed, pub_seed, a1);
    return wotsfv_verify(pk, sig, msg, pub_seed, a2) == WOTSFV_OK ? T_OK : T_FAIL;
}

/* All-zero msg: every digit is 0; checksum hits its maximum (960). */
static enum test_status test_wots_msg_all_zero(void) {
    uint8_t sk_seed[32];
    uint8_t pub_seed[32];
    uint8_t msg[32] = {0};
    if (fill_random(sk_seed, 32) || fill_random(pub_seed, 32)) { return T_ERROR; }
    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    zero_addr(a0); zero_addr(a1); zero_addr(a2);
    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  sk_seed, pub_seed, a0);
    wotsfv_sign (sig, msg, sk_seed, pub_seed, a1);
    return wotsfv_verify(pk, sig, msg, pub_seed, a2) == WOTSFV_OK ? T_OK : T_FAIL;
}

/* All-0xff msg: every digit is 15; checksum is 0. */
static enum test_status test_wots_msg_all_ff(void) {
    uint8_t sk_seed[32];
    uint8_t pub_seed[32];
    uint8_t msg[32];
    memset(msg, 0xff, 32);
    if (fill_random(sk_seed, 32) || fill_random(pub_seed, 32)) { return T_ERROR; }
    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    zero_addr(a0); zero_addr(a1); zero_addr(a2);
    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  sk_seed, pub_seed, a0);
    wotsfv_sign (sig, msg, sk_seed, pub_seed, a1);
    return wotsfv_verify(pk, sig, msg, pub_seed, a2) == WOTSFV_OK ? T_OK : T_FAIL;
}

/* Two signatures over the same (key, msg) must be byte-identical. */
static enum test_status test_wots_addr_reuse(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    const uint8_t *sk_seed  = input +  0;
    const uint8_t *pub_seed = input + 32;
    const uint8_t *msg      = input + 64;

    wotsfv_addr a;
    wotsfv_addr b;
    unpack_addr(a, input + 96);
    unpack_addr(b, input + 96);

    uint8_t sig_a[WOTSFV_SIG_BYTES];
    uint8_t sig_b[WOTSFV_SIG_BYTES];
    wotsfv_sign(sig_a, msg, sk_seed, pub_seed, a);
    wotsfv_sign(sig_b, msg, sk_seed, pub_seed, b);
    return memcmp(sig_a, sig_b, WOTSFV_SIG_BYTES) == 0 ? T_OK : T_FAIL;
}

/* ---------- Tamper checks ---------- */

static enum test_status test_wots_tamper_sig(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  input + 0, input + 32, a0);
    wotsfv_sign (sig, input + 64, input + 0, input + 32, a1);
    sig[1234] ^= 0x10;
    return wotsfv_verify(pk, sig, input + 64, input + 32, a2) != WOTSFV_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_tamper_pk(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  input + 0, input + 32, a0);
    wotsfv_sign (sig, input + 64, input + 0, input + 32, a1);
    pk[0] ^= 0x01;
    return wotsfv_verify(pk, sig, input + 64, input + 32, a2) != WOTSFV_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_tamper_pub_seed(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  input + 0, input + 32, a0);
    wotsfv_sign (sig, input + 64, input + 0, input + 32, a1);
    uint8_t bad_pub_seed[32];
    memcpy(bad_pub_seed, input + 32, 32);
    bad_pub_seed[7] ^= 0x80;
    return wotsfv_verify(pk, sig, input + 64, bad_pub_seed, a2) != WOTSFV_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_wrong_addr(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    wotsfv_addr a_sign;
    wotsfv_addr a_ver;
    wotsfv_addr a_pk;
    unpack_addr(a_sign, input + 96);
    unpack_addr(a_pk,   input + 96);
    unpack_addr(a_ver,  input + 96);
    a_ver[4] ^= 1;

    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  input + 0, input + 32, a_pk);
    wotsfv_sign (sig, input + 64, input + 0, input + 32, a_sign);
    return wotsfv_verify(pk, sig, input + 64, input + 32, a_ver) != WOTSFV_OK ? T_OK : T_FAIL;
}

static enum test_status test_wots_tamper_msg(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) { return T_ERROR; }
    const uint8_t *sk_seed  = input +  0;
    const uint8_t *pub_seed = input + 32;
    uint8_t *msg            = input + 64;

    wotsfv_addr a0;
    wotsfv_addr a1;
    wotsfv_addr a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTSFV_PK_BYTES];
    uint8_t sig[WOTSFV_SIG_BYTES];
    wotsfv_pkgen(pk,  sk_seed, pub_seed, a0);
    wotsfv_sign (sig, msg, sk_seed, pub_seed, a1);
    msg[0] ^= 0x01;
    return wotsfv_verify(pk, sig, msg, pub_seed, a2) != WOTSFV_OK ? T_OK : T_FAIL;
}

int run_wots_tests(void) {
    int failures = 0;
    (void)printf("wots+ (RFC 8391, XMSS-SHA2_10_256)\n");
    RUN(test_wots_self_roundtrip);
    RUN(test_wots_msg_all_zero);
    RUN(test_wots_msg_all_ff);
    RUN(test_wots_addr_reuse);
    RUN(test_wots_tamper_msg);
    RUN(test_wots_tamper_sig);
    RUN(test_wots_tamper_pk);
    RUN(test_wots_tamper_pub_seed);
    RUN(test_wots_wrong_addr);
    return failures;
}

/* ---------- Vector cross-check (stdin) ---------- */
/* Returns 1 = clean EOF, 0 = mismatch, -1 = malformed input. */
static int check_vectors(int *nread) {
    *nread = 0;
    for (;;) {
        uint8_t input[128];
        size_t got = fread(input, 1, sizeof input, stdin);
        if (got == 0 && feof(stdin)) { return 1; }
        if (got != sizeof input) { return -1; }
        uint8_t pk_ref[WOTSFV_PK_BYTES];
        uint8_t sig_ref[WOTSFV_SIG_BYTES];
        if (read_exact(stdin, pk_ref,  sizeof pk_ref) ||
            read_exact(stdin, sig_ref, sizeof sig_ref)) { return -1; }
        const uint8_t *sk_seed  = input +  0;
        const uint8_t *pub_seed = input + 32;
        const uint8_t *msg      = input + 64;

        wotsfv_addr a_pk;
        wotsfv_addr a_sig;
        unpack_addr(a_pk,  input + 96);
        unpack_addr(a_sig, input + 96);

        uint8_t pk_ours[WOTSFV_PK_BYTES];
        uint8_t sig_ours[WOTSFV_SIG_BYTES];
        wotsfv_pkgen(pk_ours,  sk_seed, pub_seed, a_pk);
        wotsfv_sign (sig_ours, msg, sk_seed, pub_seed, a_sig);

        if (memcmp(pk_ours,  pk_ref,  WOTSFV_PK_BYTES)  != 0) {
            (void)fprintf(stderr, "    vector %d: pk mismatch\n", *nread);
            return 0;
        }
        if (memcmp(sig_ours, sig_ref, WOTSFV_SIG_BYTES) != 0) {
            (void)fprintf(stderr, "    vector %d: sig mismatch\n", *nread);
            return 0;
        }
        (*nread)++;
    }
}

int run_wots_vector_xcheck(void) {
    (void)printf("wots+ cross-check vs. upstream xmss-reference vectors (stdin)\n");
    int n = 0;
    int ok = check_vectors(&n);
    if (ok == 1 && n > 0) {
        (void)printf("  %-28s ... ok (%d vectors)\n", "test_wots_vectors", n);
        return 0;
    }
    if (ok == 1 && n == 0) {
        (void)printf("  %-28s ... SKIP (no vectors on stdin)\n", "test_wots_vectors");
        return 0;
    }
    (void)printf("  %-28s ... FAIL (read %d ok)\n", "test_wots_vectors", n);
    return 1;
}
