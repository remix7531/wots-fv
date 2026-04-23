/* WOTS+ test harness for wots+fv.
   Reads N vectors produced by test/gen_vectors from stdin, re-runs each
   with our src/wots.c, and byte-compares pk + sig.  Also runs a handful
   of standalone SHA-256 KATs and a roundtrip/tamper sanity check. */

#include "wots.h"
#include "sha256.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* -------- SHA-256 KATs -------- */

static int test_sha256_empty(void) {
    static const uint8_t e[32] = {
        0xe3,0xb0,0xc4,0x42,0x98,0xfc,0x1c,0x14,
        0x9a,0xfb,0xf4,0xc8,0x99,0x6f,0xb9,0x24,
        0x27,0xae,0x41,0xe4,0x64,0x9b,0x93,0x4c,
        0xa4,0x95,0x99,0x1b,0x78,0x52,0xb8,0x55
    };
    uint8_t got[32];
    sha256(got, (const uint8_t *)"", 0);
    return memcmp(got, e, 32) == 0;
}

static int test_sha256_abc(void) {
    static const uint8_t e[32] = {
        0xba,0x78,0x16,0xbf,0x8f,0x01,0xcf,0xea,
        0x41,0x41,0x40,0xde,0x5d,0xae,0x22,0x23,
        0xb0,0x03,0x61,0xa3,0x96,0x17,0x7a,0x9c,
        0xb4,0x10,0xff,0x61,0xf2,0x00,0x15,0xad
    };
    uint8_t got[32];
    sha256(got, (const uint8_t *)"abc", 3);
    return memcmp(got, e, 32) == 0;
}

/* -------- Helpers -------- */

static void unpack_addr(wots_addr addr, const uint8_t bytes[32]) {
    for (int i = 0; i < 8; i++) {
        addr[i] = ((uint32_t)bytes[4*i+0] << 24) |
                  ((uint32_t)bytes[4*i+1] << 16) |
                  ((uint32_t)bytes[4*i+2] <<  8) |
                  ((uint32_t)bytes[4*i+3]);
    }
}

static int fill_random(uint8_t *buf, size_t n) {
    FILE *f = fopen("/dev/urandom", "rb");
    if (!f) return -1;
    int rc = fread(buf, 1, n, f) == n ? 0 : -1;
    fclose(f);
    return rc;
}

static int read_exact(FILE *f, void *buf, size_t n) {
    return fread(buf, 1, n, f) == n ? 0 : -1;
}

/* -------- Self consistency -------- */

static int test_wots_self_roundtrip(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) return 0;
    const uint8_t *sk_seed  = input +  0;
    const uint8_t *pub_seed = input + 32;
    const uint8_t *msg      = input + 64;

    wots_addr a0, a1, a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  sk_seed, pub_seed, a0);
    wots_sign (sig, msg, sk_seed, pub_seed, a1);
    return wots_verify(pk, sig, msg, pub_seed, a2) == 0;
}

/* Edge case: all-zero msg → every digit is 0 → sign chains 0 steps per
   chunk, verify chains W-1 steps.  Checksum hits its maximum (960). */
static int test_wots_msg_all_zero(void) {
    uint8_t sk_seed[32], pub_seed[32];
    uint8_t msg[32] = {0};
    if (fill_random(sk_seed, 32) || fill_random(pub_seed, 32)) return 0;

    wots_addr a0 = {0}, a1 = {0}, a2 = {0};
    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  sk_seed, pub_seed, a0);
    wots_sign (sig, msg, sk_seed, pub_seed, a1);
    return wots_verify(pk, sig, msg, pub_seed, a2) == 0;
}

/* Edge case: all-0xff msg → every digit is 15 → sign chains W-1 steps
   per chunk, verify chains 0 steps.  Checksum hits its minimum (0). */
static int test_wots_msg_all_ff(void) {
    uint8_t sk_seed[32], pub_seed[32];
    uint8_t msg[32];
    memset(msg, 0xff, 32);
    if (fill_random(sk_seed, 32) || fill_random(pub_seed, 32)) return 0;

    wots_addr a0 = {0}, a1 = {0}, a2 = {0};
    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  sk_seed, pub_seed, a0);
    wots_sign (sig, msg, sk_seed, pub_seed, a1);
    return wots_verify(pk, sig, msg, pub_seed, a2) == 0;
}

/* Tamper checks: flipping any trusted input must reject the signature. */

static int test_wots_tamper_sig(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) return 0;
    wots_addr a0, a1, a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  input + 0, input + 32, a0);
    wots_sign (sig, input + 64, input + 0, input + 32, a1);
    sig[1234] ^= 0x10;
    return wots_verify(pk, sig, input + 64, input + 32, a2) != 0;
}

static int test_wots_tamper_pk(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) return 0;
    wots_addr a0, a1, a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  input + 0, input + 32, a0);
    wots_sign (sig, input + 64, input + 0, input + 32, a1);
    pk[0] ^= 0x01;
    return wots_verify(pk, sig, input + 64, input + 32, a2) != 0;
}

static int test_wots_tamper_pub_seed(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) return 0;
    wots_addr a0, a1, a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  input + 0, input + 32, a0);
    wots_sign (sig, input + 64, input + 0, input + 32, a1);
    uint8_t bad_pub_seed[32];
    memcpy(bad_pub_seed, input + 32, 32);
    bad_pub_seed[7] ^= 0x80;
    return wots_verify(pk, sig, input + 64, bad_pub_seed, a2) != 0;
}

/* Verifying under a different ADRS must fail: the tweakable hash is
   keyed by (pub_seed, ADRS), so any ADRS mismatch propagates. */
static int test_wots_wrong_addr(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) return 0;
    wots_addr a_sign, a_ver, a_pk;
    unpack_addr(a_sign, input + 96);
    unpack_addr(a_pk,   input + 96);
    unpack_addr(a_ver,  input + 96);
    a_ver[4] ^= 1;                       /* bump OTS index */

    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  input + 0, input + 32, a_pk);
    wots_sign (sig, input + 64, input + 0, input + 32, a_sign);
    return wots_verify(pk, sig, input + 64, input + 32, a_ver) != 0;
}

static int test_wots_tamper(void) {
    uint8_t input[128];
    if (fill_random(input, sizeof input)) return 0;
    const uint8_t *sk_seed  = input +  0;
    const uint8_t *pub_seed = input + 32;
    uint8_t *msg            = input + 64;

    wots_addr a0, a1, a2;
    unpack_addr(a0, input + 96);
    unpack_addr(a1, input + 96);
    unpack_addr(a2, input + 96);

    uint8_t pk[WOTS_PK_BYTES], sig[WOTS_SIG_BYTES];
    wots_pkgen(pk,  sk_seed, pub_seed, a0);
    wots_sign (sig, msg, sk_seed, pub_seed, a1);
    msg[0] ^= 0x01;
    return wots_verify(pk, sig, msg, pub_seed, a2) != 0;
}

/* -------- Vector cross-check.  Reads records from stdin; each record is
           input[128] || pk_ref[2144] || sig_ref[2144].  Returns #records
           consumed in *nread, or -1 on malformed input. */

static int check_vectors(int *nread) {
    *nread = 0;
    for (;;) {
        uint8_t input[128];
        size_t got = fread(input, 1, sizeof input, stdin);
        if (got == 0 && feof(stdin)) return 1;    /* clean EOF */
        if (got != sizeof input)     return -1;

        uint8_t pk_ref[WOTS_PK_BYTES], sig_ref[WOTS_SIG_BYTES];
        if (read_exact(stdin, pk_ref,  sizeof pk_ref) ||
            read_exact(stdin, sig_ref, sizeof sig_ref)) return -1;

        const uint8_t *sk_seed  = input +  0;
        const uint8_t *pub_seed = input + 32;
        const uint8_t *msg      = input + 64;

        wots_addr a_pk, a_sig;
        unpack_addr(a_pk,  input + 96);
        unpack_addr(a_sig, input + 96);

        uint8_t pk_ours[WOTS_PK_BYTES], sig_ours[WOTS_SIG_BYTES];
        wots_pkgen(pk_ours,  sk_seed, pub_seed, a_pk);
        wots_sign (sig_ours, msg, sk_seed, pub_seed, a_sig);

        if (memcmp(pk_ours,  pk_ref,  WOTS_PK_BYTES)  != 0) {
            fprintf(stderr, "    vector %d: pk mismatch\n", *nread);
            return 0;
        }
        if (memcmp(sig_ours, sig_ref, WOTS_SIG_BYTES) != 0) {
            fprintf(stderr, "    vector %d: sig mismatch\n", *nread);
            return 0;
        }
        (*nread)++;
    }
}

#define RUN(T) do { \
    int ok = T(); \
    printf("  %-28s ... %s\n", #T, ok ? "ok" : "FAIL"); \
    if (!ok) failures++; \
} while (0)

int main(void) {
    int failures = 0;

    printf("sha256\n");
    RUN(test_sha256_empty);
    RUN(test_sha256_abc);

    printf("wots+ (RFC 8391, XMSS-SHA2_10_256)\n");
    RUN(test_wots_self_roundtrip);
    RUN(test_wots_msg_all_zero);
    RUN(test_wots_msg_all_ff);
    RUN(test_wots_tamper);
    RUN(test_wots_tamper_sig);
    RUN(test_wots_tamper_pk);
    RUN(test_wots_tamper_pub_seed);
    RUN(test_wots_wrong_addr);

    printf("wots+ cross-check vs. upstream xmss-reference vectors (stdin)\n");
    int n = 0;
    int ok = check_vectors(&n);
    if (ok == 1 && n > 0) {
        printf("  %-28s ... ok (%d vectors)\n", "test_wots_vectors", n);
    } else if (ok == 1 && n == 0) {
        printf("  %-28s ... SKIP (no vectors on stdin)\n", "test_wots_vectors");
    } else {
        printf("  %-28s ... FAIL (read %d ok)\n", "test_wots_vectors", n);
        failures++;
    }

    if (failures) {
        printf("%d test(s) FAILED\n", failures);
        return 1;
    }
    printf("all tests passed\n");
    return 0;
}
