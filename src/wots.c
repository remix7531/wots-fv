/* RFC 8391 WOTS+ with XMSS-SHA2_10_256 parameters (OID 0x00000001).
   Written with VST verification in mind: small helpers, fixed loop
   bounds, single-pass key-gen and signing, chunk-at-a-time verification. */

#include "wots.h"
#include "sha256.h"
#include <string.h>

/* ---- Private algorithm parameters. ---- */

#define N        32
#define W        16
#define LEN1     64
#define LEN2     3
#define LEN      67       /* LEN1 + LEN2 */
#define PAD      32       /* padding_len for SHA2-256 WOTS+ */

_Static_assert(WOTS_SK_SEED_BYTES  == N,       "sk_seed == n");
_Static_assert(WOTS_PUB_SEED_BYTES == N,       "pub_seed == n");
_Static_assert(WOTS_MSG_BYTES      == N,       "msg == n");
_Static_assert(WOTS_PK_BYTES       == LEN * N, "pk == len*n");
_Static_assert(WOTS_SIG_BYTES      == LEN * N, "sig == len*n");

/* ---- ADRS serialization: 8 big-endian uint32s → 32 bytes. ---- */
static void addr_bytes(uint8_t out[32], const uint32_t a[8]) {
    for (unsigned i = 0; i < 8; i++) {
        out[4*i + 0] = (uint8_t)(a[i] >> 24);
        out[4*i + 1] = (uint8_t)(a[i] >> 16);
        out[4*i + 2] = (uint8_t)(a[i] >>  8);
        out[4*i + 3] = (uint8_t)(a[i]);
    }
}

/* ---- PRF(key, in[32]) = SHA256(toByte(3,32) || key || in). ---- */
static void prf(uint8_t out[N], const uint8_t in[32], const uint8_t key[N]) {
    uint8_t buf[PAD + N + 32];
    memset(buf, 0, PAD);
    buf[PAD - 1] = 3;
    memcpy(buf + PAD,        key, N);
    memcpy(buf + PAD + N,    in,  32);
    sha256(out, buf, sizeof buf);
}

/* ---- PRF_keygen(key, in[n+32]) = SHA256(toByte(4,32) || key || in). ---- */
static void prf_keygen(uint8_t out[N],
                       const uint8_t in[N + 32],
                       const uint8_t key[N]) {
    uint8_t buf[PAD + 2 * N + 32];
    memset(buf, 0, PAD);
    buf[PAD - 1] = 4;
    memcpy(buf + PAD,        key, N);
    memcpy(buf + PAD + N,    in,  N + 32);
    sha256(out, buf, sizeof buf);
}

/* ---- Tweakable hash F.  Input/output both N bytes. ---- */
static void thash_f(uint8_t out[N], const uint8_t in[N],
                    const uint8_t pub_seed[N], uint32_t addr[8]) {
    uint8_t buf[PAD + 2 * N];
    uint8_t ab[32], mask[N];

    memset(buf, 0, PAD);        /* toByte(0, 32) */

    addr[7] = 0;
    addr_bytes(ab, addr);
    prf(buf + PAD, ab, pub_seed);

    addr[7] = 1;
    addr_bytes(ab, addr);
    prf(mask, ab, pub_seed);

    for (unsigned i = 0; i < N; i++) {
        buf[PAD + N + i] = in[i] ^ mask[i];
    }
    sha256(out, buf, sizeof buf);
}

/* ---- Derive chain-i secret-key start from sk_seed (PRF_keygen). ---- */
static void derive_sk(uint8_t out[N], unsigned chain_i,
                      const uint8_t sk_seed[N],
                      const uint8_t pub_seed[N],
                      uint32_t addr[8]) {
    addr[5] = chain_i;
    addr[6] = 0;
    addr[7] = 0;
    uint8_t in[N + 32];
    memcpy(in,     pub_seed, N);
    addr_bytes(in + N, addr);
    prf_keygen(out, in, sk_seed);
}

/* ---- F iterated `steps` times on `buf`, in place.  Callers must have
       set addr[5] (chain) before calling. ---- */
static void chain(uint8_t buf[N], unsigned start, unsigned steps,
                  const uint8_t pub_seed[N], uint32_t addr[8]) {
    for (unsigned i = 0; i < steps; i++) {
        addr[6] = start + i;
        thash_f(buf, buf, pub_seed, addr);
    }
}

/* ---- Expand msg into LEN base-16 digits: 64 from msg + 3-digit checksum.
       csum ≤ LEN1 * (W-1) = 64 * 15 = 960 < 2^12, so the checksum fits
       in exactly LEN2 = 3 nibbles. ---- */
static void expand_digits(uint8_t digits[LEN], const uint8_t msg[N]) {
    for (unsigned i = 0; i < N; i++) {
        digits[2*i + 0] = (uint8_t)(msg[i] >> 4);
        digits[2*i + 1] = (uint8_t)(msg[i] & 0x0f);
    }
    uint32_t csum = 0;
    for (unsigned i = 0; i < LEN1; i++) {
        csum += (uint32_t)(W - 1 - digits[i]);
    }
    digits[LEN1 + 0] = (uint8_t)((csum >> 8) & 0x0f);
    digits[LEN1 + 1] = (uint8_t)((csum >> 4) & 0x0f);
    digits[LEN1 + 2] = (uint8_t)((csum >> 0) & 0x0f);
}

/* ---- Public API. ---- */

void wots_pkgen(uint8_t pk[WOTS_PK_BYTES],
                const uint8_t sk_seed[WOTS_SK_SEED_BYTES],
                const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                wots_addr addr) {
    for (unsigned i = 0; i < LEN; i++) {
        derive_sk(pk + i * N, i, sk_seed, pub_seed, addr);
        chain(pk + i * N, 0, W - 1, pub_seed, addr);
    }
}

void wots_sign(uint8_t sig[WOTS_SIG_BYTES],
               const uint8_t msg[WOTS_MSG_BYTES],
               const uint8_t sk_seed[WOTS_SK_SEED_BYTES],
               const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
               wots_addr addr) {
    uint8_t digits[LEN];
    expand_digits(digits, msg);
    for (unsigned i = 0; i < LEN; i++) {
        derive_sk(sig + i * N, i, sk_seed, pub_seed, addr);
        chain(sig + i * N, 0, digits[i], pub_seed, addr);
    }
}

/* Algorithm 6 (WOTS_pkFromSig): derive a candidate public key from
   a signature and message. */
void wots_pk_from_sig(uint8_t pk_cand[WOTS_PK_BYTES],
                      const uint8_t sig[WOTS_SIG_BYTES],
                      const uint8_t msg[WOTS_MSG_BYTES],
                      const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                      wots_addr addr) {
    uint8_t digits[LEN];
    expand_digits(digits, msg);
    for (unsigned i = 0; i < LEN; i++) {
        memcpy(pk_cand + i * N, sig + i * N, N);
        addr[5] = i;
        chain(pk_cand + i * N, digits[i], W - 1 - digits[i], pub_seed, addr);
    }
}

int wots_verify(const uint8_t pk[WOTS_PK_BYTES],
                const uint8_t sig[WOTS_SIG_BYTES],
                const uint8_t msg[WOTS_MSG_BYTES],
                const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                wots_addr addr) {
    uint8_t pk_cand[WOTS_PK_BYTES];
    wots_pk_from_sig(pk_cand, sig, msg, pub_seed, addr);
    return memcmp(pk_cand, pk, WOTS_PK_BYTES) == 0 ? 0 : -1;
}
