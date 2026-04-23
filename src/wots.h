#ifndef WOTS_FV_WOTS_H
#define WOTS_FV_WOTS_H

#include <stdint.h>
#include <stddef.h>

/* Public API — RFC 8391 §3.1 WOTS+ with parameter set XMSS-SHA2_10_256
   (OID 0x00000001).  Only I/O buffer sizes are exposed; algorithm
   parameters (n, w, len, log_w, padding_len) are private to src/wots.c. */

#define WOTS_SK_SEED_BYTES   32
#define WOTS_PUB_SEED_BYTES  32
#define WOTS_MSG_BYTES       32
#define WOTS_PK_BYTES        2144
#define WOTS_SIG_BYTES       2144

typedef uint32_t wots_addr[8];

/* Algorithm 4 (WOTS_genPK).  Derives the public key from a secret seed. */
void wots_pkgen(uint8_t pk[WOTS_PK_BYTES],
                const uint8_t sk_seed[WOTS_SK_SEED_BYTES],
                const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                wots_addr addr);

/* Algorithm 5 (WOTS_sign). */
void wots_sign(uint8_t sig[WOTS_SIG_BYTES],
               const uint8_t msg[WOTS_MSG_BYTES],
               const uint8_t sk_seed[WOTS_SK_SEED_BYTES],
               const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
               wots_addr addr);

/* Algorithm 6 (WOTS_pkFromSig): derive candidate public key. */
void wots_pk_from_sig(uint8_t pk_cand[WOTS_PK_BYTES],
                      const uint8_t sig[WOTS_SIG_BYTES],
                      const uint8_t msg[WOTS_MSG_BYTES],
                      const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                      wots_addr addr);

/* Signature verification: returns 0 if `sig` is a valid WOTS+
   signature of `msg` under `pk`, non-zero otherwise. */
int wots_verify(const uint8_t pk[WOTS_PK_BYTES],
                const uint8_t sig[WOTS_SIG_BYTES],
                const uint8_t msg[WOTS_MSG_BYTES],
                const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                wots_addr addr);

#endif
