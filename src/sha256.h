#ifndef WOTS_FV_SHA256_H
#define WOTS_FV_SHA256_H

#include <stddef.h>
#include <stdint.h>

#define SHA256_DIGEST_SIZE 32

/* Compute SHA-256 of `in` (length `inlen`) into `out` (32 bytes). */
void sha256(uint8_t out[SHA256_DIGEST_SIZE], const uint8_t *in, size_t inlen);

#endif
