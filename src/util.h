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

#ifndef WOTSFV_UTIL_H
#define WOTSFV_UTIL_H

#include <stddef.h>
#include <stdint.h>

/* Byte copy.  In-tree replacement for libc memcpy, so VST can discharge
   it from a real proof body.  Buffers must not overlap. */
void *wotsfv_memcpy(void *dst, const void *src, size_t n);

/* Byte fill.  In-tree replacement for libc memset, so VST can discharge
   it from a real proof body. */
void *wotsfv_memset(void *dst, int byte, size_t n);

/* Byte compare.  Returns 0 iff equal.  Used by wotsfv_verify, whose
   inputs are public; no constant-time guarantee is implied. */
int wotsfv_ct_memcmp(const uint8_t *a, const uint8_t *b, size_t n);

/* Trap on contract violation.  Triggered by WOTSFV_ASSERT; does not
   return.  Uses __builtin_trap (defined-behavior abort on GCC, Clang
   and CompCert) with a trailing infinite loop as a fallback if the
   compiler ever fails to mark it noreturn.  Unreachable from VST-
   proven code, since WOTSFV_CHECKS=0 in the verification profile
   compiles every WOTSFV_ASSERT to a no-op. */
void wotsfv_panic(void);

#ifndef WOTSFV_CHECKS
#define WOTSFV_CHECKS 1
#endif

#if WOTSFV_CHECKS
#define WOTSFV_ASSERT(cond) do { if (!(cond)) wotsfv_panic(); } while (0)
#else
#define WOTSFV_ASSERT(cond) ((void)0)
#endif

#endif
