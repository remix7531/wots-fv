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

/* C bridge from the wots+fv ABI (src/wots.h) to the Rocq-extracted
   OCaml implementation.  Test infrastructure only -- not a
   production wots+fv build (see SECURITY.md).

   ocamlopt -output-complete-obj packs the OCaml runtime into a
   single .o, so callers need no OCaml toolchain at link time. */

#include "wots.h"

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <caml/config.h>
#include <string.h>

/* OCaml's tagged int is one bit narrower than [intnat].  Every
   uint32_t addr word must fit, so require 64-bit OCaml (intnat ≥ 8B,
   giving a 63-bit int range).  Building on 32-bit OCaml would silently
   truncate addr words ≥ 2^30 in make_addr below. */
_Static_assert(sizeof(intnat) >= 8,
               "wots+fv OCaml bridge requires a 64-bit OCaml runtime");

/* caml_startup is not thread-safe and runs at load time.  Safe for the
   single-threaded test harness; do NOT reuse this bridge from a
   multi-threaded consumer or under dlopen(). */
static void __attribute__((constructor)) wotsfv_ocaml_init(void) {
    static char arg0[] = "wotsfv_ocaml";
    static char *argv[] = { arg0, NULL };
    caml_startup(argv);
}

static value make_bytes(const uint8_t *src, size_t len) {
    CAMLparam0();
    CAMLlocal1(v);
    v = caml_alloc_string(len);
    memcpy(Bytes_val(v), src, len);
    CAMLreturn(v);
}

static value make_addr(const uint32_t addr[8]) {
    CAMLparam0();
    CAMLlocal1(a);
    a = caml_alloc(8, 0);
    for (int i = 0; i < 8; i++)
        Store_field(a, i, Val_long((intnat)addr[i]));
    CAMLreturn(a);
}

static void copy_bytes_out(value v, uint8_t *dst, size_t len) {
    memcpy(dst, Bytes_val(v), len);
}

void wotsfv_pkgen(uint8_t       pk      [static restrict WOTSFV_PK_BYTES],
                  const uint8_t sk_seed [static restrict WOTSFV_SK_SEED_BYTES],
                  const uint8_t pub_seed[static restrict WOTSFV_PUB_SEED_BYTES],
                  uint32_t      addr    [static restrict 8]) {
    CAMLparam0();
    CAMLlocal4(sk, ps, ad, res);
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_pkgen");

    sk  = make_bytes(sk_seed,  WOTSFV_SK_SEED_BYTES);
    ps  = make_bytes(pub_seed, WOTSFV_PUB_SEED_BYTES);
    ad  = make_addr(addr);
    res = caml_callback3(*cb, sk, ps, ad);
    copy_bytes_out(res, pk, WOTSFV_PK_BYTES);
    CAMLreturn0;
}

void wotsfv_sign(uint8_t       sig     [static restrict WOTSFV_SIG_BYTES],
                 const uint8_t msg     [static restrict WOTSFV_MSG_BYTES],
                 const uint8_t sk_seed [static restrict WOTSFV_SK_SEED_BYTES],
                 const uint8_t pub_seed[static restrict WOTSFV_PUB_SEED_BYTES],
                 uint32_t      addr    [static restrict 8]) {
    CAMLparam0();
    CAMLlocal5(m, sk, ps, ad, res);
    value argv[4];
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_sign");

    m  = make_bytes(msg,      WOTSFV_MSG_BYTES);
    sk = make_bytes(sk_seed,  WOTSFV_SK_SEED_BYTES);
    ps = make_bytes(pub_seed, WOTSFV_PUB_SEED_BYTES);
    ad = make_addr(addr);

    argv[0] = m; argv[1] = sk; argv[2] = ps; argv[3] = ad;
    res = caml_callbackN(*cb, 4, argv);
    copy_bytes_out(res, sig, WOTSFV_SIG_BYTES);
    CAMLreturn0;
}

void wotsfv_pk_from_sig(uint8_t       pk_cand [static restrict WOTSFV_PK_BYTES],
                        const uint8_t sig     [static restrict WOTSFV_SIG_BYTES],
                        const uint8_t msg     [static restrict WOTSFV_MSG_BYTES],
                        const uint8_t pub_seed[static restrict WOTSFV_PUB_SEED_BYTES],
                        uint32_t      addr    [static restrict 8]) {
    CAMLparam0();
    CAMLlocal5(sv, mv, psv, adv, res);
    value argv[4];
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_pk_from_sig");

    sv  = make_bytes(sig,      WOTSFV_SIG_BYTES);
    mv  = make_bytes(msg,      WOTSFV_MSG_BYTES);
    psv = make_bytes(pub_seed, WOTSFV_PUB_SEED_BYTES);
    adv = make_addr(addr);

    argv[0] = sv; argv[1] = mv; argv[2] = psv; argv[3] = adv;
    res = caml_callbackN(*cb, 4, argv);
    copy_bytes_out(res, pk_cand, WOTSFV_PK_BYTES);
    CAMLreturn0;
}

int wotsfv_verify(const uint8_t pk      [static restrict WOTSFV_PK_BYTES],
                  const uint8_t sig     [static restrict WOTSFV_SIG_BYTES],
                  const uint8_t msg     [static restrict WOTSFV_MSG_BYTES],
                  const uint8_t pub_seed[static restrict WOTSFV_PUB_SEED_BYTES],
                  uint32_t      addr    [static restrict 8]) {
    CAMLparam0();
    CAMLlocal5(pkv, sv, mv, psv, adv);
    CAMLlocal1(res);
    value argv[5];
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_verify");

    pkv = make_bytes(pk,       WOTSFV_PK_BYTES);
    sv  = make_bytes(sig,      WOTSFV_SIG_BYTES);
    mv  = make_bytes(msg,      WOTSFV_MSG_BYTES);
    psv = make_bytes(pub_seed, WOTSFV_PUB_SEED_BYTES);
    adv = make_addr(addr);

    argv[0] = pkv; argv[1] = sv; argv[2] = mv; argv[3] = psv; argv[4] = adv;
    res = caml_callbackN(*cb, 5, argv);
    CAMLreturnT(int, Bool_val(res) ? WOTSFV_OK : WOTSFV_VERIFY_FAILED);
}
