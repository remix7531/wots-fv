/* C bridge exposing the same ABI as src/wots.h, forwarding to the
   OCaml implementation extracted from the Rocq spec.

   The OCaml runtime is started once on library load via a constructor,
   so callers see a drop-in replacement for libwots.a.  No OCaml
   toolchain is needed at link time — [ocamlopt -output-complete-obj]
   packs the runtime into the same object this file compiles into. */

#include "wots.h"

#include <caml/mlvalues.h>
#include <caml/alloc.h>
#include <caml/memory.h>
#include <caml/callback.h>
#include <string.h>

/* One-time OCaml runtime boot.  Runs before main(). */
static void __attribute__((constructor)) wots_ocaml_init(void) {
    static char arg0[] = "wots_ocaml";
    static char *argv[] = { arg0, NULL };
    caml_startup(argv);
}

/* --- value helpers --- */

static value make_bytes(const uint8_t *src, size_t len) {
    value v = caml_alloc_string(len);    /* writable byte string */
    memcpy(Bytes_val(v), src, len);
    return v;
}

static value make_addr(const uint32_t addr[8]) {
    CAMLparam0();
    CAMLlocal1(a);
    a = caml_alloc(8, 0);                /* int array (boxed in 4.x) */
    for (int i = 0; i < 8; i++)
        Store_field(a, i, Val_long((long)addr[i]));
    CAMLreturn(a);
}

static void copy_bytes_out(value v, uint8_t *dst, size_t len) {
    memcpy(dst, Bytes_val(v), len);
}

/* --- ABI --- */

void wots_pkgen(uint8_t pk[WOTS_PK_BYTES],
                const uint8_t sk_seed[WOTS_SK_SEED_BYTES],
                const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                wots_addr addr) {
    CAMLparam0();
    CAMLlocal4(sk, ps, ad, res);
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_pkgen");

    sk  = make_bytes(sk_seed,  WOTS_SK_SEED_BYTES);
    ps  = make_bytes(pub_seed, WOTS_PUB_SEED_BYTES);
    ad  = make_addr(addr);
    res = caml_callback3(*cb, sk, ps, ad);
    copy_bytes_out(res, pk, WOTS_PK_BYTES);
    CAMLreturn0;
}

void wots_sign(uint8_t sig[WOTS_SIG_BYTES],
               const uint8_t msg[WOTS_MSG_BYTES],
               const uint8_t sk_seed[WOTS_SK_SEED_BYTES],
               const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
               wots_addr addr) {
    CAMLparam0();
    CAMLlocal5(m, sk, ps, ad, res);
    value argv[4];
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_sign");

    m  = make_bytes(msg,      WOTS_MSG_BYTES);
    sk = make_bytes(sk_seed,  WOTS_SK_SEED_BYTES);
    ps = make_bytes(pub_seed, WOTS_PUB_SEED_BYTES);
    ad = make_addr(addr);

    argv[0] = m; argv[1] = sk; argv[2] = ps; argv[3] = ad;
    res = caml_callbackN(*cb, 4, argv);
    copy_bytes_out(res, sig, WOTS_SIG_BYTES);
    CAMLreturn0;
}

int wots_verify(const uint8_t pk[WOTS_PK_BYTES],
                const uint8_t sig[WOTS_SIG_BYTES],
                const uint8_t msg[WOTS_MSG_BYTES],
                const uint8_t pub_seed[WOTS_PUB_SEED_BYTES],
                wots_addr addr) {
    CAMLparam0();
    CAMLlocal5(pkv, sv, mv, psv, adv);
    CAMLlocal1(res);
    value argv[5];
    static const value *cb = NULL;
    if (!cb) cb = caml_named_value("wots_ocaml_verify");

    pkv = make_bytes(pk,       WOTS_PK_BYTES);
    sv  = make_bytes(sig,      WOTS_SIG_BYTES);
    mv  = make_bytes(msg,      WOTS_MSG_BYTES);
    psv = make_bytes(pub_seed, WOTS_PUB_SEED_BYTES);
    adv = make_addr(addr);

    argv[0] = pkv; argv[1] = sv; argv[2] = mv; argv[3] = psv; argv[4] = adv;
    res = caml_callbackN(*cb, 5, argv);
    CAMLreturnT(int, Bool_val(res) ? 0 : -1);
}
