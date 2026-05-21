# WOTS+ Formally Verified

[![ci](https://github.com/remix7531/wots-fv/actions/workflows/ci.yml/badge.svg)](https://github.com/remix7531/wots-fv/actions/workflows/ci.yml)

Machine-checked functional-correctness proof of a C implementation of
RFC 8391 WOTS+ (`WOTSP-SHA2_256`), using VST on Rocq 9.0 + CompCert.

## What is proved

- Gallina model of RFC 8391 Algorithms 4–6 with a top-level round-trip theorem `wots_correct`.
- VST `semax_body` proofs for every WOTS+ C function against funspecs over that model.
- Zero `Admitted.`. Trusted base: three SHA-256 axioms. 

Scope: functional correctness, not EU-CMA. One-time use is a caller
obligation.

## Parameters

`n=32`, `w=16`, `len1=64`, `len2=3`, `len=67`, `padding_len=32`.

Per-chain keys follow `xmss-reference` (SLH-DSA / SP 800-208 domain
separator), not the literal RFC 8391 §3.1.7 text — so `make test`
interoperates with upstream vectors.

## Build

```
nix develop      # devshell with CompCert, VST, xmss-reference, OCaml
make             # build the C library (build/libwots.a) only
make test        # vector comparison vs xmss-reference (N=512 default)
make test-ocaml  # same vectors vs build/libwots_ocaml.a
make extract     # clightgen: C -> Clight AST for prove
make prove       # VST / Rocq proofs
make check       # full CI gate: static + sanitizers + CompCert + ctgrind +
                 #               ocaml-lib + test-ocaml + extract + prove
make check-ct    # ctgrind constant-time check (gcc + clang + CompCert)
make clean
```

## Layout

```
src/          wots.{c,h}, sha256.{c,h}, util.{c,h}
test/         runner.c, common.{c,h}, sha256.c, wots.c, gen_vectors.c, vectors/
proof/        model/, contract/, verif/, clight/
ocaml/        sources for Rocq-extracted library
.nix/         xmss-reference package
```

## Rocq-extracted library

`make ocaml-lib` produces `build/libwots_ocaml.a` — same ABI as
`libwots.a`, built from the OCaml that Rocq extracts out of the
Gallina model in `proof/model/`, with the OCaml runtime embedded via
`ocamlopt -output-complete-obj` so consumers need no OCaml at link time.
`make test-ocaml` reuses the vector pipeline against that library.

## Side channels

`wotsfv_verify` operates only on public inputs (`pk`, `sig`, `msg`,
`pub_seed`), so its timing is not security-relevant. `wotsfv_sign`
and `wotsfv_pkgen` consume `sk_seed` and rely on the SHA-256 core
being free of secret-dependent branches and table lookups; this is
argued by inspection of `src/sha256.c`, not formally verified.

## License

GPL-3.0-or-later. See `LICENSE`.
