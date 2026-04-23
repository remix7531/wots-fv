# WOTS+ Formally Verified

Machine-checked functional-correctness proof of a C implementation of
RFC 8391 WOTS+ (`WOTSP-SHA2_256`), using VST on Rocq 9.0 + CompCert.

> **Do not use this code.** Vibe-coded cryptography; educational artifact
> only.

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
make             # c lib + ocaml lib + tests + clightgen + proofs
make proof       # proofs only
make test        # vector comparison vs xmss-reference (N=32 default)
make test-ocaml  # same vectors vs build/libwots_ocaml.a
make clean
```

## Layout

```
src/          wots.{c,h}, sha256.{c,h}
test/         main.c, gen_vectors.c
proof/        model/, contract/, verif/, clight/
ocaml/        sources for Rocq-extracted library
.nix/         xmss-reference package
```

## Rocq-extracted library

`make ocaml-lib` produces `build/libwots_ocaml.a` — same ABI as
`libwots.a`, with the OCaml runtime embedded via
`ocamlopt -output-complete-obj` so consumers need no OCaml at link time.
`make test-ocaml` reuses the vector pipeline against that library.

## Known side channel

`wots_verify` compares the candidate public key with `memcmp`, which is
not constant-time and leaks per-byte equality through timing.
