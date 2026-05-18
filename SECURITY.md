# Security

## What this is

A C implementation of WOTS+ (RFC 8391, §3.1) for **XMSS-SHA2_10_256**
(XMSS OID `0x00000001`). Meant to be linked into a larger XMSS / HBS
scheme; not a full XMSS API.

The production artifact is `libwots.a`.

`libwots_ocaml.a` (built from the Rocq-extracted OCaml model) is
**test infrastructure only** — it lets the test harness cross-check 
the C library against the formally extracted reference.

## Parameters (compile-time fixed)

| n  | w  | len1 | len2 | len | hash    |
|----|----|------|------|-----|---------|
| 32 | 16 | 64   | 3    | 67  | SHA-256 |

## Threat model

**Protects against:** existential forgery under the WOTS+ security
assumptions (one-wayness of the iterated tweakable hash, second-
preimage resistance of SHA-256).

**Does NOT protect against:**

* **Key reuse.** WOTS+ is one-time; signing two messages with the
  same `(sk_seed, pub_seed, addr)` trivially forges. The surrounding
  XMSS / Merkle state machine must enforce one-shot use.
* **Timing side-channels in signing.** `wotsfv_pkgen` / `wotsfv_sign`
  feed `sk_seed` to SHA-256. Constant-time behaviour rests on
  inspection of `src/sha256.c` (no secret-dependent branches or
  table lookups), not on proof. `wotsfv_verify` is on public inputs.
* **Power / EM / fault / acoustic side-channels.** No countermeasures.
* **Bad RNG.** Callers supply `sk_seed`; it must come from a CSPRNG.
* **Secret residue.** No zeroization. Stack frames holding derived
  PRF state are left as-is on return.

## Resource usage

Peak stack ~2.7 KB (dominated by `wotsfv_verify`'s 2144-byte
`pk_cand`). No heap, no mutable globals; reentrant on disjoint
buffers.

## Verified scope

The Rocq / VST proof in `proof/` covers a Gallina model of WOTS+
(`proof/model/wots.v`) and refinement of every `wotsfv_*` C function
against it (`proof/verif/body_*.v`). The OCaml extraction is
cross-checked against `xmss-reference` (`make test-ocaml`).

**Trusted base:** SHA-256 (axiomatized in `proof/contract/trusted.v`),
the OCaml extraction pipeline + runtime, and the C compiler — though
`make test-ccomp` exercises the CompCert-compiled binary.

## Compile-time options

| Macro           | Default | Effect                                                   |
|-----------------|---------|----------------------------------------------------------|
| `WOTSFV_CHECKS` | `1`     | `=0` compiles `WOTSFV_ASSERT` out (UB on contract break) |

## API contract

Per `src/wots.h`: pointers non-NULL, buffers at least the documented
size, output buffers disjoint from inputs, `addr` slots 5..7 are
scratch and clobbered. `wotsfv_verify` returns `WOTSFV_OK` (0) or
`WOTSFV_VERIFY_FAILED` (-1) — no other values.
