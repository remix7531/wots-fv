(** * contract.gprog: the full [Gprog] funspec bundle.
    Combines [contract.trusted] (axiomatic / external specs: SHA256, libc)
    with [contract.helpers] (internal WOTS+ specs proved in [proof/verif])
    and [contract.public] (the public API specs). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Export floyd.proofauto.
From wots Require Export contract.trusted contract.public contract.helpers.

Open Scope Z_scope.

(** Full program funspec bundle -- libc, sha256, helpers, then public API. *)
Definition Gprog : funspecs :=
  sha256_spec ::
  Gprog_helpers ++
  [ wotsfv_pkgen_spec;
    wotsfv_sign_spec;
    wotsfv_pk_from_sig_spec;
    wotsfv_verify_spec ].

(** [body_sha256] is not verified here -- by design. [src/sha256.c] is a
    direct FIPS 180-4 port verified elsewhere, so we axiomatise the C
    function via [sha256_spec] rather than proving the body against our
    own model of SHA-256. The trusted surface is exactly this axiom plus
    [SHA256], [SHA256_length], [SHA256_byte_ok] in [model.wots]. *)
Axiom body_sha256 : semax_body Vprog Gprog f_wotsfv_sha256 sha256_spec.
