(** * contract.trusted: externally-specified / axiomatic funspecs.

    These specs describe functions that are NOT proved against C code in
    this repo -- they are assumed correct by construction.  Currently
    exactly one entry:

    - [sha256_spec]: the only cryptographic primitive.  [model.wots.SHA256]
      is a [Parameter] and [body_sha256] is an [Axiom] in [contract.gprog]
      by design, since [src/sha256.c] is a direct FIPS 180-4 port verified
      elsewhere.

    The in-tree libc alternatives ([wotsfv_memcpy], [wotsfv_memset],
    [wotsfv_ct_memcmp], [wotsfv_panic]) are NOT trusted -- their funspecs
    live in [contract.helpers] and their bodies are proved in
    [proof/verif].

    When auditing, the trusted surface area is exactly this file. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Export floyd.proofauto.
From wots Require Export clight.sha256 contract.public.

Open Scope Z_scope.

(** [sha256(out, in, inlen)]: writes the 32-byte digest of [in] to [out]. *)
Definition sha256_spec : ident * funspec :=
  DECLARE _wotsfv_sha256
  WITH out_ptr : val, in_ptr : val, inlen : Z,
       input : list byte,
       sh_o : share, sh_i : share
  PRE [ tptr tuchar, tptr tuchar, tulong ]
    PROP (writable_share sh_o; readable_share sh_i;
          Zlength input = inlen;
          0 <= inlen <= Int64.max_unsigned)
    PARAMS (out_ptr; in_ptr; Vlong (Int64.repr inlen))
    SEP (data_at_ sh_o (tarray tuchar 32) out_ptr;
         data_at  sh_i (tarray tuchar inlen) (block_to_vals input) in_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 32) (block_to_vals (SHA256 input)) out_ptr;
         data_at sh_i (tarray tuchar inlen) (block_to_vals input) in_ptr).
