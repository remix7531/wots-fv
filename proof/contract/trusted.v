(** * contract.trusted: externally-specified / axiomatic funspecs.
    These specs describe functions that are NOT proved against C code in
    this repo -- they are assumed correct by construction. Two groups:

    - [sha256_spec]: the only cryptographic primitive; [model.wots.SHA256]
      is a [Parameter] and [body_sha256] is an [Axiom] in [contract.gprog]
      by design, since [src/sha256.c] is a direct FIPS 180-4 port verified
      elsewhere.
    - [memset_spec], [memcpy_spec], [memcmp_spec]: libc, linked at runtime;
      the compcert-based program doesn't provide their bodies. Shapes
      mirror [VST/sha/spec_sha.v] adapted to 64-bit [tulong] size_t.

    When auditing, the trusted surface area is exactly this file. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Export floyd.proofauto.
From wots Require Export clight.sha256 contract.public.

Open Scope Z_scope.

(** [sha256(out, in, inlen)]: writes the 32-byte digest of [in] to [out]. *)
Definition sha256_spec : ident * funspec :=
  DECLARE _sha256
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

(** ** libc funspecs.

    Adapted from the canonical VST pattern in e.g. [VST/sha/spec_sha.v]:
    destination is a [memory_block] (not [data_at_]) so the spec accepts
    any [n]-byte writable region regardless of its C type; contents are
    carried as [list int] so the SEP clauses are tight. *)

Definition memset_spec : ident * funspec :=
  DECLARE _memset
  WITH sh : share, p : val, n : Z, c : int
  PRE [ tptr tvoid, tint, tulong ]
    PROP (writable_share sh; 0 <= n <= Int64.max_unsigned)
    PARAMS (p; Vint c; Vlong (Int64.repr n))
    SEP (memory_block sh n p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at sh (tarray tuchar n)
           (repeat (Vint c) (Z.to_nat n)) p).

Definition memcpy_spec : ident * funspec :=
  DECLARE _memcpy
  WITH qsh : share, psh : share, p : val, q : val,
       n : Z, contents : list int
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share qsh; writable_share psh;
          0 <= n <= Int64.max_unsigned)
    PARAMS (p; q; Vlong (Int64.repr n))
    SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
         memory_block psh n p)
  POST [ tptr tvoid ]
    PROP () RETURN (p)
    SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
         data_at psh (tarray tuchar n) (map Vint contents) p).

(** [memcmp(p, q, n)]: returns 0 iff the [n] bytes at [p] and [q] agree.
    Non-zero return value otherwise. [r] is an [int] rather than a [Z]
    so that [Vint r = Vint Int.zero] directly decides equality. *)
Definition memcmp_spec : ident * funspec :=
  DECLARE _memcmp
  WITH psh : share, qsh : share, p : val, q : val,
       n : Z, p_contents : list int, q_contents : list int
  PRE [ tptr tvoid, tptr tvoid, tulong ]
    PROP (readable_share psh; readable_share qsh;
          0 <= n <= Int64.max_unsigned;
          Zlength p_contents = n; Zlength q_contents = n)
    PARAMS (p; q; Vlong (Int64.repr n))
    SEP (data_at psh (tarray tuchar n) (map Vint p_contents) p;
         data_at qsh (tarray tuchar n) (map Vint q_contents) q)
  POST [ tint ]
    EX r : int,
    PROP (r = Int.zero <-> p_contents = q_contents)
    RETURN (Vint r)
    SEP (data_at psh (tarray tuchar n) (map Vint p_contents) p;
         data_at qsh (tarray tuchar n) (map Vint q_contents) q).
