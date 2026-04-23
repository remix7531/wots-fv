(** * contract.helpers: VST funspecs for the static helpers in [src/wots.c].

    Each funspec relates a C helper to its pure counterpart in
    [model.wots].  Bodies of these functions are proved in [verif/*]
    (currently [Admitted]). *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.

Open Scope Z_scope.
Open Scope logic.

(* ================================================================= *)
(** ** [addr_bytes(out, a)] -- serialise an [adrs] to 32 bytes. *)

Definition addr_bytes_spec : ident * funspec :=
  DECLARE _addr_bytes
  WITH out_ptr : val, a_ptr : val,
       a : adrs,
       sh_o : share, sh_a : share
  PRE [ tptr tuchar, tptr tuint ]
    PROP (writable_share sh_o; readable_share sh_a)
    PARAMS (out_ptr; a_ptr)
    SEP (data_at_ sh_o (tarray tuchar 32) out_ptr;
         data_at  sh_a t_addr (adrs_to_vals a) a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar 32)
           (block_to_vals (addr_bytes a)) out_ptr;
         data_at sh_a t_addr (adrs_to_vals a) a_ptr).

(* ================================================================= *)
(** ** [prf(out, in, key)] -- [PRF(key, in)] for a 32-byte [in]. *)

Definition prf_spec : ident * funspec :=
  DECLARE _prf
  WITH out_ptr : val, in_ptr : val, key_ptr : val,
       in_buf : list byte, key : block,
       sh_o : share, sh_i : share, sh_k : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_o;
          readable_share sh_i; readable_share sh_k;
          Zlength in_buf = 32; Zlength key = n_bytes)
    PARAMS (out_ptr; in_ptr; key_ptr)
    SEP (data_at_ sh_o (tarray tuchar n_bytes) out_ptr;
         data_at sh_i (tarray tuchar 32)       (block_to_vals in_buf) in_ptr;
         data_at sh_k (tarray tuchar n_bytes)  (block_to_vals key)    key_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes)
           (block_to_vals (PRF key in_buf)) out_ptr;
         data_at sh_i (tarray tuchar 32)      (block_to_vals in_buf) in_ptr;
         data_at sh_k (tarray tuchar n_bytes) (block_to_vals key)    key_ptr).

(* ================================================================= *)
(** ** [prf_keygen(out, in, key)] -- [PRF_keygen(key, in)] for [in] of
    length [n + 32 = 64]. *)

Definition prf_keygen_spec : ident * funspec :=
  DECLARE _prf_keygen
  WITH out_ptr : val, in_ptr : val, key_ptr : val,
       in_buf : list byte, key : block,
       sh_o : share, sh_i : share, sh_k : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_o;
          readable_share sh_i; readable_share sh_k;
          Zlength in_buf = (n_bytes + 32)%Z; Zlength key = n_bytes)
    PARAMS (out_ptr; in_ptr; key_ptr)
    SEP (data_at_ sh_o (tarray tuchar n_bytes) out_ptr;
         data_at sh_i (tarray tuchar ((n_bytes + 32)%Z))
                      (block_to_vals in_buf) in_ptr;
         data_at sh_k (tarray tuchar n_bytes)
                      (block_to_vals key) key_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes)
           (block_to_vals (PRF_keygen key in_buf)) out_ptr;
         data_at sh_i (tarray tuchar ((n_bytes + 32)%Z))
                      (block_to_vals in_buf) in_ptr;
         data_at sh_k (tarray tuchar n_bytes)
                      (block_to_vals key) key_ptr).

(* ================================================================= *)
(** ** [thash_f(out, in, pub_seed, addr)].

    Every caller aliases [out] and [in] (see [chain] in src/wots.c),
    so the spec fuses the two pointers into one [data_at] over a
    single writable 32-byte buffer.  The address is mutated: at
    entry its [keyAndMask] field is arbitrary; at exit it is [1]. *)

Definition thash_f_spec : ident * funspec :=
  DECLARE _thash_f
  WITH buf_ptr : val, ps_ptr : val, a_ptr : val,
       in_buf : block, pub_seed : block, a : adrs,
       sh_b : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_b; writable_share sh_a;
          readable_share sh_ps;
          Zlength in_buf = n_bytes; Zlength pub_seed = n_bytes)
    PARAMS (buf_ptr; buf_ptr; ps_ptr; a_ptr)
    SEP (data_at sh_b  (tarray tuchar n_bytes) (block_to_vals in_buf)   buf_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_b (tarray tuchar n_bytes)
           (block_to_vals (thash_f in_buf pub_seed a)) buf_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals (setKeyAndMask a 1)) a_ptr).

(* ================================================================= *)
(** ** [derive_sk(out, chain_i, sk_seed, pub_seed, addr)].

    Implements [genSK chain_i sk_seed pub_seed a].  Mutates [addr]:
    at exit its chain/hash/keyAndMask words are [chain_i]/[0]/[0]. *)

Definition derive_sk_spec : ident * funspec :=
  DECLARE _derive_sk
  WITH out_ptr : val, ss_ptr : val, ps_ptr : val, a_ptr : val,
       chain_i : Z,
       sk_seed : block, pub_seed : block, a : adrs,
       sh_o : share, sh_ss : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tuint, tptr tuchar, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_o; writable_share sh_a;
          readable_share sh_ss; readable_share sh_ps;
          0 <= chain_i < Z.of_nat len;
          Zlength sk_seed = n_bytes; Zlength pub_seed = n_bytes)
    PARAMS (out_ptr; Vint (Int.repr chain_i); ss_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_o  (tarray tuchar n_bytes) out_ptr;
         data_at sh_ss (tarray tuchar n_bytes) (block_to_vals sk_seed)  ss_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_o (tarray tuchar n_bytes)
           (block_to_vals (genSK (Z.to_nat chain_i) sk_seed pub_seed a))
           out_ptr;
         data_at sh_ss (tarray tuchar n_bytes) (block_to_vals sk_seed)  ss_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals (derive_sk_addr_post a chain_i)) a_ptr).

(* ================================================================= *)
(** ** [chain(buf, start, steps, pub_seed, addr)] -- iterates [thash_f]
    [steps] times in place on [buf].  Callers set [addr[5]] (chain
    address) before calling; this function only touches [addr[6]]
    (hash address) and [addr[7]] (keyAndMask). *)

Definition chain_spec : ident * funspec :=
  DECLARE _chain
  WITH buf_ptr : val, ps_ptr : val, a_ptr : val,
       start : Z, steps : Z,
       in_buf : block, pub_seed : block, a : adrs,
       sh_b : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tuint, tuint, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_b; writable_share sh_a;
          readable_share sh_ps;
          0 <= start; 0 <= steps; start + steps <= Z.of_nat w_pred;
          Zlength in_buf = n_bytes; Zlength pub_seed = n_bytes)
    PARAMS (buf_ptr; Vint (Int.repr start); Vint (Int.repr steps);
            ps_ptr; a_ptr)
    SEP (data_at sh_b (tarray tuchar n_bytes) (block_to_vals in_buf)   buf_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_b (tarray tuchar n_bytes)
           (block_to_vals
              (chain in_buf (Z.to_nat start) (Z.to_nat steps) pub_seed a))
           buf_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals
                    (chain_addr_post a (Z.to_nat start) (Z.to_nat steps)))
                 a_ptr).

(* ================================================================= *)
(** ** [expand_digits(digits, msg)] -- base-16 expansion + checksum.

    Writes [len = 67] bytes, each in [[0, 15]]. *)

Definition expand_digits_spec : ident * funspec :=
  DECLARE _expand_digits
  WITH d_ptr : val, m_ptr : val,
       msg : block,
       sh_d : share, sh_m : share
  PRE [ tptr tuchar, tptr tuchar ]
    PROP (writable_share sh_d; readable_share sh_m;
          Zlength msg = n_bytes; Forall byte_ok msg)
    PARAMS (d_ptr; m_ptr)
    SEP (data_at_ sh_d (tarray tuchar (Z.of_nat len)) d_ptr;
         data_at sh_m (tarray tuchar n_bytes) (block_to_vals msg) m_ptr)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at sh_d (tarray tuchar (Z.of_nat len))
           (digits_to_vals (expand_msg msg)) d_ptr;
         data_at sh_m (tarray tuchar n_bytes) (block_to_vals msg) m_ptr).

(* ================================================================= *)
(** ** Helper funspec bundle. *)

Definition Gprog_helpers : funspecs :=
  [ addr_bytes_spec;
    prf_spec;
    prf_keygen_spec;
    thash_f_spec;
    derive_sk_spec;
    chain_spec;
    expand_digits_spec ].
