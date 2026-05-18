(** * contract.public: VST funspecs for the WOTS+ C library.

    Re-exports the pure functional model in [model.wots] and wraps it
    in VST contracts for the three public entry points.  Internal
    helper funspecs live in [contract.helpers]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Export floyd.proofauto.
From wots Require Export model.wots clight.wots.

#[export] Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Open Scope Z_scope.

(* ================================================================= *)
(** ** C-level representation bridges. *)

(** A [block] (list of [Z]-bytes) as a list of VST [val]s. *)
Definition block_to_vals (b : block) : list val :=
  map (fun x : byte => Vubyte (Byte.repr x)) b.

Definition blocks_to_vals (bs : list block) : list val :=
  map (fun x : byte => Vubyte (Byte.repr x)) (concat bs).

(** An [adrs] record as the 8-uint array the C code expects.
    Order matches RFC Sec. 2.5: layer | tree-hi | tree-lo | type |
    OTS | chain | hash | keyAndMask. *)
Definition adrs_to_vals (a : adrs) : list val :=
  [ Vint (Int.repr (adrs_layer a));
    Vint (Int.repr (adrs_tree_hi a));
    Vint (Int.repr (adrs_tree_lo a));
    Vint (Int.repr (adrs_type  a));
    Vint (Int.repr (adrs_ots   a));
    Vint (Int.repr (adrs_chain a));
    Vint (Int.repr (adrs_hash  a));
    Vint (Int.repr (adrs_keyAndMask a)) ].

Definition t_addr : type := tarray tuint 8.

Definition n_bytes : Z := Z.of_nat n.

(** Two addresses agree on the five fields that WOTS+'s per-chunk
    operations leave untouched (layer / tree-hi / tree-lo / type / OTS).
    Used as the loop invariant in [body_wots_pk_from_sig] and as the
    precondition shared by every [_struct_eq] lemma in [chain.v] and
    [pkgen_sign.v]. *)
Definition adrs_struct_eq (a b : adrs) : Prop :=
  adrs_layer a   = adrs_layer b
  /\ adrs_tree_hi a = adrs_tree_hi b
  /\ adrs_tree_lo a = adrs_tree_lo b
  /\ adrs_type a    = adrs_type b
  /\ adrs_ots a     = adrs_ots b.

Lemma adrs_struct_eq_refl : forall a, adrs_struct_eq a a.
Proof. intros; repeat split. Qed.

Lemma adrs_struct_eq_sym : forall a b,
  adrs_struct_eq a b -> adrs_struct_eq b a.
Proof. intros a b (?&?&?&?&?); repeat split; symmetry; assumption. Qed.

Lemma adrs_struct_eq_trans : forall a b c,
  adrs_struct_eq a b -> adrs_struct_eq b c -> adrs_struct_eq a c.
Proof. intros a b c (?&?&?&?&?) (?&?&?&?&?); repeat split; congruence. Qed.

(** The three address setters used by WOTS+ touch only the chain /
    hash / keyAndMask fields, hence preserve the structural ones. *)
Lemma setChainAddress_struct_eq : forall a v,
  adrs_struct_eq (setChainAddress a v) a.
Proof. intros [????????] v; repeat split; reflexivity. Qed.

Lemma setHashAddress_struct_eq : forall a v,
  adrs_struct_eq (setHashAddress a v) a.
Proof. intros [????????] v; repeat split; reflexivity. Qed.

Lemma setKeyAndMask_struct_eq : forall a v,
  adrs_struct_eq (setKeyAndMask a v) a.
Proof. intros [????????] v; repeat split; reflexivity. Qed.

(* ================================================================= *)
(** ** [rep_lia] hints for WOTS+ parameter constants.

    Register parameter equalities with [rep_lia] so the solver sees
    [n_bytes], [pk_bytes], [sig_bytes], [len], [len_1], [len_2] and
    [w_pred] as their numeric values automatically. *)

Lemma n_bytes_eq          : n_bytes          = 32.      Proof. reflexivity. Qed.
Lemma pk_bytes_eq         : pk_bytes         = 2144.    Proof. reflexivity. Qed.
Lemma sig_bytes_eq        : sig_bytes        = 2144.    Proof. reflexivity. Qed.
Lemma len_eq_Z            : Z.of_nat len     = 67.      Proof. reflexivity. Qed.
Lemma len_1_eq_Z          : Z.of_nat len_1   = 64.      Proof. reflexivity. Qed.
Lemma len_2_eq_Z          : Z.of_nat len_2   = 3.       Proof. reflexivity. Qed.
Lemma w_pred_eq           : w_pred           = 15%nat.  Proof. reflexivity. Qed.
Lemma Byte_modulus_eq     : Byte.modulus     = 256.     Proof. reflexivity. Qed.
Lemma Byte_max_unsigned_eq: Byte.max_unsigned = 255.    Proof. reflexivity. Qed.
Lemma Int_max_unsigned_eq : Int.max_unsigned = 4294967295. Proof. reflexivity. Qed.

#[export] Hint Rewrite
  n_bytes_eq pk_bytes_eq sig_bytes_eq
  len_eq_Z len_1_eq_Z len_2_eq_Z
  Byte_modulus_eq Byte_max_unsigned_eq Int_max_unsigned_eq
  : rep_lia.

(* ================================================================= *)
(** ** [Inhabitant] instances for VST's [Znth] / [nth_Znth]. *)

#[export] Instance Inhabitant_block : Inhabitant block := zero_block.
#[export] Instance Inhabitant_adrs  : Inhabitant adrs  :=
  Build_adrs 0 0 0 0 0 0 0 0.

(** A [list nat] of base-16 digits as a list of VST byte [val]s.
    [expand_digits] stores each digit as one [uint8_t]. *)
Definition digits_to_vals (ds : list nat) : list val :=
  map (fun d : nat => Vubyte (Byte.repr (Z.of_nat d))) ds.

(** Post-state of the C [addr] array after the loop in [chain].
    - If [steps = 0] the loop body never runs, so [addr] is untouched.
    - Otherwise the last iteration sets [addr[6] = start + steps - 1]
      via [setHashAddress] and then [thash_f] leaves [addr[7] = 1]. *)
Definition chain_addr_post (a : adrs) (start steps : nat) : adrs :=
  match steps with
  | O   => a
  | S _ => setKeyAndMask
             (setHashAddress a (Z.of_nat (start + steps - 1))) 1
  end.

(** Post-state of the C [addr] array after [derive_sk]: chain=chain_i,
    hash=0, keyAndMask=0. *)
Definition derive_sk_addr_post (a : adrs) (chain_i : Z) : adrs :=
  setKeyAndMask
    (setHashAddress
       (setChainAddress a chain_i) 0) 0.

(** Post-state of [addr] after the public [wots_pkgen] loop:
    last iteration runs [derive_sk] (chain=len-1, hash=0, km=0)
    followed by [chain] over 15 steps (hash=14, km=1). *)
Definition wotsfv_pkgen_addr_post (a : adrs) : adrs :=
  chain_addr_post
    (derive_sk_addr_post a (Z.of_nat (len - 1))) 0 w_pred.

(** Post-state of [addr] after the public [wots_sign] loop.
    Depends on the last message digit [msg[len-1]]: if it's zero the
    inner [chain] call is a no-op and addr is left in the post-
    [derive_sk] state. *)
Definition wotsfv_sign_addr_post (a : adrs) (msg : block) : adrs :=
  chain_addr_post
    (derive_sk_addr_post a (Z.of_nat (len - 1))) 0
    (nth (len - 1) (expand_msg msg) 0%nat).

(* ================================================================= *)
(** ** Public API funspecs. *)

Definition wotsfv_pkgen_spec : ident * funspec :=
  DECLARE _wotsfv_pkgen
  WITH pk_ptr : val, sk_ptr : val, ps_ptr : val, a_ptr : val,
       sk_seed : block, pub_seed : block, a : adrs,
       sh_pk : share, sh_sk : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_pk; writable_share sh_a;
          readable_share sh_sk; readable_share sh_ps)
    PARAMS (pk_ptr; sk_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_pk (tarray tuchar pk_bytes) pk_ptr;
         data_at sh_sk (tarray tuchar n_bytes) (block_to_vals sk_seed) sk_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)        a_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh_pk (tarray tuchar pk_bytes)
           (blocks_to_vals (genPK sk_seed pub_seed a)) pk_ptr;
         data_at sh_sk (tarray tuchar n_bytes) (block_to_vals sk_seed) sk_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals (wotsfv_pkgen_addr_post a)) a_ptr).

Definition wotsfv_sign_spec : ident * funspec :=
  DECLARE _wotsfv_sign
  WITH sig_ptr : val, msg_ptr : val, sk_ptr : val, ps_ptr : val, a_ptr : val,
       msg : block, sk_seed : block, pub_seed : block, a : adrs,
       sh_sig : share, sh_m : share, sh_sk : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_sig; writable_share sh_a;
          readable_share sh_m; readable_share sh_sk; readable_share sh_ps;
          Forall byte_ok msg)
    PARAMS (sig_ptr; msg_ptr; sk_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_sig (tarray tuchar sig_bytes) sig_ptr;
         data_at sh_m  (tarray tuchar n_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_sk (tarray tuchar n_bytes) (block_to_vals sk_seed)  sk_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    PROP ()
    RETURN ()
    SEP (data_at sh_sig (tarray tuchar sig_bytes)
           (blocks_to_vals (sign msg sk_seed pub_seed a)) sig_ptr;
         data_at sh_m  (tarray tuchar n_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_sk (tarray tuchar n_bytes) (block_to_vals sk_seed)  sk_ptr;
         data_at sh_ps (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a  t_addr
                 (adrs_to_vals (wotsfv_sign_addr_post a msg)) a_ptr).

Definition wotsfv_pk_from_sig_spec : ident * funspec :=
  DECLARE _wotsfv_pk_from_sig
  WITH pk_ptr : val, sig_ptr : val, msg_ptr : val, ps_ptr : val, a_ptr : val,
       sig : list block, msg : block, pub_seed : block, a : adrs,
       sh_pk : share, sh_sig : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_pk; writable_share sh_a;
          readable_share sh_sig; readable_share sh_m; readable_share sh_ps;
          length sig = len; Forall byte_ok msg;
          Forall (fun b => Zlength b = n_bytes) sig)
    PARAMS (pk_ptr; sig_ptr; msg_ptr; ps_ptr; a_ptr)
    SEP (data_at_ sh_pk (tarray tuchar pk_bytes) pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes) (blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar n_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a   t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tvoid ]
    EX a' : adrs,
    PROP ()
    RETURN ()
    SEP (data_at sh_pk (tarray tuchar pk_bytes)
           (blocks_to_vals (pkFromSig msg sig pub_seed a)) pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes) (blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar n_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a   t_addr                  (adrs_to_vals a')        a_ptr).

Definition wotsfv_verify_spec : ident * funspec :=
  DECLARE _wotsfv_verify
  WITH pk_ptr : val, sig_ptr : val, msg_ptr : val, ps_ptr : val, a_ptr : val,
       pk : list block, sig : list block, msg : block, pub_seed : block, a : adrs,
       sh_pk : share, sh_sig : share, sh_m : share, sh_ps : share, sh_a : share
  PRE [ tptr tuchar, tptr tuchar, tptr tuchar, tptr tuchar, tptr tuint ]
    PROP (writable_share sh_a;
          readable_share sh_pk; readable_share sh_sig;
          readable_share sh_m; readable_share sh_ps;
          length pk = len; length sig = len; Forall byte_ok msg;
          Forall (fun b => Zlength b = n_bytes) sig;
          Forall (fun b => Zlength b = n_bytes) pk;
          Forall (Forall byte_ok) sig;
          Forall (Forall byte_ok) pk)
    PARAMS (pk_ptr; sig_ptr; msg_ptr; ps_ptr; a_ptr)
    SEP (data_at sh_pk  (tarray tuchar pk_bytes)  (blocks_to_vals pk)  pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes) (blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar n_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a   t_addr                  (adrs_to_vals a)         a_ptr)
  POST [ tint ]
    EX a' : adrs,
    PROP ()
    RETURN (Vint (Int.repr (if verify pk sig msg pub_seed a then 0 else -1)))
    SEP (data_at sh_pk  (tarray tuchar pk_bytes)  (blocks_to_vals pk)  pk_ptr;
         data_at sh_sig (tarray tuchar sig_bytes) (blocks_to_vals sig) sig_ptr;
         data_at sh_m   (tarray tuchar n_bytes) (block_to_vals msg)      msg_ptr;
         data_at sh_ps  (tarray tuchar n_bytes) (block_to_vals pub_seed) ps_ptr;
         data_at sh_a   t_addr                  (adrs_to_vals a')        a_ptr).
