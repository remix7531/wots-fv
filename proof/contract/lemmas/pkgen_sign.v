(** * contract.lemmas.pkgen_sign: per-iteration block / addr steps
    shared by [body_wots_pkgen], [body_wots_sign], and
    [body_wots_pk_from_sig]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.
From wots Require Import contract.lemmas.chain.
From wots Require Import contract.lemmas.data_at.
From wots Require Import model.notation.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Parametric addr-step helper. *)

(** [addr_step steps a i] threads the per-iteration chain step through
    the address record. The [steps] argument gives the chain length at
    each prior index; pkgen uses the constant [w_pred], while sign uses
    [nth k (expand_msg msg) 0]. *)
Definition addr_step (steps : nat -> nat) (a : adrs) (i : nat) : adrs :=
  match i with
  | O   => a
  | S k => chain_addr_post (derive_sk_addr_post a (Z.of_nat k)) 0 (steps k)
  end.

(** [addr_step] preserves structural (non-chain/hash/km) fields. *)
Lemma addr_step_struct : forall steps a i,
  adrs_struct_eq (addr_step steps a i) a.
Proof.
  intros steps a [|k]; [apply adrs_struct_eq_refl|].
  unfold adrs_struct_eq. 
  simpl.
  destruct (steps k); destruct a; simpl;
    repeat split; reflexivity.
Qed.

(** Parametric step successor: the post-state of the in-loop chain call
    matches [addr_step steps a (S iN)]. *)
Lemma chain_addr_post_derive_sk_addr_step :
  forall steps a (iZ : Z) (iN : nat),
  iZ = Z.of_nat iN ->
  chain_addr_post (derive_sk_addr_post (addr_step steps a iN) iZ)
                  0 (steps iN)
  = addr_step steps a (S iN).
Proof.
  intros steps a iZ iN ->.
  simpl addr_step. 
  f_equal.
  unfold derive_sk_addr_post.
  destruct (addr_step_struct steps a iN) as (Hl & Hth & Htl & Hty & Ho).
  destruct a, (addr_step _ _ iN). 
  simpl in *.
  subst.
  reflexivity.
Qed.

(** Parametric chain/genSK struct-eq: the in-loop chain call from
    [addr_step steps a iN] is structurally equivalent to a chain call
    launched from [setChainAddress a (Z.of_nat iN)], provided both have
    matching length [steps iN]. *)
Lemma chain_genSK_addr_step_eq :
  forall steps sk pub a (iZ : Z) (iN : nat),
  iZ = Z.of_nat iN ->
  chain (genSK iN sk pub (addr_step steps a iN)) 0 (steps iN) pub
        (derive_sk_addr_post (addr_step steps a iN) iZ)
  = let a'' := setChainAddress a (Z.of_nat iN) in
    chain (genSK iN sk pub a'') 0 (steps iN) pub a''.
Proof.
  intros steps sk pub a iZ iN ->.
  simpl.

  (* The canonical [setChainAddress] form shares structural fields
     with any [addr_step]-derived state by transitivity. *)
  pose proof (adrs_struct_eq_trans _ _ _
                (addr_step_struct steps a iN)
                (adrs_struct_eq_sym _ _
                  (setChainAddress_struct_eq a (Z.of_nat iN))))
    as Hsca.

  rewrite (genSK_struct_eq iN sk pub _ _ Hsca).
  apply chain_struct_eq; [exact Hsca|].
  unfold derive_sk_addr_post.
  destruct a.
  reflexivity.
Qed.

(* ================================================================= *)
(** ** Helpers for wots_pkgen. *)

Definition pkgen_block (sk_seed pub_seed : block) (a : adrs) (i : nat)
  : block :=
  let a := setChainAddress a (Z.of_nat i) in
  chain (genSK i sk_seed pub_seed a) 0 w_pred pub_seed a.

Definition pkgen_addr_step (a : adrs) (i : nat) : adrs :=
  addr_step (fun _ => w_pred) a i.

Lemma pkgen_addr_step_len : forall a,
  pkgen_addr_step a 67 = wotsfv_pkgen_addr_post a.
Proof. reflexivity. Qed.

Lemma pkgen_block_Zlength : forall sk pub a i,
  Zlength (pkgen_block sk pub a i) = n_bytes.
Proof.
  intros.
  unfold pkgen_block.
  apply chain_Zlength, genSK_Zlength.
Qed.

(** Post-state of the in-loop chain call matches [pkgen_addr_step a (S i)]. *)
Lemma chain_addr_post_derive_sk_pkgen_step :
  forall a (iZ : Z) (iN : nat),
  iZ = Z.of_nat iN ->
  chain_addr_post (derive_sk_addr_post (pkgen_addr_step a iN) iZ) 0 w_pred
  = pkgen_addr_step a (S iN).
Proof.
  intros a iZ iN HiZ.
  exact (chain_addr_post_derive_sk_addr_step (fun _ => w_pred) a iZ iN HiZ).
Qed.

(* ================================================================= *)
(** ** Helpers for wots_pk_from_sig. *)

Definition pkFromSig_block (sig : list block) (msg pub : block)
                           (a : adrs) (i : nat) : block :=
  let a' := setChainAddress a (Z.of_nat i) in
  chain (nth i sig default) (nth i (expand_msg msg) 0%nat)
        (w_pred - nth i (expand_msg msg) 0%nat) pub a'.

Lemma pkFromSig_block_Zlength : forall sig msg pub a i,
  Zlength (nth i sig default) = n_bytes ->
  Zlength (pkFromSig_block sig msg pub a i) = n_bytes.
Proof.
  intros.
  unfold pkFromSig_block.
  apply chain_Zlength.
  assumption.
Qed.

Lemma pkFromSig_length : forall msg sig pub a,
  Datatypes.length (pkFromSig msg sig pub a) = len.
Proof.
  intros.
  unfold pkFromSig, for_idx.
  rewrite length_map, length_seq.
  reflexivity.
Qed.

Lemma pkFromSig_Forall_Zlength : forall msg sig pub a,
  Forall (fun b => Zlength b = n_bytes) sig ->
  Forall (fun b => Zlength b = n_bytes)
         (pkFromSig msg sig pub a).
Proof.
  intros msg sig pub a Hs.
  unfold pkFromSig, for_idx.
  apply Forall_map, Forall_forall.
  intros k _.
  apply chain_Zlength, nth_block_Zlength_default, Hs.
Qed.

(** The in-loop chain call (from wots_pk_from_sig) computes a block that
    is structurally equivalent to [pkFromSig_block sig msg pub a iN],
    when the in-loop addr [A] has the same struct fields as [a]. *)
Lemma chain_pkFromSig_block_struct_eq :
  forall sig msg pub (iN : nat) A a,
  adrs_struct_eq A a ->
  chain (nth iN sig default) (nth iN (expand_msg msg) 0%nat)
        (w_pred - nth iN (expand_msg msg) 0%nat) pub
        (setChainAddress A (Z.of_nat iN))
  = pkFromSig_block sig msg pub a iN.
Proof.
  intros sig msg pub iN A a (Hl & Hth & Htl & Hty & Ho).
  unfold pkFromSig_block.
  apply chain_struct_eq;
    destruct A, a; simpl in *; subst; repeat split; reflexivity.
Qed.

(* ================================================================= *)
(** ** Helpers for wots_sign. *)

Definition sign_block (sk pub : block) (a : adrs) (msg : block)
                      (i : nat) : block :=
  let a'' := setChainAddress a (Z.of_nat i) in
  chain (genSK i sk pub a'') 0 (nth i (expand_msg msg) 0%nat) pub a''.

Definition sign_addr_step (a : adrs) (msg : block) (i : nat) : adrs :=
  addr_step (fun k => nth k (expand_msg msg) 0%nat) a i.

Lemma sign_addr_step_len : forall a msg,
  sign_addr_step a msg 67 = wotsfv_sign_addr_post a msg.
Proof. reflexivity. Qed.

Lemma sign_block_Zlength : forall sk pub a msg i,
  Zlength (sign_block sk pub a msg i) = n_bytes.
Proof.
  intros.
  unfold sign_block.
  apply chain_Zlength, genSK_Zlength.
Qed.

(** Post-state of the in-loop chain call matches
    [sign_addr_step a msg (S i)]. *)
Lemma chain_addr_post_derive_sk_sign_step :
  forall a msg (iZ : Z) (iN : nat),
  iZ = Z.of_nat iN ->
  chain_addr_post (derive_sk_addr_post (sign_addr_step a msg iN) iZ)
                  0 (nth iN (expand_msg msg) 0%nat)
  = sign_addr_step a msg (S iN).
Proof.
  intros a msg iZ iN HiZ.
  exact (chain_addr_post_derive_sk_addr_step
           (fun k => nth k (expand_msg msg) 0%nat) a iZ iN HiZ).
Qed.

(** The in-loop chain call produces [sign_block sk pub a msg i]. *)
Lemma chain_genSK_sign_step_eq :
  forall sk pub a msg (iZ : Z) (iN : nat),
  iZ = Z.of_nat iN ->
  chain (genSK iN sk pub (sign_addr_step a msg iN)) 0
        (nth iN (expand_msg msg) 0%nat) pub
        (derive_sk_addr_post (sign_addr_step a msg iN) iZ)
  = sign_block sk pub a msg iN.
Proof.
  intros sk pub a msg iZ iN HiZ.
  unfold sign_block.
  exact (chain_genSK_addr_step_eq
           (fun k => nth k (expand_msg msg) 0%nat)
           sk pub a iZ iN HiZ).
Qed.

(** The in-loop chain call produces [pkgen_block sk pub a i]. *)
Lemma chain_genSK_pkgen_step_eq :
  forall sk pub a (iZ : Z) (iN : nat),
  iZ = Z.of_nat iN ->
  chain (genSK iN sk pub (pkgen_addr_step a iN)) 0 w_pred pub
        (derive_sk_addr_post (pkgen_addr_step a iN) iZ)
  = pkgen_block sk pub a iN.
Proof.
  intros sk pub a iZ iN HiZ.
  unfold pkgen_block.
  exact (chain_genSK_addr_step_eq (fun _ => w_pred) sk pub a iZ iN HiZ).
Qed.
