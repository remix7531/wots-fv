(** * contract.lemmas.chain: length + structural-field equalities for
    [SHA256] / [thash_f] / [chain] / [genSK]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.

Open Scope Z_scope.

(* ================================================================= *)
(** ** Lengths -- [SHA256] / [thash_f] / [chain] / [genSK]. *)

(** SHA256 returns an [n]-byte block. *)
Lemma SHA256_Zlength : forall m, Zlength (SHA256 m) = n_bytes.
Proof.
  intros.
  rewrite Zlength_correct, SHA256_length.
  reflexivity.
Qed.

Lemma thash_f_Zlength : forall X SEED a,
  Zlength (thash_f X SEED a) = n_bytes.
Proof. 
  intros.
  unfold thash_f, F.
  apply SHA256_Zlength.
Qed.

Lemma chain_Zlength : forall X start steps SEED a,
  Zlength X = n_bytes ->
  Zlength (chain X start steps SEED a) = n_bytes.
Proof.
  intros X start steps SEED a HX.
  destruct steps; simpl; [exact HX | apply thash_f_Zlength].
Qed.

Lemma genSK_Zlength : forall i sk pub a,
  Zlength (genSK i sk pub a) = n_bytes.
Proof. 
  intros.
  unfold genSK, PRF_keygen.
  apply SHA256_Zlength.
Qed.


(* ================================================================= *)
(** ** Structural-field equalities -- [genSK] / [thash_f] / [chain]. *)

(** [thash_f] is insensitive to its input's keyAndMask field (it
    re-sets it internally to 0 and 1).  Needed by [body_chain]. *)
Lemma thash_f_chain_addr_post_elim : forall X SEED a start j v,
  thash_f X SEED (setHashAddress (chain_addr_post a start j) v)
  = thash_f X SEED (setHashAddress a v).
Proof.
  intros.
  unfold thash_f.
  f_equal.
  { f_equal. 
    f_equal. 
    unfold chain_addr_post.
    destruct j; unfold setKeyAndMask, setHashAddress; reflexivity. }
  { do 3 f_equal. 
    unfold chain_addr_post.
    destruct j; unfold setKeyAndMask, setHashAddress; reflexivity. }
Qed.

(** Step relation for [chain_addr_post]: the loop body in [chain]
    does [upd_Znth 6] + [thash_f] which advances the post by one. *)
Lemma chain_addr_post_succ : forall a start j,
  chain_addr_post a start (S j) =
  setKeyAndMask (setHashAddress
                   (chain_addr_post a start j)
                   (Z.of_nat (start + j))) 1.
Proof.
  intros. 
  unfold chain_addr_post at 1.
  replace (start + S j - 1)%nat with (start + j)%nat by lia.
  destruct j.
  - (* branch: j = 0 -- chain_addr_post a start 0 reduces to a *)
    replace (start + 0)%nat with start by lia.
    reflexivity.
  - (* branch: j = S k -- post already has hash+km set *)
    unfold setHashAddress, setKeyAndMask. 
    reflexivity.
Qed.

(** genSK only depends on structural fields (chain gets overwritten). *)
Lemma genSK_struct_eq : forall i sk pub A A',
  adrs_struct_eq A A' ->
  genSK i sk pub A = genSK i sk pub A'.
Proof.
  intros i sk pub A A' (Hl & Hth & Htl & Hty & Ho).
  unfold genSK, PRF_keygen. 
  do 3 f_equal.
  destruct A, A'; simpl in *; subst. 
  reflexivity.
Qed.

(** thash_f only depends on layer/tree/type/ots/chain/hash (km overwritten). *)
Lemma thash_f_struct_eq : forall X pub A A',
  adrs_struct_eq A A' ->
  adrs_chain A = adrs_chain A' ->
  adrs_hash A  = adrs_hash A' ->
  thash_f X pub A = thash_f X pub A'.
Proof.
  intros X pub A A' (Hl & Hth & Htl & Hty & Ho) Hc Hh.
  unfold thash_f, F, PRF. 
  do 4 f_equal.
  - destruct A, A'. 
    simpl in *. 
    subst. 
    reflexivity.
  - unfold xor. 
    do 4 f_equal.
    destruct A, A'. 
    simpl in *. 
    subst.
    reflexivity.
Qed.

(** chain only depends on layer/tree/type/ots/chain (hash and km overwritten). *)
Lemma chain_struct_eq : forall s X start pub A A',
  adrs_struct_eq A A' ->
  adrs_chain A = adrs_chain A' ->
  chain X start s pub A = chain X start s pub A'.
Proof.
  induction s; intros X start pub A A' Hs Hc; [reflexivity|].
  simpl chain.
  rewrite (IHs X start pub A A') by assumption.
  apply thash_f_struct_eq; try assumption. 
  reflexivity.
Qed.
