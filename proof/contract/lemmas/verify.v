(** * contract.lemmas.verify: the final link from [pkFromSig] equality
    to [verify = true] used in [body_wots_verify]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.
From wots Require Import contract.lemmas.data_at.
From wots Require Import contract.lemmas.byte_ok.
From wots Require Import contract.lemmas.pkgen_sign.

Open Scope Z_scope.

Lemma map_block_ints_inj : forall l1 l2,
  Forall byte_ok l1 -> Forall byte_ok l2 ->
  map (fun x : byte => Int.repr (x mod 256)) l1
  = map (fun x : byte => Int.repr (x mod 256)) l2 -> l1 = l2.
Proof.
  induction l1 as [|x xs IH]; intros [|y ys] Hx Hy Heq;
    simpl in Heq; try discriminate; [reflexivity|].
  inversion Hx as [|? ? Hxhd Hxtl]; subst.
  inversion Hy as [|? ? Hyhd Hytl]; subst.
  rewrite !byte_ok_mod_id in Heq by assumption.

  assert (Hhd : Int.repr x = Int.repr y)
    by (exact (f_equal (@hd _ Int.zero) Heq)).
  assert (Htl : map (fun x0 => Int.repr (x0 mod 256)) xs =
                map (fun x0 => Int.repr (x0 mod 256)) ys)
    by (exact (f_equal (@tl _) Heq)).

  f_equal.
  - apply (Int_repr_inj_byte_ok x y Hxhd Hyhd Hhd).
  - apply (IH ys Hxtl Hytl Htl).
Qed.

(** Equal-length prefix cancellation for [++]. *)
Lemma app_eq_same_length : forall {A} (a b c d : list A),
  length a = length b -> a ++ c = b ++ d -> a = b /\ c = d.
Proof.
  induction a as [|x a IH]; intros [|y b] c d Hl Heq;
    simpl in *; try discriminate.
  - split; [reflexivity | assumption].
  - injection Heq as Hhd Htl.
    injection Hl as Hl.
    specialize (IH _ _ _ Hl Htl) as [Ha Hc].
    subst.
    split; reflexivity.
Qed.

(** Splitting a flat byte-list into equal-length blocks is unique. *)
Lemma concat_eq_blocks : forall (bs1 bs2 : list block),
  length bs1 = length bs2 ->
  Forall (fun b => Zlength b = n_bytes) bs1 ->
  Forall (fun b => Zlength b = n_bytes) bs2 ->
  concat bs1 = concat bs2 -> bs1 = bs2.
Proof.
  induction bs1 as [|b1 bs1 IH]; intros bs2 Hl HF1 HF2 Hc.
  - destruct bs2; [reflexivity | simpl in Hl; discriminate].
  - destruct bs2 as [|b2 bs2]; [simpl in Hl; discriminate|].
    simpl in Hc.
    inversion HF1 as [|? ? Hzb1 Hzbs1]; subst.
    inversion HF2 as [|? ? Hzb2 Hzbs2]; subst.

    (* Convert Zlength constraints to nat-length for app_eq_same_length. *)
    assert (Hlb1 : length b1 = n).
    { rewrite Zlength_correct in Hzb1.
      change n_bytes with (Z.of_nat n) in Hzb1.
      apply Nat2Z.inj in Hzb1.
      exact Hzb1. }
    assert (Hlb2 : length b2 = n).
    { rewrite Zlength_correct in Hzb2.
      change n_bytes with (Z.of_nat n) in Hzb2.
      apply Nat2Z.inj in Hzb2.
      exact Hzb2. }
    assert (Hlen_eq : length b1 = length b2)
      by (rewrite Hlb1, Hlb2; reflexivity).

    (* Split the concat equality at the head block boundary. *)
    destruct (app_eq_same_length b1 b2 (concat bs1) (concat bs2)
                Hlen_eq Hc) as [Hb Hbs].
    subst b2.
    f_equal.
    apply IH; try assumption.
    simpl in Hl. lia.
Qed.

(** [Forall byte_ok] commutes with [concat] for a list of byte_ok blocks. *)
Lemma Forall_byte_ok_concat : forall (bs : list block),
  Forall (Forall byte_ok) bs -> Forall byte_ok (concat bs).
Proof.
  intros bs HF.
  apply Forall_forall. intros x Hx.
  rewrite in_concat in Hx.
  destruct Hx as [l [Hxl Hlbs]].
  rewrite Forall_forall in HF. specialize (HF l Hlbs).
  rewrite Forall_forall in HF. apply HF, Hxl.
Qed.

Lemma pk_int_neq_implies_verify_false :
  forall pk sig msg pub_seed a,
  block_ints (concat (pkFromSig msg sig pub_seed a))
    <> block_ints (concat pk) ->
  verify pk sig msg pub_seed a = false.
Proof.
  intros pk sig msg pub_seed a Hneq.
  unfold verify.
  destruct (list_eq_dec _ _ _) as [He|Hne]; [|reflexivity].
  exfalso.
  apply Hneq.
  unfold block_ints.
  f_equal.
  f_equal.
  exact He.
Qed.

Lemma pk_int_eq_implies_pkFromSig :
  forall pk sig msg pub_seed a,
  length pk = len ->
  Forall (fun b => Zlength b = n_bytes) pk ->
  Forall (fun b => Zlength b = n_bytes) sig ->
  Forall (Forall byte_ok) sig ->
  Forall (Forall byte_ok) pk ->
  block_ints (concat (pkFromSig msg sig pub_seed a))
    = block_ints (concat pk) ->
  pkFromSig msg sig pub_seed a = pk.
Proof.
  intros pk sig msg pub_seed a Hlenpk HZpk HZsig Hbsig Hbpk Heq.
  unfold block_ints in Heq.

  (* Build byte_ok membership for the two flat concatenations. *)
  pose proof (Forall_byte_ok_concat _
    (pkFromSig_Forall_byte_ok msg sig pub_seed a Hbsig)) as Hbconcat_pkfs.
  pose proof (Forall_byte_ok_concat _ Hbpk) as Hbconcat_pk.

  (* Lift the int-list equality to a flat byte equality. *)
  assert (Hflat : concat (pkFromSig msg sig pub_seed a) = concat pk).
  { apply (map_block_ints_inj _ _ Hbconcat_pkfs Hbconcat_pk Heq). }

  (* Uniqueness of fixed-width block decomposition. *)
  apply concat_eq_blocks.
  - unfold pkFromSig, for_idx.
    rewrite length_map, length_seq.
    symmetry.
    exact Hlenpk.
  - apply pkFromSig_Forall_Zlength.
    assumption.
  - assumption.
  - assumption.
Qed.

Lemma pk_int_eq_implies_verify :
  forall pk sig msg pub_seed a,
  length pk = len ->
  Forall (fun b => Zlength b = n_bytes) pk ->
  Forall (fun b => Zlength b = n_bytes) sig ->
  Forall (Forall byte_ok) sig ->
  Forall (Forall byte_ok) pk ->
  block_ints (concat (pkFromSig msg sig pub_seed a))
    = block_ints (concat pk) ->
  verify pk sig msg pub_seed a = true.
Proof.
  intros.
  unfold verify.
  rewrite (pk_int_eq_implies_pkFromSig pk sig msg pub_seed a); auto.
  destruct (list_eq_dec _ _ _); [reflexivity | contradiction].
Qed.
