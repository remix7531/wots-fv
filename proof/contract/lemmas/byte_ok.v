(** * contract.lemmas.byte_ok: byte-range propagation through model. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.

Open Scope Z_scope.

(* ================================================================= *)
(** ** [byte_ok] propagation through [F] / [PRF_keygen] / [thash_f]. *)

(** [SHA256_byte_ok] is an axiom in [model.wots]; the rest below is proved. *)

Lemma F_byte_ok : forall KEY M, Forall byte_ok (F KEY M).
Proof. intros. unfold F. apply SHA256_byte_ok. Qed.

Lemma thash_f_byte_ok : forall X SEED A, Forall byte_ok (thash_f X SEED A).
Proof. intros. unfold thash_f. apply F_byte_ok. Qed.

Lemma chain_byte_ok : forall s X i SEED A,
  Forall byte_ok X -> Forall byte_ok (chain X i s SEED A).
Proof.
  induction s; intros X i SEED A Hb; simpl; [assumption|].
  apply thash_f_byte_ok.
Qed.

Lemma pkFromSig_Forall_byte_ok : forall msg sig pub a,
  Forall (Forall byte_ok) sig ->
  Forall (Forall byte_ok) (pkFromSig msg sig pub a).
Proof.
  intros msg sig pub a Hs.
  unfold pkFromSig, for_idx.
  apply Forall_map, Forall_forall.
  intros k _.
  apply chain_byte_ok.

  (* Case split: is [k] in-bounds for [sig]? *)
  destruct (Nat.lt_ge_cases k (length sig)) as [Hlt|Hge].
  - (* in-bounds: the k-th block of [sig] is byte_ok *)
    rewrite Forall_forall in Hs.
    apply Hs.
    apply nth_In.
    exact Hlt.
  - (* out-of-bounds: [nth] returns the default zero block *)
    rewrite nth_overflow by exact Hge.
    unfold default, default_block, zero_block.
    apply Forall_forall.
    intros x Hin.
    apply repeat_spec in Hin.
    subst.
    unfold byte_ok. lia.
Qed.

(* ================================================================= *)
(** ** Byte injectivity. *)

(** [Int.repr] is injective on in-range bytes. *)
Lemma Int_repr_inj_byte_ok : forall x y,
  byte_ok x -> byte_ok y -> Int.repr x = Int.repr y -> x = y.
Proof.
  intros x y Hx Hy Heq.
  apply (f_equal Int.unsigned) in Heq.
  unfold byte_ok in *.
  rewrite !Int.unsigned_repr in Heq by rep_lia.
  exact Heq.
Qed.

Lemma byte_ok_mod_id : forall x, byte_ok x -> x mod 256 = x.
Proof. intros x Hb. unfold byte_ok in Hb. apply Z.mod_small; lia. Qed.
