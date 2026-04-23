(** * contract.lemmas.data_at: list/VST val bridges for blocks and addrs.

    Length, [Znth], [upd_Znth], and round-trip lemmas for the
    [block_to_vals] / [blocks_to_vals] / [adrs_to_vals] /
    [digits_to_vals] encodings that funspecs use to expose pure-Rocq
    blocks to the C side. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.
From wots Require Import model.notation.

Open Scope Z_scope.

(* ================================================================= *)
(** ** [block_to_vals] -- list-shape and indexing. *)

Lemma block_to_vals_length : forall b,
  Zlength (block_to_vals b) = Zlength b.
Proof. intros. unfold block_to_vals. now rewrite Zlength_map. Qed.

Lemma block_to_vals_app : forall b1 b2,
  block_to_vals (b1 ++ b2) = block_to_vals b1 ++ block_to_vals b2.
Proof. intros. unfold block_to_vals. apply map_app. Qed.

Lemma Znth_block_to_vals : forall i b,
  0 <= i < Zlength b ->
  Znth i (block_to_vals b) = Vubyte (Byte.repr (Znth i b)).
Proof.
  intros. unfold block_to_vals.
  rewrite Znth_map by assumption.
  reflexivity.
Qed.

(** A list of blocks flattened to a VST [list int]. *)
Definition block_ints (b : block) : list int :=
  map (fun x : byte => Int.repr (x mod 256)) b.

Lemma Zlength_concat_fixed : forall (bs : list block),
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (concat bs) = 32 * Z.of_nat (length bs).
Proof.
  induction bs as [|b bs IH]; intros HF.
  - simpl.
    reflexivity.
  - inversion HF; subst.
    simpl concat.
    rewrite Zlength_app.
    rewrite IH by assumption.
    simpl length.
    rewrite Nat2Z.inj_succ, H1.
    change n_bytes with 32. lia.
Qed.

Lemma blocks_to_vals_eq_Vint : forall bs,
  blocks_to_vals bs = map Vint (block_ints (concat bs)).
Proof.
  intros. 
  unfold blocks_to_vals, block_ints, Vubyte.
  rewrite map_map.
  apply map_ext.
  intros x.
  f_equal.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  reflexivity.
Qed.

Lemma block_to_vals_eq_Vint : forall b,
  block_to_vals b = map Vint (block_ints b).
Proof.
  intros.
  unfold block_to_vals, block_ints, Vubyte.
  rewrite map_map.
  apply map_ext.
  intros x.
  f_equal.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  reflexivity.
Qed.

Lemma Zlength_block_ints : forall b,
  Zlength (block_ints b) = Zlength b.
Proof. 
  intros.
  unfold block_ints.
  apply Zlength_map.
Qed.

(* ================================================================= *)
(** ** [adrs_to_vals] -- list form and per-slot update. *)

(** The 8 word-fields of an adrs in serialization order. *)
Definition adrs_words (a : adrs) : list word :=
  [ adrs_layer a; adrs_tree_hi a; adrs_tree_lo a;
    adrs_type a; adrs_ots a; adrs_chain a;
    adrs_hash a; adrs_keyAndMask a ].

Lemma adrs_words_length : forall a, Zlength (adrs_words a) = 8.
Proof. reflexivity. Qed.

Lemma adrs_to_vals_eq : forall a,
  adrs_to_vals a = map (fun x : word => Vint (Int.repr x)) (adrs_words a).
Proof. reflexivity. Qed.

(** Updating slot 5/6/7 of [adrs_to_vals a] corresponds to the
    [setChainAddress]/[setHashAddress]/[setKeyAndMask] setters. *)

Lemma upd_adrs_5 : forall a v,
  upd_Znth 5 (adrs_to_vals a) (Vint (Int.repr v)) =
  adrs_to_vals (setChainAddress a v).
Proof.
  intros.
  destruct a;
  reflexivity.
Qed.

Lemma upd_adrs_6 : forall a v,
  upd_Znth 6 (adrs_to_vals a) (Vint (Int.repr v)) =
  adrs_to_vals (setHashAddress a v).
Proof.
  intros.
  destruct a;
  reflexivity.
Qed.

Lemma upd_adrs_7 : forall a v,
  upd_Znth 7 (adrs_to_vals a) (Vint (Int.repr v)) =
  adrs_to_vals (setKeyAndMask a v).
Proof.
  intros.
  destruct a;
  reflexivity.
Qed.

(* ================================================================= *)
(** ** [digits_to_vals] and [blocks_to_vals] length / split. *)

Lemma Zlength_digits_to_vals : forall ds,
  Zlength (digits_to_vals ds) = Zlength ds.
Proof. 
  intros.
  unfold digits_to_vals.
  apply Zlength_map.
Qed.

(** [blocks_to_vals] distributes over list concatenation. *)
Lemma blocks_to_vals_app : forall l1 l2,
  blocks_to_vals (l1 ++ l2) = blocks_to_vals l1 ++ blocks_to_vals l2.
Proof.
  intros.
  unfold blocks_to_vals.
  rewrite concat_app, map_app.
  reflexivity.
Qed.

(** Split [blocks_to_vals sig] at position [i] when [0 <= i < length sig]. *)
Lemma blocks_to_vals_split : forall sig i (d : block),
  (i < length sig)%nat ->
  blocks_to_vals sig =
    blocks_to_vals (firstn i sig) ++ block_to_vals (nth i sig d)
    ++ blocks_to_vals (skipn (S i) sig).
Proof.
  intros sig i d Hi.

  (* Peel off the prefix [firstn i sig]. *)
  rewrite <- (firstn_skipn i sig) at 1.
  rewrite blocks_to_vals_app.
  f_equal.

  (* Peel off the single block at index i. *)
  rewrite <- (firstn_skipn 1%nat (skipn i sig)) at 1.
  rewrite blocks_to_vals_app.
  f_equal.
  - destruct (skipn i sig) eqn:Hsk.
    + apply f_equal with (f := @length block) in Hsk.
      rewrite List.length_skipn in Hsk.
      simpl in Hsk.
      lia.
    + simpl firstn.
      unfold blocks_to_vals, block_to_vals.
      simpl concat.
      rewrite app_nil_r.
      f_equal.
      rewrite <- (firstn_skipn i sig) at 1.
      rewrite app_nth2 by (rewrite firstn_length_le; lia).
      rewrite firstn_length_le by lia.
      replace (i - i)%nat with 0%nat by lia.
      rewrite Hsk.
      reflexivity.
  - rewrite skipn_skipn.
    replace (i + 1)%nat with (S i) by lia.
    reflexivity.
Qed.

(** [nth k bs default] is fixed-length whenever [bs] is, since the default
    [zero_block] is also fixed-length. *)
Lemma nth_block_Zlength_default : forall (bs : list block) (k : nat),
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (nth k bs default) = n_bytes.
Proof.
  intros bs k HF.
  destruct (Nat.lt_ge_cases k (length bs)) as [Hlt|Hge].
  - rewrite Forall_forall in HF. 
    apply HF, nth_In, Hlt.
  - rewrite nth_overflow by exact Hge. 
    reflexivity.
Qed.

(** [blocks_to_vals] of a [seq]-indexed map peels its last element. *)
Lemma blocks_to_vals_seq_S : forall (f : nat -> block) (i : nat),
  blocks_to_vals (map f (seq 0 (S i))) =
  blocks_to_vals (map f (seq 0 i)) ++ block_to_vals (f i).
Proof.
  intros. rewrite seq_S, map_app.
  unfold blocks_to_vals, block_to_vals.
  rewrite concat_app, map_app. 
  simpl concat.
  rewrite app_nil_r.
  reflexivity.
Qed.

Lemma length_blocks_to_vals_fixed : forall (bs : list block),
  Forall (fun b => Zlength b = n_bytes) bs ->
  length (blocks_to_vals bs) = (length bs * 32)%nat.
Proof.
  intros bs H.
  unfold blocks_to_vals.
  rewrite length_map, length_concat.

  induction H as [|x xs Hx IH Hi]; [reflexivity|].
  cbn [map].
  assert (Hxlen : length x = 32%nat).
  { rewrite Zlength_correct in Hx.
    change n_bytes with 32 in Hx.
    apply Nat2Z.inj.
    rewrite Hx.
    reflexivity. }

  simpl.
  rewrite Hxlen, Hi.
  lia.
Qed.

Lemma Zlength_blocks_to_vals_fixed : forall (bs : list block),
  Forall (fun b => Zlength b = n_bytes) bs ->
  Zlength (blocks_to_vals bs) = 32 * Z.of_nat (length bs).
Proof.
  intros.
  rewrite Zlength_correct, length_blocks_to_vals_fixed by assumption.
  lia.
Qed.

(* ================================================================= *)
(** ** Slot-address tactic for [forward_call] parameter matching.

    [solve_slot_addr p HFC] closes the common side obligation
    [pSLOT = field_address0 (tarray tuchar _) (SUB _) ptr] arising
    from [forward_call] PARAMS matching for a mid-array pointer
    [p := field_address0 ...].  [HFC] is a [field_compatible] hyp
    for the parent array. *)
Ltac solve_slot_addr p HFC :=
  entailer!; simpl; f_equal; subst p;
  rewrite field_address0_offset;
  [ simpl; f_equal; lia
  | apply arr_field_compatible0; [ exact HFC | lia ] ].

(** [finish_slot_addr p HFC] closes the same obligation without
    re-running [entailer! -> simpl. f_equal] -- useful when the
    obligation has been reached via other f_equals (multi-arg case). *)
Ltac finish_slot_addr p HFC :=
  subst p;
  rewrite field_address0_offset;
  [ simpl; f_equal; lia
  | apply arr_field_compatible0; [ exact HFC | lia ] ].

(** [split_sc] discharges the length side conditions of
    [split2_data_at_Tarray_app] in the common cases: suffix is a
    [Zrepeat Vundef ...], an append of two fixed-length chunks, or
    resolvable by [list_solve]. *)
Ltac split_sc :=
  first
    [ list_solve
    | rewrite Zlength_Zrepeat; lia
    | rewrite Zlength_app, ?Zlength_Zrepeat; lia ].

(** [close_tc_byte] closes the [tc_val tuchar ...] obligation left
    behind by [forward.] on a tuchar load over [block_to_vals]. *)
Ltac close_tc_byte :=
  entailer!;
  rewrite Znth_block_to_vals by lia;
  unfold Vubyte; simpl;
  match goal with
  | |- context [Byte.unsigned (Byte.repr ?X)] =>
      pose proof (Byte.unsigned_range (Byte.repr X))
  end;
  rewrite Int.unsigned_repr by rep_lia;
  rep_lia.

(** Variant for [digits_to_vals _] loads (unfolds the [map] layer). *)
Ltac close_tc_byte_digit :=
  entailer!;
  unfold digits_to_vals;
  rewrite Znth_map by lia;
  unfold Vubyte; simpl;
  match goal with
  | |- context [Byte.unsigned (Byte.repr ?X)] =>
      pose proof (Byte.unsigned_range (Byte.repr X))
  end;
  rewrite Int.unsigned_repr by rep_lia;
  rep_lia.

