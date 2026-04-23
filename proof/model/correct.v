(** * model.correct: end-to-end correctness of WOTS+.

    [wots_correct] -- [verify] accepts any signature produced by
    [sign] against the matching [genPK], provided the message bytes
    are in range. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From Stdlib Require Import List ZArith Lia.
From wots Require Import model.wots.
Import ListNotations.
Open Scope Z_scope.

(** Chain composition: iterating [a] steps then [b] more from
    position [i + a] is the same as iterating [a + b] steps. *)
Lemma chain_concat : forall X i a b SEED ADRS,
  chain (chain X i a SEED ADRS) (i + a) b SEED ADRS
  = chain X i (a + b) SEED ADRS.
Proof.
  intros X i a b SEED ADRS.
  induction b as [|b IH].
  - simpl. now rewrite Nat.add_0_r.
  - rewrite Nat.add_succ_r. simpl. rewrite IH.
    f_equal. f_equal. f_equal. lia.
Qed.

(** Every byte of [toByte x y] is in range. *)
Lemma toByte_byte_ok : forall y x, Forall byte_ok (toByte x y).
Proof.
  induction y as [|y IH]; intros x; simpl.
  - constructor.
  - apply Forall_app. split; [apply IH|].
    constructor; [|constructor].
    unfold byte_ok. apply Z.mod_pos_bound; lia.
Qed.

(** Every digit produced by [base_w] fits in a nibble,
    provided the input bytes are valid. *)
Lemma base_w_le_15 : forall X k x,
  Forall byte_ok X -> In x (base_w X k) -> (x <= 15)%nat.
Proof.
  intros X k x HX Hin. unfold base_w in Hin.
  assert (Hin' : In x (flat_map
    (fun b : byte => [Z.to_nat (b / 16); Z.to_nat (b mod 16)]) X)).
  { rewrite <- (firstn_skipn k
      (flat_map (fun b : byte =>
        [Z.to_nat (b / 16); Z.to_nat (b mod 16)]) X)).
    apply in_or_app. left. exact Hin. }
  rewrite in_flat_map in Hin'.
  destruct Hin' as [b [Hb Hx]].
  rewrite Forall_forall in HX. specialize (HX _ Hb).
  unfold byte_ok in HX.
  destruct Hx as [Hx|[Hx|[]]]; subst.
  - assert (H1 : 0 <= b / 16 < 16)
      by (split; [apply Z.div_pos; lia
                 |apply Z.div_lt_upper_bound; lia]).
    change 15%nat with (Z.to_nat 15).
    apply Z2Nat.inj_le; lia.
  - pose proof (Z.mod_pos_bound b 16 ltac:(lia)) as H2.
    change 15%nat with (Z.to_nat 15).
    apply Z2Nat.inj_le; lia.
Qed.

(** The [i]-th digit of [expand_msg M] is at most [w - 1 = 15]. *)
Lemma nth_expand_msg_le_15 : forall M i,
  Forall byte_ok M -> (nth i (expand_msg M) 0%nat <= 15)%nat.
Proof.
  intros M i HM.
  destruct (Nat.lt_ge_cases i (length (expand_msg M))) as [Hi|Hi];
    [|rewrite nth_overflow by lia; lia].
  pose proof (nth_In _ 0%nat Hi) as Hin.
  unfold expand_msg in Hin.
  apply in_app_or in Hin.
  destruct Hin as [H|H].
  - eapply base_w_le_15; eauto.
  - eapply base_w_le_15; [|exact H]. apply toByte_byte_ok.
Qed.

(** Indexing a [for i < n {{ f i }}] at [i < n] recovers [f i]. *)
Lemma nth_for_idx : forall {A} (f : nat -> A) (d : A) (i k : nat),
  (i < k)%nat -> nth i (for_idx k f) d = f i.
Proof.
  intros A f d i k Hi. unfold for_idx.
  rewrite (nth_indep _ d (f 0%nat))
    by (rewrite length_map, length_seq; lia).
  rewrite map_nth, seq_nth by lia. reflexivity.
Qed.

(** Specialization of [chain_concat] matching the WOTS+ call shape:
    splitting a length-[k] chain starting at 0 at any [d <= k]. *)
Lemma chain_split : forall X d k SEED ADRS,
  (d <= k)%nat ->
  chain (chain X 0 d SEED ADRS) d (k - d) SEED ADRS
  = chain X 0 k SEED ADRS.
Proof.
  intros X d k SEED ADRS Hd.
  pose proof (chain_concat X 0 d (k - d) SEED ADRS) as H.
  simpl in H. rewrite H. f_equal. lia.
Qed.

(** End-to-end correctness. *)
Theorem wots_correct : forall M sk_seed pub_seed ADRS,
  Forall byte_ok M ->
  verify (genPK sk_seed pub_seed ADRS)
         (sign M sk_seed pub_seed ADRS)
         M pub_seed ADRS = true.
Proof.
  intros M sk_seed pub_seed ADRS HM.
  unfold verify.
  destruct (list_eq_dec _ _ _) as [?|Hne]; [reflexivity|].
  exfalso. apply Hne. clear Hne.
  unfold pkFromSig, sign, genPK.
  apply map_ext_in.
  intros i Hi. rewrite in_seq in Hi. destruct Hi as [_ Hi]. simpl in Hi.
  rewrite nth_for_idx by exact Hi.
  assert (Hb : (nth i (expand_msg M) 0%nat <= w_pred)%nat)
    by (pose proof (nth_expand_msg_le_15 M i HM); unfold w_pred; lia).
  rewrite chain_split by exact Hb.
  reflexivity.
Qed.
