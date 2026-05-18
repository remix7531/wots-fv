(** * body_wotsfv_ct_memcmp: VST body proof for [wotsfv_ct_memcmp].

    Proves that the in-tree constant-time byte-compare returns
    [Int.zero] iff the two byte-arrays agree element-wise.  The
    accumulator [_diff] is a [uint8_t] so its zero-extension is the
    identity throughout the loop; the bidirectional equivalence is
    carried by the loop invariant. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog.

Open Scope Z_scope.

(* ===== Bitwise helper lemmas ===== *)

(** Two ints are equal iff their XOR is zero. *)
Lemma int_xor_eq_zero_iff (a b : int) :
  Int.xor a b = Int.zero <-> a = b.
Proof.
  split; intro H.
  - apply Int.same_bits_eq; intros i Hi.
    pose proof (Int.bits_xor a b i Hi) as Hbit.
    assert (Hz : Int.testbit (Int.xor a b) i = false).
    { rewrite H. apply Int.bits_zero. }
    rewrite Hbit in Hz.
    destruct (Int.testbit a i), (Int.testbit b i); simpl in Hz; congruence.
  - subst. apply Int.xor_idem.
Qed.

(** Bitwise OR is zero iff each operand is zero. *)
Lemma int_or_eq_zero_iff (a b : int) :
  Int.or a b = Int.zero <-> a = Int.zero /\ b = Int.zero.
Proof.
  split.
  - intro H. split; apply Int.same_bits_eq; intros i Hi.
    + pose proof (Int.bits_or a b i Hi) as Hbit.
      assert (Hz : Int.testbit (Int.or a b) i = false).
      { rewrite H. apply Int.bits_zero. }
      rewrite Hbit in Hz. rewrite Int.bits_zero.
      destruct (Int.testbit a i); simpl in Hz; congruence.
    + pose proof (Int.bits_or a b i Hi) as Hbit.
      assert (Hz : Int.testbit (Int.or a b) i = false).
      { rewrite H. apply Int.bits_zero. }
      rewrite Hbit in Hz. rewrite Int.bits_zero.
      destruct (Int.testbit a i), (Int.testbit b i); simpl in Hz; congruence.
  - intros [Ha Hb]. subst. apply Int.or_zero.
Qed.

(** If [a, b] both fit in 8 bits then so does [Int.xor a b]. *)
Lemma int_xor_byte_bound (a b : int) :
  0 <= Int.unsigned a < 256 ->
  0 <= Int.unsigned b < 256 ->
  0 <= Int.unsigned (Int.xor a b) < 256.
Proof.
  intros Ha Hb.
  unfold Int.xor.
  rewrite Int.unsigned_repr_eq.
  assert (Hnn : 0 <= Z.lxor (Int.unsigned a) (Int.unsigned b))
    by (apply Z.lxor_nonneg; lia).
  assert (Ha8 : Z.log2 (Int.unsigned a) < 8).
  { destruct (Z.eq_dec (Int.unsigned a) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hb8 : Z.log2 (Int.unsigned b) < 8).
  { destruct (Z.eq_dec (Int.unsigned b) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hub : Z.lxor (Int.unsigned a) (Int.unsigned b) < 256).
  { destruct (Z.eq_dec (Z.lxor (Int.unsigned a) (Int.unsigned b)) 0) as [E|E].
    { rewrite E. lia. }
    change 256 with (2 ^ 8).
    apply Z.log2_lt_pow2; [lia| ].
    apply (Z.le_lt_trans _ (Z.max (Z.log2 (Int.unsigned a)) (Z.log2 (Int.unsigned b))) _).
    { apply Z.log2_lxor; lia. }
    apply Z.max_lub_lt; lia. }
  rewrite Z.mod_small by (change Int.modulus with 4294967296; lia).
  lia.
Qed.

(** If [a, b] both fit in 8 bits then so does [Int.or a b]. *)
Lemma int_or_byte_bound (a b : int) :
  0 <= Int.unsigned a < 256 ->
  0 <= Int.unsigned b < 256 ->
  0 <= Int.unsigned (Int.or a b) < 256.
Proof.
  intros Ha Hb.
  unfold Int.or.
  rewrite Int.unsigned_repr_eq.
  assert (Hnn : 0 <= Z.lor (Int.unsigned a) (Int.unsigned b))
    by (apply Z.lor_nonneg; lia).
  assert (Ha8 : Z.log2 (Int.unsigned a) < 8).
  { destruct (Z.eq_dec (Int.unsigned a) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hb8 : Z.log2 (Int.unsigned b) < 8).
  { destruct (Z.eq_dec (Int.unsigned b) 0) as [E|E].
    - rewrite E. simpl. lia.
    - apply Z.log2_lt_pow2; [lia|change (2^8) with 256; lia]. }
  assert (Hub : Z.lor (Int.unsigned a) (Int.unsigned b) < 256).
  { destruct (Z.eq_dec (Z.lor (Int.unsigned a) (Int.unsigned b)) 0) as [E|E].
    { rewrite E. lia. }
    change 256 with (2 ^ 8).
    apply Z.log2_lt_pow2; [lia| ].
    rewrite Z.log2_lor by lia.
    apply Z.max_lub_lt; lia. }
  rewrite Z.mod_small by (change Int.modulus with 4294967296; lia).
  lia.
Qed.

(** Byte-bounded ints are fixed points of [Int.zero_ext 8]. *)
Lemma zero_ext_8_byte (x : int) :
  0 <= Int.unsigned x < 256 ->
  Int.zero_ext 8 x = x.
Proof.
  intros H. apply zero_ext_inrange.
  change (two_p 8) with 256. lia.
Qed.

(* ===== Body proof ===== *)

Lemma body_wotsfv_ct_memcmp :
  semax_body Vprog Gprog f_wotsfv_ct_memcmp wotsfv_ct_memcmp_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.
  match goal with
  | H : Forall _ p_contents |- _ => rename H into Hpb
  end.
  match goal with
  | H : Forall _ q_contents |- _ => rename H into Hqb
  end.

  (* ===== Initialise [diff = 0] ===== *)

  forward.

  (* ===== Loop: invariant carries byte-bound + biconditional ===== *)

  forward_for_simple_bound n
    (EX i : Z, EX diff_v : int,
      PROP (0 <= Int.unsigned diff_v < 256;
            diff_v = Int.zero <->
              sublist 0 i p_contents = sublist 0 i q_contents)
      LOCAL (temp _diff (Vint diff_v); temp _a p; temp _b q;
             temp _n (Vlong (Int64.repr n)))
      SEP (data_at psh (tarray tuchar n) (map Vint p_contents) p;
           data_at qsh (tarray tuchar n) (map Vint q_contents) q)).

  (* ----- Loop entry: i = 0, diff = 0 ----- *)

  - Exists Int.zero.
    entailer!.
    split; intros _.
    + rewrite !sublist_nil_gen by lia. reflexivity.
    + reflexivity.

  (* ----- Loop body ----- *)

  - Intros.
    rename H3 into Hdb.
    rename H4 into Hbi.

    assert (Hai : 0 <= Int.unsigned (Znth i p_contents) < 256).
    { rewrite Forall_forall in Hpb. apply Hpb, Znth_In. lia. }
    assert (Hbj : 0 <= Int.unsigned (Znth i q_contents) < 256).
    { rewrite Forall_forall in Hqb. apply Hqb, Znth_In. lia. }

    (* Load a[i] *)
    forward.

    (* Load b[i] *)
    forward.

    (* diff = diff | (uint8_t)(a[i] ^ b[i]) *)
    forward.

    set (xv := Int.xor (Znth i p_contents) (Znth i q_contents)).
    assert (Hxb : 0 <= Int.unsigned xv < 256)
      by (subst xv; apply int_xor_byte_bound; auto).
    assert (Hxz : Int.zero_ext 8 xv = xv) by (apply zero_ext_8_byte; auto).
    set (nv := Int.or diff_v xv).
    assert (Hnb : 0 <= Int.unsigned nv < 256)
      by (subst nv; apply int_or_byte_bound; auto).
    assert (Hnz : Int.zero_ext 8 nv = nv) by (apply zero_ext_8_byte; auto).

    Exists nv.
    entailer!.
    split.
    + intro Hnv0.
      apply int_or_eq_zero_iff in Hnv0 as [Hd0 Hx0].
      apply (proj1 (int_xor_eq_zero_iff _ _)) in Hx0.
      rewrite (sublist_split 0 i (i + 1)) by lia.
      rewrite (sublist_split 0 i (i + 1) q_contents) by lia.
      rewrite (sublist_one i (i + 1) p_contents) by lia.
      rewrite (sublist_one i (i + 1) q_contents) by lia.
      rewrite Hx0.
      f_equal.
      apply Hbi; exact Hd0.
    + intro Heq.
      rewrite (sublist_split 0 i (i + 1)) in Heq by lia.
      rewrite (sublist_split 0 i (i + 1) q_contents) in Heq by lia.
      rewrite (sublist_one i (i + 1) p_contents) in Heq by lia.
      rewrite (sublist_one i (i + 1) q_contents) in Heq by lia.
      assert (Hlens : length (sublist 0 i p_contents) =
                      length (sublist 0 i q_contents)).
      { rewrite <- !ZtoNat_Zlength.
        rewrite !Zlength_sublist by lia. reflexivity. }
      destruct (app_eq_len_eq Heq Hlens) as [Hpre Htail].
      assert (Hknth : Znth i p_contents = Znth i q_contents).
      { inversion Htail. reflexivity. }
      assert (Hd0 : diff_v = Int.zero) by (apply Hbi; exact Hpre).
      rewrite Hd0.
      rewrite Int.or_zero_l.
      apply int_xor_eq_zero_iff.
      exact Hknth.

  (* ----- Loop exit: return _diff ----- *)

  - Intros diff_v.
    rename H2 into Hdb.
    rename H3 into Hbi.

    forward.

    Exists diff_v.
    entailer!.
    rewrite !sublist_same in Hbi by auto.
    exact Hbi.
Qed.
