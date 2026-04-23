(** * contract.lemmas.arith: byte / nibble / xor / [toByte] arithmetic.

    Ad-hoc VST-friendly bridges: [toByte] shape, [Int.zero_ext 8],
    nibble extraction, [Int.xor] vs [Z.lxor], [upd_Znth] shape lemmas
    used across several body proofs. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public.
From wots Require Import contract.lemmas.data_at.
From wots Require Import model.notation.

Open Scope Z_scope.

(* ================================================================= *)
(** ** [toByte] and [addr_bytes] -- lengths. *)

Lemma toByte_length : forall y x,
  length (toByte x y) = y.
Proof.
  induction y; intros; cbn; [reflexivity|].
  rewrite length_app, IHy. cbn. lia.
Qed.

Lemma toByte_Zlength : forall x y,
  Zlength (toByte x y) = Z.of_nat y.
Proof. intros. rewrite Zlength_correct, toByte_length. reflexivity. Qed.

Lemma toByte_0_zeros : forall y,
  toByte 0 y = repeat 0%Z y.
Proof.
  induction y; [reflexivity|].
  cbn [toByte].
  change (0 / 256) with 0.
  change (0 mod 256) with 0%Z.
  rewrite IHy, <- repeat_cons.
  reflexivity.
Qed.

Lemma toByte_small : forall (x : Z) (y : nat),
  0 <= x < 256 -> (0 < y)%nat ->
  toByte x y = repeat 0%Z (Nat.pred y) ++ [x].
Proof.
  intros x y Hx Hy.
  destruct y; [lia|].
  cbn [toByte Nat.pred].
  assert (Hdiv : x / 256 = 0) by (apply Zdiv_small; lia).
  rewrite Hdiv, toByte_0_zeros.
  f_equal.
  f_equal.
  apply Zmod_small; lia.
Qed.

Lemma addr_bytes_length : forall a,
  Zlength (addr_bytes a) = 32.
Proof.
  intros.
  unfold addr_bytes.
  repeat rewrite Zlength_app.
  repeat rewrite toByte_Zlength.
  reflexivity.
Qed.

(** [firstn (S n) l = firstn n l ++ [nth n l d]] when [n < length l]. *)
Lemma firstn_S_snoc : forall [A : Type] n (l : list A) d,
  (n < length l)%nat -> firstn (S n) l = firstn n l ++ [nth n l d].
Proof.
  induction n; intros [|x xs] d Hn; cbn in *; try lia.
  - reflexivity.
  - rewrite (IHn xs d) by lia. reflexivity.
Qed.

(** The prefix of [addr_bytes a] up through field [j]. *)
Definition addr_bytes_prefix (a : adrs) (j : nat) : list byte :=
  flat_map (fun x : word => toByte x 4) (firstn j (adrs_words a)).

Lemma addr_bytes_prefix_succ : forall a j,
  (j < 8)%nat ->
  addr_bytes_prefix a (S j) =
  addr_bytes_prefix a j ++ toByte (nth j (adrs_words a) 0) 4.
Proof.
  intros a j Hj. 
  unfold addr_bytes_prefix.
  rewrite (firstn_S_snoc _ _ 0) by (unfold adrs_words; simpl; lia).
  rewrite List.flat_map_app. cbn [flat_map]. now rewrite app_nil_r.
Qed.

Lemma addr_bytes_prefix_length : forall a j,
  (j <= 8)%nat ->
  Zlength (addr_bytes_prefix a j) = 4 * Z.of_nat j.
Proof.
  intros a j Hj.
  induction j; [reflexivity|].
  assert (j < 8)%nat by lia.
  rewrite addr_bytes_prefix_succ by auto.
  rewrite Zlength_app, toByte_Zlength, IHj by lia. 
  lia.
Qed.

(* ================================================================= *)
(** ** [toByte x 4] as four big-endian byte shifts of a 32-bit word. *)

Lemma toByte_4_eq : forall x,
  toByte x 4 = [x / 2^24 mod 256;
                x / 2^16 mod 256;
                x / 2^8  mod 256;
                x        mod 256].
Proof.
  intros. 
  cbn [toByte app]. 
  rewrite !Zdiv_Zdiv by lia.
  reflexivity.
Qed.

(** Extracting one of the four big-endian bytes of a 32-bit word.
    Key arithmetic identity used in the byte-extraction proof.
    For [k <= 24], the top 32-[k] bits of [v / 2^k] contribute only
    multiples of 256, hence vanish mod 256. *)
Lemma div_mod256_mod2pow32 : forall v k,
  (k = 0 \/ k = 8 \/ k = 16 \/ k = 24) ->
  (v mod 2^32) / 2^k mod 256 = v / 2^k mod 256.
Proof.
  intros v k Hk.

  (* Setup: factor 2^32 = 2^k * m with 256 | m *)
  assert (Hfact : exists m, 2^32 = 2^k * m /\ (256 | m) /\ 0 < 2^k).
  { destruct Hk as [Hc|[Hc|[Hc|Hc]]]; subst k.
    - exists 4294967296.
      split; [reflexivity | split; [exists 16777216; reflexivity | lia]].
    - exists 16777216.
      split; [reflexivity | split; [exists 65536;    reflexivity | lia]].
    - exists 65536.
      split; [reflexivity | split; [exists 256;      reflexivity | lia]].
    - exists 256.
      split; [reflexivity | split; [exists 1;        reflexivity | lia]]. }

  destruct Hfact as [m [H32 [[c Hc] Hk0]]].

  (* Main computation: rewrite v = 2^32*q + r, then cancel the 256-multiple *)
  set (q := v / 2^32).
  set (r := v mod 2^32).
  replace v with (2^32 * q + r) by (unfold q, r; symmetry; apply Z.div_mod; lia).
  rewrite H32.
  replace (2^k * m * q + r) with (((c * q) * 256) * 2^k + r) by (rewrite Hc; ring).
  rewrite Z.div_add_l by lia.
  rewrite <- Z.add_mod_idemp_l by lia.
  rewrite Z.mod_mul by lia.
  reflexivity.
Qed.

(** Bit [i >= 8] of any value [< 256] is zero. *)
Lemma Z_testbit_above_8 : forall x i,
  0 <= x < 256 -> 8 <= i -> Z.testbit x i = false.
Proof.
  intros x i Hx Hi.
  apply Z.bits_above_log2; [lia|].
  destruct (Z.eq_dec x 0) as [->|Hne]; [simpl; lia|].
  assert (Z.log2 x < 8) by (apply Z.log2_lt_pow2; [lia | change (2^8) with 256; lia]).
  lia.
Qed.

Lemma zero_ext_shru_byte : forall (v k : Z),
  k = 0 \/ k = 8 \/ k = 16 \/ k = 24 ->
  Vint (Int.zero_ext 8 (Int.shru (Int.repr v) (Int.repr k))) =
  Vubyte (Byte.repr ((v / 2^k) mod 256)).
Proof.
  intros v k Hk.

  (* Setup: normalize and unfold *)
  assert (Hrng : 0 <= k <= 24)
    by (destruct Hk as [H|[H|[H|H]]]; lia).
  unfold Vubyte.
  f_equal.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  rewrite Zmod_mod.
  unfold Int.zero_ext.
  rewrite Zbits.Zzero_ext_mod by lia.
  change (two_p 8) with 256.
  unfold Int.shru.
  rewrite !Int.unsigned_repr_eq.
  change Int.modulus with (2^32).

  (* Simplify the shift amount modulus *)
  assert (Hkmod : k mod 2^32 = k) by (apply Zmod_small; lia).
  rewrite Hkmod.
  rewrite Z.shiftr_div_pow2 by lia.

  (* Bounds on the shifted value so Zmod_small applies *)
  assert (Hlt : (v mod 2^32) / 2^k < 2^32).
  { apply Z.div_lt_upper_bound; [apply Z.pow_pos_nonneg; lia|].
    apply Z.lt_le_trans with (2^32); [apply Z.mod_pos_bound; lia|].
    rewrite <- (Z.mul_1_l (2^32)) at 1.
    apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia|].
    destruct Hk as [Hc|[Hc|[Hc|Hc]]]; lia. }
  assert (Hge : 0 <= (v mod 2^32) / 2^k).
  { apply Z.div_pos; [apply Z.mod_pos_bound; lia | apply Z.pow_pos_nonneg; lia]. }

  (* Closeout: apply eqm and delegate to div_mod256_mod2pow32 *)
  rewrite (Zmod_small _ (2^32)) by lia.
  apply Int.eqm_samerepr.
  unfold Int.eqm, Zbits.eqmod.
  exists 0.
  rewrite Z.mul_0_l, Z.add_0_l.
  apply div_mod256_mod2pow32.
  exact Hk.
Qed.

(** Byte-level xor: zero-ext 8 of [Int.xor] matches [Byte.repr Z.lxor]. *)
Lemma xor_byte_identity : forall (x y : Z),
  Vint (Int.zero_ext 8
    (Int.xor (Int.repr (Byte.unsigned (Byte.repr x)))
             (Int.repr (Byte.unsigned (Byte.repr y))))) =
  Vubyte (Byte.repr (Z.lxor x y)).
Proof.
  intros x y.
  unfold Vubyte.
  f_equal.
  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite Int.testbit_repr by assumption.
  rewrite Byte.unsigned_repr_eq.
  change Byte.modulus with 256.
  destruct (zlt i 8).
  - (* bit i < 8: xor distributes through the byte mask *)
    rewrite Int.bits_xor by assumption.
    rewrite !Int.testbit_repr by assumption.
    rewrite !Byte.unsigned_repr_eq.
    change Byte.modulus with 256.
    change 256 with (2 ^ 8).
    rewrite !Z.mod_pow2_bits_low by lia.
    symmetry.
    apply Z.lxor_spec.
  - (* bit i >= 8: high bits of byte are zero *)
    rewrite Byte.unsigned_repr_eq.
    change Byte.modulus with 256.
    change 256 with (2 ^ 8).
    rewrite Z.mod_pow2_bits_high by lia.
    reflexivity.
Qed.

(** Single-byte update step in the [thash_f] xor loop: writing
    the xor result at position [64+i] advances the [XOR] prefix
    by one element. *)
Lemma xor_store_step : forall (Z0 KEY XOR : list val) (i : Z) (vxor : val),
  Zlength Z0 = 32 -> Zlength KEY = 32 -> Zlength XOR = 32 ->
  0 <= i < 32 ->
  vxor = Znth i XOR ->
  upd_Znth (32 + (32 + i))
    (Z0 ++ KEY ++ sublist 0 i XOR ++ Zrepeat Vundef (32 - i)) vxor
  = Z0 ++ KEY ++ sublist 0 (i + 1) XOR ++ Zrepeat Vundef (32 - (i + 1)).
Proof. intros. subst vxor. list_solve. Qed.

Lemma zero_ext_byte : forall (v : Z),
  Vint (Int.zero_ext 8 (Int.repr v)) = Vubyte (Byte.repr (v mod 256)).
Proof.
  intros v.
  replace (Int.repr v) with (Int.shru (Int.repr v) (Int.repr 0))
    by (rewrite Int.shru_zero; reflexivity).
  rewrite zero_ext_shru_byte by auto.
  rewrite Z.pow_0_r, Z.div_1_r. 
  reflexivity.
Qed.

(** [upd_Znth] of the last element of [repeat v n] equals
    [repeat v (n-1) ++ [x]]. *)
Lemma upd_Znth_last_repeat :
  forall {A} {dA : Inhabitant A} (n : Z) (v x : A),
  0 < n ->
  upd_Znth (n - 1) (repeat v (Z.to_nat n)) x =
  repeat v (Z.to_nat (n - 1)) ++ [x].
Proof.
  intros A dA n v x Hn.
  replace (Z.to_nat n) with (Z.to_nat (n - 1) + 1)%nat by lia.
  rewrite repeat_app.
  simpl repeat at 3.
  apply upd_Znth_char.
  rewrite Zlength_repeat by lia.
  lia.
Qed.

(** Specialisation used in [body_prf] / [body_prf_keygen]: the buffer
    after [memset; buf[n-1] := id] equals [block_to_vals (toByte id n)]. *)
Lemma buf_after_memset_store :
  forall (n : Z) (id : Z),
  0 < n -> 0 <= id < 256 ->
  upd_Znth (n - 1) (repeat (Vint (Int.repr 0)) (Z.to_nat n))
           (Vint (Int.zero_ext 8 (Int.repr id)))
  = block_to_vals (toByte id (Z.to_nat n)).
Proof.
  intros n id Hn Hid.

  (* Setup: apply last-element update lemma and normalize the stored value *)
  rewrite upd_Znth_last_repeat by lia.
  rewrite zero_ext_byte.
  rewrite (Zmod_small id 256) by lia.
  rewrite toByte_small by lia.

  (* Closeout: unfold block_to_vals and match the repeat prefix *)
  unfold block_to_vals.
  rewrite map_app, map_repeat.
  simpl.
  unfold Vubyte.
  replace (Byte.unsigned (Byte.repr 0)) with 0%Z
    by (rewrite Byte.unsigned_repr_eq; reflexivity).
  replace (Z.to_nat (n - 1)) with (Nat.pred (Z.to_nat n)) by lia.
  reflexivity.
Qed.

(** Four consecutive [upd_Znth] at positions [n..n+3] of a list shaped
    [L ++ [_;_;_;_] ++ rest] with [Zlength L = n] replace exactly the
    four middle cells. *)
Lemma upd_Znth4_of_prefix :
  forall {A} {dA : Inhabitant A}
         (L : list A) (a0 a1 a2 a3 b0 b1 b2 b3 : A)
         (rest : list A) (n : Z),
  Zlength L = n ->
  upd_Znth (n + 3)
    (upd_Znth (n + 2)
      (upd_Znth (n + 1)
        (upd_Znth n (L ++ [a0; a1; a2; a3] ++ rest) b0) b1) b2) b3 =
  L ++ [b0; b1; b2; b3] ++ rest.
Proof.
  intros A dA L a0 a1 a2 a3 b0 b1 b2 b3 rest n HL.
  list_solve.
Qed.

(* ================================================================= *)
(** ** Nibble extraction (for [body_expand_digits]). *)

(** For a byte [0 <= x < 256]:
    - [Int.shr] by 4 equals [x / 16].
    - [Int.and] with 15 equals [x mod 16].
    The [zero_ext 8 (zero_ext 8 _)] wrapper is what Clight produces for
    [(uint8_t)(x >> 4)] / [(uint8_t)(x & 0xf)]. *)
Lemma nibble_hi : forall x : Z, 0 <= x < 256 ->
  Int.zero_ext 8 (Int.zero_ext 8
    (Int.shr (Int.repr x) (Int.repr 4))) = Int.repr (x / 16).
Proof.
  intros x Hx.

  (* Setup: signed value and unfold shift *)
  assert (Hs : Int.signed (Int.repr x) = x)
    by (apply Int.signed_repr; rep_lia).
  unfold Int.shr.
  rewrite Hs.
  change (Int.unsigned (Int.repr 4)) with 4.
  rewrite Int.zero_ext_idem by lia.

  (* Main computation: bit equality *)
  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite !Int.testbit_repr by (try destruct (zlt i 8); lia).
  destruct (zlt i 8).
  - (* low bits: shift matches division *)
    rewrite Z.shiftr_div_pow2 by lia.
    change (2^4) with 16.
    reflexivity.
  - (* high bits: x/16 < 256, so bit i is zero *)
    symmetry. 
    apply Z_testbit_above_8; [|lia].
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Lemma Zland_15_mod16 : forall x : Z, 0 <= x -> Z.land x 15 = x mod 16.
Proof.
  intros x Hx. 
  change 15 with (Z.ones 4).
  rewrite Z.land_ones by lia.
  reflexivity.
Qed.

Lemma Int_and_15 : forall x,
  Int.and (Int.repr x) (Int.repr 15) = Int.repr (Z.land x 15).
Proof.
  intros x.
  apply Int.same_bits_eq.
  intros j Hj.
  rewrite Int.bits_and by lia.
  rewrite !Int.testbit_repr by lia.
  rewrite Z.land_spec.
  reflexivity.
Qed.

Lemma nibble_lo : forall x : Z, 0 <= x < 256 ->
  Int.zero_ext 8 (Int.zero_ext 8
    (Int.and (Int.repr x) (Int.repr 15))) = Int.repr (x mod 16).
Proof.
  intros x Hx.

  (* Setup: collapse double zero_ext, rewrite land as mod *)
  rewrite Int.zero_ext_idem by lia.
  rewrite Int_and_15, Zland_15_mod16 by lia.

  (* Main computation: bit equality *)
  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite !Int.testbit_repr by lia.
  assert (Hmod : 0 <= x mod 16 < 16) by (apply Z.mod_pos_bound; lia).
  destruct (zlt i 8); [reflexivity|].

  (* High bits: x mod 16 < 16 < 256, so bit i is zero *)
  symmetry.
  apply Z_testbit_above_8; [lia | lia].
Qed.

(** The nibble-extraction function. *)
Definition nibbleF (b : byte) : list nat :=
  [Z.to_nat (b / 16); Z.to_nat (b mod 16)].

Lemma length_flat_map_nibbleF : forall l : list byte,
  length (flat_map nibbleF l) = (length l * 2)%nat.
Proof.
  induction l as [|x xs IH]; [reflexivity|]. 
  simpl.
  rewrite IH. 
  lia.
Qed.

Lemma Zlength_flat_map_nibbleF : forall l : block,
  Zlength (flat_map nibbleF l) = Zlength l * 2.
Proof.
  intros. 
  rewrite !Zlength_correct. 
  rewrite length_flat_map_nibbleF.
  lia.
Qed.

(** For [Zlength msg = 32], the full [base_w msg 64] is just the
    un-truncated [flat_map] since the flat_map has exactly 64 entries. *)
Lemma base_w_full_32 : forall msg : block,
  Zlength msg = 32 -> base_w msg 64 = flat_map nibbleF msg.
Proof.
  intros msg HlM.
  unfold base_w.
  pose proof (length_flat_map_nibbleF msg) as Hlen.
  rewrite Zlength_correct in HlM.
  assert (Hn : length msg = 32%nat) by lia.
  rewrite Hn in Hlen.
  apply firstn_all2.
  lia.
Qed.

Lemma flat_map_nibbleF_sublist_step :
  forall (msg : block) (i : Z),
    0 <= i < Zlength msg ->
    flat_map nibbleF (sublist 0 (i+1) msg) =
    flat_map nibbleF (sublist 0 i msg) ++ nibbleF (Znth i msg).
Proof.
  intros msg i Hi.
  rewrite (sublist_split 0 i (i+1)) by lia.
  rewrite <- flat_map_app.
  rewrite (sublist_one i (i+1) msg) by lia.
  reflexivity.
Qed.

(** Shape step using [flat_map nibbleF (sublist 0 i msg)]. *)
Lemma nibble_step_shape :
  forall (msg : block) (i : Z),
    0 <= i < 32 -> Zlength msg = 32 -> Forall byte_ok msg ->
    let b := Byte.unsigned (Byte.repr (Znth i msg)) in
    upd_Znth (2 * i + 1)
      (upd_Znth (2 * i)
        (digits_to_vals (flat_map nibbleF (sublist 0 i msg))
          ++ Zrepeat Vundef (67 - 2*i))
        (Vint (Int.repr (b / 16))))
      (Vint (Int.repr (b mod 16)))
    = digits_to_vals (flat_map nibbleF (sublist 0 (i+1) msg))
      ++ Zrepeat Vundef (67 - 2*(i+1)).
Proof.
  intros msg i Hi HlM HAll b.

  (* Setup: extract byte value and its range *)
  assert (Hbyte : Znth i msg = b).
  { subst b.
    rewrite Byte.unsigned_repr; [reflexivity|].
    rewrite Forall_forall in HAll.
    specialize (HAll (Znth i msg) (Znth_In i msg ltac:(lia))).
    unfold byte_ok in HAll.
    rep_lia. }
  assert (Hb_rng : 0 <= b < 256)
    by (subst b; pose proof (Byte.unsigned_range
                  (Byte.repr (Znth i msg))); rep_lia).

  (* Expand the flat_map sublist by one step *)
  rewrite flat_map_nibbleF_sublist_step by lia.
  set (D := digits_to_vals (flat_map nibbleF (sublist 0 i msg))).
  assert (HDlen : Zlength D = 2 * i).
  { subst D.
    rewrite Zlength_digits_to_vals, Zlength_flat_map_nibbleF.
    rewrite Zlength_sublist by lia.
    lia. }

  (* Fold D back and unfold nibbleF for the new byte *)
  unfold digits_to_vals.
  rewrite map_app.
  fold digits_to_vals.
  fold D.
  change (map (fun d : nat => Vubyte (Byte.repr (Z.of_nat d)))
          (flat_map nibbleF (sublist 0 i msg))) with D.
  unfold nibbleF.
  rewrite Hbyte.
  simpl map.
  change (let (q, _) := Z.div_eucl b 16 in q) with (b / 16).

  (* Bounds for the nibble values *)
  assert (Hdiv : 0 <= b / 16 < 256)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hmod : 0 <= b mod 16 < 256)
    by (pose proof (Z.mod_pos_bound b 16 ltac:(lia)); lia).
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).

  (* Convert Vubyte to Vint for both nibbles *)
  assert (Hvb : forall x, 0 <= x < 256 ->
    Vubyte (Byte.repr x) = Vint (Int.repr x)).
  { intros x Hx. 
    unfold Vubyte.
    do 2 f_equal.
    rewrite Byte.unsigned_repr by rep_lia.
    reflexivity. }

  rewrite (Hvb _ Hdiv), (Hvb _ Hmod).

  (* Closeout: list arithmetic *)
  list_solve.
Qed.

(* ================================================================= *)
(** ** Checksum facts (for [body_expand_digits] phase 2). *)

Lemma Zlength_flat_map_nibbleF_32 : forall msg,
  Zlength msg = 32 -> Zlength (flat_map nibbleF msg) = 64.
Proof.
  intros. rewrite Zlength_flat_map_nibbleF. lia.
Qed.

(** Every element of [flat_map nibbleF msg] for byte_ok msg is <= 15. *)
Lemma Forall_flat_map_nibbleF_le_15 : forall msg : block,
  Forall byte_ok msg ->
  Forall (fun n => (n <= 15)%nat) (flat_map nibbleF msg).
Proof.
  intros msg H. 
  induction msg as [|b rest IH]; simpl.
  - constructor.
  - inversion H.
    subst. 
    unfold byte_ok in H2.
    constructor; [|constructor].
    + apply Nat2Z.inj_le. 
      rewrite Z2Nat.id by (apply Z.div_pos; lia).
      assert (Hle : b / 16 <= 255 / 16).
      { apply Z.div_le_mono; lia. }
      change (255 / 16) with 15 in Hle.
      assumption.
    + apply Nat2Z.inj_le.
      rewrite Z2Nat.id by (apply Z.mod_pos_bound; lia).
      assert (0 <= b mod 16 < 16) by (apply Z.mod_pos_bound; lia). 
      lia.
    + apply IH. 
      assumption.
Qed.

Lemma nibble_le_15 : forall (msg : block) (k : Z),
  Zlength msg = 32 -> Forall byte_ok msg ->
  0 <= k < 64 ->
  (Znth k (flat_map nibbleF msg) <= 15)%nat.
Proof.
  intros msg k HlM HAll Hk.
  pose proof (Forall_flat_map_nibbleF_le_15 msg HAll) as HF.
  rewrite Forall_Znth in HF.
  apply HF. 
  rewrite Zlength_flat_map_nibbleF_32; lia.
Qed.

Lemma nibble_shru_and_15 : forall v k,
  0 <= v < 2^16 -> 0 <= k <= 32 ->
  Int.zero_ext 8 (Int.zero_ext 8
    (Int.and (Int.shru (Int.repr v) (Int.repr k)) (Int.repr 15)))
  = Int.repr ((v / 2^k) mod 16).
Proof.
  intros v k Hv Hk.

  (* Setup: bound the quotient and simplify shru *)
  assert (Hq_bnd : 0 <= v / 2^k < 2^16).
  { assert (Hpos : 0 < 2^k) by (apply Z.pow_pos_nonneg; lia).
    split; [apply Z.div_pos; lia|].
    apply Z.le_lt_trans with v; [| lia].
    apply Z.div_le_upper_bound; [lia|].
    nia. }
  assert (Hshru : Int.shru (Int.repr v) (Int.repr k) = Int.repr (v / 2^k)).
  { unfold Int.shru.
    rewrite !Int.unsigned_repr_eq.
    change Int.modulus with (2^32).
    rewrite (Z.mod_small v) by
      (split; [lia|];
       apply Z.lt_le_trans with (2^16); [lia | apply Z.pow_le_mono_r; lia]).
    rewrite (Z.mod_small k) by
      (split; [lia|]; apply Z.le_lt_trans with 32; [lia|]; lia).
    rewrite Z.shiftr_div_pow2 by lia.
    reflexivity. }
  rewrite Hshru.

  (* Main computation: collapse zero_ext and and, then bit equality *)
  rewrite Int.zero_ext_idem by lia.
  rewrite Int_and_15, Zland_15_mod16 by lia.
  apply Int.same_bits_eq.
  intros i Hi.
  rewrite Int.bits_zero_ext by lia.
  rewrite !Int.testbit_repr by lia.
  assert (Hmod : 0 <= (v / 2^k) mod 16 < 16)
    by (apply Z.mod_pos_bound; lia).
  destruct (zlt i 8); [reflexivity|].

  (* High bits are zero: the mod 16 result fits in 4 bits *)
  symmetry.
  apply Z_testbit_above_8; lia.
Qed.

(** Nibble-valued [Vubyte] in [Z.to_nat] form equals [Vint]. *)
Lemma Vubyte_nibble_eq_Vint : forall x : Z,
  0 <= x < 16 ->
  Vubyte (Byte.repr (Z.of_nat (Z.to_nat x))) = Vint (Int.repr x).
Proof.
  intros x Hx. 
  unfold Vubyte.
  rewrite Z2Nat.id by lia.
  rewrite Byte.unsigned_repr by rep_lia. 
  reflexivity.
Qed.

(** Tail of [expand_msg]: the 3-element checksum encoding. *)
Lemma base_w_checksum_tail : forall c : Z,
  0 <= c <= 960 ->
  base_w (toByte (c * 16) 2) 3 =
    [Z.to_nat (c / 256);
     Z.to_nat ((c / 16) mod 16);
     Z.to_nat (c mod 16)].
Proof.
  intros c Hc.

  (* Setup: simplify the two toByte bytes *)
  assert (Hhi : c * 16 / 256 = c / 16).
  { change 256 with (16*16).
    rewrite <- Z.div_div by lia.
    rewrite Z.div_mul by lia.
    reflexivity. }

  assert (Hlo : c * 16 mod 256 = (c mod 16) * 16).
  { replace (c * 16) with (16 * c) by lia.
    change 256 with (16 * 16).
    rewrite Z.mul_mod_distr_l by lia.
    lia. }

  cbn [toByte].
  rewrite Hhi, Hlo.
  cbn [app].

  (* Bounds for the three nibble-sized values *)
  assert (Hb1 : 0 <= c / 16 <= 60).
  { split; [apply Z.div_pos; lia|].
    assert (c/16 <= 960/16) by (apply Z.div_le_mono; lia).
    cbn in *. 
    lia. }
  assert (Hbmod : 0 <= c mod 16 < 16) by (apply Z.mod_pos_bound; lia).

  (* Closeout: unfold base_w and match the three list entries *)
  rewrite (Z.mod_small (c/16) 256) by lia.
  unfold base_w.
  cbn [flat_map].
  rewrite app_nil_r.
  cbn [firstn].
  cbn [app].
  f_equal.
  { f_equal.
    change 256 with (16*16).
    rewrite Z.div_div by lia.
    reflexivity. }
  do 3 f_equal.
  rewrite Z.div_mul by lia.
  reflexivity.
Qed.

Lemma csum_prefix_le : forall (l : list nat) i,
  Forall (fun n => (n <= 15)%nat) l ->
  (list_sum (map (fun d => w_pred - d)%nat (firstn i l)) <= 15 * i)%nat.
Proof.
  intros l i Hall.
  revert i.
  induction l as [|x xs IH]; intros [|j]; try (cbn; lia).
  cbn [firstn map list_sum].
  inversion Hall; subst.
  specialize (IH H2 j).
  assert (Hxx : (w_pred - x <= 15)%nat) by (unfold w_pred; lia).
  replace (15 * S j)%nat with (15 + 15 * j)%nat by lia.
  apply Nat.add_le_mono; assumption.
Qed.

(* ================================================================= *)
(** ** [expand_msg] / [digits_to_vals] lengths. *)

Lemma expand_msg_Zlength : forall m,
  Zlength m = n_bytes -> Zlength (expand_msg m) = 67.
Proof.
  intros m Hm.
  unfold expand_msg, len_1, len_2, base_w.
  rewrite Zlength_app, !Zlength_correct, !length_firstn.
  rewrite !length_flat_map_nibbleF, toByte_length.
  assert (Hlen : length m = 32%nat)
    by (apply Nat2Z.inj; rewrite <- Zlength_correct; rewrite Hm; reflexivity).
  rewrite Hlen.
  reflexivity.
Qed.

Lemma digits_to_vals_expand_Zlength : forall m,
  Zlength m = n_bytes ->
  Zlength (digits_to_vals (expand_msg m)) = 67.
Proof.
  intros m Hm.
  unfold digits_to_vals.
  rewrite Zlength_map.
  apply expand_msg_Zlength.
  assumption.
Qed.

