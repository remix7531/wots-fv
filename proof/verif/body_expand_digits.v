(** * body_expand_digits: VST body proof for [expand_digits]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.
From wots Require Import model.wots.

Open Scope Z_scope.

Lemma body_expand_digits :
  semax_body Vprog Gprog f_expand_digits expand_digits_spec.
Proof.
  start_function.

  (* ===== Setup ===== *)

  change (Z.of_nat len) with 67.
  change n_bytes with 32 in *.

  (* ===== Phase 1: nibble extraction loop (i < 32) ===== *)

  forward_for_simple_bound 32
    (EX i : Z,
      PROP ()
      LOCAL (temp _digits d_ptr; temp _msg m_ptr)
      SEP (data_at sh_d (tarray tuchar 67)
             (digits_to_vals (flat_map nibbleF (sublist 0 i msg))
              ++ Zrepeat Vundef (67 - 2*i)) d_ptr;
           data_at sh_m (tarray tuchar 32) (block_to_vals msg) m_ptr)).
  - entailer!.
  - forward.
    { close_tc_byte. }
    rewrite Znth_block_to_vals by lia.
    do 2 forward.
    { close_tc_byte. }
    rewrite Znth_block_to_vals by lia.
    forward.

    assert (Hrng : 0 <= Byte.unsigned (Byte.repr (Znth i msg)) < 256)
      by (pose proof (Byte.unsigned_range (Byte.repr (Znth i msg))); rep_lia).

    rewrite (nibble_hi _ Hrng).
    rewrite (nibble_lo _ Hrng).
    entailer!.
    apply derives_refl'. 
    f_equal.
    apply nibble_step_shape; auto.

  (* ===== Post-phase-1 setup ===== *)

  - rewrite sublist_same by lia.
    replace (67 - 2 * 32) with 3 by lia.

    forward.

    assert (HFall : Forall (fun n => (n <= 15)%nat) (flat_map nibbleF msg)).
    { apply Forall_flat_map_nibbleF_le_15. exact H0. }

    (* ===== Phase 2: checksum accumulator loop (j < 64) ===== *)

    forward_for_simple_bound 64
      (EX j : Z,
        PROP ()
        LOCAL (temp _csum (Vint (Int.repr (Z.of_nat
                 (list_sum (map (fun d => w_pred - d)%nat
                   (firstn (Z.to_nat j) (flat_map nibbleF msg)))))));
               temp _digits d_ptr; temp _msg m_ptr)
        SEP (data_at sh_d (tarray tuchar 67)
               (digits_to_vals (flat_map nibbleF msg) ++ Zrepeat Vundef 3)
               d_ptr;
             data_at sh_m (tarray tuchar 32) (block_to_vals msg) m_ptr)).
    + entailer!.
    + assert (Hlen64 : Zlength (flat_map nibbleF msg) = 64).
      { apply Zlength_flat_map_nibbleF_32; assumption. }
      assert (Hnib_le : (Znth i (flat_map nibbleF msg) <= 15)%nat).
      { apply nibble_le_15; [exact H | exact H0 | lia]. }

      forward.
      { entailer!.
        rewrite Znth_app1 by (rewrite Zlength_digits_to_vals; lia).
        unfold digits_to_vals.
        rewrite Znth_map by lia.
        unfold Vubyte.
        simpl.
        rewrite Int.unsigned_repr by rep_lia.
        rep_lia. }

      rewrite Znth_app1 by (rewrite Zlength_digits_to_vals; lia).
      unfold digits_to_vals.
      rewrite Znth_map by lia.
      fold digits_to_vals.
      forward.
      entailer!.
      do 2 f_equal.

      rewrite Byte.unsigned_repr by rep_lia.
      replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
      rewrite (firstn_S_snoc _ (flat_map nibbleF msg) 0%nat)
        by (rewrite <- ZtoNat_Zlength; lia).
      rewrite map_app, list_sum_app.
      rewrite Nat2Z.inj_add.
      cbn [map list_sum].

      replace (nth (Z.to_nat i) (flat_map nibbleF msg) 0%nat)
        with (Znth i (flat_map nibbleF msg))
        by (rewrite <- (nth_Znth i (flat_map nibbleF msg)) by lia;
            reflexivity).
      unfold w_pred.
      assert (Hls : list_sum ((15 - Znth i (flat_map nibbleF msg))%nat :: nil)
                  = (15 - Znth i (flat_map nibbleF msg))%nat)
        by (cbn; lia).
      rewrite Hls.
      rewrite Nat2Z.inj_sub by lia.
      change (Z.of_nat 15) with 15.
      lia.

    (* ===== Phase 3: three checksum-nibble writes digits[64..67) ===== *)

    + set (csum_nat := list_sum (map (fun d => w_pred - d)%nat
                         (firstn (Z.to_nat 64) (flat_map nibbleF msg)))).

      assert (Hcs_bnd : (csum_nat <= 15 * 64)%nat).
      { subst csum_nat. apply csum_prefix_le. exact HFall. }
      assert (Hcs_Z : 0 <= Z.of_nat csum_nat <= 960).
      { split; [lia |].
        change 960 with (Z.of_nat 960).
        apply Nat2Z.inj_le. lia. }
      assert (Hv16 : 0 <= Z.of_nat csum_nat < 2^16) by lia.

      do 3 forward.
      entailer!.
      apply derives_refl'. 
      f_equal.

      rewrite (nibble_shru_and_15 _ 8 Hv16 ltac:(lia)).
      rewrite (nibble_shru_and_15 _ 4 Hv16 ltac:(lia)).
      rewrite (nibble_shru_and_15 _ 0 Hv16 ltac:(lia)).

      assert (Hem : expand_msg msg = flat_map nibbleF msg ++
        [Z.to_nat (Z.of_nat csum_nat / 256);
         Z.to_nat ((Z.of_nat csum_nat / 16) mod 16);
         Z.to_nat (Z.of_nat csum_nat mod 16)]).
      { unfold expand_msg, len_1, len_2.
        rewrite (base_w_full_32 msg) by assumption.
        assert (Hcs_eq : csum (flat_map nibbleF msg) = csum_nat).
        { subst csum_nat. unfold csum.
          assert (length (flat_map nibbleF msg) = 64%nat).
          { apply Nat2Z.inj.
            rewrite <- Zlength_correct.
            rewrite Zlength_flat_map_nibbleF_32; [reflexivity | assumption]. }
          rewrite firstn_all2 by lia. reflexivity. }
        rewrite Hcs_eq.
        rewrite (base_w_checksum_tail (Z.of_nat csum_nat) Hcs_Z).
        reflexivity. }

      rewrite Hem.
      unfold digits_to_vals at 2.
      rewrite map_app.
      fold digits_to_vals.
      cbn [map].
      change (let (q, _) := Z.div_eucl (Z.of_nat csum_nat) 256 in q)
        with (Z.of_nat csum_nat / 256).
      change (let (q, _) := Z.div_eucl (Z.of_nat csum_nat) 16 in q)
        with (Z.of_nat csum_nat / 16).

      assert (Hflen : Zlength (digits_to_vals (flat_map nibbleF msg)) = 64).
      { rewrite Zlength_digits_to_vals.
        apply Zlength_flat_map_nibbleF_32; assumption. }
      assert (Hcsmod_16 : 0 <= Z.of_nat csum_nat mod 16 < 16)
        by (apply Z.mod_pos_bound; lia).
      assert (Hcsmod_256 : 0 <= Z.of_nat csum_nat / 256 < 16).
      { split; [apply Z.div_pos; lia |].
        apply Z.div_lt_upper_bound; lia. }
      assert (Hcsdiv_mod : 0 <= (Z.of_nat csum_nat / 16) mod 16 < 16)
        by (apply Z.mod_pos_bound; lia).

      change (2^0) with 1.
      rewrite Z.div_1_r.

      rewrite (Vubyte_nibble_eq_Vint _ Hcsmod_256).
      rewrite (Vubyte_nibble_eq_Vint _ Hcsdiv_mod).
      rewrite (Vubyte_nibble_eq_Vint _ Hcsmod_16).
      change (2^8) with 256.
      change (2^4) with 16.

      replace ((Z.of_nat csum_nat / 256) mod 16)
        with (Z.of_nat csum_nat / 256).
      2: { symmetry. apply Z.mod_small.
           split; [apply Z.div_pos; lia |].
           apply Z.div_lt_upper_bound; lia. }

      change (map (fun d : nat => Vubyte (Byte.repr (Z.of_nat d)))
                  (flat_map nibbleF msg))
        with (digits_to_vals (flat_map nibbleF msg)).
      list_solve.
Qed.
