(** * body_wots_sign: VST body proof for [wots_sign]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.
From wots Require Import model.wots model.notation model.correct.

Open Scope Z_scope.

Lemma body_wots_sign : semax_body Vprog Gprog f_wots_sign wots_sign_spec.
Proof.
  start_function.

  (* ===== Setup: unfold sig_bytes, assert Zlength facts ===== *)

  change sig_bytes with 2144.
  assert_PROP (Zlength (block_to_vals sk_seed) = n_bytes) as Hlss
    by entailer!.
  assert_PROP (Zlength (block_to_vals pub_seed) = n_bytes) as Hlps
    by entailer!.
  assert_PROP (Zlength (block_to_vals msg) = n_bytes) as Hlmsg
    by entailer!.
  rewrite block_to_vals_length in Hlss, Hlps, Hlmsg.

  (* ===== expand_digits call (writes _digits buffer) ===== *)

  (* expand_digits(v_digits, msg_ptr, msg) *)
  forward_call (v_digits, msg_ptr, msg, Tsh, sh_m).
  assert (Hdigit_le : forall k,
            (nth k (expand_msg msg) 0%nat <= 15)%nat)
    by (intros k; apply nth_expand_msg_le_15; assumption).

  (* ===== forward_for_simple_bound invariant ===== *)

  forward_for_simple_bound 67
    (EX i : Z,
      PROP ()
      LOCAL (temp _sig sig_ptr; temp _msg msg_ptr;
             temp _sk_seed sk_ptr; temp _pub_seed ps_ptr;
             temp _addr a_ptr;
             lvar _digits (tarray tuchar 67) v_digits)
      SEP (data_at sh_sig (tarray tuchar 2144)
             (blocks_to_vals
                (map (sign_block sk_seed pub_seed a msg)
                     (seq 0 (Z.to_nat i)))
              ++ Zrepeat Vundef (2144 - 32 * i)) sig_ptr;
           data_at Tsh (tarray tuchar (Z.of_nat len))
             (digits_to_vals (expand_msg msg)) v_digits;
           data_at sh_m (tarray tuchar n_bytes)
             (block_to_vals msg) msg_ptr;
           data_at sh_sk (tarray tuchar n_bytes)
             (block_to_vals sk_seed) sk_ptr;
           data_at sh_ps (tarray tuchar n_bytes)
             (block_to_vals pub_seed) ps_ptr;
           data_at sh_a t_addr
             (adrs_to_vals (sign_addr_step a msg (Z.to_nat i)))
             a_ptr)).

  - (* ===== loop entry ===== *)

    entailer!.

  - (* ===== loop body: split sig into FILLED + MID + TAIL ===== *)

    assert_PROP (field_compatible (tarray tuchar 2144) nil sig_ptr)
      as Hfc_sig by entailer!.

    set (FILLED := blocks_to_vals
                     (map (sign_block sk_seed pub_seed a msg)
                          (seq 0 (Z.to_nat i)))).
    assert (HlFILLED : Zlength FILLED = 32 * i).
    { subst FILLED. 
      rewrite Zlength_blocks_to_vals_fixed.
      - rewrite length_map, length_seq. 
        lia.
      - apply Forall_map, Forall_forall.
        intros k _.
        apply sign_block_Zlength. }

    erewrite (split2_data_at_Tarray_app (32*i) 2144 sh_sig tuchar
               FILLED (Zrepeat Vundef (2144 - 32*i)))
      by (try exact HlFILLED; split_sc).
    replace (2144 - 32*i) with (32 + (2144 - 32*(i+1))) by lia.
    rewrite <- Zrepeat_app by lia.
    erewrite (split2_data_at_Tarray_app 32 _ sh_sig tuchar
               (Zrepeat Vundef 32) (Zrepeat Vundef (2144 - 32*(i+1))))
      by split_sc.

    set (pSUFF := field_address0 (tarray tuchar 2144) (SUB (32*i)) sig_ptr).
    Intros.
    replace (Zrepeat (A:=val) Vundef 32)
      with (default_val (tarray tuchar 32)) by reflexivity.
    rewrite <- data_at__eq.

    (* ===== derive_sk on MID slot pSUFF ===== *)

    (* derive_sk(pSUFF, sk_ptr, ps_ptr, a_ptr, i) *)
    forward_call (pSUFF, sk_ptr, ps_ptr, a_ptr,
                  i, sk_seed, pub_seed,
                  sign_addr_step a msg (Z.to_nat i),
                  sh_sig, sh_sk, sh_ps, sh_a).
    { solve_slot_addr pSUFF Hfc_sig. }

    (* ===== read digits[i] twice; hoist shared facts ===== *)

    change (Z.of_nat len) with 67 in *.
    pose proof (expand_msg_Zlength msg Hlmsg) as Hexpand_Zlen.
    pose proof (digits_to_vals_expand_Zlength msg Hlmsg) as Hdtv_len.
    assert (Hnth_Znth :
              nth (Z.to_nat i) (expand_msg msg) 0%nat
              = Znth i (expand_msg msg))
      by (rewrite <- (nth_Znth i (expand_msg msg)
                       ) by lia; reflexivity).
    pose proof (Hdigit_le (Z.to_nat i)) as Hd_le.

    forward.
    { close_tc_byte_digit. }

    (* ===== chain with steps = digits[i] ===== *)

    unfold digits_to_vals.
    rewrite Znth_map by lia.
    fold digits_to_vals.

    (* chain(pSUFF, ps_ptr, a_ptr, 0, digits[i]) *)
    forward_call (pSUFF, ps_ptr, a_ptr,
                  0, Z.of_nat (Znth i (expand_msg msg)),
                  genSK (Z.to_nat i) sk_seed pub_seed
                    (sign_addr_step a msg (Z.to_nat i)),
                  pub_seed,
                  derive_sk_addr_post
                    (sign_addr_step a msg (Z.to_nat i)) i,
                  sh_sig, sh_ps, sh_a).
    { entailer!.
      simpl.
      f_equal.
      { finish_slot_addr pSUFF Hfc_sig. }
      do 3 f_equal.
      rewrite Byte.unsigned_repr; [reflexivity|].
      rewrite <- Hnth_Znth. 
      rep_lia. }
    { unfold w_pred. 
      split. 
      - lia. 
      - apply genSK_Zlength. }

    (* ===== merge back: FILLED ++ sig_block ++ TAIL ===== *)

    change (Z.to_nat 0) with 0%nat.
    replace (Z.to_nat (Z.of_nat (Znth i (expand_msg msg))))
      with (Znth i (expand_msg msg))%nat by lia.
    rewrite <- Hnth_Znth.
    rewrite (chain_genSK_sign_step_eq sk_seed pub_seed a msg i
               (Z.to_nat i)) by lia.
    rewrite (chain_addr_post_derive_sk_sign_step a msg i
               (Z.to_nat i)) by lia.

    replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia.
    replace (32 + (2144 - 32 * (i + 1)) - 32)
      with (2144 - 32 * i - 32) by lia.
    replace (32 + (2144 - 32 * (i + 1)))
      with (2144 - 32 * i) by lia.
    change n_bytes with 32 in *.

    assert (Hlsgn : Zlength (block_to_vals
                      (sign_block sk_seed pub_seed a msg
                                  (Z.to_nat i))) = 32).
    { rewrite block_to_vals_length, sign_block_Zlength. reflexivity. }

    gather_SEP
      (data_at sh_sig (tarray tuchar 32)
         (block_to_vals (sign_block sk_seed pub_seed a msg (Z.to_nat i)))
         pSUFF)
      (data_at sh_sig (tarray tuchar (2144 - 32 * i - 32)) _ _).
    erewrite <- (split2_data_at_Tarray_app 32 (2144 - 32 * i) sh_sig tuchar
                   (block_to_vals
                      (sign_block sk_seed pub_seed a msg (Z.to_nat i)))
                   (Zrepeat Vundef (2144 - 32 * (i + 1)))
                   pSUFF Hlsgn)
      by split_sc.
    unfold pSUFF.
    gather_SEP
      (data_at sh_sig (tarray tuchar (32 * i)) FILLED sig_ptr)
      (data_at sh_sig (tarray tuchar (2144 - 32 * i)) _ _).
    entailer!.
    erewrite <- (split2_data_at_Tarray_app (32 * i) 2144 sh_sig tuchar
                   FILLED
                   (block_to_vals
                      (sign_block sk_seed pub_seed a msg (Z.to_nat i))
                    ++ Zrepeat Vundef (2144 - 32 * (i + 1)))
                   sig_ptr HlFILLED)
      by (rewrite Zlength_app, block_to_vals_length,
              sign_block_Zlength, Zlength_Zrepeat;
          rep_lia).
    apply derives_refl'. 
    f_equal.
    rewrite blocks_to_vals_seq_S, <- app_assoc.
    reflexivity.

  - (* ===== loop exit ===== *)

    replace (Z.to_nat 67) with 67%nat by lia.
    rewrite sign_addr_step_len.
    replace (2144 - 32 * 67) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.
    change (map (sign_block sk_seed pub_seed a msg) (seq 0 67))
      with (sign msg sk_seed pub_seed a).
    entailer!.
Qed.
