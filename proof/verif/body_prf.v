(** * body_prf: VST body proof for [prf]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.

Lemma body_prf : semax_body Vprog Gprog f_prf prf_spec.
Proof.
  start_function.

  (* ===== Setup: split buf[96] into [0..32) + [32..64) + [64..96) ===== *)

  assert_PROP (field_compatible (Tarray tuchar 96 noattr) nil v_buf) as FC
    by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Tsh 96 32 v_buf) by (auto; lia).
  Intros.

  (* ===== memset(buf, 0, 32); buf[31] = 3  (toByte(3, 32) tag) ===== *)

  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) v_buf).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  (* memset(buf, 0, PAD) *)
  forward_call (Tsh, v_buf, 32, Int.repr 0).
  forward.

  (* ===== memcpy(buf + PAD, key, N) ===== *)

  set (p32 := field_address0 (Tarray tuchar 96 noattr) (SUB 32) v_buf).
  assert_PROP (field_compatible (Tarray tuchar 64 noattr) nil p32) as FC2
    by (entailer!; auto).
  rewrite (split2_data_at__Tarray_tuchar Tsh 64 32 p32) by (auto; lia).
  Intros.
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) p32).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  rewrite (block_to_vals_eq_Vint key), (block_to_vals_eq_Vint in_buf).
  assert (Hkl : Zlength (block_ints key) = 32)
    by (rewrite Zlength_block_ints; rep_lia).
  unfold n_bytes.
  change (Z.of_nat n) with 32.
  (* memcpy(buf + PAD, key, N) *)
  forward_call (sh_k, Tsh, p32, key_ptr, 32, block_ints key).
  { entailer!.
    unfold p32. 
    rewrite field_address0_offset by auto with field_compatible.
    reflexivity. }

  (* ===== memcpy(buf + PAD + N, in, N) ===== *)

  set (p64 := field_address0 (Tarray tuchar 64 noattr) (SUB 32) p32).
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) p64).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  assert (Hil : Zlength (block_ints in_buf) = 32)
    by (rewrite Zlength_block_ints; lia).
  (* memcpy(buf + PAD + N, in, N) *)
  forward_call (sh_i, Tsh, p64, in_ptr, 32, block_ints in_buf).
  { entailer!.
    unfold p64, p32.
    rewrite !field_address0_offset by auto with field_compatible.
    destruct v_buf; try contradiction. 
    simpl.
    rewrite Ptrofs.add_assoc. 
    reflexivity. }

  (* ===== Re-gather chunks: v_buf + p32 + p64 back into a single buf[0..96) ===== *)

  gather_SEP (data_at Tsh (tarray tuchar 32) _ v_buf)
             (data_at Tsh (tarray tuchar 32) _ p32)
             (data_at Tsh (tarray tuchar 32) _ p64).
  set (X2 := map Vint (block_ints key)).
  set (X3 := map Vint (block_ints in_buf)).
  set (X1 := upd_Znth (32 - 1) (repeat (Vint (Int.repr 0)) (Z.to_nat 32))
                      (Vint (Int.zero_ext 8 (Int.repr 3)))).
  assert (HlX1 : Zlength X1 = 32)
    by (subst X1; rewrite upd_Znth_Zlength; rewrite Zlength_repeat; lia).
  assert (HlX2 : Zlength X2 = 32)
    by (subst X2; rewrite Zlength_map; lia).
  assert (HlX3 : Zlength X3 = 64 - 32)
    by (subst X3; rewrite Zlength_map; lia).
  assert (HlX23 : Zlength (X2 ++ X3) = 96 - 32)
    by (rewrite Zlength_app, HlX2, HlX3; lia).

  unfold p64.
  change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
  replace (data_at Tsh (tarray tuchar 32) X3
             (field_address0 (tarray tuchar 64) (SUB 32) p32))
    with  (data_at Tsh (tarray tuchar (64 - 32)) X3
             (field_address0 (tarray tuchar 64) (SUB 32) p32))
    by (f_equal; f_equal; lia).
  rewrite sepcon_assoc.
  rewrite <- (split2_data_at_Tarray_app 32 64 Tsh tuchar X2 X3 p32
                HlX2 HlX3).
  change (Tarray tuchar 96 noattr) with (tarray tuchar 96) in p32.
  unfold p32.
  rewrite <- (split2_data_at_Tarray_app 32 96 Tsh tuchar X1 (X2 ++ X3) v_buf HlX1 HlX23).

  (* Unify X1 ++ X2 ++ X3 with block_to_vals of the abstract SHA256 input. *)
  assert (Heq : X1 ++ X2 ++ X3 =
                block_to_vals (toByte 3 32 ++ key ++ in_buf)).
  { rewrite !block_to_vals_app.
    subst X1 X2 X3.
    rewrite <- !block_to_vals_eq_Vint.
    rewrite (buf_after_memset_store 32 3) by lia.
    reflexivity. }
  setoid_rewrite Heq.

  (* ===== sha256(out, buf, sizeof buf) ===== *)

  (* sha256(out, buf, sizeof buf) *)
  forward_call (out_ptr, v_buf, 96,
                toByte 3 32 ++ key ++ in_buf, sh_o, Tsh).
  { rewrite !Zlength_app, toByte_Zlength. rep_lia. }

  (* ===== Postcondition ===== *)

  subst X2 X3.
  rewrite <- !block_to_vals_eq_Vint.
  unfold PRF, n_bytes.
  change (Z.of_nat n) with 32.
  entailer!.
Qed.
