(** * body_prf_keygen: VST body proof for [prf_keygen]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.

Lemma body_prf_keygen : semax_body Vprog Gprog f_prf_keygen prf_keygen_spec.
Proof.
  start_function.

  (* ===== Setup: split buf[128] into [0..32) + [32..128) ===== *)

  assert_PROP (field_compatible (Tarray tuchar 128 noattr) nil v_buf) as FC
    by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Tsh 128 32 v_buf) by (auto; lia).
  Intros.

  (* ===== memset(buf, 0, 32); buf[31] = 4  (toByte(4, 32) tag) ===== *)

  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) v_buf).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  (* memset(buf, 0, PAD) *)
  forward_call (Tsh, v_buf, 32, Int.repr 0).
  (* buf[PAD - 1] = 4  (write toByte(4, 32) tag) *)
  forward.

  (* ===== memcpy(buf + PAD, key, N) ===== *)

  set (p32 := field_address0 (Tarray tuchar 128 noattr) (SUB 32) v_buf).
  assert_PROP (field_compatible (Tarray tuchar 96 noattr) nil p32) as FC2
    by (replace 96 with (128 - 32) by lia; entailer!).
  rewrite (split2_data_at__Tarray_tuchar Tsh 96 32 p32) by (auto; lia).
  Intros.
  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) p32).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  rewrite (block_to_vals_eq_Vint key), (block_to_vals_eq_Vint in_buf).
  assert (Hkl : Zlength (block_ints key) = 32)
    by (rewrite Zlength_block_ints; rep_lia).
  unfold n_bytes in *. 
  change (Z.of_nat n) with 32 in *.
  (* memcpy(buf + PAD, key, N) *)
  forward_call (sh_k, Tsh, p32, key_ptr, 32, block_ints key).
  { entailer!.
    unfold p32.
    rewrite field_address0_offset by auto with field_compatible.
    reflexivity. }

  (* ===== memcpy(buf + PAD + N, in, N + 32) ===== *)

  set (p64 := field_address0 (Tarray tuchar 96 noattr) (SUB 32) p32).
  sep_apply (data_at__memory_block_cancel Tsh
               (Tarray tuchar (96 - 32) noattr) p64).
  change (sizeof (Tarray tuchar (96 - 32) noattr)) with 64.
  assert (Hil : Zlength (block_ints in_buf) = 64)
    by (rewrite Zlength_block_ints; lia).
  (* memcpy(buf + PAD + N, in, N + 32) *)
  forward_call (sh_i, Tsh, p64, in_ptr, 64, block_ints in_buf).
  { entailer!.
    unfold p64, p32.
    rewrite !field_address0_offset by auto with field_compatible.
    simpl.
    destruct v_buf; try contradiction.
    simpl.
    rewrite Ptrofs.add_assoc.
    reflexivity. }

  (* ===== Re-gather chunks: v_buf + p32 + p64 back into buf[0..128) ===== *)

  gather_SEP (data_at Tsh (tarray tuchar 32) _ v_buf)
             (data_at Tsh (tarray tuchar 32) _ p32)
             (data_at Tsh (tarray tuchar 64) _ p64).
  set (X1 := upd_Znth (32 - 1) (repeat (Vint (Int.repr 0)) (Z.to_nat 32))
                      (Vint (Int.zero_ext 8 (Int.repr 4)))).
  set (X2 := map Vint (block_ints key)).
  set (X3 := map Vint (block_ints in_buf)).
  assert (HlX1 : Zlength X1 = 32)
    by (subst X1; rewrite upd_Znth_Zlength; rewrite Zlength_repeat; lia).
  assert (HlX2 : Zlength X2 = 32)
    by (subst X2; rewrite Zlength_map; lia).
  assert (HlX3 : Zlength X3 = 96 - 32)
    by (subst X3; rewrite Zlength_map; lia).
  assert (HlX23 : Zlength (X2 ++ X3) = 128 - 32)
    by (rewrite Zlength_app, HlX2, HlX3; lia).

  unfold p64.
  change (Tarray tuchar 96 noattr) with (tarray tuchar 96).
  replace (data_at Tsh (tarray tuchar 64) X3
             (field_address0 (tarray tuchar 96) (SUB 32) p32))
    with  (data_at Tsh (tarray tuchar (96 - 32)) X3
             (field_address0 (tarray tuchar 96) (SUB 32) p32))
    by (f_equal; f_equal; lia).
  rewrite sepcon_assoc.
  rewrite <- (split2_data_at_Tarray_app 32 96 Tsh tuchar X2 X3 p32
                HlX2 HlX3).
  change (Tarray tuchar 128 noattr) with (tarray tuchar 128) in p32.
  unfold p32.
  rewrite <- (split2_data_at_Tarray_app 32 128 Tsh tuchar X1 (X2 ++ X3) v_buf
                HlX1 HlX23).

  (* Unify X1 ++ X2 ++ X3 with block_to_vals of the abstract SHA256 input. *)
  assert (Heq : X1 ++ X2 ++ X3 =
                block_to_vals (toByte 4 32 ++ key ++ in_buf)).
  { rewrite !block_to_vals_app. 
    subst X1 X2 X3.
    rewrite <- !block_to_vals_eq_Vint.
    rewrite (buf_after_memset_store 32 4) by lia.
    reflexivity. }
  setoid_rewrite Heq.

  (* ===== sha256(out, buf, sizeof buf) ===== *)

  (* sha256(out, buf, sizeof buf) *)
  forward_call (out_ptr, v_buf, 128,
                toByte 4 32 ++ key ++ in_buf, sh_o, Tsh).
  { rewrite !Zlength_app, toByte_Zlength. lia. }

  (* ===== Postcondition ===== *)

  subst X2 X3.
  rewrite <- !block_to_vals_eq_Vint.
  unfold PRF_keygen.
  entailer!.
Qed.
