(** * body_derive_sk: VST body proof for [derive_sk]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.

Lemma body_derive_sk : semax_body Vprog Gprog f_derive_sk derive_sk_spec.
Proof.
  start_function.

  (* ===== Setup: write addr fields, split in[64] into [0..32) + [32..64) == *)

  forward.
  forward.
  forward.
  rewrite upd_adrs_5, upd_adrs_6, upd_adrs_7.
  assert_PROP (field_compatible (Tarray tuchar 64 noattr) nil v_in) as FC
    by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Tsh 64 32 v_in) by (auto; lia).
  Intros.

  (* ===== memcpy pub_seed: copy pub_seed into in[0..32) ===== *)

  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) v_in).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  rewrite (block_to_vals_eq_Vint pub_seed).
  unfold n_bytes in *.
  change (Z.of_nat n) with 32 in *.
  assert (Hpsl : Zlength (block_ints pub_seed) = 32)
    by (rewrite Zlength_block_ints; lia).
  (* memcpy(in, pub_seed, N) *)
  forward_call (sh_ps, Tsh, v_in, ps_ptr, 32, block_ints pub_seed).

  (* ===== addr_bytes: write addr_bytes into in[32..64) ===== *)

  set (p32 := field_address0 (Tarray tuchar 64 noattr) (SUB 32) v_in).
  (* addr_bytes(in + N, addr) *)
  forward_call (p32, a_ptr,
                setKeyAndMask (setHashAddress (setChainAddress a chain_i) 0) 0,
                Tsh, sh_a).
  { entailer!.
    unfold p32.
    rewrite field_address0_offset by auto with field_compatible.
    reflexivity. }

  (* ===== Re-gather: merge in[0..32) + in[32..64) back into in[0..64) ===== *)

  gather_SEP (data_at Tsh (tarray tuchar 32)
                (map Vint (block_ints pub_seed)) v_in)
             (data_at Tsh (tarray tuchar 32)
                (block_to_vals (addr_bytes _)) p32).
  set (X1 := map Vint (block_ints pub_seed)).
  set (X2 := block_to_vals
              (addr_bytes (setKeyAndMask
                (setHashAddress (setChainAddress a chain_i) 0) 0))).
  assert (HlX1 : Zlength X1 = 32)
    by (subst X1; rewrite Zlength_map; lia).
  assert (HlX2 : Zlength X2 = 64 - 32)
    by (subst X2; rewrite block_to_vals_length, addr_bytes_length; lia).
  unfold p32.
  rewrite <- (split2_data_at_Tarray_app 32 64 Tsh tuchar X1 X2 v_in
                HlX1 HlX2).
  assert (Heq : X1 ++ X2 =
                block_to_vals (pub_seed ++
                  addr_bytes (setKeyAndMask
                    (setHashAddress (setChainAddress a chain_i) 0) 0))).
  { subst X1 X2.
    rewrite block_to_vals_app.
    rewrite <- block_to_vals_eq_Vint.
    reflexivity. }

  setoid_rewrite Heq.

  (* ===== prf_keygen: call prf_keygen(out, in, sk_seed) ===== *)

  (* prf_keygen(out, in, sk_seed) *)
  forward_call (out_ptr, v_in, ss_ptr,
                pub_seed ++ addr_bytes (setKeyAndMask
                  (setHashAddress (setChainAddress a chain_i) 0) 0),
                sk_seed, sh_o, Tsh, sh_ss).
  { rewrite Zlength_app, addr_bytes_length.
    lia. }

  (* ===== Postcondition ===== *)

  unfold genSK, derive_sk_addr_post.
  entailer!.
  rewrite Z2Nat.id by lia.
  subst X1.
  rewrite <- block_to_vals_eq_Vint.
  cancel.
Qed.
