(** * body_thash_f: VST body proof for [thash_f]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.

Lemma body_thash_f : semax_body Vprog Gprog f_thash_f thash_f_spec.
Proof.
  start_function.

  (* ===== Setup: split buf[96] into [0..32) + [32..64) + [64..96) ===== *)

  assert_PROP (field_compatible (Tarray tuchar 96 noattr) nil v_buf) as FC_buf
    by entailer!.
  rewrite (split2_data_at__Tarray_tuchar Tsh 96 32 v_buf) by (auto; lia).
  Intros.

  set (vb32 := field_address0 (Tarray tuchar 96 noattr) (SUB 32) v_buf).
  assert_PROP (field_compatible (Tarray tuchar (96 - 32) noattr) nil vb32)
    as FC_vb32 by entailer!.
  replace (96 - 32) with 64 in * by reflexivity.
  rewrite (split2_data_at__Tarray_tuchar Tsh 64 32 vb32) by (auto; lia).
  Intros.

  set (vb64 := field_address0 (Tarray tuchar 64 noattr) (SUB 32) vb32).

  (* ===== memset buf[0..32) ===== *)

  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) v_buf).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  (* memset(v_buf, 0, 32) *)
  forward_call (Tsh, v_buf, 32, Int.repr 0).

  (* ===== addr[7]=0 + addr_bytes(ab) ===== *)

  unfold n_bytes in *.
  change (Z.of_nat n) with 32 in *.
  forward.
  rewrite upd_adrs_7.
  (* addr_bytes(v_ab, addr) *)
  forward_call (v_ab, a_ptr, setKeyAndMask a 0, Tsh, sh_a).

  (* ===== prf(buf+32, ab, pub_seed) = KEY ===== *)

  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) vb32).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  (* prf(v_buf + 32, v_ab, pub_seed):
       writes KEY := PRF pub_seed (addr_bytes (setKeyAndMask a 0)) *)
  forward_call (vb32, v_ab, ps_ptr,
                addr_bytes (setKeyAndMask a 0), pub_seed,
                Tsh, Tsh, sh_ps).
  { entailer!.
    unfold vb32. 
    rewrite field_address0_offset by auto with field_compatible.
    reflexivity. }
  { rewrite (memory_block_data_at__tarray_tuchar_eq Tsh vb32 32) by rep_lia.
    cancel. }

  (* ===== addr[7]=1 + addr_bytes(ab) ===== *)

  forward.
  rewrite upd_adrs_7.
  (* addr_bytes(v_ab, addr) -- overwrites v_ab *)
  forward_call (v_ab, a_ptr, setKeyAndMask a 1, Tsh, sh_a).

  (* ===== prf(mask, ab, pub_seed) = BM ===== *)

  sep_apply (data_at__memory_block_cancel Tsh (Tarray tuchar 32 noattr) v_mask).
  change (sizeof (Tarray tuchar 32 noattr)) with 32.
  (* prf(v_mask, v_ab, pub_seed):
       writes BM := PRF pub_seed (addr_bytes (setKeyAndMask a 1)) *)
  forward_call (v_mask, v_ab, ps_ptr,
                addr_bytes (setKeyAndMask a 1), pub_seed,
                Tsh, Tsh, sh_ps).
  { rewrite (memory_block_data_at__tarray_tuchar_eq Tsh v_mask 32) by rep_lia.
    cancel. }

  (* ===== Re-gather: v_buf + vb32 + vb64 back into buf[0..96) ===== *)

  replace (64 - 32) with 32 in * by reflexivity.

  set (KEY := block_to_vals (PRF pub_seed
                (addr_bytes (setKeyAndMask a 0)))).
  set (Z0  := repeat (Vint (Int.repr 0)) (Z.to_nat 32)).
  set (BM  := block_to_vals (PRF pub_seed
                (addr_bytes (setKeyAndMask a 1)))).
  set (XOR := block_to_vals (xor in_buf
                (PRF pub_seed (addr_bytes (setKeyAndMask a 1))))).

  assert (HlZ0 : Zlength Z0 = 32)
    by (subst Z0; rewrite Zlength_repeat; lia).
  assert (HlKEY : Zlength KEY = 32).
  { subst KEY. rewrite block_to_vals_length. apply SHA256_Zlength. }
  assert (HlPRF : Zlength (PRF pub_seed (addr_bytes (setKeyAndMask a 1))) = 32)
    by apply SHA256_Zlength.
  assert (HlBM : Zlength BM = 32)
    by (subst BM; rewrite block_to_vals_length; apply SHA256_Zlength).
  assert (HlxorBM : Zlength (xor in_buf (PRF pub_seed (addr_bytes (setKeyAndMask a 1)))) = 32).
  { unfold xor.
    rewrite Zlength_map, Zlength_combine.
    transitivity (Z.min 32 32); [| reflexivity].
    f_equal; [exact H | exact HlPRF]. }
  assert (HlXOR : Zlength XOR = 32)
    by (subst XOR; rewrite block_to_vals_length; exact HlxorBM).

  gather_SEP (data_at Tsh (tarray tuchar 32) Z0 v_buf)
             (data_at Tsh (tarray tuchar 32) KEY vb32)
             (data_at_ Tsh (Tarray tuchar 32 noattr) vb64).
  rewrite (data_at__eq _ (Tarray tuchar 32 noattr) vb64).
  unfold default_val.
  unfold vb64.
  change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
  replace (data_at Tsh (tarray tuchar 32) (Zrepeat Vundef 32)
             (field_address0 (tarray tuchar 64) (SUB 32) vb32))
    with  (data_at Tsh (tarray tuchar (64 - 32)) (Zrepeat Vundef (64 - 32))
             (field_address0 (tarray tuchar 64) (SUB 32) vb32))
    by (f_equal; f_equal; lia).
  rewrite sepcon_assoc.
  assert (HlVundef : Zlength (Zrepeat (@Vundef) (64 - 32)) = 64 - 32)
    by split_sc.
  rewrite <- (split2_data_at_Tarray_app 32 64 Tsh tuchar KEY
                (Zrepeat Vundef (64 - 32)) vb32 HlKEY HlVundef).
  assert (HlKeyRest : Zlength (KEY ++ Zrepeat Vundef 32) = 96 - 32)
    by (rewrite Zlength_app, HlKEY, Zlength_Zrepeat; lia).
  unfold vb32.
  change (Tarray tuchar 96 noattr) with (tarray tuchar 96).
  rewrite <- (split2_data_at_Tarray_app 32 96 Tsh tuchar Z0
                (KEY ++ Zrepeat Vundef 32) v_buf HlZ0 HlKeyRest).

  (* ===== xor-loop: buf[64+i] = in[i] XOR mask[i] ===== *)

  (* xor loop: for i in 0..32: v_buf[64+i] = in[i] ^ mask[i]. *)
  forward_for_simple_bound 32
    (EX j : Z,
      PROP ()
      LOCAL (lvar _mask (tarray tuchar 32) v_mask;
             lvar _ab (tarray tuchar 32) v_ab;
             lvar _buf (tarray tuchar 96) v_buf;
             temp _out buf_ptr; temp _in buf_ptr; temp _pub_seed ps_ptr;
             temp _addr a_ptr)
      SEP (data_at Tsh (tarray tuchar 32) BM v_mask;
           data_at Tsh (tarray tuchar 32)
             (block_to_vals (addr_bytes (setKeyAndMask a 1))) v_ab;
           data_at sh_ps (tarray tuchar 32) (block_to_vals pub_seed) ps_ptr;
           data_at sh_a t_addr (adrs_to_vals (setKeyAndMask a 1)) a_ptr;
           data_at Tsh (tarray tuchar 96)
             (Z0 ++ KEY ++ sublist 0 j XOR ++ Zrepeat Vundef (32 - j)) v_buf;
           data_at sh_b (tarray tuchar 32) (block_to_vals in_buf) buf_ptr)).
  - (* loop entry *) entailer!.
  - (* loop body *)
    forward.
    { close_tc_byte. }
    forward.
    { subst BM. close_tc_byte. }
    forward.

    (* ===== Re-establish the loop invariant ===== *)

    (* Hoist the [combine] length so [Znth_map] dispatches cleanly. *)
    assert (Hcomblen : Zlength (combine in_buf
        (PRF pub_seed (addr_bytes (setKeyAndMask a 1)))) = 32).
    { rewrite Zlength_combine.
      transitivity (Z.min 32 32); [|reflexivity].
      f_equal; assumption. }

    (* The newly-stored byte at index 64+i equals [Znth i XOR]. *)
    match goal with
    | |- context[upd_Znth _ _ ?v] =>
        assert (Hxor_val : v = Znth i XOR)
    end.
    { (* Peel the three [Znth_block_to_vals] layers. *)
      rewrite Znth_block_to_vals by lia.
      subst BM. rewrite Znth_block_to_vals by lia.
      simpl force_val.
      subst XOR. rewrite Znth_block_to_vals by lia.

      (* Collapse to the byte-level xor identity. *)
      unfold xor.
      rewrite Znth_map
        by (replace (Zlength _) with 32 by (symmetry; exact Hcomblen); lia).
      rewrite (Znth_combine i in_buf _ (eq_trans H (eq_sym HlPRF))).
      apply xor_byte_identity. }

    (* Plug [Hxor_val] in and reduce to the per-step [xor_store_step]. *)
    rewrite Hxor_val.
    entailer!.
    apply derives_refl'.
    f_equal.
    apply xor_store_step; auto. 

  (* ===== Post-loop gather ===== *)

  - rewrite sublist_same by lia.
    replace (32 - 32) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.

    (* ===== sha256 ===== *)

    (* Buf contents equal
       block_to_vals (toByte 0 32 ++ KEY_bytes ++ xor_bytes). *)
    set (INPUT := toByte 0 (Z.to_nat 32) ++
                  PRF pub_seed (addr_bytes (setKeyAndMask a 0)) ++
                  xor in_buf
                    (PRF pub_seed (addr_bytes (setKeyAndMask a 1)))).
    assert (HlPRF0 : Zlength (PRF pub_seed (addr_bytes (setKeyAndMask a 0))) = 32)
      by apply SHA256_Zlength.

    assert (HlINPUT : Zlength INPUT = 96).
    { subst INPUT.
      rewrite !Zlength_app, toByte_Zlength, HlxorBM, HlPRF0.
      change (Z.of_nat (Z.to_nat 32)) with 32.
      reflexivity. }

    assert (Hbufeq : Z0 ++ KEY ++ XOR = block_to_vals INPUT).
    { subst Z0 KEY XOR INPUT.
      rewrite !block_to_vals_app.
      replace (repeat (Vint (Int.repr 0)) (Z.to_nat 32))
        with (block_to_vals (toByte 0 (Z.to_nat 32))).
        - reflexivity. 
        - unfold block_to_vals.
          rewrite toByte_0_zeros.
          rewrite map_repeat.
          reflexivity. }

    rewrite Hbufeq.
    sep_apply (data_at_data_at_ sh_b (tarray tuchar 32)
                 (block_to_vals in_buf) buf_ptr).
    (* sha256(buf_ptr, v_buf, 96, INPUT) *)
    forward_call (buf_ptr, v_buf, 96, INPUT, sh_b, Tsh).
    { entailer!. }
Qed.
