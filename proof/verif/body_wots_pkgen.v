(** * body_wots_pkgen: VST body proof for [wots_pkgen]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.
From wots Require Import model.wots model.notation.

Open Scope Z_scope.

Lemma body_wots_pkgen : semax_body Vprog Gprog f_wots_pkgen wots_pkgen_spec.
Proof.
  start_function.

  (* ===== Setup ===== *)

  change pk_bytes with 2144.

  (* ===== forward_for_simple_bound invariant ===== *)

  forward_for_simple_bound 67
    (EX i : Z,
      PROP ()
      LOCAL (temp _pk pk_ptr; temp _sk_seed sk_ptr;
             temp _pub_seed ps_ptr; temp _addr a_ptr)
      SEP (data_at sh_pk (tarray tuchar 2144)
             (blocks_to_vals (map (pkgen_block sk_seed pub_seed a)
                                  (seq 0 (Z.to_nat i)))
              ++ Zrepeat Vundef (2144 - 32 * i)) pk_ptr;
           data_at sh_sk (tarray tuchar n_bytes)
             (block_to_vals sk_seed) sk_ptr;
           data_at sh_ps (tarray tuchar n_bytes)
             (block_to_vals pub_seed) ps_ptr;
           data_at sh_a t_addr
             (adrs_to_vals (pkgen_addr_step a (Z.to_nat i))) a_ptr)).

  (* ===== Loop entry ===== *)

  - entailer!.

  (* ===== Loop body ===== *)

  - (* Hoist field_compatible for the whole pk buffer. *)
    assert_PROP (field_compatible (tarray tuchar 2144) nil pk_ptr)
      as Hfc_pk by entailer!.

    (* Split pk into FILLED (32*i) | MID (32) | TAIL (2144-32*(i+1)) *)
    set (FILLED := blocks_to_vals
                     (map (pkgen_block sk_seed pub_seed a)
                          (seq 0 (Z.to_nat i)))).
    assert (HlFILLED : Zlength FILLED = 32 * i).
    { subst FILLED. 
      rewrite Zlength_blocks_to_vals_fixed.
      - rewrite length_map, length_seq. lia.
      - apply Forall_map, Forall_forall. 
        intros k _.
        apply pkgen_block_Zlength. }
    erewrite (split2_data_at_Tarray_app (32*i) 2144 sh_pk tuchar
                FILLED (Zrepeat Vundef (2144 - 32*i)))
      by (try exact HlFILLED; split_sc).
    replace (2144 - 32*i) with (32 + (2144 - 32*(i+1))) by lia.
    rewrite <- Zrepeat_app by lia.
    erewrite (split2_data_at_Tarray_app 32 _ sh_pk tuchar
                (Zrepeat Vundef 32) (Zrepeat Vundef (2144 - 32*(i+1))))
      by split_sc.
    set (pSUFF := field_address0 (tarray tuchar 2144) (SUB (32*i)) pk_ptr).
    Intros.

    (* Convert MID slot to data_at_ *)
    replace (Zrepeat (A:=val) Vundef 32)
      with (default_val (tarray tuchar 32)) by reflexivity.
    rewrite <- data_at__eq.

    (* Hoist length facts used by both forward_calls. *)
    assert_PROP (Zlength (block_to_vals sk_seed) = n_bytes) as Hlss
      by entailer!.
    assert_PROP (Zlength (block_to_vals pub_seed) = n_bytes) as Hlps
      by entailer!.
    rewrite block_to_vals_length in Hlss, Hlps.

    (* derive_sk(pk + i*N, i, sk_seed, pub_seed, addr) *)
    forward_call (pSUFF, sk_ptr, ps_ptr, a_ptr,
                  i, sk_seed, pub_seed,
                  pkgen_addr_step a (Z.to_nat i),
                  sh_pk, sh_sk, sh_ps, sh_a).
    { solve_slot_addr pSUFF Hfc_pk. }

    (* chain(pk + i*N, 0, W - 1, pub_seed, addr) *)
    forward_call (pSUFF, ps_ptr, a_ptr,
                  0, 15,
                  genSK (Z.to_nat i) sk_seed pub_seed
                    (pkgen_addr_step a (Z.to_nat i)),
                  pub_seed,
                  derive_sk_addr_post (pkgen_addr_step a (Z.to_nat i)) i,
                  sh_pk, sh_ps, sh_a).
    { solve_slot_addr pSUFF Hfc_pk. }
    { unfold w_pred. 
      repeat split; try lia;
        try (apply genSK_Zlength); try assumption. }

    (* Rewrite chain/addr results to pkgen_block / pkgen_addr_step. *)
    change (Z.to_nat 0) with 0%nat.
    change (Z.to_nat 15) with w_pred.
    rewrite
      (chain_genSK_pkgen_step_eq sk_seed pub_seed a i (Z.to_nat i)),
      (chain_addr_post_derive_sk_pkgen_step a i (Z.to_nat i)) by lia.
    replace (Z.to_nat (i+1)) with (S (Z.to_nat i)) by lia.

    (* Arithmetic helpers for the merge rewrites below. *)
    replace (32 + (2144 - 32 * (i + 1)) - 32)
      with (2144 - 32 * i - 32) by lia.
    replace (32 + (2144 - 32 * (i + 1)))
      with (2144 - 32 * i) by lia.
    change n_bytes with 32.

    (* Merge MID + TAIL: slot @ pSUFF ++ tail = suffix @ pSUFF *)
    assert (Hlpkgen :
      Zlength (block_to_vals
        (pkgen_block sk_seed pub_seed a (Z.to_nat i))) = 32).
    { rewrite block_to_vals_length, pkgen_block_Zlength. 
      reflexivity. }

    gather_SEP
      (data_at sh_pk (tarray tuchar 32)
         (block_to_vals (pkgen_block sk_seed pub_seed a (Z.to_nat i)))
         pSUFF)
      (data_at sh_pk (tarray tuchar (2144 - 32 * i - 32)) _ _).

    erewrite <- (split2_data_at_Tarray_app 32 (2144 - 32 * i)
                   sh_pk tuchar
                   (block_to_vals
                     (pkgen_block sk_seed pub_seed a (Z.to_nat i)))
                   (Zrepeat Vundef (2144 - 32 * (i + 1)))
                   pSUFF Hlpkgen)
      by split_sc.

    (* Merge FILLED + suffix: FILLED @ pk_ptr ++ suffix = full array *)
    unfold pSUFF.
    gather_SEP
      (data_at sh_pk (tarray tuchar (32 * i)) FILLED pk_ptr)
      (data_at sh_pk (tarray tuchar (2144 - 32 * i)) _ _).
    entailer!.
    erewrite <- (split2_data_at_Tarray_app (32 * i) 2144 sh_pk tuchar
                   FILLED
                   (block_to_vals
                     (pkgen_block sk_seed pub_seed a (Z.to_nat i))
                    ++ Zrepeat Vundef (2144 - 32 * (i + 1)))
                   pk_ptr HlFILLED)
      by (rewrite Zlength_app, block_to_vals_length,
          pkgen_block_Zlength, Zlength_Zrepeat;
          rep_lia).
    apply derives_refl'. 
    f_equal.
    rewrite blocks_to_vals_seq_S, <- app_assoc. 
    reflexivity.

  (* ===== Loop exit ===== *)

  - replace (Z.to_nat 67) with 67%nat by lia.
    rewrite pkgen_addr_step_len.
    replace (2144 - 32 * 67) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.
    change (map (pkgen_block sk_seed pub_seed a) (seq 0 67))
      with (genPK sk_seed pub_seed a).
    entailer!.
Qed.
