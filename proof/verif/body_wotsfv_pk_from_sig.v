(** * body_wotsfv_pk_from_sig: VST body proof for [wots_pk_from_sig]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.
From wots Require Import model.wots model.notation model.correct.

Open Scope Z_scope.

Lemma body_wotsfv_pk_from_sig :
  semax_body Vprog Gprog f_wotsfv_pk_from_sig wotsfv_pk_from_sig_spec.
Proof.
  start_function.

  (* ===== Null-check prelude (dead panic branches) ===== *)

  step_null_assert pk_ptr  Hpk.
  step_null_assert sig_ptr Hsig.
  step_null_assert msg_ptr Hmsg.
  step_null_assert ps_ptr  Hps.
  step_null_assert a_ptr   Ha.

  (* ===== Setup ===== *)

  change pk_bytes with 2144 in *.
  change sig_bytes with 2144 in *.
  assert_PROP (Zlength (block_to_vals msg) = n_bytes) as Hlmsg
    by entailer!.
  assert_PROP (Zlength (block_to_vals pub_seed) = n_bytes) as Hlps
    by entailer!.
  rewrite block_to_vals_length in Hlmsg, Hlps.

  (* ===== expand_digits call ===== *)

  (* expand_digits(digits, msg) *)
  forward_call (v_digits, msg_ptr, msg, Tsh, sh_m).
  assert (Hdigit_le : forall k,
      (nth k (expand_msg msg) 0%nat <= 15)%nat)
    by (intros k; apply nth_expand_msg_le_15; assumption).
  pose proof (expand_msg_Zlength msg Hlmsg) as Hexpand_Zlen.
  pose proof (digits_to_vals_expand_Zlength msg Hlmsg) as Hdtv_len.

  (* ===== forward_for_simple_bound invariant ===== *)

  (* Main loop. Addr state is tracked existentially (post is EX a'). *)
  forward_for_simple_bound 67
    (EX i : Z, EX a_cur : adrs,
      PROP (adrs_struct_eq a_cur a)
      LOCAL (temp _pk_cand pk_ptr; temp _sig sig_ptr;
             temp _msg msg_ptr; temp _pub_seed ps_ptr;
             temp _addr a_ptr;
             lvar _digits (tarray tuchar 67) v_digits)
      SEP (data_at sh_pk (tarray tuchar 2144)
             (blocks_to_vals
                (map (pkFromSig_block sig msg pub_seed a)
                     (seq 0 (Z.to_nat i)))
              ++ Zrepeat Vundef (2144 - 32 * i)) pk_ptr;
           data_at Tsh (tarray tuchar (Z.of_nat len))
             (digits_to_vals (expand_msg msg)) v_digits;
           data_at sh_sig (tarray tuchar 2144)
             (blocks_to_vals sig) sig_ptr;
           data_at sh_m (tarray tuchar n_bytes)
             (block_to_vals msg) msg_ptr;
           data_at sh_ps (tarray tuchar n_bytes)
             (block_to_vals pub_seed) ps_ptr;
           data_at sh_a t_addr (adrs_to_vals a_cur) a_ptr)).

  (* ===== loop entry ===== *)

  - Exists a. 
    entailer!.
    apply adrs_struct_eq_refl.

  (* ===== loop body ===== *)

  - Intros.

    (* Save root field_compatibles before splitting. *)
    assert_PROP (field_compatible (tarray tuchar 2144) nil pk_ptr)
      as Hfc_pk by entailer!.
    assert_PROP (field_compatible (tarray tuchar 2144) nil sig_ptr)
      as Hfc_sig by entailer!.
    set (FILLED := blocks_to_vals
                     (map (pkFromSig_block sig msg pub_seed a)
                          (seq 0 (Z.to_nat i)))).

    assert (Hnth_sig : forall k,
        Zlength (nth k sig default) = n_bytes)
      by (intros k; apply nth_block_Zlength_default; assumption).
    assert (Hlen_sig : length sig = 67%nat)
      by (change 67%nat with len; assumption).
    assert (Hnth_Znth :
        nth (Z.to_nat i) (expand_msg msg) 0%nat =
        Znth i (expand_msg msg))
      by (rewrite <- (nth_Znth i (expand_msg msg)
                      ) by lia;
          reflexivity).
    assert (HlFILLED : Zlength FILLED = 32 * i).
    { subst FILLED. 
      rewrite Zlength_blocks_to_vals_fixed.
      - rewrite length_map, length_seq. 
        lia.
      - apply Forall_map, Forall_forall. 
        intros k _.
        apply pkFromSig_block_Zlength, Hnth_sig. }

    (* Split pk into FILLED + MID(32) + TAIL. *)
    erewrite (split2_data_at_Tarray_app (32*i) 2144 sh_pk tuchar
               FILLED (Zrepeat Vundef (2144 - 32*i)))
      by (try exact HlFILLED; split_sc).
    replace (2144 - 32*i) with (32 + (2144 - 32*(i+1))) by lia.
    rewrite <- Zrepeat_app by lia.
    erewrite (split2_data_at_Tarray_app 32 _ sh_pk tuchar
               (Zrepeat Vundef 32)
               (Zrepeat Vundef (2144 - 32*(i+1))))
      by split_sc.
    set (pSUFF :=
      field_address0 (tarray tuchar 2144) (SUB (32*i)) pk_ptr).
    Intros.
    replace (Zrepeat (A:=val) Vundef 32)
      with (default_val (tarray tuchar 32)) by reflexivity.
    rewrite <- data_at__eq.

    (* Split sig into SFILLED + SCHUNK(32) + STAIL. *)
    set (SFILLED := blocks_to_vals (firstn (Z.to_nat i) sig)).
    set (SCHUNK :=
      block_to_vals (nth (Z.to_nat i) sig default)).
    set (STAIL :=
      blocks_to_vals (skipn (S (Z.to_nat i)) sig)).
    rewrite (blocks_to_vals_split sig (Z.to_nat i) default).
    2: { assert (length sig = len) by assumption.
         change len with 67%nat in *. lia. }
    fold SFILLED SCHUNK STAIL.

    assert (HlSFILLED : Zlength SFILLED = 32 * i).
    { subst SFILLED. 
      rewrite Zlength_blocks_to_vals_fixed.
      - rewrite firstn_length_le by lia. 
        lia.
      - apply Forall_firstn. 
        assumption. }
    assert (HlSCHUNK : Zlength SCHUNK = 32).
    { subst SCHUNK.
      rewrite block_to_vals_length. 
      apply Hnth_sig. }
    assert (HlSTAIL : Zlength STAIL = 32 * (66 - i)).
    { subst STAIL. 
      rewrite Zlength_blocks_to_vals_fixed.
      - rewrite List.length_skipn. 
        lia.
      - apply Forall_skipn.
        assumption. }

    erewrite (split2_data_at_Tarray_app (32*i) 2144 sh_sig tuchar
               SFILLED (SCHUNK ++ STAIL))
      by (try exact HlSFILLED;
          rewrite Zlength_app, HlSCHUNK, HlSTAIL; lia).
    erewrite (split2_data_at_Tarray_app 32 _ sh_sig tuchar
               SCHUNK STAIL)
      by (try exact HlSCHUNK; split_sc).
    set (pSIG := field_address0 (tarray tuchar 2144) (SUB (32*i)) sig_ptr).
    Intros.

    (* Prepare src for memcpy: convert SCHUNK to map Vint. *)
    sep_apply
      (data_at__memory_block_cancel sh_pk (tarray tuchar 32) pSUFF).
    change (sizeof (tarray tuchar 32)) with 32.
    unfold SCHUNK.
    rewrite (block_to_vals_eq_Vint (nth (Z.to_nat i) sig default)).
    set (SCHUNK_int :=
      block_ints (nth (Z.to_nat i) sig default)).
    assert (HlSCI : Zlength SCHUNK_int = 32).
    { subst SCHUNK_int.
      rewrite Zlength_block_ints. 
      apply Hnth_sig. }

    (* memcpy(pk + i*N, sig + i*N, N) *)
    forward_call (sh_sig, sh_pk, pSUFF, pSIG, 32, SCHUNK_int).
    { entailer!. 
      simpl.
      f_equal.
      { finish_slot_addr pSUFF Hfc_pk. }
      f_equal.
      finish_slot_addr pSIG Hfc_sig. }

    (* ===== Reset addr scratch slots ===== *)

    (* Store addr[5] = i *)
    forward.
    rewrite upd_adrs_5.

    (* Store addr[6] = 0 *)
    forward.
    rewrite upd_adrs_6.

    (* Store addr[7] = 0 *)
    forward.
    rewrite upd_adrs_7.

    (* Convert pSUFF back from Vint for chain call. *)
    unfold SCHUNK_int.
    rewrite <- !(block_to_vals_eq_Vint (nth (Z.to_nat i) sig default)).

    (* Load digits[i] into _t'5 *)
    change (Z.of_nat len) with 67.
    assert (Hi_digit_le :
        (nth (Z.to_nat i) (expand_msg msg) 0%nat <= 15)%nat)
      by (apply Hdigit_le).
    forward.
    { close_tc_byte_digit. }
    unfold digits_to_vals.
    rewrite Znth_map by lia.
    fold digits_to_vals.

    (* Load digits[i] into _t'6 *)
    forward.
    { entailer!.
      rewrite Znth_map by lia.
      unfold Vubyte.
      simpl.
      pose proof (Byte.unsigned_range
        (Byte.repr (Z.of_nat (Znth i (expand_msg msg))))) as Hrng1.
      rewrite Int.unsigned_repr by rep_lia.
      rep_lia. }

    (* chain(pk + i*N, digits[i], W - 1 - digits[i], pub_seed, addr) *)
    forward_call (pSUFF, ps_ptr, a_ptr,
                  Z.of_nat (Znth i (expand_msg msg)),
                  15 - Z.of_nat (Znth i (expand_msg msg)),
                  nth (Z.to_nat i) sig default,
                  pub_seed,
                  setKeyAndMask
                    (setHashAddress (setChainAddress a_cur i) 0) 0,
                  sh_pk, sh_ps, sh_a).
    { entailer!.
      simpl.
      f_equal.
      { finish_slot_addr pSUFF Hfc_pk. }
      f_equal.
      { unfold Vubyte.
        f_equal.
        rewrite Byte.unsigned_repr by rep_lia.
        reflexivity. }
      f_equal.
      rewrite Znth_map by lia.
      unfold Vubyte. 
      rewrite Byte.unsigned_repr by rep_lia.
      unfold sem_sub_default.
      simpl.
      f_equal. 
      unfold Int.sub.
      rewrite !Int.unsigned_repr by rep_lia.
      reflexivity. }
    { (* PROP of chain_spec *)
      unfold w_pred.
      repeat split; try lia;
        try (apply (Hnth_sig (Z.to_nat i))); try assumption. }

    (* post-chain: normalise nat/Z coercions *)
    change (Z.to_nat 0) with 0%nat.
    replace (Z.to_nat (Z.of_nat (Znth i (expand_msg msg))))
      with (Znth i (expand_msg msg))%nat by lia.
    rewrite <- Hnth_Znth.
    replace (Z.to_nat (15 - Z.of_nat (nth (Z.to_nat i) (expand_msg msg) 0%nat)))
      with (w_pred - nth (Z.to_nat i) (expand_msg msg) 0%nat)%nat.
    2: { unfold w_pred.
         pose proof (Hdigit_le (Z.to_nat i)) as Hd.
         rewrite Z2Nat.inj_sub by lia.
         change (Z.to_nat 15) with 15%nat.
         f_equal. 
         rewrite Nat2Z.id.
         reflexivity. }

    (* chain output on pSUFF = pkFromSig_block *)
    replace i with (Z.of_nat (Z.to_nat i)) at 7 by lia.
    replace (setKeyAndMask
               (setHashAddress (setChainAddress a_cur (Z.of_nat (Z.to_nat i))) 0) 0)
      with (setChainAddress
              (setKeyAndMask (setHashAddress a_cur 0) 0)
              (Z.of_nat (Z.to_nat i)))
      by (destruct a_cur; reflexivity).
    rewrite (chain_pkFromSig_block_struct_eq sig msg pub_seed
               (Z.to_nat i)
               (setKeyAndMask (setHashAddress a_cur 0) 0) a).
    2: { destruct a_cur as [al ath atl aty aot ac ah akm].
         unfold adrs_struct_eq in *; simpl in *; tauto. }
    Exists (chain_addr_post
              (setKeyAndMask
                 (setHashAddress (setChainAddress a_cur i) 0) 0)
              (nth (Z.to_nat i) (expand_msg msg) 0%nat)
              (w_pred -
               nth (Z.to_nat i) (expand_msg msg) 0%nat)).

    (* Simplify arithmetic on slice offsets. *)
    replace (32 + (2144 - 32 * (i + 1)) - 32)
      with (2144 - 32 * i - 32) by lia.
    replace (32 + (2144 - 32 * (i + 1)))
      with (2144 - 32 * i) by lia.
    change n_bytes with 32 in *.
    assert (Hlb_block : Zlength (block_to_vals
        (pkFromSig_block sig msg pub_seed a (Z.to_nat i))) = 32).
    { rewrite block_to_vals_length, pkFromSig_block_Zlength; auto. }

    (* Merge pk: pSUFF slot + TAIL -> (2144 - 32*i) chunk. *)
    gather_SEP
      (data_at sh_pk (tarray tuchar 32)
         (block_to_vals
            (pkFromSig_block sig msg pub_seed a (Z.to_nat i)))
         pSUFF)
      (data_at sh_pk (tarray tuchar (2144 - 32 * i - 32)) _ _).
    erewrite <- (split2_data_at_Tarray_app 32 (2144 - 32 * i)
                   sh_pk tuchar
                   (block_to_vals
                      (pkFromSig_block sig msg pub_seed a
                         (Z.to_nat i)))
                   (Zrepeat Vundef (2144 - 32 * (i + 1)))
                   pSUFF Hlb_block)
      by split_sc.
    unfold pSUFF.
    gather_SEP
      (data_at sh_pk (tarray tuchar (32 * i)) FILLED pk_ptr)
      (data_at sh_pk (tarray tuchar (2144 - 32 * i)) _ _).

    (* Merge sig: SCHUNK slot + STAIL -> (2144 - 32*i) chunk. *)
    gather_SEP
      (data_at sh_sig (tarray tuchar 32) _ pSIG)
      (data_at sh_sig (tarray tuchar (2144 - 32 * i - 32)) _ _).
    assert (HlSCHUNK_eq :
        Zlength (block_to_vals (nth (Z.to_nat i) sig default)) = 32)
      by exact HlSCHUNK.
    assert (HlSTAIL_eq : Zlength STAIL = 2144 - 32 * i - 32)
      by (rewrite HlSTAIL; lia).
    erewrite <- (split2_data_at_Tarray_app 32 (2144 - 32 * i)
                   sh_sig tuchar
                   (block_to_vals (nth (Z.to_nat i) sig default))
                   STAIL pSIG HlSCHUNK_eq)
      by (exact HlSTAIL_eq).
    unfold pSIG.
    gather_SEP
      (data_at sh_sig (tarray tuchar (32 * i)) SFILLED sig_ptr)
      (data_at sh_sig (tarray tuchar (2144 - 32 * i)) _ _).
    erewrite <- (split2_data_at_Tarray_app (32 * i) 2144 sh_sig
                   tuchar SFILLED
                   (block_to_vals (nth (Z.to_nat i) sig default)
                    ++ STAIL)
                   sig_ptr HlSFILLED)
      by (rewrite Zlength_app, HlSCHUNK_eq, HlSTAIL_eq; lia).

    (* Reshape sig content back to blocks_to_vals sig. *)
    replace (SFILLED ++
             block_to_vals (nth (Z.to_nat i) sig default)
             ++ STAIL)
      with (blocks_to_vals sig).
    2: { subst SFILLED STAIL.
         assert (Hlen' : (Z.to_nat i < length sig)%nat)
           by (rewrite Hlen_sig; lia).
         pose proof
           (blocks_to_vals_split sig (Z.to_nat i) default Hlen')
           as Hbsplit.
         rewrite <- Hbsplit. 
         reflexivity. }
    entailer!.
    { (* PROP of next invariant: adrs_struct_eq preserved through chain *)
      unfold adrs_struct_eq, chain_addr_post in *.
      destruct a_cur as [al ath atl aty aot ac ah akm].
      destruct (w_pred -
                nth (Z.to_nat i) (expand_msg msg) 0)%nat;
        simpl in *; repeat split; tauto. }

    (* Merge pk: FILLED + new-block -> seq 0 (i+1) prefix. *)
    erewrite <- (split2_data_at_Tarray_app (32 * i) 2144 sh_pk
                   tuchar FILLED
                   (block_to_vals
                      (pkFromSig_block sig msg pub_seed a
                         (Z.to_nat i))
                    ++ Zrepeat Vundef (2144 - 32 * (i + 1)))
                   pk_ptr HlFILLED)
      by (rewrite Zlength_app, Hlb_block, Zlength_Zrepeat; lia).
    apply derives_refl'.
    f_equal.
    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite blocks_to_vals_seq_S, <- app_assoc. 
    reflexivity.

  (* ===== loop exit ===== *)

  - Intros a_cur.
    Exists a_cur.
    replace (Z.to_nat 67) with 67%nat by lia.
    replace (2144 - 32 * 67) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.
    (* blocks_to_vals (map pkFromSig_block (seq 0 67))
       = blocks_to_vals (pkFromSig msg sig pub_seed a) *)
    change (map (pkFromSig_block sig msg pub_seed a) (seq 0 67))
      with (pkFromSig msg sig pub_seed a).
    entailer!.
Qed.
