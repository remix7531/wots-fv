(** * body_addr_bytes: VST body proof for [addr_bytes]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.

Lemma body_addr_bytes : semax_body Vprog Gprog f_addr_bytes addr_bytes_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.

  (* ===== forward_for_simple_bound 8 invariant
         (accumulate addr_bytes_prefix) ===== *)

  forward_for_simple_bound 8
    (EX i : Z,
      PROP ()
      LOCAL (temp _out out_ptr; temp _a a_ptr)
      SEP (data_at sh_o (tarray tuchar 32)
             (block_to_vals (addr_bytes_prefix a (Z.to_nat i)) ++
              Zrepeat Vundef (32 - 4 * i)) out_ptr;
           data_at sh_a t_addr (adrs_to_vals a) a_ptr)).

  (* ===== Loop entry ===== *)

  - entailer!.

  (* ===== Loop body: load adrs word, 4 byte-writes with shifts,
         reassemble invariant ===== *)

  - set (v := nth (Z.to_nat i) (adrs_words a) 0).
    assert (Hnth : Znth i (adrs_to_vals a) = Vint (Int.repr v)).
    { subst v.
      rewrite adrs_to_vals_eq, Znth_map
        by (rewrite adrs_words_length; lia).
      rewrite <- nth_Znth by (rewrite adrs_words_length; lia).
      reflexivity. }

    forward.
    { entailer!.
      rewrite adrs_to_vals_eq, Znth_map
        by (rewrite adrs_words_length; lia).
      apply I. }

    do 7 forward. 

    entailer!.
    apply derives_refl'.
    f_equal.
    replace (Znth i (adrs_to_vals a)) with (Vint (Int.repr v)) by auto.
    simpl force_val.

    assert (Hsucc : Z.to_nat (i + 1) = S (Z.to_nat i)) by lia.
    rewrite Hsucc, addr_bytes_prefix_succ by lia. fold v.
    rewrite block_to_vals_app, toByte_4_eq.
    cbn [block_to_vals map].
    rewrite !zero_ext_shru_byte by auto.
    rewrite zero_ext_byte.

    assert (Hpfx : Zlength (block_to_vals (addr_bytes_prefix a (Z.to_nat i))) = 4 * i)
      by (rewrite block_to_vals_length, addr_bytes_prefix_length by lia; lia).
    set (L := block_to_vals (addr_bytes_prefix a (Z.to_nat i))) in *.
    assert (Hrest : Zrepeat (@Vundef) (32 - 4 * i) =
        [Vundef; Vundef; Vundef; Vundef] ++ Zrepeat (@Vundef) (32 - 4 * (i + 1))).
    { replace (32 - 4 * i) with (4 + (32 - 4 * (i + 1))) by lia.
      rewrite <- Zrepeat_app by lia.
      reflexivity. }

    rewrite Hrest, app_assoc.
    rewrite <- !app_assoc.
    apply (upd_Znth4_of_prefix L Vundef Vundef Vundef Vundef _ _ _ _
             (Zrepeat Vundef (32 - 4 * (i + 1))) (4 * i) Hpfx).

  (* ===== Loop exit ===== *)

  - entailer!.
Qed.
