(** * body_wotsfv_memcpy: VST body proof for [wotsfv_memcpy]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog.

Open Scope Z_scope.

Lemma body_wotsfv_memcpy :
  semax_body Vprog Gprog f_wotsfv_memcpy wotsfv_memcpy_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.

  (* Recover [Zlength contents = n] from the source [data_at]. *)

  assert_PROP (Zlength (map Vint contents) = n) as Hlen_map by entailer!.
  rewrite Zlength_map in Hlen_map.

  (* ===== Convert [memory_block] on dst to [data_at_] over uchars ===== *)

  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.

  (* ===== Cast d and s to (uint8_t ptr) ===== *)

  forward.
  forward.

  (* ===== Main loop: byte-wise copy ===== *)

  forward_for_simple_bound n
    (EX i : Z,
      PROP ()
      LOCAL (temp _d p; temp _s q; temp _dst p; temp _src q;
             temp _n (Vlong (Int64.repr n)))
      SEP (data_at qsh (tarray tuchar n) (map Vint contents) q;
           data_at psh (tarray tuchar n)
             (sublist 0 i (map Vint contents) ++
              Zrepeat Vundef (n - i)) p)).

  (* Loop entry: i = 0 *)

  - rewrite data_at__tarray.
    rewrite sublist_nil, app_nil_l.
    change (default_val tuchar) with Vundef.
    entailer!.
    apply derives_refl.

  (* Loop body: read s[i] into _t'1, then write d[i] *)

  - assert (HZnth : Znth i (map Vint contents) = Vint (Znth i contents)).
    { rewrite Znth_map by lia. reflexivity. }

    assert_PROP (Forall (value_fits tuchar) (map Vint contents))
      as Hfit by entailer!.
    assert (Hi_in : 0 <= i < Zlength (map Vint contents))
      by (rewrite Zlength_map; lia).
    pose proof (proj1 (Forall_Znth _ _) Hfit _ Hi_in) as Hfit_i.
    (* Hfit_i has [Znth i (map Vint contents)] in goal-printer form, but
       Rocq normalised it; restore via [HZnth]. *)
    assert (Hfit_v : value_fits tuchar (Vint (Znth i contents)))
      by (rewrite <- HZnth; exact Hfit_i).
    clear Hfit_i. rename Hfit_v into Hfit_i.

    rewrite value_fits_eq in Hfit_i. simpl in Hfit_i.
    assert (Hrng : 0 <= Int.unsigned (Znth i contents) <= Byte.max_unsigned).
    { specialize (Hfit_i ltac:(discriminate)).
      simpl in Hfit_i. rep_lia. }

    forward.
    forward.

    entailer!.
    apply derives_refl'. f_equal.

    assert (Hpfx_len :
      Zlength (sublist 0 i (map Vint contents)) = i).
    { rewrite Zlength_sublist; rewrite ?Zlength_map; lia. }

    rewrite upd_Znth_app2
      by (rewrite Hpfx_len, Zlength_Zrepeat by lia; lia).
    rewrite Hpfx_len.
    replace (i - i) with 0 by lia.

    assert (Hrep : Zrepeat (@Vundef) (Zlength contents - i) =
                   Vundef :: Zrepeat (@Vundef) (Zlength contents - i - 1)).
    { unfold Zrepeat.
      replace (Z.to_nat (Zlength contents - i))
        with (S (Z.to_nat (Zlength contents - i - 1))) by lia.
      reflexivity. }
    rewrite Hrep.
    rewrite upd_Znth0.

    rewrite (sublist_split 0 i (i + 1) (map Vint contents))
      by (rewrite ?Zlength_map; lia).
    rewrite (sublist_one i (i + 1) (map Vint contents))
      by (rewrite ?Zlength_map; lia).
    rewrite Znth_map by lia.
    rewrite <- app_assoc. simpl.
    replace (Zlength contents - (i + 1)) with (Zlength contents - i - 1) by lia.
    reflexivity.

  (* ===== Loop exit: collapse to [map Vint contents] ===== *)

  - rewrite sublist_same by (rewrite ?Zlength_map; lia).
    replace (n - n) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.

    (* ===== Return [dst] ===== *)

    forward.
Qed.
