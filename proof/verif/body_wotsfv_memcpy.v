(** * body_wotsfv_memcpy: VST body proof for [wotsfv_memcpy]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog.

Open Scope Z_scope.

Section body_wotsfv_memcpy_proof.
Context `{!VSTGS OK_ty Σ}.

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
    (∃ i : Z,
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

  - assert_PROP (Forall (value_fits tuchar) (map Vint contents))
      as Hfit by entailer!.
    forward.
    { entailer!.
      pose proof (proj1 (Forall_Znth _ _) Hfit i) as Hfit_i.
      rewrite Znth_map in Hfit_i by lia.
      specialize (Hfit_i ltac:(rewrite Zlength_map; lia)).
      rewrite value_fits_by_value in Hfit_i by reflexivity.
      apply (Hfit_i ltac:(discriminate)). }
    forward.

    (* The loop-invariant re-establishment is pure list algebra
       (upd_Znth / sublist / Zrepeat / Znth_map): list_solve proves the
       data_at array entailment directly via data_subsume_array_ext. *)
    entailer!.
    list_solve.

  (* ===== Loop exit: collapse to [map Vint contents] ===== *)

  - rewrite sublist_same by (rewrite ?Zlength_map; lia).
    replace (n - n) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.

    (* ===== Return [dst] ===== *)

    forward.
Qed.

End body_wotsfv_memcpy_proof.
