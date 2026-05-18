(** * body_wotsfv_memset: VST body proof for [wotsfv_memset]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog.

Open Scope Z_scope.

Lemma body_wotsfv_memset : semax_body Vprog Gprog f_wotsfv_memset wotsfv_memset_spec.
Proof.

  (* ===== Setup ===== *)

  start_function.

  (* ===== Convert [memory_block] to [data_at_] over [tarray tuchar n] ===== *)

  rewrite memory_block_data_at__tarray_tuchar_eq by rep_lia.

  (* ===== Cast d = (uint8_t ptr) dst ===== *)

  forward.

  (* ===== Cast [_b = (uint8_t) byte] ===== *)

  forward.
  rewrite Int.zero_ext_idem by lia.

  (* ===== Loop: invariant builds [repeat (Vint c) i] prefix ===== *)

  forward_for_simple_bound n
    (EX i : Z,
      PROP ()
      LOCAL (temp _d p; temp _b (Vint (Int.zero_ext 8 c));
             temp _dst p; temp _n (Vlong (Int64.repr n)))
      SEP (data_at sh (tarray tuchar n)
             (repeat (Vint c) (Z.to_nat i) ++
              Zrepeat Vundef (n - i)) p)).

  (* Loop entry: i = 0 *)

  - rewrite data_at__tarray.
    entailer!.
    apply derives_refl'. f_equal.

  (* Loop body: write byte b at index i *)

  - forward.
    entailer!.
    apply derives_refl'. f_equal.
    assert (Hzx : Int.zero_ext 8 c = c).
    { apply zero_ext_inrange. simpl.
      change (two_p 8) with 256. lia. }
    rewrite Hzx.
    replace (Z.to_nat (i + 1)) with (Z.to_nat i + 1)%nat by lia.
    rewrite repeat_app. simpl repeat.
    rewrite <- app_assoc. simpl app.
    list_solve.

  (* ===== Loop exit ===== *)

  - replace (n - n) with 0 by lia.
    rewrite Zrepeat_0, app_nil_r.

    (* ===== Return [dst] ===== *)

    forward.
Qed.
