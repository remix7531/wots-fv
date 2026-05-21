(** * body_wotsfv_verify: VST body proof for [wots_verify]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.
From wots Require Import model.wots.

Open Scope Z_scope.

Lemma body_wotsfv_verify : semax_body Vprog Gprog f_wotsfv_verify wotsfv_verify_spec.
Proof.
  start_function.

  (* ===== Setup: resolve pk_bytes constant ===== *)

  change pk_bytes with 2144 in *.

  (* ===== wots_pk_from_sig(pk_cand, sig, msg, ps, a) ===== *)

  (* wots_pk_from_sig(v_pk_cand, sig_ptr, msg_ptr, ps_ptr, a_ptr) *)
  forward_call (v_pk_cand, sig_ptr, msg_ptr, ps_ptr, a_ptr,
                sig, msg, pub_seed, a,
                Tsh, sh_sig, sh_m, sh_ps, sh_a).
  Intros a_post.

  (* ===== memcmp preparation: rewrite to map Vint + Zlength asserts ===== *)

  rewrite (blocks_to_vals_eq_Vint (pkFromSig msg sig pub_seed a)).
  rewrite (blocks_to_vals_eq_Vint pk).
  set (pkc_int := block_ints (concat (pkFromSig msg sig pub_seed a))).
  set (pk_int  := block_ints (concat pk)).

  assert (Hl_pkc_int : Zlength pkc_int = 2144).
  { subst pkc_int. 
    unfold block_ints.
    rewrite Zlength_map.
    rewrite Zlength_concat_fixed by (apply pkFromSig_Forall_Zlength; auto).
    rewrite pkFromSig_length.
    reflexivity. }
  assert (Hl_pk_int : Zlength pk_int = 2144).
  { subst pk_int.
    unfold block_ints.
    rewrite Zlength_map.
    rewrite Zlength_concat_fixed by assumption.
    rewrite H.
    reflexivity. }

  (* ===== memcmp(pk_candidate, pk, WOTS_PK_BYTES) ===== *)

  (* memcmp(v_pk_cand, pk_ptr, WOTS_PK_BYTES) *)
  assert (Hbr : forall b : block,
            Forall (fun i : int => 0 <= Int.unsigned i < 256)
              (block_ints b)).
  { intros b. unfold block_ints.
    apply Forall_map, Forall_forall. intros x _.
    unfold Basics.compose.
    pose proof (Z.mod_pos_bound x 256 ltac:(lia)) as [Hlo Hhi].
    rewrite Int.unsigned_repr by rep_lia. lia. }

  forward_call (Tsh, sh_pk, v_pk_cand, pk_ptr, 2144, pkc_int, pk_int).
  { subst pkc_int pk_int. split; apply Hbr. }
  Intros r.
  (* VST's Intros doesn't name bare PROP props, so grab by pattern. *)
  match goal with
  | H : r = Int.zero <-> pkc_int = pk_int |- _ => rename H into Hrmemcmp
  end.

  (* ===== forward_if: branch on memcmp result ===== *)

  (* if (memcmp(pk_cand, pk, WOTS_PK_BYTES) == 0) *)
  forward_if (temp _t'2
    (Vint (Int.repr (if verify pk sig msg pub_seed a then 0 else -1)))).
  - (* r = Int.zero branch: contents match *)
    forward.
    entailer!.
    assert (Hcontents : pkc_int = pk_int)
      by (apply Hrmemcmp; reflexivity).
    subst pkc_int pk_int.
    rewrite (pk_int_eq_implies_verify pk sig msg pub_seed a) by auto.
    reflexivity.
  - (* r <> Int.zero branch: contents differ *)
    forward.
    entailer!.
    assert (Hne : pkc_int <> pk_int).
    { intro Heq.
      apply H6.
      rewrite (proj2 Hrmemcmp Heq).
      reflexivity. }
    subst pkc_int pk_int.
    rewrite (pk_int_neq_implies_verify_false pk sig msg pub_seed a Hne).
    reflexivity.

  (* ===== Postcondition ===== *)

  - forward.
    Exists a_post.
    subst pk_int pkc_int.
    rewrite <- (blocks_to_vals_eq_Vint pk).
    apply andp_right; [apply prop_right; auto|].
    sep_apply (data_at_data_at_ Tsh (tarray tuchar 2144)
                (map Vint (block_ints
                  (concat (pkFromSig msg sig pub_seed a))))
                v_pk_cand).
    cancel.
Qed.
