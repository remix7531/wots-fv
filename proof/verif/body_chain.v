(** * body_chain: VST body proof for [chain]. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog contract.lemmas.

Lemma body_chain : semax_body Vprog Gprog f_chain chain_spec.
Proof.
  start_function.

  (* ===== forward_for_simple_bound invariant ===== *)

  forward_for_simple_bound steps
    (EX j : Z,
      PROP ()
      LOCAL (temp _buf buf_ptr;
             temp _start (Vint (Int.repr start));
             temp _steps (Vint (Int.repr steps));
             temp _pub_seed ps_ptr;
             temp _addr a_ptr)
      SEP (data_at sh_b (tarray tuchar n_bytes)
             (block_to_vals
                (chain in_buf (Z.to_nat start) (Z.to_nat j)
                   pub_seed a))
             buf_ptr;
           data_at sh_ps (tarray tuchar n_bytes)
             (block_to_vals pub_seed) ps_ptr;
           data_at sh_a t_addr
             (adrs_to_vals
                (chain_addr_post a (Z.to_nat start) (Z.to_nat j)))
             a_ptr)).

  (* ===== Loop entry: j = 0 ===== *)

  - unfold w_pred in H1.
    rep_lia.

  (* ===== Loop entry invariant ===== *)

  - entailer!.

  (* ===== Loop body: thash_f call + addr update ===== *)

  - pose proof (chain_Zlength in_buf (Z.to_nat start) (Z.to_nat i)
                  pub_seed a H2) as Hlen_chain.
    forward.
    rewrite add_repr, upd_adrs_6.

    (* thash_f(buf, buf, pub_seed, addr) *)
    forward_call (buf_ptr, ps_ptr, a_ptr,
                  chain in_buf (Z.to_nat start) (Z.to_nat i) pub_seed a,
                  pub_seed,
                  setHashAddress
                    (chain_addr_post a (Z.to_nat start) (Z.to_nat i))
                    (start + i),
                  sh_b, sh_ps, sh_a).

    replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia.
    rewrite chain_addr_post_succ.
    simpl chain.
    replace (Z.of_nat (Z.to_nat start + Z.to_nat i))
      with (start + i) by lia.
    rewrite (thash_f_chain_addr_post_elim
               (chain in_buf (Z.to_nat start) (Z.to_nat i) pub_seed a)
               pub_seed a (Z.to_nat start) (Z.to_nat i) (start + i)).
    entailer!.

  (* ===== Loop exit ===== *)

  - entailer!.
Qed.
