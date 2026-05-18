(** * body_wotsfv_panic: VST body proof for [wotsfv_panic].

    The funspec has a [PROP(False)] precondition (panic is only invoked
    on unreachable error paths), so the body proof is vacuous: any
    caller able to establish the precondition has already derived
    [False] and the body can be anything. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.gprog.

Open Scope Z_scope.

Lemma body_wotsfv_panic :
  semax_body Vprog Gprog f_wotsfv_panic wotsfv_panic_spec.
Proof.
  start_function.
  contradiction.
Qed.
