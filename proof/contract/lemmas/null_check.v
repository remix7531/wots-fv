(** * contract.lemmas.null_check: prelude tactic for [WOTSFV_ASSERT(ptr)].

    Every public entry in [src/wots.c] guards itself with a sequence of
    single-pointer [WOTSFV_ASSERT] calls that expand (per [src/util.h])
    to

        do { if (!ptr) wotsfv_panic(); } while (0);

    Clightgen renders each as

        Sloop (Sifthenelse (!ptr) (call panic) Sskip) Sbreak

    The panic branch is dead for every valid caller (pointers come in
    via [data_at], which forces [isptr]), so stepping past one such
    block is uniform: extract [isptr], take the [Sskip] side, exit via
    [Sbreak].  This file provides one Ltac that performs that step for
    one pointer, given the caller's invariant. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From VST Require Import floyd.proofauto.
From wots Require Import contract.public contract.helpers.

Open Scope Z_scope.

(** Step past one [WOTSFV_ASSERT(ptr)] expansion.

    Arguments:
    - [ptr]: the [val] argument the assertion is guarding.
    - [Hisptr]: a hypothesis name; the tactic populates it with
      [isptr ptr] (proved via [entailer!] against the current SEP).

    The loop invariant + break post is captured automatically from the
    current pre-condition.  Because the assertion-block is semantically
    a no-op when [isptr ptr] holds, using the same predicate for both
    discharges the loop trivially.

    After the tactic the goal advances past the [Sloop ... Sbreak]
    block: any subsequent [WOTSFV_ASSERT] (or the real function body)
    is now the head of the residual statement. *)
Ltac step_null_assert ptr Hisptr :=
  assert_PROP (isptr ptr) as Hisptr by entailer!;
  match goal with
  | |- semax _ ?inv _ _ =>
      forward_loop inv break: inv;
      only 1: solve [ entailer! ];
      only 1: solve
        [ forward_if True;
          only 1: solve [ destruct ptr; try contradiction; discriminate ];
          only 1: solve [ forward; entailer! ];
          forward; entailer! ]
  end.
