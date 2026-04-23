(** * model.notation: helpers and syntactic sugar for the WOTS+ spec.

    Defines the three pieces of sugar used by [model.wots] to read
    like the RFC 8391 pseudocode:

    - [for i < k {{ body }}] -- indexed list comprehension, sugar for
      [map (fun i => body) (seq 0 k)].
    - [set x := e ; body]   -- sequential rebinding, sugar for
      [let x := e in body].
    - [l[i]]                -- list indexing with a per-type default
      supplied through the [Default] typeclass. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From Stdlib Require Import List.
Import ListNotations.

(* ================================================================= *)
(** ** Indexed list comprehension. *)

Definition for_idx {A} (k : nat) (f : nat -> A) : list A :=
  map f (seq 0 k).

Notation "'for' i < k {{ body }}" :=
  (for_idx k (fun i => body))
  (i binder, at level 200, body at level 200,
   format "'[hv' 'for'  i  <  k  {{ '//'  body '//' }} ']'").

(* ================================================================= *)
(** ** Sequential rebinding. *)

Notation "'set' x := e ; body" :=
  (let x := e in body)
  (x ident, at level 200, right associativity,
   format "'[v' 'set'  x  :=  e ; '//' body ']'").

(* ================================================================= *)
(** ** List indexing via a per-type default. *)

Class Default (A : Type) := default : A.
#[global] Instance default_nat : Default nat := 0%nat.

Notation "l [ i ]" := (nth i l default)
  (at level 2, left associativity, format "l [ i ]").
