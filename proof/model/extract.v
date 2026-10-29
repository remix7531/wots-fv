(** * model.extract: build a C-linkable library from the WOTS+ Rocq spec.

    Extracts [genPK], [sign], [verify] to OCaml.  [SHA256] is realised
    at link time by [ocaml/sha256_ext.ml] via Digestif.  See
    [ocaml/wrap.c] and the Makefile for the C bridge. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From Stdlib Require Import Extraction ExtrOcamlBasic.
From Stdlib Require Import ExtrOcamlZInt ExtrOcamlNatInt.
From wots Require Import model.wots.

Set Extraction Output Directory "build/ocaml".
Set Extraction AccessOpaque.

(** SHA-256: realized by [ocaml/sha256_ext.ml] via Digestif. *)
Extract Constant SHA256 => "Sha256_ext.sha256".

Extraction "wots_extracted.ml" genPK sign verify adrs_of_words.
