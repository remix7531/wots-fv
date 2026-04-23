(** * model.wots: RFC 8391 WOTS+ -- types, primitives, and algorithms.

    Parameters are fixed to [WOTSP-SHA2_256] (RFC 8391 Sec.5.2):
    [n = 32], [w = 16], [len_1 = 64], [len_2 = 3], [len = 67].

    The top-level algorithms ([genPK], [sign], [pkFromSig], [verify])
    at the bottom of this file are written to mirror RFC 8391 Sec.3.1
    pseudocode as directly as possible. *)
(** Copyright (C) 2026 remix7531
    SPDX-License-Identifier: GPL-3.0-or-later *)

From Stdlib Require Import List ZArith.
From wots Require Export model.notation.
Import ListNotations.
Open Scope Z_scope.

(* ================================================================= *)
(** ** RFC 8391 Sec.5.2 parameters -- [WOTSP-SHA2_256]. *)

Definition n     : nat := 32.
Definition w     : Z   := 16.
Definition log_w : Z   := 4.
Definition len_1 : nat := 64.
Definition len_2 : nat := 3.
Definition len   : nat := len_1 + len_2.

(** [w - 1] as a [nat] (chain-step count); RFC writes this as [w - 1]. *)
Definition w_pred : nat := 15.

Definition pk_bytes  : Z := Z.of_nat (len * n).
Definition sig_bytes : Z := Z.of_nat (len * n).

(* ================================================================= *)
(** ** Flat data types.

    A [byte] holds values in [[0, 256)]; a [word] holds values in
    [[0, 2^32)]; a [block] is an [n]-byte string.  Validity is
    treated as a property, not a type invariant -- this keeps the
    algorithms readable. *)

Definition byte  : Type := Z.
Definition word  : Type := Z.
Definition block : Type := list byte.

Definition byte_ok  (b : byte)  : Prop := 0 <= b < 256.
Definition word_ok  (x : word)  : Prop := 0 <= x < 2^32.
Definition block_ok (b : block) : Prop := length b = n.

Definition zero_block : block := repeat 0%Z n.
#[global] Instance default_block : Default block := zero_block.

(* ================================================================= *)
(** ** RFC Sec.2.5 -- OTS hash address.

    Eight named 32-bit words in RFC order.  The 64-bit tree address
    is carried as two words [tree_hi] / [tree_lo] to avoid 64-bit
    integer overflow once the spec is extracted.  Only the last
    three words (chain / hash / keyAndMask) are manipulated by
    WOTS+. *)

Record adrs : Type := {
  adrs_layer      : word;
  adrs_tree_hi    : word;
  adrs_tree_lo    : word;
  adrs_type       : word;
  adrs_ots        : word;
  adrs_chain      : word;
  adrs_hash       : word;
  adrs_keyAndMask : word;
}.

Definition setChainAddress (a : adrs) (v : word) : adrs :=
  {| adrs_layer      := adrs_layer a;
     adrs_tree_hi    := adrs_tree_hi a;
     adrs_tree_lo    := adrs_tree_lo a;
     adrs_type       := adrs_type a;
     adrs_ots        := adrs_ots a;
     adrs_chain      := v;
     adrs_hash       := adrs_hash a;
     adrs_keyAndMask := adrs_keyAndMask a |}.

Definition setHashAddress (a : adrs) (v : word) : adrs :=
  {| adrs_layer      := adrs_layer a;
     adrs_tree_hi    := adrs_tree_hi a;
     adrs_tree_lo    := adrs_tree_lo a;
     adrs_type       := adrs_type a;
     adrs_ots        := adrs_ots a;
     adrs_chain      := adrs_chain a;
     adrs_hash       := v;
     adrs_keyAndMask := adrs_keyAndMask a |}.

Definition setKeyAndMask (a : adrs) (v : word) : adrs :=
  {| adrs_layer      := adrs_layer a;
     adrs_tree_hi    := adrs_tree_hi a;
     adrs_tree_lo    := adrs_tree_lo a;
     adrs_type       := adrs_type a;
     adrs_ots        := adrs_ots a;
     adrs_chain      := adrs_chain a;
     adrs_hash       := adrs_hash a;
     adrs_keyAndMask := v |}.

(** Build an [adrs] from its 8 serialized words (as produced by
    external tooling that views the address as a [uint32_t[8]]).
    Entries past the 8th are ignored; missing entries default to 0. *)
Definition adrs_of_words (l : list word) : adrs :=
  {| adrs_layer      := nth 0 l 0;
     adrs_tree_hi    := nth 1 l 0;
     adrs_tree_lo    := nth 2 l 0;
     adrs_type       := nth 3 l 0;
     adrs_ots        := nth 4 l 0;
     adrs_chain      := nth 5 l 0;
     adrs_hash       := nth 6 l 0;
     adrs_keyAndMask := nth 7 l 0 |}.

(* ================================================================= *)
(** ** RFC Sec.2.4 -- [toByte(x, y)]: big-endian [y]-byte encoding of [x]. *)

Fixpoint toByte (x : Z) (y : nat) : list byte :=
  match y with
  | O    => []
  | S y' => toByte (x / 256) y' ++ [x mod 256]
  end.

(** Serialize an address to its 32-byte wire form: 8 words x 4 bytes. *)
Definition addr_bytes (a : adrs) : list byte :=
  toByte (adrs_layer a)      4 ++
  toByte (adrs_tree_hi a)    4 ++
  toByte (adrs_tree_lo a)    4 ++
  toByte (adrs_type a)       4 ++
  toByte (adrs_ots a)        4 ++
  toByte (adrs_chain a)      4 ++
  toByte (adrs_hash a)       4 ++
  toByte (adrs_keyAndMask a) 4.

(* ================================================================= *)
(** ** RFC Sec.5.1 -- keyed hashes built from SHA-256.

    [SHA256] is left abstract here; external tooling instantiates it. *)

Parameter SHA256 : list byte -> block.
Axiom SHA256_length   : forall m, length (SHA256 m) = n.
Axiom SHA256_byte_ok  : forall m, Forall byte_ok (SHA256 m).

Definition F (KEY M : block) : block :=
  SHA256 (toByte 0 n ++ KEY ++ M).

Definition PRF (KEY : block) (M : list byte) : block :=
  SHA256 (toByte 3 n ++ KEY ++ M).

Definition PRF_keygen (KEY : block) (M : list byte) : block :=
  SHA256 (toByte 4 n ++ KEY ++ M).

(* ================================================================= *)
(** ** RFC Sec.3.1.2 -- chaining function building blocks. *)

Definition xor (X Y : block) : block :=
  map (fun p => Z.lxor (fst p) (snd p)) (combine X Y).

(** One step of the chain: keyed hash [F] applied after XORing with
    the bitmask, both derived from [SEED] and [ADRS] via [PRF]. *)
Definition thash_f (X SEED : block) (ADRS : adrs) : block :=
  let KEY := PRF SEED (addr_bytes (setKeyAndMask ADRS 0)) in
  let BM  := PRF SEED (addr_bytes (setKeyAndMask ADRS 1)) in
  F KEY (xor X BM).

(** Algorithm 2 -- [chain(X, i, s, SEED, ADRS)].

    Iterates [thash_f] on [X] for [s] steps, with hash-address word
    set to [i], [i+1], ..., [i+s-1] in turn.  Callers in WOTS+ never
    pick [i + s > w - 1 = 15]. *)
Fixpoint chain (X : block) (i s : nat)
               (SEED : block) (ADRS : adrs) : block :=
  match s with
  | O    => X
  | S k  =>
      thash_f (chain X i k SEED ADRS) SEED
              (setHashAddress ADRS (Z.of_nat (i + k)))
  end.

(* ================================================================= *)
(** ** RFC Sec.2.6 Algorithm 1 -- [base_w] specialised to [w = 16].

    Splits each byte into its high and low nibble, then keeps the
    first [out_len] nibbles. *)

Definition base_w (X : list byte) (out_len : nat) : list nat :=
  firstn out_len
    (flat_map (fun b : byte => [Z.to_nat (b / 16); Z.to_nat (b mod 16)]) X).

(* ================================================================= *)
(** ** Pseudorandom per-chain secret key (XMSS-style [genSK]).

    [sk[i] = PRF_keygen(sk_seed, pub_seed || addr_bytes(ADRS'))], where
    [ADRS'] has chain address [i], hash address [0], keyAndMask [0]. *)

Definition genSK (i : nat) (sk_seed pub_seed : block) (ADRS : adrs) : block :=
  set ADRS := setChainAddress ADRS (Z.of_nat i);
  set ADRS := setHashAddress  ADRS 0;
  set ADRS := setKeyAndMask   ADRS 0;
  PRF_keygen sk_seed (pub_seed ++ addr_bytes ADRS).

(* ================================================================= *)
(** ** RFC Sec.3.1.5 -- message + checksum expansion.

    [expand_msg M] returns [len_1 + len_2 = len] base-[w] digits: the
    message digest split into [len_1] nibbles, followed by its
    checksum split into [len_2] nibbles. *)

Definition csum (msg : list nat) : nat :=
  list_sum (map (fun d => w_pred - d)%nat msg).

Definition expand_msg (M : block) : list nat :=
  let msg := base_w M len_1 in
  msg ++ base_w (toByte (Z.of_nat (csum msg) * 16) 2) len_2.

(* ================================================================= *)
(** ** RFC Sec.3.1 -- WOTS+ algorithms.

    The four definitions below mirror RFC 8391 Sec.3.1 pseudocode
    directly. *)

(** Algorithm 4 -- [WOTS_genPK].  [sk[i]] is derived on the fly from
    [sk_seed] via [genSK]. *)
Definition genPK (sk_seed pub_seed : block) (ADRS : adrs) : list block :=
  for i < len {{
    set ADRS := setChainAddress ADRS (Z.of_nat i);
    chain (genSK i sk_seed pub_seed ADRS) 0 w_pred pub_seed ADRS
  }}.

(** Algorithm 5 -- [WOTS_sign]. *)
Definition sign (M sk_seed pub_seed : block) (ADRS : adrs) : list block :=
  let msg := expand_msg M in
  for i < len {{
    set ADRS := setChainAddress ADRS (Z.of_nat i);
    chain (genSK i sk_seed pub_seed ADRS) 0 msg[i] pub_seed ADRS
  }}.

(** Algorithm 6 -- [WOTS_pkFromSig]. *)
Definition pkFromSig (M : block) (sig : list block)
                     (pub_seed : block) (ADRS : adrs) : list block :=
  let msg := expand_msg M in
  for i < len {{
    set ADRS := setChainAddress ADRS (Z.of_nat i);
    chain sig[i] msg[i] (w_pred - msg[i])%nat pub_seed ADRS
  }}.

(** Signature verification -- accept iff [pkFromSig] recovers [pk]. *)
Definition verify (pk sig : list block) (M pub_seed : block)
                  (ADRS : adrs) : bool :=
  if list_eq_dec (list_eq_dec Z.eq_dec) (pkFromSig M sig pub_seed ADRS) pk
  then true else false.
