(* Hand-written OCaml wrapper around the Rocq-extracted WOTS+.
   Bridges OCaml [bytes] with the extracted flat [int list] form. *)

module E = Wots_extracted

type addr = int array

let block_bytes = 32
let pk_bytes    = 2144
let sig_bytes   = 2144
let msg_bytes   = 32
let seed_bytes  = 32

(* bytes ↔ int list *)

let bytes_to_list (b : bytes) : int list =
  List.init (Bytes.length b) (fun i -> Bytes.get_uint8 b i)

(* [addr : int array] of length 8 — the 8 × 32-bit words in C layout —
   into the extracted [adrs] record, via [adrs_of_words]. *)
let adrs_of_array (a : addr) : E.adrs =
  E.adrs_of_words (Array.to_list a)

let bytes_of_block_list (bs : E.block list) (total : int) : bytes =
  let out = Bytes.create total in
  let k = ref 0 in
  List.iter (fun blk ->
    List.iter (fun v ->
      if !k < total then
        (Bytes.set_uint8 out !k (v land 0xff); incr k)) blk) bs;
  out

let split_blocks (b : bytes) : E.block list =
  let n = Bytes.length b / block_bytes in
  List.init n (fun i ->
    List.init block_bytes (fun j ->
      Bytes.get_uint8 b (i * block_bytes + j)))

(* Public API *)

let pkgen ~sk_seed ~pub_seed ~addr =
  bytes_of_block_list
    (E.genPK (bytes_to_list sk_seed) (bytes_to_list pub_seed)
             (adrs_of_array addr))
    pk_bytes

let sign ~msg ~sk_seed ~pub_seed ~addr =
  bytes_of_block_list
    (E.sign (bytes_to_list msg) (bytes_to_list sk_seed)
            (bytes_to_list pub_seed) (adrs_of_array addr))
    sig_bytes

let pk_from_sig ~signat ~msg ~pub_seed ~addr =
  bytes_of_block_list
    (E.pkFromSig (bytes_to_list msg) (split_blocks signat)
                 (bytes_to_list pub_seed) (adrs_of_array addr))
    pk_bytes

let verify ~pk ~signat ~msg ~pub_seed ~addr =
  E.verify (split_blocks pk) (split_blocks signat)
           (bytes_to_list msg) (bytes_to_list pub_seed)
           (adrs_of_array addr)
