(* Clean interface to the WOTS+ spec extracted from Rocq.
   All inputs/outputs are [bytes]; the extracted [int list] plumbing
   is hidden. *)

type addr = int array  (** 8 × uint32, big-endian within each word. *)

val pkgen    : sk_seed:bytes -> pub_seed:bytes -> addr:addr -> bytes
val sign     : msg:bytes -> sk_seed:bytes -> pub_seed:bytes
            -> addr:addr -> bytes
val verify   : pk:bytes -> signat:bytes -> msg:bytes
            -> pub_seed:bytes -> addr:addr -> bool

(** Sizes (bytes). *)
val block_bytes : int  (** 32 *)
val pk_bytes    : int  (** 2144 *)
val sig_bytes   : int  (** 2144 *)
val msg_bytes   : int  (** 32 *)
val seed_bytes  : int  (** 32 *)
