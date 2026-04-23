(* Realization of the abstract [SHA256] parameter from the Rocq spec.
   Feeds each [int list] of bytes through Digestif and returns the 32
   output bytes as an [int list]. *)

let sha256 (input : int list) : int list =
  let n = List.length input in
  let buf = Bytes.create n in
  List.iteri (fun i b -> Bytes.set_uint8 buf i (b land 0xff)) input;
  let d = Digestif.SHA256.digest_bytes buf in
  let s = Digestif.SHA256.to_raw_string d in
  List.init 32 (fun i -> Char.code s.[i])
