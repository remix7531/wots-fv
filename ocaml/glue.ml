(* Registers named OCaml callbacks for the C bridge (ocaml/wrap.c).
   No exported functions — the top-level [let ()] runs once at runtime
   init (after caml_startup) and wires up the names. *)

let () =
  Callback.register "wots_ocaml_pkgen"
    (fun sk_seed pub_seed addr -> Wots.pkgen ~sk_seed ~pub_seed ~addr);
  Callback.register "wots_ocaml_sign"
    (fun msg sk_seed pub_seed addr ->
       Wots.sign ~msg ~sk_seed ~pub_seed ~addr);
  Callback.register "wots_ocaml_pk_from_sig"
    (fun signat msg pub_seed addr ->
       Wots.pk_from_sig ~signat ~msg ~pub_seed ~addr);
  Callback.register "wots_ocaml_verify"
    (fun pk signat msg pub_seed addr ->
       Wots.verify ~pk ~signat ~msg ~pub_seed ~addr)
