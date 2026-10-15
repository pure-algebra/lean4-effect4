(* Expected compiler refusal: a readable flow does not expose Lookup. *)
let () = ignore (Resource_probe.lookup (Eio.Flow.string_source "x") 1)
