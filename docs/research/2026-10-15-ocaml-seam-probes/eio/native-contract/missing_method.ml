(* Expected compiler refusal: a native SOURCE dictionary needs read_methods. *)
module Missing = struct
  type t = unit
  let single_read () _ = raise End_of_file
end
let _ = Eio.Flow.Pi.source (module Missing)
