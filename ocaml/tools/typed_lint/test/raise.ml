(* Typed_lint's rule-6 fixture: each line marked "report" is a finding of --raises; the others
   must pass. No rule-7 finding, so the run exits 0. Represents no Effect4 program. *)
let parse s = if String.equal s "" then failwith "empty" else s (* report *)
let parse_exn s = if String.equal s "" then failwith "empty" else s
let outer_exn () = let go () = invalid_arg "inner" in go ()
let caught () = try raise Exit with Exit -> ()
let matched () = match raise Not_found with exception Not_found -> 0 | n -> n
let rethrow f = try f () with e -> raise e (* report: the handler is not guarded *)
let () = if Sys.word_size < 0 then raise_notrace Exit (* report: the top level *)
