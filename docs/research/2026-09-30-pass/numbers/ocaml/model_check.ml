(* Numbers seat, probe 7: the Lean OCaml model against the generated engine.

   Reads a vector file (argv 1; ml-vectors.txt, or the red control exact-vectors.txt, both written by ../Models.lean: `op a b model` per line, a and b any
   63-bit ints) and evaluates each pair with the GENERATED atom evaluator,
   `Api_engine_inst.program_native_atom_eval` (ocaml/engine/api_engine.ml:2969), i.e. the
   code the engine runs for `add`, `sub`, `mul`, `div`, `mod`, `lt`. Prints the number of
   lines and of differences per operation. Depends on effect4_engine. Writes nothing. *)

module I = Effect4_engine.Api_engine_inst

let atom = function
  | "add" -> I.NativeAtom_add
  | "sub" -> I.NativeAtom_natSub
  | "mul" -> I.NativeAtom_mul
  | "div" -> I.NativeAtom_natDiv
  | "mod" -> I.NativeAtom_natMod
  | "lt" -> I.NativeAtom_lt
  | op -> failwith ("unknown op " ^ op)

let show = function
  | Some (I.Val_nat n) -> string_of_int n
  | Some (I.Val_bool b) -> string_of_bool b
  | Some _ -> "other"
  | None -> "none"

let () =
  let path = Sys.argv.(1) in
  let ic = open_in path in
  let counts = Hashtbl.create 8 in
  let first = ref [] in
  let total = ref 0 in
  (try
     while true do
       let line = input_line ic in
       if String.length line > 0 then begin
         incr total;
         match String.split_on_char ' ' line with
         | [ op; a; b; m ] ->
           let got = show (I.program_native_atom_eval (atom op)
                             [ I.Val_nat (int_of_string a); I.Val_nat (int_of_string b) ]) in
           let n, bad = try Hashtbl.find counts op with Not_found -> (0, 0) in
           let differs = got <> m in
           Hashtbl.replace counts op (n + 1, if differs then bad + 1 else bad);
           if differs && List.length !first < 5 then first := (line ^ " ocaml=" ^ got) :: !first
         | _ -> failwith ("bad line " ^ line)
       end
     done
   with End_of_file -> close_in ic);
  Printf.printf "vectors %d\n" !total;
  List.iter (fun op ->
      match Hashtbl.find_opt counts op with
      | Some (n, bad) -> Printf.printf "  %-4s %d lines, %d differ\n" op n bad
      | None -> ())
    [ "add"; "sub"; "mul"; "div"; "mod"; "lt" ];
  List.iter (fun s -> Printf.printf "  first difference: %s\n" s) (List.rev !first)
