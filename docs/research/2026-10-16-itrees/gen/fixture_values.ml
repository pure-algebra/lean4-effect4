(* fixture_values.ml -- the to-do lane's fixture as OCaml values, for the toplevel to print.

   What it is: a toplevel script. It reads ocaml/engine/test/todo/todo-host.txt (Lean's bytes),
   decodes each request's program with Eff_wire and each recorded result with Eff_val, and binds
   for each request i: `program_i` (the program), `calls_i` (each host call's row, request and
   answer, as Lean's run recorded them, under the reference host) and `exit_i` (the root's exit
   image), and the same for the broken host (`bcalls_i`, `bexit_i`). The toplevel prints each
   binding as OCaml source; fixture_to_ml.py wraps the printed values into a module.
   Depends on: effect4_eff (Eff_wire, Eff_val, Eff_types), loaded by the toplevel.

   Properties:
   X1  Each value is decoded exactly from Lean's bytes: a block that does not read stops the
       script.                                                              by construction
   X2  The printed module re-encodes to the same bytes (check_fixture.ml).  tested *)

#print_depth 100000000;;
#print_length 100000000;;

let fixture = Sys.getenv "TODO_FIXTURE";;

let lines key =
  let ic = open_in fixture in
  let n = String.length key + 1 in
  let rec go acc =
    match input_line ic with
    | exception End_of_file -> close_in ic; List.rev acc
    | l when String.length l > n && String.sub l 0 n = key ^ " " ->
      go (String.sub l n (String.length l - n) :: acc)
    | _ -> go acc
  in
  go [];;

let bytes hex = String.init (String.length hex / 2) (fun i -> Char.chr (int_of_string ("0x" ^ String.sub hex (2 * i) 2)));;
let exactly what f hex = match f (bytes hex) with Some x -> x | None -> failwith ("does not read: " ^ what);;

(* A result is [calls, exit, state]; a call is [row, request, completion]; a completion is
   [0, exit image] (`Completion.ofExit`). *)
let split_result v =
  match v with
  | Eff_types.Val_list [ Eff_types.Val_list calls; exit_; _state ] ->
    ( List.map
        (function
          | Eff_types.Val_list [ Eff_types.Val_nat row; request; Eff_types.Val_list [ Eff_types.Val_nat 0; answer ] ] ->
            (row, request, answer)
          | _ -> failwith "a call is not a row, a request and an exit")
        calls,
      exit_ )
  | _ -> failwith "a result is not calls, an exit and a state";;

let programs = List.map (exactly "a program" Eff_wire.decode_program_exact) (lines "program");;
let results = List.map (fun h -> split_result (exactly "a result" Eff_val.decode_exact h)) (lines "result");;
let brokens = List.map (fun h -> split_result (exactly "a result" Eff_val.decode_exact h)) (lines "broken");;
let entries = lines "request";;
