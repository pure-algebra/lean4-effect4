(* check_fixture.ml -- the printed fixture module re-encodes to Lean's bytes.

   What it is: for each request, the module's program encoded by Eff_wire is the fixture's
   `program` line, byte for byte; and its calls and exit, packed back as Lean's result shape with
   the fixture's state, are the fixture's `result` line (and `broken` for the broken host).
   Depends on: effect4_eff, the generated Todo_fixture.

   Run: ocamlfind ocamlopt -package zarith -I EFF_OBJS -I . effect4_eff.cmxa todo_fixture.ml
        check_fixture.ml -o check && TODO_FIXTURE=... ./check *)

let hex s = String.concat "" (List.init (String.length s) (fun i -> Printf.sprintf "%02x" (Char.code s.[i])))

let lines key =
  let ic = open_in (Sys.getenv "TODO_FIXTURE") in
  let n = String.length key + 1 in
  let rec go acc =
    match input_line ic with
    | exception End_of_file -> close_in ic; List.rev acc
    | l when String.length l > n && String.sub l 0 n = key ^ " " -> go (String.sub l n (String.length l - n) :: acc)
    | _ -> go acc
  in
  go []

let bytes h = String.init (String.length h / 2) (fun i -> Char.chr (int_of_string ("0x" ^ String.sub h (2 * i) 2)))

let pack calls exit_ state =
  Eff_types.Val_list
    [ Eff_types.Val_list
        (List.map
           (fun (row, request, answer) ->
             Eff_types.Val_list [ Eff_types.Val_nat row; request; Eff_types.Val_list [ Eff_types.Val_nat 0; answer ] ])
           calls);
      exit_; state ]

let () =
  let progs = lines "program" and results = lines "result" and brokens = lines "broken" in
  let states =
    List.map
      (fun h ->
        match Eff_val.decode_exact (bytes h) with
        | Some (Eff_types.Val_list [ _; _; s ]) -> s
        | _ -> failwith "result shape")
      results
  in
  let bstates =
    List.map
      (fun h ->
        match Eff_val.decode_exact (bytes h) with
        | Some (Eff_types.Val_list [ _; _; s ]) -> s
        | _ -> failwith "result shape")
      brokens
  in
  let ok = ref true in
  let get = Todo_fixture.(fun i -> List.nth [ program_0; program_1; program_2; program_3; program_4; program_5; program_6 ] i) in
  let calls = Todo_fixture.[ (calls_0, exit_0); (calls_1, exit_1); (calls_2, exit_2); (calls_3, exit_3); (calls_4, exit_4); (calls_5, exit_5); (calls_6, exit_6) ] in
  let bcalls = Todo_fixture.[ (bcalls_0, bexit_0); (bcalls_1, bexit_1); (bcalls_2, bexit_2); (bcalls_3, bexit_3); (bcalls_4, bexit_4); (bcalls_5, bexit_5); (bcalls_6, bexit_6) ] in
  List.iteri
    (fun i p ->
      let same = hex (Eff_wire.encode_program (get i)) = p in
      let c, e = List.nth calls i and bc, be = List.nth bcalls i in
      let r = hex (Eff_val.to_bytes (pack c e (List.nth states i))) = List.nth results i in
      let b = hex (Eff_val.to_bytes (pack bc be (List.nth bstates i))) = List.nth brokens i in
      Printf.printf "%s request %d: program %b, result %b, broken %b\n" (if same && r && b then "PASS" else "FAIL") i same r b;
      if not (same && r && b) then ok := false)
    progs;
  if Todo_fixture.count <> List.length progs then (print_endline "FAIL count"; ok := false);
  exit (if !ok then 0 else 1)
