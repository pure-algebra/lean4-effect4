(* check_vessel.ml -- the generated vessel module holds exactly the saved runs.

   What it is: for each replay.json named on the command line, in order, the module's program is
   the one Eff_wire decodes from programHex, and its requests, replies and exit are the ones the
   tagged JSON writes. Comparison is on Eff_types values. Depends on: effect4_eff, yojson, the
   generated Vessel_fixture.

   Run: ocamlfind ocamlopt -package zarith,yojson -I EFF_OBJS effect4_eff.cmxa vessel_fixture.ml
        check_vessel.ml -o check_vessel && ./check_vessel REPLAY.json... *)

open Vessel_fixture

let rec value (j : Yojson.Safe.t) : Eff_types.val_ =
  match j with
  | `List [ `String "nat"; `String n ] -> Eff_types.Val_nat (int_of_string n)
  | `List [ `String "str"; `String s ] -> Eff_types.Val_str s
  | `List [ `String "bool"; `Bool b ] -> Eff_types.Val_bool b
  | `List [ `String "unit" ] -> Eff_types.Val_unit
  | `List [ `String "list"; `List xs ] -> Eff_types.Val_list (List.map value xs)
  | `List [ `String "ctor"; `Int i; `List xs ] -> Eff_types.Val_ctor (i, List.map value xs)
  | _ -> failwith ("no value: " ^ Yojson.Safe.to_string j)

let outcome (j : Yojson.Safe.t) : outcome =
  match j with
  | `Assoc [ ("success", v) ] -> Succeeded (value v)
  | `Assoc [ ("failure", `List [ `String t; `String m ]) ] -> Failed (t, m)
  | _ -> failwith ("no outcome: " ^ Yojson.Safe.to_string j)

let bytes h = String.init (String.length h / 2) (fun i -> Char.chr (int_of_string ("0x" ^ String.sub h (2 * i) 2)))

let () =
  let runs =
    [ (program_0, requests_0, replies_0, exit_0); (program_1, requests_1, replies_1, exit_1);
      (program_2, requests_2, replies_2, exit_2); (program_3, requests_3, replies_3, exit_3);
      (program_4, requests_4, replies_4, exit_4); (program_5, requests_5, replies_5, exit_5) ]
  in
  let paths = List.tl (Array.to_list Sys.argv) in
  let ok = ref (List.length paths = count && count = List.length runs) in
  List.iteri
    (fun i path ->
      let j = Yojson.Safe.from_file path in
      let field k = Yojson.Safe.Util.member k j in
      let program, requests, replies, exit_ = List.nth runs i in
      let p = Eff_wire.decode_program_exact (bytes (Yojson.Safe.Util.to_string (field "programHex"))) = Some program in
      let rs = Yojson.Safe.Util.to_list (field "replies") in
      let q = List.map (fun r -> value (Yojson.Safe.Util.member "request" r)) rs = requests in
      let a = List.map (fun r -> outcome (Yojson.Safe.Util.member "reply" r)) rs = replies in
      let e = outcome (field "exit") = exit_ in
      Printf.printf "%s run %d (%s): program %b, requests %b, replies %b, exit %b\n"
        (if p && q && a && e then "PASS" else "FAIL") i (Filename.basename (Filename.dirname path)) p q a e;
      if not (p && q && a && e) then ok := false)
    paths;
  exit (if !ok then 0 else 1)
