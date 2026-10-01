(* Seat Q: run the LCNF-lowered canon, paired value sort and wave sub on fixed vectors; the
   expected lines are printed by the same vectors in Lean (Q/probes/Q5/LowerVectors.lean). *)
open Canon_gen
let b x = if x then "true" else "false"
let rec vs = function
  | Val_nat n -> string_of_int n
  | Val_str s -> "\"" ^ s ^ "\""
  | Val_list xs -> "[" ^ String.concat ", " (List.map vs xs) ^ "]"
  | Val_ctor (i, xs) -> "ctor " ^ string_of_int i ^ " [" ^ String.concat ", " (List.map vs xs) ^ "]"
  | _ -> "?"
let () =
  let (ns, xs) = probe_q5_canon_record ["\xc3\xa9"; "z"; "a"] [Val_nat 1; Val_nat 2; Val_nat 3] in
  print_endline ("canonRecord: " ^ String.concat "," ns ^ " / " ^ String.concat "," (List.map vs xs));
  let fs = probe_q5_canon_fields [("b", (Ty_nat, false)); ("a", (Ty_string, true)); ("b", (Ty_int, true))] in
  print_endline ("canonFields: " ^ String.concat "," (List.map (fun (n, (t, o)) -> n ^ ":" ^ (match t with Ty_nat -> "nat" | Ty_string -> "string" | Ty_int -> "int" | _ -> "?") ^ ":" ^ b o) fs));
  (match probe_q5_canon_record_val (Val_ctor (0, [Val_list [Val_str "y"; Val_str "x"]; Val_list [Val_nat 1; Val_nat 2]])) with
   | Some v -> print_endline ("canonRecordVal: " ^ vs v) | None -> print_endline "canonRecordVal: none");
  let s a c = b (probe_qw_ty_sub a c) in
  print_endline ("sub: " ^ String.concat " " [
    s Ty_nat Ty_number; s Ty_number Ty_nat; s Ty_undefined Ty_unit; s Ty_nat Ty_bytes;
    s (Ty_record [("a", (Ty_nat, false))]) (Ty_record [("a", (Ty_int, false))]);
    s (Ty_record [("a", (Ty_nat, false))]) (Ty_record [("a", (Ty_int, true))]);
    s (Ty_record [("b", (Ty_nat, false)); ("a", (Ty_unit, false))]) (Ty_record [("a", (Ty_unit, false)); ("b", (Ty_number, false))]);
    s (Ty_tuple [Ty_nat]) (Ty_tuple [Ty_int]); s (Ty_tuple [Ty_nat]) (Ty_tuple [Ty_nat; Ty_nat]);
    s (Ty_map (Ty_nat, Ty_nat)) (Ty_map (Ty_int, Ty_nat)); s (Ty_map (Ty_nat, Ty_nat)) (Ty_map (Ty_nat, Ty_int));
    s (Ty_app ("Effect.Effect", [Ty_nat; Ty_string; Ty_unit])) (Ty_app ("Effect.Effect", [Ty_int; Ty_string; Ty_unit]));
    s (Ty_app ("Ref.Ref", [Ty_nat])) (Ty_app ("Ref.Ref", [Ty_int]));
    s (Ty_app ("Nominal.Unknown", [Ty_nat])) (Ty_app ("Nominal.Unknown", [Ty_int]));
    s (Ty_app ("Ref.Ref", [Ty_nat])) (Ty_app ("Fiber.Fiber", [Ty_nat]))])

(* seat Q: the text tyO and tyOcaml print for one wave sample, type-checked against the lowered ty *)
let _sample_tyO : ty = (Ty_record [("b", ((Ty_tuple [Ty_nat; Ty_null]), true)); ("a", ((Ty_app ("Ref.Ref", [(Ty_map (Ty_string, Ty_number))])), false))])
let _sample_tyOcaml : ty = Ty_record ([("b", (Ty_tuple ([Ty_nat; Ty_null]), true)); ("a", (Ty_app ("Ref.Ref", [Ty_map (Ty_string, Ty_number)]), false))])
