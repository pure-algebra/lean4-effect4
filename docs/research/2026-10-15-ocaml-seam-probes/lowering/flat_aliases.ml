(* Compiles against an isolated copy of the current generated Eff_types module.
   This witnesses OCaml construction only, before an engine admission check. *)
let negative_name : Eff_types.service_name = -1
let negative_type_code : Eff_types.service_type_code = negative_name
let negative_natural_literal : Eff_types.lit = Eff_types.Lit_nat (-1)

let () =
  assert (negative_name = -1);
  assert (negative_type_code = -1);
  assert (negative_natural_literal = Eff_types.Lit_nat (-1));
  print_endline "flat-aliases: compiler accepts negative naturals and mixed name domains"
