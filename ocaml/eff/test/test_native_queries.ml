(* Native query typing controls over the actual emitted Eff_native module.
   Depends on generated Eff_types/Eff_native and handwritten Eff_typing.
   Tested: both advertised Cause/Exit input families, result error payloads,
   missing/extra arguments, invalid input families, and retained ordinary atoms.
   These finite target checks do not assert execution or universal equivalence. *)
open Eff_types

let cases =
  [ ("causeIsFail", [Ty_causeOf Ty_string], Some Ty_bool)
  ; ("causeIsFail", [Ty_exitOf (Ty_nat, Ty_string)], Some Ty_bool)
  ; ("causeIsDie", [Ty_causeOf Ty_never], Some Ty_bool)
  ; ("causeIsDie", [Ty_exitOf (Ty_nat, Ty_never)], Some Ty_bool)
  ; ("causeIsInterrupt", [Ty_causeOf Ty_never], Some Ty_bool)
  ; ("causeIsInterrupt", [Ty_exitOf (Ty_nat, Ty_never)], Some Ty_bool)
  ; ("causeError", [Ty_causeOf Ty_string], Some (Ty_option Ty_string))
  ; ("causeError", [Ty_exitOf (Ty_nat, Ty_prod (Ty_string, Ty_string))],
      Some (Ty_option (Ty_prod (Ty_string, Ty_string))))
  ; ("causeError", [Ty_causeOf Ty_never], Some (Ty_option Ty_never))
  ; ("causeIsFail", [Ty_nat], None)
  ; ("causeIsDie", [], None)
  ; ("causeIsInterrupt", [Ty_causeOf Ty_never; Ty_causeOf Ty_never], None)
  ; ("causeError", [Ty_string], None)
  ; ("causeError", [Ty_list (Ty_causeOf Ty_nat)], None)
  ; ("causeError", [], None)
  ; ("eq", [Ty_string; Ty_string], Some Ty_bool)
  ; ("eq", [Ty_nat; Ty_nat], Some Ty_bool)
  ; ("eq", [Ty_string; Ty_nat], None)
  ; ("eq", [Ty_bool; Ty_bool], None)
  ; ("or", [Ty_bool; Ty_bool], Some Ty_bool)
  ; ("and", [Ty_bool; Ty_bool], Some Ty_bool)
  ; ("or", [Ty_bool], None)
  ; ("and", [Ty_nat; Ty_bool], None)
  ; ("succ", [Ty_nat], Some Ty_nat)
  ; ("strings", [], Some (Ty_list Ty_string))
  ; ("unregisteredQuery", [Ty_causeOf Ty_string], None)
  ]

let () =
  List.iter
    (fun (name, args, expected) ->
      if Eff_native.atom_ty name args <> expected then
        failwith ("native query typing disagrees: " ^ name))
    cases;
  Printf.printf "PASS: %d independent emitted native-query controls\n" (List.length cases)
