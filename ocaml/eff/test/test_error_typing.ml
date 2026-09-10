(* DI-62 decision-checker controls, independent of Lean's emitted verdicts.
   Tested: all three failure forms accept represented errors and refuse unsupported
   Boolean, handle, product, and union columns. This tests admission, not execution.
   Depends on Eff_types and the handwritten Eff_typing checker. *)
open Eff_types

let str s = Term_lit (Lit_str s)
let nat n = Term_lit (Lit_nat n)
let boolean = Term_lit (Lit_bool true)
let pair a b = Term_app ("pair", Terms_cons (a, Terms_cons (b, Terms_nil)))

let cases =
  [ ("fail text", [], Eff_fail (str "lost"), true)
  ; ("yield text", [], Eff_yieldError (str "lost"), true)
  ; ("cause text", [], Eff_failCause (Cause_term_fail (str "lost")), true)
  ; ("fail nat", [], Eff_fail (nat 1), true)
  ; ("fail pair", [], Eff_fail (pair (str "A") (str "message")), true)
  ; ("fail bool", [], Eff_fail boolean, false)
  ; ("yield bool", [], Eff_yieldError boolean, false)
  ; ("cause bool", [], Eff_failCause (Cause_term_fail boolean), false)
  ; ("one bad cause reason", [],
      Eff_failCause (Cause_term_both (Cause_term_fail (nat 1), Cause_term_fail boolean)), false)
  ; ("wrong pair column", [], Eff_fail (pair (str "A") (nat 1)), false)
  ; ("handle error", [Ty_handle "Scope.Scope"], Eff_fail (Term_var 0), false)
  ; ("supported union", [Ty_union (Ty_nat, Ty_string)], Eff_fail (Term_var 0), true)
  ; ("unsupported union", [Ty_union (Ty_nat, Ty_bool)], Eff_fail (Term_var 0), false)
  ; ("empty error column", [Ty_never], Eff_fail (Term_var 0), true)
  ]

let () =
  List.iter
    (fun (name, env, program, expected) ->
      let admitted = match Eff_typing.check_eff env program with Ok _ -> true | Error _ -> false in
      if admitted <> expected then failwith ("error admission disagrees: " ^ name))
    cases;
  Printf.printf "PASS: %d independent error-admission controls\n" (List.length cases)
