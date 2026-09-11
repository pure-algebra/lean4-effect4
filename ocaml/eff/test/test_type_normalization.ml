(* DI-53 independent controls: deep normalization and its precise new checker admissions.
   Universal laws are Lean obligations; this is a bounded mirror battery. No machine-value
   snapshot interpreter exists on this OCaml face, so those controls belong to Lean. *)
open Eff_types

let raw = Ty_union (Ty_bool, Ty_union (Ty_never, Ty_union (Ty_nat, Ty_bool)))
let canon = Ty_union (Ty_nat, Ty_bool)
let unary = [ (fun x -> Ty_option x); (fun x -> Ty_list x); (fun x -> Ty_causeOf x) ]
let binary =
  [ (fun a b -> Ty_except (a,b))
  ; (fun a b -> Ty_exitOf (a,b)); (fun a b -> Ty_fiberOf (a,b)) ]

let checks = ref 0

let check name expected actual =
  incr checks;
  if actual <> expected then failwith ("normalization control failed: " ^ name)

let admitted env program = match Eff_typing.check_eff env program with Ok _ -> true | Error _ -> false

let () =
  let open Eff_typing in
  check "top union" canon (normalize raw);
  List.iter (fun f -> check "unary child" (f canon) (normalize (f raw))) unary;
  List.iter (fun f -> check "binary children" (f canon canon) (normalize (f raw raw))) binary;
  check "product distribution"
    (Ty_union (Ty_prod (Ty_nat, Ty_nat), Ty_union (Ty_prod (Ty_nat, Ty_bool),
      Ty_union (Ty_prod (Ty_bool, Ty_nat), Ty_prod (Ty_bool, Ty_bool)))))
    (normalize (Ty_prod (raw, raw)));
  check "literal absorption" Ty_string (join (Ty_lit "A") Ty_string);
  check "product absorption" (Ty_prod (Ty_string, Ty_string))
    (join (Ty_prod (Ty_lit "A", Ty_string)) (Ty_prod (Ty_string, Ty_string)));
  check "list retains its union" (Ty_list (Ty_union (Ty_nat, Ty_string)))
    (normalize (Ty_list (Ty_union (Ty_nat, Ty_string))));
  check "utf8 order" (Ty_union (Ty_handle "A", Ty_handle "é"))
    (normalize (Ty_union (Ty_handle "é", Ty_handle "A")));
  check "literal utf8 key" [15; 195; 169] (key (Ty_lit "é"));
  check "literal union order" (Ty_union (Ty_lit "A", Ty_lit "é"))
    (normalize (Ty_union (Ty_lit "é", Ty_union (Ty_lit "A", Ty_lit "é"))));
  check "empty union" Ty_never (normalize (Ty_union (Ty_never, Ty_never)));
  check "deep duplicate" (Ty_option canon)
    (normalize (Ty_union (Ty_option raw, Ty_option canon)));
  let samples = [Ty_never; Ty_nat; Ty_bool; Ty_string; raw; Ty_option raw; Ty_list raw;
    Ty_prod (raw, raw); Ty_union (Ty_handle "A", Ty_handle "é")] in
  List.iter (fun a ->
    check "idempotent" (normalize a) (normalize (normalize a));
    check "self" (normalize a) (join a a);
    check "unit" (normalize a) (join Ty_never a);
    List.iter (fun b ->
      check "commutative" (join a b) (join b a);
      List.iter (fun c -> check "associative" (join (join a b) c) (join a (join b c))) samples
    ) samples
  ) samples;
  let hidden_pair = Ty_prod (Ty_union (Ty_string, Ty_never), Ty_string) in
  check "raw support is unchanged" false (supported_error_ty hidden_pair);
  check "canonical support" true (admitted_error_ty hidden_pair);
  List.iter (fun program -> check "normalized failure admission" true (admitted [hidden_pair] program))
    [Eff_fail (Term_var 0); Eff_yieldError (Term_var 0); Eff_failCause (Cause_term_fail (Term_var 0))];
  check "bad pair remains refused" false
    (admitted [Ty_prod (Ty_union (Ty_string, Ty_bool), Ty_string)] (Eff_fail (Term_var 0)));
  check "perform request" true
    (admitted [Ty_union (Ty_nat, Ty_never)] (Eff_perform (Native_op_refMake, Term_var 0)));
  check "callback request" true
    (admitted [Ty_union (Eff_native.deferred_ty, Ty_never)]
      (Eff_callback (Native_op_deferredAwait, Term_var 0)));
  check "wrong request" false
    (admitted [Ty_union (Ty_bool, Ty_never)] (Eff_perform (Native_op_refMake, Term_var 0)));
  check "wrong callback kind" false
    (admitted [Ty_nat] (Eff_callback (Native_op_refMake, Term_var 0)));
  check "provided service" true
    (admitted [Ty_union (Eff_native.scope_ty, Ty_never)]
      (Eff_provideService (Eff_native.scope_key, Term_var 0, Eff_service Eff_native.scope_key)));
  Printf.printf "PASS: %d normalization/algebra/admission controls over a %d-type grid\n"
    !checks (List.length samples)
