(* DI-63 scoped typing controls, independent of regenerated corpus expectations.
   Depends on Eff_typing, Eff_native and the generated Eff_types carrier.
   Properties tested: only Scope is removed; A/E and refusal are retained; nested
   discharge is idempotent; a same-code/different-name key survives. No execution claim. *)
open Eff_types

let checks = ref 0
let check name holds =
  incr checks;
  if not holds then failwith ("scoped typing: " ^ name)

let expect_type name program answer error requires =
  check name (match Eff_typing.type_of program with
    | Error _ -> false
    | Ok t -> t.eff_ty_answer = answer && t.eff_ty_error = error && t.eff_ty_requires = requires)

let () =
  let scope = Eff_native.scope_key in
  let other : service_key =
    { service_key_name = { service_name_value = 4 };
      service_key_service = { service_type_code_value = 4 } } in
  let same_code_other_name : service_key = { other with service_key_service = scope.service_key_service } in
  let acquire = Eff_acquireRelease
    (Eff_succeed (Term_lit (Lit_nat 7)), Eff_succeed (Term_lit Lit_unit)) in
  let mixed = Eff_bind (acquire, Eff_service other) in
  expect_type "unscoped acquisition retains Scope" acquire Ty_nat Ty_never [scope];
  expect_type "scope discharges acquisition" (Eff_scoped acquire) Ty_nat Ty_never [];
  expect_type "unrelated key retained" (Eff_scoped mixed) Ty_nat Ty_never [other];
  check "nested scope result unchanged"
    (Eff_typing.type_of (Eff_scoped (Eff_scoped mixed)) = Eff_typing.type_of (Eff_scoped mixed));
  expect_type "error retained" (Eff_scoped (Eff_fail (Term_lit (Lit_nat 9)))) Ty_never Ty_nat [];
  let ill = Eff_succeed (Term_var 0) in
  check "ill-typed body remains the same refusal"
    (match Eff_typing.type_of ill, Eff_typing.type_of (Eff_scoped ill) with
     | Error before, Error after -> before = after
     | _ -> false);
  check "nested ill-typed scope remains refused" (not (Eff_typing.well_typed (Eff_scoped (Eff_scoped ill))));
  let t : eff_ty = { eff_ty_answer = Ty_nat; eff_ty_error = Ty_string;
    eff_ty_requires = Eff_typing.req_of_list [scope; same_code_other_name] } in
  check "same service code different name survives"
    (Eff_typing.body_requires t = [same_code_other_name]);
  check "row discharge idempotent"
    (Eff_typing.body_requires { t with eff_ty_requires = Eff_typing.body_requires t } = Eff_typing.body_requires t);
  Printf.printf "test_scoped_typing: %d checks passed\n%!" !checks
