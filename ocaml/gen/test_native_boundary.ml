(* S0 finite generated-runtime controls.
   Depends on the sealed Effect4_gen.Api_gen interface.
   Tested: lawful ask/learn/hit/bind, full admission/open/save/restore, both budgets,
   repeated-field refusal, and record-version refusal. No native proof is claimed. *)
open Eff_types
module A = Effect4_gen.Api_gen

let check name condition =
  if not condition then failwith name;
  Printf.printf "PASS %s\n" name
;;

let get = function
  | Ok value -> value
  | Error _ -> failwith "unexpected refusal"
;;

let refused = function
  | Error _ -> true
  | Ok _ -> false
;;

let program : NativeOp.t Eff.t = Eff.Succeed (Term.Lit (Lit.Nat 7))

let malformed : NativeOp.t Eff.t =
  Eff.Succeed
    (Term.Record
       ( [ "x", (false, Ty.Nat); "x", (true, Ty.String) ]
       , [ "x" ]
       , Terms.Cons (Term.Lit (Lit.Nat 7), Terms.Nil) ))
;;

let app : A.sig_app = { rows = []; services = []; types = [] }
let budget : A.budget = { fuel = 37; compile_fuel = 53 }

type public_memo_alias = A.memo

let lawful_alias : public_memo_alias = A.program_check_memo_empty

let () =
  let input = A.CheckInput_module (app, [], program) in
  let checked = A.program_check_checked_ask A.program_check_oracle_uncached input in
  let memo = A.program_check_memo_learn lawful_alias checked in
  let rule =
    A.program_check_hit_rule_or_
      A.program_check_hit_rule_exact
      A.program_check_hit_rule_exact
  in
  let answer =
    A.program_check_checked_ask (A.program_check_memo_oracle memo rule) input
  in
  let bound = A.program_check_checked_bind' answer A.program_check_checked_pure' in
  check
    "ask-learn-hit-bind-readVerdict"
    (Result.is_ok (A.program_check_checked_read_verdict bound).result);
  let built = get (A.api_built_of_sketch app { program; holes = [] }) in
  let live = A.live_open_ built "seams-s0" budget "test" in
  let record = A.live_record_save live in
  let restored = A.live_record_save (get (A.live_record_restore record)) in
  check
    "full-admission-open-save-restore"
    (restored.session = "seams-s0" && restored.binding = "test");
  check "both-budgets" (restored.budget.fuel = 37 && restored.budget.compile_fuel = 53);
  check
    "duplicate-field-admission-refused"
    (refused (A.api_built_of_sketch app { program = malformed; holes = [] }));
  check
    "duplicate-field-restore-refused"
    (refused (A.live_record_restore { record with program = malformed }));
  let unnamed =
    get (A.live_record_restore { record with session = ""; row_names = [ "stored", 9 ] })
  in
  let retained = A.live_record_save unnamed in
  check
    "restore-stored-names-and-empty-session"
    (retained.session = "" && retained.row_names = [ "stored", 9 ]);
  check
    "unadmitted-call-refused"
    (refused
       (A.api_built_of_sketch
          app
          { program = Eff.Perform (NativeOp.External 0, Term.Lit Lit.Unit); holes = [] }));
  check
    "record-version-refused"
    (refused (A.live_record_restore { record with version = 2 }))
;;
