(* api_check.ml -- the G0 smoke: the GENERATED engine (api_gen.ml, rooted at
   `Effect4.Api.run` / `Effect4.Api.replay`) actually runs a program.

   The programs are the byte-pinned corpus of src/Effect4/Program/Wire.lean:74-106, spelled
   in the generated `eff` type:
     p42    = succeed (lit (nat 42))
     pFork  = bind (withFiber (fork (bind (yieldNow 0) (succeed (lit (nat 7)))) opts))
                   (awaitFiber (var 0) awaitValue)
     pAwait = bind (perform (deferredMakeOf nat nat) (lit unit)) (perform deferredAwait (var 0))
   Each is run through `api_run` with fuel 1000; the check is the root
   fiber's exit. Exit code 0 iff every check passed.

   Properties (tested): these three program outcomes and the option atoms' none/some
   selection, nested option preservation, malformed outer-shape refusal and handle
   identity preservation. The option checks call the generated atom evaluator directly;
   they are bounded generated-runtime checks, not Lean proofs. *)

open Effect4_gen
module A = Api_gen

let failures = ref 0
let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ---------------------------------------------------------------- printing *)

let rec show_val (v : Eff_types.Val.t) =
  match v with
  | Eff_types.Val.Unit -> "unit"
  | Eff_types.Val.Bool b -> string_of_bool b
  | Eff_types.Val.Nat n -> string_of_int n
  | Eff_types.Val.Str s -> "\"" ^ s ^ "\""
  | Eff_types.Val.None -> "none"
  | Eff_types.Val.Some x -> "some " ^ show_val x
  | Eff_types.Val.Pair (a, b) -> "pair (" ^ show_val a ^ ", " ^ show_val b ^ ")"
  | Eff_types.Val.List xs -> "list [" ^ String.concat ", " (List.map show_val xs) ^ "]"
  | Eff_types.Val.Bytes _ -> "bytes"
  | Eff_types.Val.Ctor (i, args) ->
    Printf.sprintf "ctor %d [%s]" i (String.concat ", " (List.map show_val args))
  | Eff_types.Val.Ref (k, _) -> Printf.sprintf "ref %d" k
  | Eff_types.Val.Handle (k, n) -> Printf.sprintf "handle %d/%d" k n
  | Eff_types.Val.NegInt n -> string_of_int (- (n + 1))
  | Eff_types.Val.Float b -> Printf.sprintf "float %d" b

let show_reason = function
  | Eff_types.Reason.Fail (Eff_types.Err.Boom, _) -> "fail(boom)"
  | Eff_types.Reason.Fail (Eff_types.Err.Tag t, _) -> Printf.sprintf "fail(tag %d)" t
  | Eff_types.Reason.Fail (Eff_types.Err.Payload p, _) -> "fail(payload " ^ show_val p ^ ")"
  | Eff_types.Reason.Fail _ -> "fail"
  | Eff_types.Reason.Die (_, _) -> "die"
  | Eff_types.Reason.Interrupt (None, _) -> "interrupt(none)"
  | Eff_types.Reason.Interrupt (Some i, _) -> Printf.sprintf "interrupt(%d)" i

let show_exit = function
  | None -> "<no exit>"
  | Some (Eff_types.Exit.Success v) -> "success " ^ show_val v
  | Some (Eff_types.Exit.Failure c) ->
    "failure [" ^ String.concat "; " (List.map show_reason c) ^ "]"

let show_outcome = function
  | A.Outcome_finished -> "finished"
  | A.Outcome_frontier -> "frontier"
  | A.Outcome_stuck _ -> "stuck"

(* the root fiber's exit, the way `Api.Inspection.exit` reads it: fiber 0 of the machine.
   `Effect4.Api.Run` was renamed `Effect4.Api.Inspection` in the tree; the record is the same
   three fields and `api_run` still answers it. *)
let root_exit (r : A.inspection) =
  match List.find_opt (fun (f : (_, _, _, _, _, _, _, _, _, _) A.run_fiber) -> f.A.id = 0)
          r.A.machine.A.fibers with
  | None -> None
  | Some f -> f.A.exit_

let run_and_show name (p : Eff_types.NativeOp.t Eff_types.Eff.t) =
  let r = A.api_run p 1000 [] 1000 in
  let e = root_exit r in
  Printf.printf "  %s: outcome=%s fibers=%d exit=%s\n" name (show_outcome r.A.outcome)
    (List.length r.A.machine.A.fibers) (show_exit e);
  (r, e)

(* ---------------------------------------------------------------- the programs *)

let p42 : Eff_types.NativeOp.t Eff_types.Eff.t = Eff_types.Eff.Succeed (Eff_types.Term.Lit (Eff_types.Lit.Nat 42))

let fork_options : Eff_types.ForkOptions.t =
  { Eff_types.ForkOptions.start_immediately = false; daemon = false; mask_mode = Eff_types.MaskMode.Inherit }

let p_fork : Eff_types.NativeOp.t Eff_types.Eff.t =
  Eff_types.Eff.Bind
    ( Eff_types.Eff.WithFiber
        (Eff_types.ActionTerm.Fork
           ( Eff_types.Eff.Bind (Eff_types.Eff.YieldNow 0, Eff_types.Eff.Succeed (Eff_types.Term.Lit (Eff_types.Lit.Nat 7))),
             fork_options )),
      Eff_types.Eff.AwaitFiber (Eff_types.Term.Var 0, Eff_types.ObserverMode.AwaitValue) )

let p_await : Eff_types.NativeOp.t Eff_types.Eff.t =
  Eff_types.Eff.Bind
    ( Eff_types.Eff.Perform (Eff_types.NativeOp.DeferredMakeOf (Eff_types.Ty.Nat, Eff_types.Ty.Nat), Eff_types.Term.Lit Eff_types.Lit.Unit),
      Eff_types.Eff.Perform (Eff_types.NativeOp.DeferredAwait, Eff_types.Term.Var 0) )

let () =
  print_endline "== G0. the generated engine runs a program (Api.run, fuel 1000) ==";
  let _, e = run_and_show "p42" p42 in
  check "p42 exits success 42" (e = Some (Eff_types.Exit.Success (Eff_types.Val.Nat 42)));
  (* `awaitFiber … awaitValue` answers the child's *reified exit*, `ctor 0 [nat 7]`, not a
     bare 7; the Lean side (`Api.run Wire.Corpus.pFork 1000`) prints exactly the same. *)
  let r, e = run_and_show "pFork" p_fork in
  check "pFork exits success (ctor 0 [7]), two fibers"
    (e = Some (Eff_types.Exit.Success (Eff_types.Val.Ctor (0, [ Eff_types.Val.Nat 7 ])))
    && List.length r.A.machine.A.fibers = 2);
  let _, e = run_and_show "pAwait" p_await in
  check "pAwait parks on the deferred (no exit, frontier)" (e = None)

let () =
  print_endline "== generated option atoms (bounded smoke checks) ==";
  check "isSome none is false"
    (A.program_native_atom_eval A.NativeAtom_isSome [ Eff_types.Val.None ]
    = Some (Eff_types.Val.Bool false));
  check "isSome some unit is true"
    (A.program_native_atom_eval A.NativeAtom_isSome [ Eff_types.Val.Some Eff_types.Val.Unit ]
    = Some (Eff_types.Val.Bool true));
  check "getOrElse none selects the default"
    (A.program_native_atom_eval A.NativeAtom_getOrElse [ Eff_types.Val.None; Eff_types.Val.Nat 9 ]
    = Some (Eff_types.Val.Nat 9));
  check "getOrElse some selects its payload"
    (A.program_native_atom_eval A.NativeAtom_getOrElse
       [ Eff_types.Val.Some (Eff_types.Val.Nat 3); Eff_types.Val.Nat 9 ]
    = Some (Eff_types.Val.Nat 3));
  check "getOrElse retains a nested none payload"
    (A.program_native_atom_eval A.NativeAtom_getOrElse
       [ Eff_types.Val.Some Eff_types.Val.None; Eff_types.Val.Some (Eff_types.Val.Nat 9) ]
    = Some Eff_types.Val.None);
  check "isSome refuses a malformed outer shape"
    (A.program_native_atom_eval A.NativeAtom_isSome [ Eff_types.Val.Nat 3 ] = None);
  check "getOrElse refuses a malformed outer shape"
    (A.program_native_atom_eval A.NativeAtom_getOrElse [ Eff_types.Val.Nat 3; Eff_types.Val.Nat 9 ]
    = None);
  let kind = A.handle_kind_byte A.HandleKind_external in
  let payload = Eff_types.Val.Handle (kind, 41) in
  let fallback = Eff_types.Val.Handle (kind, 77) in
  check "getOrElse preserves the selected payload handle"
    (A.program_native_atom_eval A.NativeAtom_getOrElse [ Eff_types.Val.Some payload; fallback ]
    = Some payload);
  check "getOrElse preserves the selected default handle"
    (A.program_native_atom_eval A.NativeAtom_getOrElse [ Eff_types.Val.None; fallback ]
    = Some fallback)

let () =
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
