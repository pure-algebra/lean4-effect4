(* api_check.ml -- the G0 smoke: the GENERATED engine (api_gen.ml, rooted at
   `Effect4.Api.run` / `Effect4.Api.replay`) actually runs a program.

   The programs are the byte-pinned corpus of src/Effect4/Program/Wire.lean:74-106, spelled
   in the generated `eff` type:
     p42    = succeed (lit (nat 42))
     pFork  = bind (withFiber (fork (bind (yieldNow 0) (succeed (lit (nat 7)))) opts))
                   (awaitFiber (var 0) awaitValue)
     pAwait = bind (perform deferredMake (lit unit)) (perform deferredAwait (var 0))
   Each is run through `api_run` with fuel 1000 and no choices; the check is the root
   fiber's exit. Exit code 0 iff every check passed. *)

open Effect4_gen
module A = Api_gen

let failures = ref 0
let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

(* ---------------------------------------------------------------- printing *)

let rec show_val (v : A.val_) =
  match v with
  | A.Val_unit -> "unit"
  | A.Val_bool b -> string_of_bool b
  | A.Val_nat n -> string_of_int n
  | A.Val_str s -> "\"" ^ s ^ "\""
  | A.Val_none -> "none"
  | A.Val_some x -> "some " ^ show_val x
  | A.Val_pair (a, b) -> "pair (" ^ show_val a ^ ", " ^ show_val b ^ ")"
  | A.Val_list xs -> "list [" ^ String.concat ", " (List.map show_val xs) ^ "]"
  | A.Val_bytes _ -> "bytes"
  | A.Val_ctor (i, args) ->
    Printf.sprintf "ctor %d [%s]" i (String.concat ", " (List.map show_val args))
  | A.Val_ref (k, _) -> Printf.sprintf "ref %d" k
  | A.Val_handle (k, n) -> Printf.sprintf "handle %d/%d" k n

let show_reason = function
  | A.Reason_fail (A.Err_boom, _) -> "fail(boom)"
  | A.Reason_fail (A.Err_tag t, _) -> Printf.sprintf "fail(tag %d)" t
  | A.Reason_fail _ -> "fail"
  | A.Reason_die (_, _) -> "die"
  | A.Reason_interrupt (None, _) -> "interrupt(none)"
  | A.Reason_interrupt (Some i, _) -> Printf.sprintf "interrupt(%d)" i

let show_exit = function
  | None -> "<no exit>"
  | Some (A.Exit_success v) -> "success " ^ show_val v
  | Some (A.Exit_failure c) ->
    "failure [" ^ String.concat "; " (List.map show_reason c) ^ "]"

let show_outcome = function
  | A.Outcome_finished -> "finished"
  | A.Outcome_frontier -> "frontier"
  | A.Outcome_stuck _ -> "stuck"

(* the root fiber's exit, the way `Api.Run.exit` reads it: fiber 0 of the machine *)
let root_exit (r : A.run) =
  match List.find_opt (fun (f : (_, _, _, _, _, _, _, _, _, _) A.run_fiber) -> f.A.id = 0)
          r.A.machine.A.fibers with
  | None -> None
  | Some f -> f.A.exit_

let run_and_show name (p : A.native_op A.eff) =
  let r = A.api_run p 1000 [] [] [] 1000 in
  let e = root_exit r in
  Printf.printf "  %s: outcome=%s fibers=%d exit=%s\n" name (show_outcome r.A.outcome)
    (List.length r.A.machine.A.fibers) (show_exit e);
  (r, e)

(* ---------------------------------------------------------------- the programs *)

let p42 : A.native_op A.eff = A.Eff_succeed (A.Term_lit (A.Lit_nat 42))

let fork_options : A.fork_options =
  { A.start_immediately = false; daemon = false; mask_mode = A.MaskMode_inherit }

let p_fork : A.native_op A.eff =
  A.Eff_bind
    ( A.Eff_withFiber
        (A.ActionTerm_fork
           ( A.Eff_bind (A.Eff_yieldNow 0, A.Eff_succeed (A.Term_lit (A.Lit_nat 7))),
             fork_options )),
      A.Eff_awaitFiber (A.Term_var 0, A.ObserverMode_awaitValue) )

let p_await : A.native_op A.eff =
  A.Eff_bind
    ( A.Eff_perform (A.NativeOp_deferredMake, A.Term_lit A.Lit_unit),
      A.Eff_perform (A.NativeOp_deferredAwait, A.Term_var 0) )

let () =
  print_endline "== G0. the generated engine runs a program (Api.run, fuel 1000, no choices) ==";
  let _, e = run_and_show "p42" p42 in
  check "p42 exits success 42" (e = Some (A.Exit_success (A.Val_nat 42)));
  (* `awaitFiber … awaitValue` answers the child's *reified exit*, `ctor 0 [nat 7]`, not a
     bare 7; the Lean side (`Api.run Wire.Corpus.pFork 1000`) prints exactly the same. *)
  let r, e = run_and_show "pFork" p_fork in
  check "pFork exits success (ctor 0 [7]), two fibers"
    (e = Some (A.Exit_success (A.Val_ctor (0, [ A.Val_nat 7 ])))
    && List.length r.A.machine.A.fibers = 2);
  let _, e = run_and_show "pAwait" p_await in
  check "pAwait parks on the deferred (no exit, frontier)" (e = None)

let () =
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
