(* test_serve.ml -- E4_host.Make.serve: what each stop says, on both engine instances.

   What it is: the host boundary's controls (the OCaml estate refactor's slice 0.1). Codex's
   round-2 reply control, its positive control, the assessment's programs (a step that leaves
   the host numeric profile, a load that does), a machine short of fuel, a machine waiting on a
   timer, a stuck answer, and a reply admission refuses. Every check runs over E4_engine.Fast
   and E4_engine.Ref, and each sits beside the control that shows its premise stands.
   Depends on: E4_host, E4_engine, E4_clock, Eff_types.

   Properties (E4_host's H2, H8, H9 and H10 name these):
   S1  A reply inside the profile at ingress and admitted (9007199254740991 to a natural row)
       whose step leaves the profile (the program adds 1), at `~rounds:2`: the stop is
       `Outside_profile`, the provider was called once, the host's state is the one before the
       call, no call is recorded, the call is still outstanding, and the engine is the machine
       before the reply. Premise: the reply passes `answer_async` and `admits`, and `step` of it
       answers `Outside_profile`.                                           tested
   S2  A reply admission refuses (a string to a natural row): the stop is `Refused`, with the
       same four facts as S1. Premise: `admits` refuses it.                 tested
   S3  The positive control, the program of S1 answered 41: the stop is `Finished`, the root's
       exit is 42, one call is recorded, and the host's state is the one after it.  tested
   S4  A machine short of fuel stops with `Delay`, never `Finished`: at `evaluate 0` (a chain of
       allocations), with no call; and at a reply (the chain after the call), with the call
       recorded and the host's state after it. Red control: with fuel to spare each finishes.
                                                                            tested
   S5  A stuck answer stops with `Stuck` and the engine's reason, never `Finished`: after
       `evaluate 0`, and after a reply with the call recorded. No program of the alphabet
       reaches a stuck machine (test_replay_steps R1: each `Stuck` names an identity the machine
       mints, and admission refuses a reply that names one it did not), so the engine here is a
       stand-in: the real instance, with its `Finished` answer read as `Refused`. Red control:
       the real instance finishes.                                          tested
   S6  A machine sleeping with no clock advance stops with `Waiting`, a live frontier: no host
       call, no root exit. Premise: the engine answers `Suspended`.         tested
   S7  Loading has its own result: a natural literal outside the profile, and a closed sum
       whose loading computes outside it, are `Error (Load_outside_profile _)`, and nothing
       raises. Premise: `E.load` raises on each, and for the sum `compile` passes, so the
       refusal is the load's own. Red control: the largest literal inside the profile loads and
       finishes.                                                            tested
   S8  The assessment's program, whose `evaluate 0` leaves the profile: the stop is
       `Outside_profile`, the provider is never called, and the engine is the machine as loaded.
       Red control: the same shape inside the profile finishes with 42.     tested

   What it does not establish: a stuck machine reached by a real program (S5 is a stand-in);
   `Unknown_row`, `Declined` and `Out_of_rounds`, which test_todo and the kit lane reach.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test *)

open Eff_types
module E4_engine = Effect4_engine.E4_engine

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  if ok then Printf.printf "PASS %s\n" name
  else begin
    incr failures;
    Printf.printf "FAIL %s\n" name
  end

let nat n = Term_lit (Lit_nat n)
let add a b = Term_app ("add", Terms_cons (a, Terms_cons (b, Terms_nil)))
let success v : (val_, err, defect, int, unit) completion = Completion_ofExit (Exit_success v)

(* One host row: a call with no request, answered by a natural. *)
let table : row list =
  [ { name = "next"; spelling = "next"; shape = RowShape_call; trailing = []; kind = RowKind_async;
      request = Ty_unit; answer = Ty_nat; error = Ty_never; requires = []; cite = "test_serve";
      type_args = []; registration = Registration_external } ]

(* Codex's program: call the row, then add 1 to its answer. *)
let call_add1 : native_op eff =
  Eff_bind (Eff_perform (NativeOp_external 0, Term_lit Lit_unit), Eff_succeed (add (Term_var 0) (nat 1)))

let rec chain n : native_op eff =
  if n <= 0 then Eff_succeed (Term_lit Lit_unit)
  else Eff_bind (Eff_perform (NativeOp_refMake, nat (n - 1)), chain (n - 1))

let call_then_chain : native_op eff = Eff_bind (Eff_perform (NativeOp_external 0, Term_lit Lit_unit), chain 50)

(* The assessment's programs (docs/research/2026-10-17-ocaml-refactor-assessment/evidence/
   actual_host.ml): a sum bound to a literal, at the profile's edge and inside it. *)
let bound_sum a b : native_op eff = Eff_bind (Eff_succeed (nat a), Eff_succeed (add (Term_var 0) (nat b)))
let closed_sum : native_op eff = Eff_succeed (add (nat 9007199254740991) (nat 1))
let sleeper : native_op eff = Eff_perform (NativeOp_sleep, nat 1000)

(* A stand-in for a stuck machine (S5): the real instance, with its `Finished` read as stuck. *)
module Stuck_engine (E : E4_engine.ENGINE) : E4_engine.ENGINE = struct
  include E

  let answer t = match E.answer t with E4_engine.Finished -> E4_engine.Refused "unknownFiber 9" | a -> a
end

module Checks (E : E4_engine.ENGINE) = struct
  module H = Effect4_engine.E4_host.Make (E)

  let name what = Printf.sprintf "%s: %s" E.name what

  (* A provider answering [answer] to every call, counting its calls in [count]. *)
  let counting count answer : int H.provider =
   fun _ _ st ->
    incr count;
    Some (answer, st + 1)

  let serve ?(table = table) ?rounds ~fuel program provider =
    H.serve ~table ?rounds provider program ~fuel 0

  (* What an engine shows: its outcome, fibers, trace and the calls it waits on. *)
  let observation e = (E.outcome e, E.fiber_rows e, E.trace_rows e, E.host_calls e)

  let evaluated ?(table = table) ~fuel program = E.step (E.load ~table program ~fuel) (E.evaluate 0)

  (* The stops, read by pattern: a stop may carry an exception, which `=` must not compare. *)
  let is_finished = function H.Machine H.Finished -> true | _ -> false
  let is_delay = function H.Machine H.Delay -> true | _ -> false
  let is_waiting = function H.Machine H.Waiting -> true | _ -> false
  let is_outside = function H.Host (H.Outside_profile _) -> true | _ -> false
  let finished = function Ok (s : int H.served) -> is_finished s.stop | Error _ -> false

  (* S1, S2: a refused reply stops the drive at once, leaving everything as before the call. *)
  let refused_reply label answer expected =
    let count = ref 0 in
    let before = evaluated ~fuel:1000 call_add1 in
    match serve ~rounds:2 ~fuel:1000 call_add1 (counting count answer) with
    | Error _ -> check (name (label ^ ": the program loads")) false
    | Ok s ->
      check (name (label ^ ": the stop names the refusal")) (expected s.stop);
      check (name (label ^ ": the provider was called once")) (!count = 1);
      check (name (label ^ ": the host's state is the one before the call")) (s.state = 0);
      check (name (label ^ ": no call is recorded")) (s.calls = []);
      check (name (label ^ ": the call is still outstanding")) (List.length (E.host_calls s.engine) = 1);
      check (name (label ^ ": the engine is the machine before the reply"))
        (observation s.engine = observation before)

  let run () =
    (* S1 *)
    let edge = success (Val_nat 9007199254740991) in
    let t = evaluated ~fuel:1000 call_add1 in
    (match E.host_calls t with
     | (fiber, token, _, _) :: _ ->
       let d = E.answer_async fiber token edge in
       check (name "S1 premise: the reply passes ingress and admission") (E.admits t d);
       check (name "S1 premise: the step that applies it leaves the profile")
         (match E.answer (E.step t d) with E4_engine.Outside_profile _ -> true | _ -> false)
     | [] -> check (name "S1 premise: the program calls its row") false);
    refused_reply "S1 a reply whose step leaves the profile" edge is_outside;
    (* S2 *)
    let text = success (Val_str "forty-one") in
    (match E.host_calls t with
     | (fiber, token, _, _) :: _ ->
       check (name "S2 premise: admission refuses a string for a natural")
         (not (E.admits t (E.answer_async fiber token text)))
     | [] -> check (name "S2 premise: the program calls its row") false);
    refused_reply "S2 a reply admission refuses" text (function H.Host H.Refused -> true | _ -> false);
    (* S3 *)
    let count = ref 0 in
    (match serve ~rounds:2 ~fuel:1000 call_add1 (counting count (success (Val_nat 41))) with
     | Ok s ->
       check (name "S3 the reply 41 finishes") (is_finished s.stop);
       check (name "S3 the root's exit is 42") (E.root_exit_of s.engine = Some (Exit_success (Val_nat 42)));
       check (name "S3 one call is recorded, with the host's state after it")
         (!count = 1 && List.length s.calls = 1 && s.state = 1)
     | Error _ -> check (name "S3 the program loads") false);
    (* S4 *)
    let starved = serve ~fuel:5 (chain 50) (counting (ref 0) (success (Val_nat 0))) in
    check (name "S4 a chain short of fuel at evaluate stops with Delay, never Finished")
      (match starved with Ok s -> is_delay s.stop && s.calls = [] | Error _ -> false);
    check (name "S4 red control: the chain with fuel to spare finishes")
      (finished (serve ~fuel:100_000 (chain 50) (counting (ref 0) (success (Val_nat 0)))));
    (* The least fuel at which [call_then_chain] parks on its call runs out in the chain. *)
    let rec parks_at fuel =
      if fuel > 1000 then None
      else
        let t = evaluated ~fuel call_then_chain in
        match E.answer t, E.host_calls t with
        | E4_engine.Suspended _, _ :: _ -> Some fuel
        | _ -> parks_at (fuel + 1)
    in
    (match parks_at 1 with
     | None -> check (name "S4 premise: the call is reached at some fuel") false
     | Some fuel ->
       let count = ref 0 in
       (match serve ~fuel call_then_chain (counting count (success (Val_nat 0))) with
        | Ok s ->
          check (name (Printf.sprintf "S4 at fuel %d a reply short of fuel stops with Delay" fuel))
            (is_delay s.stop);
          check (name "S4 the reply was applied: its call is recorded, with the state after it")
            (!count = 1 && List.length s.calls = 1 && s.state = 1)
        | Error _ -> check (name "S4 the program loads") false);
       check (name "S4 red control: the same program with fuel to spare finishes")
         (finished (serve ~fuel:100_000 call_then_chain (counting (ref 0) (success (Val_nat 0))))));
    (* S6 *)
    (match serve ~table:[] ~fuel:1000 sleeper (counting (ref 0) (success Val_unit)) with
     | Ok s ->
       check (name "S6 premise: the sleeping machine is suspended")
         (match E.answer s.engine with E4_engine.Suspended _ -> true | _ -> false);
       check (name "S6 a machine sleeping with no clock advance stops with Waiting")
         (is_waiting s.stop && s.calls = [] && E.root_exit_of s.engine = None)
     | Error _ -> check (name "S6 the program loads") false);
    (* S7 *)
    let raises p = match E.load p ~fuel:1000 with exception E4_clock.Profile_refusal _ -> true | _ -> false in
    let refused_load p =
      match H.serve (fun _ _ st -> Some (success Val_unit, st)) p ~fuel:1000 () with
      | Error (H.Load_outside_profile _) -> true
      | Ok _ -> false
      | exception _ -> false
    in
    let big = Eff_succeed (nat (1 lsl 53)) in
    check (name "S7 premise: E.load raises on a literal outside the profile") (raises big);
    check (name "S7 a literal outside the profile is the loading refusal, nothing raised") (refused_load big);
    check (name "S7 premise: the closed sum compiles, and E.load raises on it")
      ((match E.compile closed_sum with exception _ -> false | _ -> true) && raises closed_sum);
    check (name "S7 a closed sum whose loading leaves the profile is the loading refusal") (refused_load closed_sum);
    check (name "S7 red control: the largest literal inside the profile loads and finishes")
      (finished (serve ~table:[] ~fuel:1000 (Eff_succeed (nat 9007199254740991)) (counting (ref 0) (success Val_unit))));
    (* S8 *)
    let count = ref 0 in
    let overflow = bound_sum 9007199254740991 1 in
    (match serve ~table:[] ~fuel:1000 overflow (counting count (success Val_unit)) with
     | Ok s ->
       check (name "S8 an evaluation that leaves the profile stops with Outside_profile, no provider call")
         (is_outside s.stop && !count = 0);
       check (name "S8 the engine is the machine as loaded")
         (observation s.engine = observation (E.load ~table:[] overflow ~fuel:1000))
     | Error _ -> check (name "S8 the program loads") false);
    (match serve ~table:[] ~fuel:1000 (bound_sum 20 22) (counting (ref 0) (success Val_unit)) with
     | Ok s ->
       check (name "S8 red control: 20 + 22 finishes with 42")
         (is_finished s.stop && E.root_exit_of s.engine = Some (Exit_success (Val_nat 42)))
     | Error _ -> check (name "S8 red control: the program loads") false)
end

(* S5: the stuck answer, read through the stand-in on both instances. *)
module Stuck_checks (E : E4_engine.ENGINE) = struct
  module S = Stuck_engine (E)
  module H = Effect4_engine.E4_host.Make (S)
  module R = Effect4_engine.E4_host.Make (E)

  let name what = Printf.sprintf "%s: %s" E.name what
  let stuck = function H.Machine (H.Stuck why) -> why = "unknownFiber 9" | _ -> false

  let run () =
    let unit_provider _ _ st = Some (success Val_unit, st) in
    check (name "S5 a stuck answer after evaluate stops with Stuck and the engine's reason")
      (match H.serve unit_provider (bound_sum 20 22) ~fuel:1000 () with
       | Ok s -> stuck s.stop && s.calls = []
       | Error _ -> false);
    check (name "S5 red control: the real instance finishes the same program")
      (match R.serve unit_provider (bound_sum 20 22) ~fuel:1000 () with
       | Ok s -> (match s.stop with R.Machine R.Finished -> true | _ -> false)
       | Error _ -> false);
    let answer41 _ _ st = Some (success (Val_nat 41), st + 1) in
    check (name "S5 a stuck answer after a reply stops with Stuck, the call recorded")
      (match H.serve ~table answer41 call_add1 ~fuel:1000 0 with
       | Ok s -> stuck s.stop && List.length s.calls = 1 && s.state = 1
       | Error _ -> false)
end

module Fast = Checks (E4_engine.Fast)
module Ref = Checks (E4_engine.Ref)
module Stuck_fast = Stuck_checks (E4_engine.Fast)
module Stuck_ref = Stuck_checks (E4_engine.Ref)

let () =
  Fast.run ();
  Ref.run ();
  Stuck_fast.run ();
  Stuck_ref.run ();
  Printf.printf "%d checks, %d failures\n" !checks !failures;
  if !failures > 0 then exit 1
