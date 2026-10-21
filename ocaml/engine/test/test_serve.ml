(* test_serve.ml -- E4_host.Make.serve: what each stop says, on both engine instances.

   What it is: the host boundary's controls (the OCaml estate refactor's slice 0.1). Codex's
   round-2 reply control, its positive control, the assessment's programs (a step that leaves
   the host numeric profile, a load that does), a machine short of fuel, a machine waiting on a
   timer, a stuck answer, and a reply admission refuses. Every check runs over E4_engine.Fast,
   and each sits beside the control that shows its premise stands.
   Depends on: E4_host, E4_engine, Lcnf_crossing, Eff_types, Zarith.

   Properties (E4_host's H2, H8, H9 and H10 name these):
   S1  A reply inside the profile at ingress and admitted (9007199254740991 to a natural row)
       whose step a crossing refuses, at `~rounds:2`: the stop is `Outside_profile`, the
       provider was called once, the host's state is the one before the call, no call is
       recorded, the call is still outstanding, and the engine is the machine before the reply.
       Premise: the reply passes `answer_async` and `admits`, and `step` of it answers
       `Outside_profile`. Since M4 the run is exact, so the program's `+ 1` answers
       9007199254740992 on the real instance, and the refusing step is a stand-in's (the real
       instance, whose step of a reply computes a shift past the target's int, which the runtime
       library refuses at the arithmetic crossing). Red control: the real instance finishes
       with 9007199254740992.                                               tested
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
   S7  Loading has its own result: a natural literal outside the profile is
       `Error (Load_outside_profile (Unsupported _))`, Lean's profile support at ingress, and a
       load a crossing refuses is `Error (Load_outside_profile (Crossing _))`; nothing raises.
       Premise: `literal_refusal` refuses the literal at its node, and admits the closed sum
       9007199254740991 + 1, which the real instance loads and finishes exactly (M4); the
       crossing's load is a stand-in's, on which `E.load` raises at the arithmetic crossing.
       Red control: the largest literal inside the profile loads and finishes.   tested
   S8  The assessment's program, 9007199254740991 + 1 bound to a literal: on the real instance
       its `evaluate 0` computes 9007199254740992 exactly (M4); on a stand-in whose evaluation
       a crossing refuses, the stop is `Outside_profile`, the provider is never called, and the
       engine is the machine as loaded. Red control: 20 + 22 finishes with 42.   tested

   What it does not establish: a stuck machine or a crossing's refusal reached by a real
   program (S5, and the crossing halves of S1, S7 and S8, are stand-ins: since M4 no program
   reaches a crossing); `Unknown_row`, `Declined` and `Out_of_rounds`, which test_todo and the
   kit lane reach.

   Run: cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test *)

open Eff_types
module E4_engine = Effect4_engine.E4_engine

let check = E4_check.check
let nat n = Term.Lit (Lit.Nat (Z.of_int n))
let add a b = Term.App ("add", Terms.Cons (a, Terms.Cons (b, Terms.Nil)))

let success v : (Val.t, Err.t, Defect.t, Z.t, unit) Completion.t =
  Completion.OfExit (Exit.Success v)
;;

(* The root's exit, a success with this natural. *)
let succeeded_with (n : string) = function
  | Some (Exit.Success (Val.Nat v)) -> Z.equal v (Z.of_string n)
  | _ -> false
;;

(* One host row: a call with no request, answered by a natural. *)
let table : Row.t list =
  [ { Row.name = "next"
    ; spelling = "next"
    ; shape = RowShape.Call
    ; trailing = []
    ; kind = RowKind.Async
    ; request = Ty.Unit
    ; answer = Ty.Nat
    ; error = Ty.Never
    ; requires = []
    ; cite = "test_serve"
    ; type_args = []
    ; registration = Registration.External
    }
  ]
;;

(* Codex's program: call the row, then add 1 to its answer. *)
let call_add1 : NativeOp.t Eff.t =
  Eff.Bind
    ( Eff.Perform (NativeOp.External (Z.of_int 0), Term.Lit Lit.Unit)
    , Eff.Succeed (add (Term.Var (Z.of_int 0)) (nat 1)) )
;;

let rec chain n : NativeOp.t Eff.t =
  if n <= 0
  then Eff.Succeed (Term.Lit Lit.Unit)
  else Eff.Bind (Eff.Perform (NativeOp.RefMake, nat (n - 1)), chain (n - 1))
;;

let call_then_chain : NativeOp.t Eff.t =
  Eff.Bind (Eff.Perform (NativeOp.External (Z.of_int 0), Term.Lit Lit.Unit), chain 50)
;;

(* The assessment's programs (docs/research/2026-10-17-ocaml-refactor-assessment/evidence/
   actual_host.ml): a sum bound to a literal, at the profile's edge and inside it. *)
let bound_sum a b : NativeOp.t Eff.t =
  Eff.Bind (Eff.Succeed (nat a), Eff.Succeed (add (Term.Var (Z.of_int 0)) (nat b)))
;;

let closed_sum : NativeOp.t Eff.t = Eff.Succeed (add (nat 9007199254740991) (nat 1))
let sleeper : NativeOp.t Eff.t = Eff.Perform (NativeOp.Sleep, nat 1000)

(* The crossing's stand-ins (S1, S7, S8): the real instance, whose step of a host reply, whose
   evaluation, or whose load computes a shift past the target's int, which the runtime library
   refuses at the arithmetic crossing (`Lcnf_crossing.Refused`). Since M4 no program reaches a
   crossing, so the refusal is the stand-in's, and what is checked is what the engine and the
   host do with it. *)
let refuse () = ignore (Lcnf_nat.shift_left Z.one (Z.shift_left Z.one 62))

module Refusing (W : sig
    val step : Effect4_engine.Api_engine_inst.api_decision -> bool
    val load : bool
  end) =
struct
  include Effect4_engine.Api_engine_inst

  let name = "Refusing"

  let step prepared ~fuel m d =
    if W.step d then refuse ();
    Effect4_engine.Api_engine_inst.step prepared ~fuel m d
  ;;

  let load p ~fuel =
    if W.load then refuse ();
    Effect4_engine.Api_engine_inst.load p ~fuel
  ;;
end

module Refuse_reply = E4_engine.Make (Refusing (struct
    let step = function
      | Effect4_engine.Api_engine_inst.RunDecision_answerAsync _ -> true
      | _ -> false
    ;;

    let load = false
  end))

module Refuse_evaluate = E4_engine.Make (Refusing (struct
    let step = function
      | Effect4_engine.Api_engine_inst.RunDecision_evaluate _ -> true
      | _ -> false
    ;;

    let load = false
  end))

module Refuse_load = E4_engine.Make (Refusing (struct
    let step _ = false
    let load = true
  end))

(* A stand-in for a stuck machine (S5): the real instance, with its `Finished` read as stuck. *)
module Stuck_engine (E : E4_engine.ENGINE) : E4_engine.ENGINE = struct
  include E

  let answer t =
    match E.answer t with
    | E4_engine.Finished -> E4_engine.Refused "unknownFiber 9"
    | a -> a
  ;;
end

module Checks (E : E4_engine.ENGINE) = struct
  module H = Effect4_engine.E4_host.Make (E)

  let name what = Printf.sprintf "%s: %s" E.name what

  (* A provider answering [answer] to every call, counting its calls in [count]. *)
  let counting count answer : int H.provider =
    fun _ _ st ->
    incr count;
    Some (answer, st + 1)
  ;;

  let serve ?(table = table) ?rounds ~fuel program provider =
    H.serve ~table ?rounds provider program ~fuel 0
  ;;

  (* What an engine shows: its outcome, fibers, trace and the calls it waits on. *)
  let observation e = E.outcome e, E.fiber_rows e, E.trace_rows e, E.host_calls e

  let evaluated ?(table = table) ~fuel program =
    E.step (E.load ~table program ~fuel) (E.evaluate 0)
  ;;

  (* The stops, read by pattern: a stop may carry an exception, which `=` must not compare. *)
  let is_finished = function
    | H.Machine H.Finished -> true
    | _ -> false
  ;;

  let is_delay = function
    | H.Machine H.Delay -> true
    | _ -> false
  ;;

  let is_waiting = function
    | H.Machine H.Waiting -> true
    | _ -> false
  ;;

  let is_outside = function
    | H.Host (H.Outside_profile _) -> true
    | _ -> false
  ;;

  let finished = function
    | Ok (s : int H.served) -> is_finished s.stop
    | Error _ -> false
  ;;

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
      check
        (name (label ^ ": the call is still outstanding"))
        (List.length (E.host_calls s.engine) = 1);
      check
        (name (label ^ ": the engine is the machine before the reply"))
        (observation s.engine = observation before)
  ;;

  let run () =
    (* S1 on the real instance: the reply's step is exact (M4) *)
    let edge = success (Val.Nat (Z.of_int 9007199254740991)) in
    let t = evaluated ~fuel:1000 call_add1 in
    (match E.host_calls t with
     | (fiber, token, _, _) :: _ ->
       let d = E.answer_async fiber token edge in
       check (name "S1 premise: the reply passes ingress and admission") (E.admits t d)
     | [] -> check (name "S1 premise: the program calls its row") false);
    check
      (name
         "S1 red control: the reply's step computes 9007199254740992 exactly and finishes")
      (match serve ~rounds:2 ~fuel:1000 call_add1 (counting (ref 0) edge) with
       | Ok s ->
         is_finished s.stop && succeeded_with "9007199254740992" (E.root_exit_of s.engine)
       | Error _ -> false);
    (* S2 *)
    let text = success (Val.Str "forty-one") in
    (match E.host_calls t with
     | (fiber, token, _, _) :: _ ->
       check
         (name "S2 premise: admission refuses a string for a natural")
         (not (E.admits t (E.answer_async fiber token text)))
     | [] -> check (name "S2 premise: the program calls its row") false);
    refused_reply "S2 a reply admission refuses" text (function
      | H.Host H.Refused -> true
      | _ -> false);
    (* S3 *)
    let count = ref 0 in
    (match
       serve
         ~rounds:2
         ~fuel:1000
         call_add1
         (counting count (success (Val.Nat (Z.of_int 41))))
     with
     | Ok s ->
       check (name "S3 the reply 41 finishes") (is_finished s.stop);
       check
         (name "S3 the root's exit is 42")
         (succeeded_with "42" (E.root_exit_of s.engine));
       check
         (name "S3 one call is recorded, with the host's state after it")
         (!count = 1 && List.length s.calls = 1 && s.state = 1)
     | Error _ -> check (name "S3 the program loads") false);
    (* S4 *)
    let starved =
      serve ~fuel:5 (chain 50) (counting (ref 0) (success (Val.Nat (Z.of_int 0))))
    in
    check
      (name "S4 a chain short of fuel at evaluate stops with Delay, never Finished")
      (match starved with
       | Ok s -> is_delay s.stop && s.calls = []
       | Error _ -> false);
    check
      (name "S4 red control: the chain with fuel to spare finishes")
      (finished
         (serve
            ~fuel:100_000
            (chain 50)
            (counting (ref 0) (success (Val.Nat (Z.of_int 0))))));
    (* The least fuel at which [call_then_chain] parks on its call runs out in the chain. *)
    let rec parks_at fuel =
      if fuel > 1000
      then None
      else (
        let t = evaluated ~fuel call_then_chain in
        match E.answer t, E.host_calls t with
        | E4_engine.Suspended _, _ :: _ -> Some fuel
        | _ -> parks_at (fuel + 1))
    in
    (match parks_at 1 with
     | None -> check (name "S4 premise: the call is reached at some fuel") false
     | Some fuel ->
       let count = ref 0 in
       (match
          serve ~fuel call_then_chain (counting count (success (Val.Nat (Z.of_int 0))))
        with
        | Ok s ->
          check
            (name
               (Printf.sprintf
                  "S4 at fuel %d a reply short of fuel stops with Delay"
                  fuel))
            (is_delay s.stop);
          check
            (name
               "S4 the reply was applied: its call is recorded, with the state after it")
            (!count = 1 && List.length s.calls = 1 && s.state = 1)
        | Error _ -> check (name "S4 the program loads") false);
       check
         (name "S4 red control: the same program with fuel to spare finishes")
         (finished
            (serve
               ~fuel:100_000
               call_then_chain
               (counting (ref 0) (success (Val.Nat (Z.of_int 0)))))));
    (* S6 *)
    (match serve ~table:[] ~fuel:1000 sleeper (counting (ref 0) (success Val.Unit)) with
     | Ok s ->
       check
         (name "S6 premise: the sleeping machine is suspended")
         (match E.answer s.engine with
          | E4_engine.Suspended _ -> true
          | _ -> false);
       check
         (name "S6 a machine sleeping with no clock advance stops with Waiting")
         (is_waiting s.stop && s.calls = [] && E.root_exit_of s.engine = None)
     | Error _ -> check (name "S6 the program loads") false);
    (* S7 *)
    let raises p =
      match E.load p ~fuel:1000 with
      | exception Lcnf_crossing.Refused _ -> true
      | _ -> false
    in
    let load_refusal p =
      match H.serve (fun _ _ st -> Some (success Val.Unit, st)) p ~fuel:1000 () with
      | Error (H.Load_outside_profile why) -> Some why
      | Ok _ -> None
      | exception _ -> None
    in
    let big = Eff.Succeed (nat (1 lsl 53)) in
    let big_n = Z.of_int (1 lsl 53) in
    check
      (name
         "S7 premise: profile support refuses a literal outside the profile, at its node")
      (E.literal_refusal big
       = Some { Located.site = []; reason = ProfileReason.AboveBound big_n });
    check
      (name "S7 a literal outside the profile is the loading refusal, nothing raised")
      (match load_refusal big with
       | Some (E4_engine.Unsupported _) -> true
       | _ -> false);
    check
      (name
         "S7 premise: profile support admits the closed sum, and E.load does not raise")
      (Option.is_none (E.literal_refusal closed_sum) && not (raises closed_sum));
    check
      (name "S7 the closed sum 9007199254740991 + 1 loads and finishes exactly (M4)")
      (match
         serve ~table:[] ~fuel:1000 closed_sum (counting (ref 0) (success Val.Unit))
       with
       | Ok s ->
         is_finished s.stop && succeeded_with "9007199254740992" (E.root_exit_of s.engine)
       | Error _ -> false);
    check
      (name "S7 red control: the largest literal inside the profile loads and finishes")
      (finished
         (serve
            ~table:[]
            ~fuel:1000
            (Eff.Succeed (nat 9007199254740991))
            (counting (ref 0) (success Val.Unit))));
    (* S8 on the real instance: the evaluation is exact (M4) *)
    let overflow = bound_sum 9007199254740991 1 in
    check
      (name
         "S8 the evaluation of 9007199254740991 + 1 finishes with 9007199254740992 (M4)")
      (match
         serve ~table:[] ~fuel:1000 overflow (counting (ref 0) (success Val.Unit))
       with
       | Ok s ->
         is_finished s.stop && succeeded_with "9007199254740992" (E.root_exit_of s.engine)
       | Error _ -> false);
    match
      serve ~table:[] ~fuel:1000 (bound_sum 20 22) (counting (ref 0) (success Val.Unit))
    with
    | Ok s ->
      check
        (name "S8 red control: 20 + 22 finishes with 42")
        (is_finished s.stop && succeeded_with "42" (E.root_exit_of s.engine))
    | Error _ -> check (name "S8 red control: the program loads") false
  ;;
end

(* S5: the stuck answer, read through the stand-in. *)
module Stuck_checks (E : E4_engine.ENGINE) = struct
  module S = Stuck_engine (E)
  module H = Effect4_engine.E4_host.Make (S)
  module R = Effect4_engine.E4_host.Make (E)

  let name what = Printf.sprintf "%s: %s" E.name what

  let stuck = function
    | H.Machine (H.Stuck why) -> why = "unknownFiber 9"
    | _ -> false
  ;;

  let run () =
    let unit_provider _ _ st = Some (success Val.Unit, st) in
    check
      (name "S5 a stuck answer after evaluate stops with Stuck and the engine's reason")
      (match H.serve unit_provider (bound_sum 20 22) ~fuel:1000 () with
       | Ok s -> stuck s.stop && s.calls = []
       | Error _ -> false);
    check
      (name "S5 red control: the real instance finishes the same program")
      (match R.serve unit_provider (bound_sum 20 22) ~fuel:1000 () with
       | Ok s ->
         (match s.stop with
          | R.Machine R.Finished -> true
          | _ -> false)
       | Error _ -> false);
    let answer41 _ _ st = Some (success (Val.Nat (Z.of_int 41)), st + 1) in
    check
      (name "S5 a stuck answer after a reply stops with Stuck, the call recorded")
      (match H.serve ~table answer41 call_add1 ~fuel:1000 0 with
       | Ok s -> stuck s.stop && List.length s.calls = 1 && s.state = 1
       | Error _ -> false)
  ;;
end

(* S1, S7, S8: a crossing's refusal, through the stand-ins. *)
module Crossing_checks = struct
  let name what = "Refusing: " ^ what

  module R = Checks (Refuse_reply)
  module V = Effect4_engine.E4_host.Make (Refuse_evaluate)
  module L = Effect4_engine.E4_host.Make (Refuse_load)

  let run () =
    (* S1 *)
    let edge = success (Val.Nat (Z.of_int 9007199254740991)) in
    let t = R.evaluated ~fuel:1000 call_add1 in
    (match Refuse_reply.host_calls t with
     | (fiber, token, _, _) :: _ ->
       let d = Refuse_reply.answer_async fiber token edge in
       check
         (name "S1 premise: the reply passes ingress and admission")
         (Refuse_reply.admits t d);
       check
         (name
            "S1 premise: the step that applies it is refused at the arithmetic crossing")
         (match Refuse_reply.answer (Refuse_reply.step t d) with
          | E4_engine.Outside_profile r ->
            r.Lcnf_crossing.crossing = Lcnf_crossing.Arithmetic
          | _ -> false)
     | [] -> check (name "S1 premise: the program calls its row") false);
    R.refused_reply "S1 a reply whose step a crossing refuses" edge R.is_outside;
    (* S7 *)
    check
      (name "S7 premise: the stand-in's load raises at the crossing")
      (match Refuse_load.load closed_sum ~fuel:1000 with
       | exception Lcnf_crossing.Refused _ -> true
       | _ -> false);
    check
      (name "S7 a load a crossing refuses is the loading refusal, nothing raised")
      (match
         L.serve (fun _ _ st -> Some (success Val.Unit, st)) closed_sum ~fuel:1000 ()
       with
       | Error (L.Load_outside_profile (E4_engine.Crossing _)) -> true
       | _ -> false
       | exception _ -> false);
    (* S8 *)
    let count = ref 0 in
    let overflow = bound_sum 9007199254740991 1 in
    let counting answer _ _ st =
      incr count;
      Some (answer, st)
    in
    match V.serve ~table:[] (counting (success Val.Unit)) overflow ~fuel:1000 () with
    | Ok s ->
      check
        (name
           "S8 an evaluation a crossing refuses stops with Outside_profile, no provider \
            call")
        ((match s.stop with
          | V.Host (V.Outside_profile _) -> true
          | _ -> false)
         && !count = 0);
      let observe e =
        ( Refuse_evaluate.outcome e
        , Refuse_evaluate.fiber_rows e
        , Refuse_evaluate.trace_rows e
        , Refuse_evaluate.host_calls e )
      in
      check
        (name "S8 the engine is the machine as loaded")
        (observe s.engine = observe (Refuse_evaluate.load ~table:[] overflow ~fuel:1000))
    | Error _ -> check (name "S8 the program loads") false
  ;;
end

module Fast = Checks (E4_engine.Fast)
module Stuck_fast = Stuck_checks (E4_engine.Fast)

let () =
  Fast.run ();
  Stuck_fast.run ();
  Crossing_checks.run ();
  E4_check.finish ()
;;
