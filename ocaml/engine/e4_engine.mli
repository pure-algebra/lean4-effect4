(* E4_engine -- the drive loop over an instance of the generated engine.

   What it is: docs/research/2026-09-08-engine-a1-state.md §5.  Load a program, apply
   decisions, replay a tape, take a snapshot, and answer in the four-letter alphabet of
   proposal 16.  It adds NO semantics: every transition is the generated
   `stepDecisionState` (api_engine.ml:11424) and the answer is a projection of what that
   function and the generated `settled` (:11330) already say.

   The four letters, and where each comes from:
     Finished   every fiber has exited (`RunMachine.finished`, Fibers.lean:608-609), the
                tape is spent, and the last step settled.
     Suspended  the TAPE ran out with the machine live and settled: a frontier whose
                command residue is empty.
     Delay      the FUEL ran out: `driveState` returned a NON-EMPTY command residue
                (Fibers.lean:1886), which is exactly `settled = false`.  `Api.Outcome`
                conflates this with Suspended (Api.lean:144-148); the engine does not,
                because a caller that can give more fuel must be able to tell them apart.
     Refused    `ReplayResult.stuck` -- `Stuck.unknownFiber/unknownScope/unknownRace`.

   ONE loop, TWO instances.  {!Fast} is `Api_engine.Make(E4_table)(E4_trace)(E4_memo)
   (E4_buckets)`; {!Ref} is the same generated bodies over Lean's list carriers.  Both are
   {!Make} applied to the module the instance file supplies, so the loop, the answer
   alphabet, the ordinal pin and every renderer below exist once.  A differential can then
   call both through {!ENGINE} with one signature -- which is what `test/test_engine.ml`
   does over the 37 byte goldens.

   Depends on: Api_engine_inst, Api_engine_ref, E4_program, effect4_eff (Eff_types,
   Eff_wire), stdlib.

   Behaviours:
   EN1 `run p ~fuel` is `Api.run p fuel []`: same outcome, same fiber table, same trace
       rows, same exits.  The check is against the instance's OWN `api_run` (the generated
       `Effect4.Api.run`, untouched) on every program of the corpus.
                                                          tested (test_engine, check 1/2)
   EN2 the alphabet REFINES Lean's and never contradicts it: Finished iff
       `Outcome.finished`, Refused iff `Outcome.stuck`, and Suspended-or-Delay iff
       `Outcome.frontier`.                                 tested (test_engine)
   EN3 `step` is total: it answers a machine for every decision and never raises -- the two
       `failwith` rows of the generated prelude (`sh_dispatcher_mk`, `sh_memo_map_mk`) are
       the only exception, and they fire on a construction the closure does not contain.
       test_engine counts them over the whole corpus and expects 0.
                                                          by construction; counted
   EN4 THE TAPE AXIS.  `replay_steps m tape` yields `List.length tape + 1` machines, the
       initial one first, position i equal to `replay m (the first i decisions)`, and the
       last equal to `replay m tape`.  It is TOTAL, and it is total because a viewer and a
       differential index by tape position and must have a machine at every one.
                                    tested (test_engine check 4, test_diff, test_replay_steps)
   EN4b THE RUN AXIS, and lane P6's finding F1.  Lean's `replayEval` (Fibers.lean:2028-2040)
       STOPS: at a stuck machine it answers `stuck why m` WITHOUT applying the decision, and
       after a step that left a non-empty command residue — the fuel ran out — it answers
       `frontier r.1` and reads no further.  Past that point Lean defines no machine, and
       `replay_steps` fills the gap by repeating the halted one, so a 64-decision tape at low
       fuel has 65 TAPE positions and 2 RUN positions.  P6 met this as one machine
       checkpointed 64 times.  The run axis is `replay_positions`, which ENDS at the stop and
       repeats nothing, and `replay_to`, which hands back the unread suffix — whose head is
       the REFUSED decision when the machine is stuck, at position
       `|tape| - |residue|`.  On the three corpora of `test_diff` 414 of 3 376 tapes stop
       early, so this is the common case and not a corner.
                                                        tested (test_replay_steps, 41 checks)
   EN5 a snapshot is the machine VALUE: {!snapshot} is the identity, and the value holds no
       mutable structure anywhere (brief §2.3).            by construction
   EN6 fuel is explicit and never implicit: no function of this module invents fuel.
                                                          by construction
   EN7 free rows cost no fuel and never reach the tape: every projection below is a pure
       function of a machine value (INV-TAPE-1, brief §2.4).  by construction

   The projection, stated so its limits are loud (deviation D-D3 of the lane receipt).
   `Api_engine_inst.event` and `Api_engine_ref.event` are two OCaml types -- the generated
   type group lives inside the functor, so each application generates its own -- and a
   differential must therefore compare RENDERINGS, not values.  {!ENGINE.trace_rows}
   renders every constructor of `RunEvent`, `Task`, `Prim`, `FrameEvent`, `Exit`, `Cause`,
   `Val`, `Ctx` and `Observer` in full.  Two payloads are NOT descended into and print as
   `<name>` and `<thunk>`: `Effect4.Program.EffName` and `Effect4.Program.EffThunk`.  They
   are program-shaped, not carrier-shaped -- no carrier can reach them -- but the claim
   "the trace rows are equal" is exactly this projection and nothing wider. *)

(** {1 The answer alphabet} *)

type frontier = {
  parked : (int * int) list;  (** (fiber id, park guard token), ascending by fiber *)
  armed : int list;           (** owners with an armed dispatcher, in arming order *)
  due : int;                  (** resumes the deferred store owes right now *)
}

type answer =
  | Finished
  | Suspended of frontier
  | Refused of string  (** the `Stuck` constructor, spelled *)
  | Delay of frontier  (** the fuel ran out; the command residue is non-empty *)

(** {1 What an instance must supply} *)

module type INSTANCE = sig
  include E4_program.PROGRAM_TYPES

  val name : string
  val carriers : string

  (** The two payloads the projection does not descend into. *)

  type nu  (** [Effect4.Program.EffName], api_engine.ml:279 *)

  type s  (** [Effect4.Program.EffThunk], api_engine.ml:392 *)

  (** The machine-side alphabet, transcribed from api_engine.ml.  As with
      {!E4_program.PROGRAM_TYPES}, `ocamlopt` checks this transcription against every
      instance: a constructor added, dropped, renamed or re-ordered in the generated file is
      a compile error here. *)

  type fiber_id = int  (* :775 *)
  type ref_key = int  (* :782 *)
  type 'a reason_annotations = (string * 'a) list  (* :776 *)

  type ('e, 'd, 'i, 'a) reason =  (* :654 *)
    | Reason_fail of 'e * 'a reason_annotations
    | Reason_die of 'd * 'a reason_annotations
    | Reason_interrupt of 'i option * 'a reason_annotations

  type ('e, 'd, 'i, 'a) cause = ('e, 'd, 'i, 'a) reason list  (* :777 *)

  type ('b, 'e, 'd, 'i, 'a) exit_ =  (* :573 *)
    | Exit_success of 'b
    | Exit_failure of ('e, 'd, 'i, 'a) cause

  type ('b, 'e, 'd, 'i, 'a) completion =  (* :574 *)
    | Completion_ofExit of ('b, 'e, 'd, 'i, 'a) exit_
    | Completion_ofRefGet of ref_key

  type err = Err_boom | Err_tag of int  (* :653 *)

  type defect =  (* :236-241 *)
    | Defect_notImplemented
    | Defect_asyncFiber
    | Defect_badName
    | Defect_missingService
    | Defect_user of int

  type val_ =  (* :208-220 *)
    | Val_unit
    | Val_bool of bool
    | Val_nat of int
    | Val_str of string
    | Val_bytes of int list
    | Val_list of val_ list
    | Val_pair of val_ * val_
    | Val_none
    | Val_some of val_
    | Val_ctor of int * val_ list
    | Val_ref of int * int list
    | Val_handle of int * int

  type stuck =  (* :651 *)
    | Stuck_unknownFiber of fiber_id
    | Stuck_unknownScope of int
    | Stuck_unknownRace of int

  type parked = Parked_notParked | Parked_withGuard of int  (* :234 *)

  type observer =  (* :353-359 *)
    | Observer_resumeAwait of fiber_id * int * observer_mode
    | Observer_untrackChild of fiber_id
    | Observer_dropScopeFinalizer of int * int
    | Observer_countdown of fiber_id * int
    | Observer_raceCallback of int
    | Observer_callback of int

  type scope_mode = ScopeMode_forkIn | ScopeMode_fiberRunIn  (* :540 *)
  type outcome = Outcome_finished | Outcome_frontier | Outcome_stuck of stuck  (* :78 *)
  type 'u service = { key : service_key; value : 'u }  (* :749 *)
  type 'u context = 'u service list  (* :778 *)

  type ctx = {  (* :235 *)
    services : val_ context;
    max_ops_before_yield : int;
    prevent_yield : bool;
  }

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim =  (* :408-426 *)
    | Prim_success of 'b
    | Prim_failure of ('e, 'd, 'i, 'a) cause
    | Prim_sync of 's
    | Prim_suspend of 's
    | Prim_withFiber of 's
    | Prim_yieldableError of 'e
    | Prim_iterator of 'nu * 'b
    | Prim_onSuccess of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu
    | Prim_onSuccessConst of
        ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | Prim_onFailure of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu
    | Prim_onSuccessAndFailure of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu * 'nu
    | Prim_exitFrame of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | Prim_onExit of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim * 'nu * bool
    | Prim_setInterruptible of bool
    | Prim_whileLoop of 'nu * 'b
    | Prim_yieldNowWith of int
    | Prim_async of 'nu * bool * 'nu option
    | Prim_asyncFinalizer of 'nu

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) frame_event =  (* :765-772 *)
    | FrameEvent_popped of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | FrameEvent_ranContAll of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | FrameEvent_pushed of ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim
    | FrameEvent_ranFinalizer of 'nu * ('b, 'e, 'd, 'i, 'a) exit_
    | FrameEvent_substituted of ('e, 'd, 'i, 'a) cause
    | FrameEvent_deferred of ('e, 'd, 'i, 'a) cause
    | FrameEvent_yielded of ('b, 'e, 'd, 'i, 'a) exit_

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task =  (* :734 *)
    | Task_start of fiber_id
    | Task_resume of fiber_id * int * 'k

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'ch, 'k, 'h) run_event =  (* :174-195 *)
    | RunEvent_forked of fiber_id * fiber_id * bool
    | RunEvent_started of fiber_id
    | RunEvent_scheduledTask of fiber_id * int * ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task
    | RunEvent_ranTask of fiber_id * ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task
    | RunEvent_yieldInjected of fiber_id * int
    | RunEvent_parkedOn of fiber_id * int
    | RunEvent_resumedWith of fiber_id * int * 'k
    | RunEvent_interruptRecorded of fiber_id option * fiber_id
    | RunEvent_interruptDeferred of fiber_id
    | RunEvent_childrenInterrupted of fiber_id * fiber_id list
    | RunEvent_observerFired of fiber_id * observer
    | RunEvent_frame of fiber_id * 'h
    | RunEvent_finalizerProgram of fiber_id * 'nu * ('b, 'e, 'd, 'i, 'a) exit_
    | RunEvent_scopeLinked of scope_mode * int * int * fiber_id
    | RunEvent_scopeClosedOnLink of int * fiber_id
    | RunEvent_raceStarted of int * fiber_id * int
    | RunEvent_raceLaunched of int * fiber_id
    | RunEvent_raceSettled of int * ('b, 'e, 'd, 'i, 'a) exit_
    | RunEvent_contextSet of fiber_id * 'ch
    | RunEvent_callback of int * ('b, 'e, 'd, 'i, 'a) exit_
    | RunEvent_exited of fiber_id * ('b, 'e, 'd, 'i, 'a) exit_

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) run_decision =  (* :69-76 *)
    | RunDecision_fire of fiber_id
    | RunDecision_flush
    | RunDecision_evaluate of fiber_id
    | RunDecision_yieldVerdict of fiber_id * bool
    | RunDecision_answerAsync of fiber_id * int * ('b, 'e, 'd, 'i, 'a) completion
    | RunDecision_interruptFrom of fiber_id option * 'a reason_annotations * fiber_id
    | RunDecision_installMiddleware

  (** The fully applied machine.  `machine`, `fiber` and `interp` are abstract: they mention
      the carriers. *)

  type machine
  type fiber
  type interp
  type program = native_op eff

  type event =
    ( nu,
      s,
      val_,
      err,
      defect,
      fiber_id,
      unit,
      ctx,
      (nu, s, val_, err, defect, fiber_id, unit) prim,
      (nu, s, val_, err, defect, fiber_id, unit) frame_event )
    run_event

  type decision = (nu, s, val_, err, defect, fiber_id, unit) run_decision

  val api_evaluate : decision
  (** `Effect4.Api.evaluate`, the first row of `Api.run`'s tape. *)

  val interp_of : program -> interp
  val load : program -> fuel:int -> choices:bool list -> machine
  val step : program -> interp -> fuel:int -> machine -> decision -> machine * bool
  val run_api : program -> fuel:int -> choices:bool list -> outcome * machine

  (** The free rows. *)

  val fibers : machine -> (fiber_id * fiber) list
  val fiber_count : machine -> int
  val trace : machine -> event list
  val trace_length : machine -> int
  val stuck_of : machine -> stuck option
  val armed_of : machine -> fiber_id list
  val next_id : machine -> int
  val next_token : machine -> int
  val race_count : machine -> int
  val middleware : machine -> bool
  val finished : machine -> bool
  val completed_exits :
    machine -> (fiber_id * (val_, err, defect, fiber_id, unit) exit_) list
  val refs : machine -> val_ list
  val next_name : machine -> int
  val due_count : machine -> int
  val cell_count : machine -> int
  val scope_count : machine -> int
  val memo_map_count : machine -> int
  val memo_paths : machine -> (int * int list list) list
  val f_id : fiber -> fiber_id
  val f_exit : fiber -> (val_, err, defect, fiber_id, unit) exit_ option
  val f_parked : fiber -> parked
  val f_running : fiber -> bool
  val f_finalizing : fiber -> bool
  val f_pending_tokens : fiber -> int list
  val f_observers : fiber -> observer list
  val f_children : fiber -> fiber_id list
  val f_op_count : fiber -> int
  val f_max_ops : fiber -> int
  val f_prevent_yield : fiber -> bool
  val f_yield_override : fiber -> bool option
  val f_context : fiber -> ctx
  val f_dispatcher_armed : fiber -> bool
  val f_dispatcher : fiber -> (int * int) list
end

(** {1 The engine} *)

module type ENGINE = sig
  val name : string
  val carriers : string

  type t
  type decision
  type program

  (** {2 The tape} *)

  val evaluate : int -> decision
  val flush : decision
  val fire : int -> decision
  val yield_verdict : int -> bool -> decision

  val answer_async_success : int -> int -> int -> decision
  (** [answer_async_success fiber token n] answers the parked token with
      `Completion.ofExit (Exit.success (Val.nat n))`. *)

  val interrupt_from : int option -> int -> decision
  val install_middleware : decision

  (** {2 Loading} *)

  val compile : Eff_types.eff -> program
  (** {!E4_program}'s conversion, behind the ordinal pin.
      @raise E4_program.Ordinal_mismatch when the alphabets disagree. *)

  val of_bytes : string -> program option
  val load_program : program -> fuel:int -> t
  val load : Eff_types.eff -> fuel:int -> t
  val load_bytes : string -> fuel:int -> t option

  (** {2 Driving} *)

  val step : t -> decision -> t

  val replay : t -> decision list -> t
  (** `Api.replay`'s machine (Api.lean:156-162): decisions are applied until the replay stops
      (EN4), and the rest of the tape is never read. *)

  val replay_to : t -> decision list -> t * decision list
  (** {!replay} beside the decisions it did NOT read: `([], …)` when the tape was spent, and
      otherwise the suffix that begins at the position the replay stopped at.  When the
      machine is stuck (`answer` = {!Refused}) the head of that suffix is the REFUSED decision
      -- Lean answers `ReplayResult.stuck why m` without applying it -- and the position of
      the refusal is `List.length tape - List.length residue`.  When the fuel ran out
      (`answer` = {!Delay}) the head is simply the next unread decision. *)

  val replay_steps : t -> decision list -> t Seq.t
  (** THE TAPE AXIS (EN4): `|tape| + 1` machines, the initial one first, position i equal to
      {!replay} of the first i decisions.  Past the stop the machine is PHYSICALLY the halted
      one — `a == b` is how a caller tells a repetition from a step — so a caller counting
      the positions a RUN has must use {!replay_positions} or {!replay_to} and not the length
      of this sequence (EN4b, lane P6's finding F1). *)

  val replay_positions : t -> decision list -> t Seq.t
  (** THE RUN AXIS (EN4b): the machines the replay actually visits, the initial one first,
      ending at the position `replayEval` stops in and repeating nothing.  It is
      `replay_steps` truncated to `|tape| - |residue| + 1` machines, and equal to it when the
      tape is spent. *)

  val drive : t -> t
  (** `Api.run`'s tape, `[evaluate root; flush]` (Api.lean:171-172). *)

  val run : Eff_types.eff -> fuel:int -> t
  val run_program : program -> fuel:int -> t

  val api_run : program -> fuel:int -> string
  (** The GENERATED `Effect4.Api.run`, unwrapped, answering only its outcome: the W1 bench
      cell, and the oracle {!run} is checked against. *)

  (** {2 Reading -- every row free} *)

  val answer : t -> answer
  val outcome : t -> string
  val exits : t -> (int * string) list
  val root_exit : t -> string option
  val fiber_rows : t -> (int * string) list
  val fiber_count : t -> int
  val trace_rows : t -> string list
  val trace_length : t -> int

  val refs : t -> string list
  (** The ref heap, ascending by cell key. *)

  val store_row : t -> string
  val snapshot : t -> t
  val fuel : t -> int
end

module Make (I : INSTANCE) : ENGINE with type program = I.program

module Fast : ENGINE
(** `Api_engine.Make(E4_table)(E4_trace)(E4_memo)(E4_buckets)`. *)

module Ref : ENGINE
(** `Api_engine.Make(E4_table_list)(E4_trace_list)(E4_memo_list)(E4_buckets_list)`: the same
    generated bodies over Lean's own carriers. *)
