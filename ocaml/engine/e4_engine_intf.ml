(* E4_engine_intf -- E4_engine's answer alphabet and its two module types, each written once.

   What it is: the `_intf` file of Jane Street's convention (`Validated_intf`, `Map_intf`).  It
   holds the declarations `E4_engine` exposes beside its implementations: the answer alphabet
   (`frontier`, `answer`), `INSTANCE` (what an instance of the generated engine supplies),
   `ENGINE` (the drive loop's face), and last `E4_engine`, the module type of the whole
   interface.  e4_engine.ml includes this module and e4_engine.mli includes `E4_engine`, so each
   declaration and its documentation is written here and nowhere else.  The component's header,
   with its behaviours EN1-EN9, stays in e4_engine.mli.

   Depends on: effect4_eff (Eff_types, Eff_wire), effect4_clock (E4_clock).

   Behaviours:
   EI1 Each module type is declared once.  e4_engine.ml includes this module and e4_engine.mli
       includes `E4_engine`, so `ocamlopt` checks the implementation against the interface
       through the same declarations.                               by construction
   EI2 Callers keep their paths: `E4_engine.ENGINE`, `E4_engine.INSTANCE`, `E4_engine.answer`
       with its constructors, `E4_engine.frontier` with its fields, `E4_engine.check_answer`,
       `E4_engine.Make`, `E4_engine.Fast` and `E4_engine.Ref`.     by construction *)

open Eff_types

(** {1 The answer alphabet} *)

(* One submodule, so that `E4_engine` re-exports the two types with their constructors and
   fields (`include module type of struct include Alphabet end`) without a second copy. *)
module Alphabet = struct
  type frontier = {
    parked : (int * int) list;  (** (fiber id, park guard token), ascending by fiber *)
    armed : int list;           (** owners with an armed dispatcher, in arming order *)
    due : int;                  (** resumes the deferred store owes right now *)
  }

  type answer =
    | Finished
    | Suspended of frontier
    | Refused of string  (** the `Stuck` constructor, spelled *)
    | Outside_profile of E4_clock.refusal
        (** a value refused at a named crossing (D9); the input machine is retained *)
    | Delay of frontier  (** the fuel ran out; the command residue is non-empty *)
end

include Alphabet

(** {1 What an instance must supply} *)

module type INSTANCE = sig
  val name : string
  val carriers : string

  (** The two payloads the projection does not descend into. *)

  type nu  (** [Effect4.Program.EffName], api_engine.ml:279 *)

  type s  (** [Effect4.Program.EffThunk], api_engine.ml:392 *)

  (** The machine-side alphabet, transcribed from api_engine.ml. The program alphabet is
      `Eff_types`, opened here and by the generated engine. `ocamlopt` checks this transcription
      against every instance: a constructor added, dropped, renamed or re-ordered in the generated file is
      a compile error here. *)

  type fiber_id = int  (* :775 *)

  type stuck =  (* :651 *)
    | Stuck_unknownFiber of fiber_id
    | Stuck_unknownScope of int
    | Stuck_unknownRace of int

  type parked = Parked_notParked | Parked_withGuard of int  (* :234 *)

  type observer =  (* :353-359 *)
    | Observer_resumeAwait of fiber_id * int * ObserverMode.t
    | Observer_untrackChild of fiber_id
    | Observer_dropScopeFinalizer of int * int
    | Observer_countdown of fiber_id * int
    | Observer_raceCallback of int
    | Observer_callback of int

  type scope_mode = ScopeMode_forkIn | ScopeMode_fiberRunIn  (* :540 *)
  type outcome = Outcome_finished | Outcome_frontier | Outcome_stuck of stuck  (* :78 *)
  type 'u service = { key : ServiceKey.t; value : 'u }  (* :749 *)
  type 'u context = 'u service list  (* :778 *)

  type ctx = {  (* :235 *)
    services : Val.t context;
    max_ops_before_yield : int;
    prevent_yield : bool;
  }

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim =  (* :408-426 *)
    | Prim_success of 'b
    | Prim_failure of ('e, 'd, 'i, 'a) Cause.t
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
    | FrameEvent_ranFinalizer of 'nu * ('b, 'e, 'd, 'i, 'a) Exit.t
    | FrameEvent_substituted of ('e, 'd, 'i, 'a) Cause.t
    | FrameEvent_deferred of ('e, 'd, 'i, 'a) Cause.t
    | FrameEvent_yielded of ('b, 'e, 'd, 'i, 'a) Exit.t

  type handle_kind =
    | HandleKind_fiber
    | HandleKind_cell
    | HandleKind_promise
    | HandleKind_scope
    | HandleKind_memoMap
    | HandleKind_external

  type wake_key = { kind : handle_kind; index : int }

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task =  (* :734 *)
    | Task_start of fiber_id
    | Task_resume of fiber_id * int * 'k
    | Task_wake of wake_key * int

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
    | RunEvent_finalizerProgram of fiber_id * 'nu * ('b, 'e, 'd, 'i, 'a) Exit.t
    | RunEvent_scopeLinked of scope_mode * int * int * fiber_id
    | RunEvent_scopeClosedOnLink of int * fiber_id
    | RunEvent_raceStarted of int * fiber_id * int
    | RunEvent_raceLaunched of int * fiber_id
    | RunEvent_raceSettled of int * ('b, 'e, 'd, 'i, 'a) Exit.t
    | RunEvent_contextSet of fiber_id * 'ch
    | RunEvent_callback of int * ('b, 'e, 'd, 'i, 'a) Exit.t
    | RunEvent_exited of fiber_id * ('b, 'e, 'd, 'i, 'a) Exit.t

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) run_decision =  (* :69-76 *)
    | RunDecision_fire of fiber_id
    | RunDecision_flush
    | RunDecision_evaluate of fiber_id
    | RunDecision_yieldVerdict of fiber_id * bool
    | RunDecision_answerAsync of fiber_id * int * ('b, 'e, 'd, 'i, 'a) Completion.t
    | RunDecision_interruptFrom of fiber_id option * 'a ReasonAnnotations.t * fiber_id
    | RunDecision_installMiddleware
    | RunDecision_advance of E4_clock.t

  (** The fully applied machine.  `machine`, `fiber` and `interp` are abstract: they mention
      the carriers. *)

  type machine
  type fiber
  type interp
  type program = NativeOp.t Eff.t

  type event =
    ( nu,
      s,
      Val.t,
      Err.t,
      Defect.t,
      fiber_id,
      unit,
      ctx,
      (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) prim,
      (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) frame_event )
    run_event

  type api_decision = (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) run_decision

  val api_evaluate : api_decision
  (** `Effect4.Api.evaluate`, the first row of `Api.run`'s tape. *)

  (** The row table: the program's host rows, as `Api.Built` carries them; `[]` for a program
      with none. *)
  val interp_of : Row.t list -> program -> interp
  val load : program -> fuel:int -> machine
  val step : Row.t list -> program -> interp -> fuel:int -> machine -> api_decision -> machine * bool
  val run_api : Row.t list -> program -> fuel:int -> outcome * machine
  (* Lean's checked replay asks this before each decision (`Effect4.Program.admit`): a stale
     token, a call that is not a host row's, a wrong answer type, a dead handle or a reserved
     defect is refused. `true` when the decision is admitted. *)
  val admit : Row.t list -> machine -> api_decision -> bool
  (* The calls the machine waits on (`Effect4.Program.awaits`): each parked fiber's token, its
     operation and its request. A host driver answers the host rows among them. *)
  type await = { fiber : fiber_id; token : int; op : NativeOp.t; request : Val.t }
  val program_awaits : machine -> await list
  (* An exit as a value (`Effect4.Machine.exitImage`), as Lean's `reifyExitVal` writes it. *)
  val reify_exit_val : (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t -> Val.t

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
    machine -> (fiber_id * (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t) list
  val refs : machine -> Val.t list
  val next_name : machine -> int
  val due_count : machine -> int
  val cell_count : machine -> int
  val scope_count : machine -> int
  val memo_map_count : machine -> int
  val memo_paths : machine -> (int * (int list * int list list) list) list
  val f_id : fiber -> fiber_id
  val f_exit : fiber -> (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t option
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
      `Completion.ofExit (Exit.success (Val.nat n))`.
      @raise E4_clock.Profile_refusal at [Reply] for a negative or out-of-profile natural. *)

  val answer_async : int -> int -> (Val.t, Err.t, Defect.t, int, unit) Completion.t -> decision
  (* [answer_async fiber token c] answers the parked token with the completion [c], a success or a
     failure, after the host-ingress check (EN9). *)

  val answer_async_value : int -> int -> Val.t -> decision
  (* [answer_async_value fiber token v] answers the parked token with `Completion.ofExit
     (Exit.success v)`, any value, after the host-ingress check every natural passes (EN9,
     {!check_answer}). Whether it fits the call's row is `admits`'s question.
     @raise E4_clock.Profile_refusal at [Reply] for an out-of-profile natural or a string that
     is not valid UTF-8 inside [v]. *)

  val answer_async_float : int -> int -> float -> decision
  (** Answers with the exact IEEE-754 bit pattern when it fits [Val.Float]'s carrier.
      @raise E4_clock.Profile_refusal at [Reply] before conversion when those bits do not fit. *)

  val interrupt_from : int option -> int -> decision
  val install_middleware : decision
  val advance : int -> decision
  val advance_exact : E4_clock.t -> decision
  (** Exact logical milliseconds. [advance] promotes a nonnegative host integer;
      [advance_exact] also accepts values above the host integer range. *)

  (** {2 Loading} *)

  val compile : Eff_wire.program -> program
  (** The program, its natural literals checked against the selected profile. The program type
      is `Eff_types`', which the LCNF route declares once for every instance.
      @raise E4_clock.Profile_refusal at [Literal] for a negative or out-of-profile natural
      literal. *)

  val of_bytes : string -> program option

  (* [?table] is the program's row table (`Api.Built.table`); [[]] when omitted, for a program
     with no host row. Every step reads it. *)
  val load_program : ?table:Row.t list -> program -> fuel:int -> t
  val load : ?table:Row.t list -> Eff_wire.program -> fuel:int -> t
  val load_bytes : ?table:Row.t list -> string -> fuel:int -> t option

  (** {2 Driving} *)

  val step : t -> decision -> t
  (* Whether Lean's checked replay (`Api.replayChecked`) admits the decision here, at the
     program's row table. `step` applies a decision either way, as `Api.replay` does; a host
     driver asks `admits` first, so a reply that does not fit its row is refused. *)
  val admits : t -> decision -> bool

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

  val run : ?table:Row.t list -> Eff_wire.program -> fuel:int -> t
  val run_program : ?table:Row.t list -> program -> fuel:int -> t

  val api_run : ?table:Row.t list -> program -> fuel:int -> string
  (** The GENERATED `Effect4.Api.run`, unwrapped, answering only its outcome: the W1 bench
      cell, and the oracle {!run} is checked against. *)

  (** {2 Reading -- every row free} *)

  val answer : t -> answer
  val outcome : t -> string
  val exits : t -> (int * string) list
  val root_exit : t -> string option
  val root_exit_of : t -> (Val.t, Err.t, Defect.t, int, unit) Exit.t option
  (* The root's exit itself, as Lean's `Run.exit` answers it; `root_exit` renders it. *)
  val host_calls : t -> (int * int * int * Val.t) list
  (* The host calls the machine waits on: (fiber, token, the row's external position, request),
     in the order of `Effect4.Program.awaits`. *)
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

(** {1 E4_engine's interface} *)

module type E4_engine = sig
  include module type of struct include Alphabet end

  (** {1 A host's answer at ingress} *)

  val check_answer : (Val.t, Err.t, Defect.t, int, unit) Completion.t -> unit
  (** EN9: every natural of a host's answer ([Api.HostSession.Answer], src/Effect4/Api/HostSession.lean)
      through [E4_clock.check_nat Reply]: [Val.nat], a [Val.ctor] index, a [Val.handle] key, a
      [Val.negInt] magnitude, [Err.tag], [Defect.user], an interrupting fiber and a [RefKey].
      Every string of the answer must be valid UTF-8, since a Lean [String] is: [Val.str], both
      strings of [Err.tagged], [Err.text] and each annotation's key. Raises
      [E4_clock.Profile_refusal] at [Reply] at the first natural outside the profile or the first
      string that is not valid UTF-8. The byte and bit-pattern fields are not read here. *)

  module type INSTANCE = INSTANCE
  module type ENGINE = ENGINE

  module Make (I : INSTANCE) : ENGINE with type program = I.program

  module Fast : ENGINE
  (** {!Make} of `Api_engine_inst`: the generated engine over the substituted carriers,
      `E4_instance.Make (E4_table) (E4_trace) (E4_memo) (E4_buckets) (E4_ppath) (E4_env)
      (E4_fibers_view)`. *)

  module Ref : ENGINE
  (** {!Make} of `Api_engine_ref`: the same generated bodies over Lean's own carriers, the
      seven list twins given to `E4_instance.Make`. *)
end
