(* E4_engine_intf -- E4_engine's answer alphabet and its two module types, each written once.

   What it is: the `_intf` file of Jane Street's convention (`Validated_intf`, `Map_intf`).  It
   holds the declarations `E4_engine` exposes beside its implementations: the answer alphabet
   (`frontier`, `answer`), `INSTANCE` (what an instance of the generated engine supplies),
   `ENGINE` (the drive loop's face), and last `E4_engine`, the module type of the whole
   interface.  e4_engine.ml includes this module and e4_engine.mli includes `E4_engine`, so each
   declaration and its documentation is written here and nowhere else.  The component's header,
   with its behaviours EN1-EN9, stays in e4_engine.mli.

   Depends on: effect4_eff (Eff_types, Eff_codec), effect4_lcnf (Lcnf_crossing), Zarith (Z).

   Behaviours:
   EI1 Each module type is declared once.  e4_engine.ml includes this module and e4_engine.mli
       includes `E4_engine`, so `ocamlopt` checks the implementation against the interface
       through the same declarations.                               by construction
   EI2 Callers keep their paths: `E4_engine.ENGINE`, `E4_engine.INSTANCE`, `E4_engine.answer`
       with its constructors, `E4_engine.frontier` with its fields, `E4_engine.outside` with its
       constructors, `E4_engine.Make` and `E4_engine.Fast`.        by construction
   EI3 The machine's naturals are Zarith's `Z.t`, as the generated alphabet spells every Lean
       `Nat` (M4): `INSTANCE` transcribes them so. A count the host reads (a cardinal, a
       length) is an `int`, narrowed once in the instance.               by construction *)

open Eff_types

(** {1 The answer alphabet} *)

(* One submodule, so that `E4_engine` re-exports the two types with their constructors and
   fields (`include module type of struct include Alphabet end`) without a second copy. *)
module Alphabet = struct
  type frontier =
    { parked : (int * int) list (** (fiber id, park guard token), ascending by fiber *)
    ; armed : int list (** owners with an armed dispatcher, in arming order *)
    ; due : int (** resumes the deferred store owes right now *)
    }

  type answer =
    | Finished
    | Suspended of frontier
    | Refused of string (** the `Stuck` constructor, spelled *)
    | Outside_profile of Lcnf_crossing.refusal
    (** a value refused at a named crossing (D9); the input machine is retained *)
    | Delay of frontier (** the fuel ran out; the command residue is non-empty *)

  (** Lean's profile-support refusal ([Effect4.Program.ProfileRefusal],
      src/Effect4/Program/ProfileSupport.lean): a number outside the profile's bound, at its path
      in a value tree, or at the address of the program node whose literal it is. *)
  type profile_refusal = (Z.t list, ProfileReason.t) Located.t

  (** Why a value is outside the profile (DI-56; decisions row 408 (2)). *)
  type outside =
    | Unsupported of profile_refusal
    (** Lean's profile support refused it at ingress, at the selected profile ([rc112]):
            a host's answer ([ProfileData.valueRefusal] over its value tree) or a program's
            literal ([ProfileData.literalRefusal]), lowered *)
    | Not_a_value
    (** a host's answer is no Lean value: a natural below zero, a byte outside 0..255 or a
            string that is not UTF-8 ([Eff_val.valid] over its value tree). Lean's judgments
            cannot ask, since a Lean value has no such shape *)
    | Crossing of Lcnf_crossing.refusal
    (** a step's crossing refused a value the step computed ([Lcnf_crossing]): an exponent,
            a shift or an index past the target's [int]. The run's arithmetic is exact since
            M4 *)
end

include Alphabet

(** {1 What an instance must supply} *)

module type INSTANCE = sig
  val name : string
  val carriers : string

  (** The two payloads the projection does not descend into. *)

  (** [Effect4.Program.EffName]; [eff_name] in ocaml/engine/api_engine.ml. *)
  type nu

  (** [Effect4.Program.EffThunk]; [eff_thunk] in ocaml/engine/api_engine.ml. *)
  type s

  (** The machine-side alphabet, transcribed from api_engine.ml. The program alphabet is
      `Eff_types`, opened here and by the generated engine. `ocamlopt` checks this transcription
      against every instance: a constructor added, dropped, renamed or re-ordered in the generated file is
      a compile error here. *)

  type fiber_id = Z.t (* fiber_id (ocaml/engine/api_engine.ml) *)

  type stuck =
    (* stuck (ocaml/engine/api_engine.ml) *)
    | Stuck_unknownFiber of fiber_id
    | Stuck_unknownScope of Z.t
    | Stuck_unknownRace of Z.t

  type parked =
    | Parked_notParked
    | Parked_withGuard of Z.t (* parked (ocaml/engine/api_engine.ml) *)

  type observer =
    (* observer (ocaml/engine/api_engine.ml) *)
    | Observer_resumeAwait of fiber_id * Z.t * ObserverMode.t
    | Observer_untrackChild of fiber_id
    | Observer_dropScopeFinalizer of Z.t * Z.t
    | Observer_countdown of fiber_id * Z.t
    | Observer_raceCallback of Z.t
    | Observer_callback of Z.t

  type scope_mode =
    | ScopeMode_forkIn
    | ScopeMode_fiberRunIn (* scope_mode (ocaml/engine/api_engine.ml) *)

  type outcome =
    | Outcome_finished
    | Outcome_frontier
    | Outcome_stuck of stuck (* outcome (ocaml/engine/api_engine.ml) *)

  type 'u service =
    { key : ServiceKey.t
    ; value : 'u
    }

  (* service (ocaml/engine/api_engine.ml) *)
  type 'u context = 'u service list (* context (ocaml/engine/api_engine.ml) *)

  type ctx =
    { (* ctx (ocaml/engine/api_engine.ml) *)
      services : Val.t context
    ; max_ops_before_yield : Z.t
    ; prevent_yield : bool
    }

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) prim =
    (* prim (ocaml/engine/api_engine.ml) *)
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
    | Prim_yieldNowWith of Z.t
    | Prim_async of 'nu * bool * 'nu option
    | Prim_asyncFinalizer of 'nu

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) frame_event =
    (* frame_event (ocaml/engine/api_engine.ml) *)
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

  type wake_key =
    { kind : handle_kind
    ; index : Z.t
    }

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task =
    (* task (ocaml/engine/api_engine.ml) *)
    | Task_start of fiber_id
    | Task_resume of fiber_id * Z.t * 'k
    | Task_wake of wake_key * Z.t

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'ch, 'k, 'h) run_event =
    (* run_event (ocaml/engine/api_engine.ml) *)
    | RunEvent_forked of fiber_id * fiber_id * bool
    | RunEvent_started of fiber_id
    | RunEvent_scheduledTask of fiber_id * Z.t * ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task
    | RunEvent_ranTask of fiber_id * ('nu, 's, 'b, 'e, 'd, 'i, 'a, 'k) task
    | RunEvent_yieldInjected of fiber_id * Z.t
    | RunEvent_parkedOn of fiber_id * Z.t
    | RunEvent_resumedWith of fiber_id * Z.t * 'k
    | RunEvent_interruptRecorded of fiber_id option * fiber_id
    | RunEvent_interruptDeferred of fiber_id
    | RunEvent_childrenInterrupted of fiber_id * fiber_id list
    | RunEvent_observerFired of fiber_id * observer
    | RunEvent_frame of fiber_id * 'h
    | RunEvent_finalizerProgram of fiber_id * 'nu * ('b, 'e, 'd, 'i, 'a) Exit.t
    | RunEvent_scopeLinked of scope_mode * Z.t * Z.t * fiber_id
    | RunEvent_scopeClosedOnLink of Z.t * fiber_id
    | RunEvent_raceStarted of Z.t * fiber_id * Z.t
    | RunEvent_raceLaunched of Z.t * fiber_id
    | RunEvent_raceSettled of Z.t * ('b, 'e, 'd, 'i, 'a) Exit.t
    | RunEvent_contextSet of fiber_id * 'ch
    | RunEvent_callback of Z.t * ('b, 'e, 'd, 'i, 'a) Exit.t
    | RunEvent_exited of fiber_id * ('b, 'e, 'd, 'i, 'a) Exit.t

  type ('nu, 's, 'b, 'e, 'd, 'i, 'a) run_decision =
    (* run_decision (ocaml/engine/api_engine.ml) *)
    | RunDecision_fire of fiber_id
    | RunDecision_flush
    | RunDecision_evaluate of fiber_id
    | RunDecision_yieldVerdict of fiber_id * bool
    | RunDecision_answerAsync of fiber_id * Z.t * ('b, 'e, 'd, 'i, 'a) Completion.t
    | RunDecision_interruptFrom of fiber_id option * 'a ReasonAnnotations.t * fiber_id
    | RunDecision_installMiddleware
    | RunDecision_advance of Z.t

  (** The fully applied machine.  `machine`, `fiber` and `interp` are abstract: they mention
      the carriers. *)

  type machine
  type fiber
  type interp
  type prepared
  type program = NativeOp.t Eff.t

  type event =
    ( nu
      , s
      , Val.t
      , Err.t
      , Defect.t
      , fiber_id
      , unit
      , ctx
      , (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) prim
      , (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) frame_event )
      run_event

  type api_decision = (nu, s, Val.t, Err.t, Defect.t, fiber_id, unit) run_decision

  (** `Effect4.Api.evaluate`, the first row of `Api.run`'s tape. *)
  val api_evaluate : api_decision

  (** The row table: the program's host rows, as `Api.Built` carries them; `[]` for a program
      with none. *)
  val interp_of : Row.t list -> program -> interp

  val prepare : Row.t list -> program -> prepared
  val load : program -> fuel:Z.t -> machine
  val step : prepared -> fuel:Z.t -> machine -> api_decision -> machine * bool
  val run_api : Row.t list -> program -> fuel:Z.t -> outcome * machine

  (* Lean's checked replay asks this before each decision (`Effect4.Program.admit`): a stale
     token, a call that is not a host row's, a wrong answer type, a dead handle or a reserved
     defect is refused. `true` when the decision is admitted. *)
  val admit : prepared -> machine -> api_decision -> bool

  (* The calls the machine waits on (`Effect4.Program.awaits`): each parked fiber's token, its
     operation and its request. A host driver answers the host rows among them. *)
  type await =
    { fiber : fiber_id
    ; token : Z.t
    ; op : NativeOp.t
    ; request : Val.t
    }

  val program_awaits : machine -> await list

  (* An exit as a value (`Effect4.Machine.exitImage`), as Lean's `reifyExitVal` writes it. *)
  val reify_exit_val : (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t -> Val.t

  (** Profile support (src/Effect4/Program/ProfileSupport.lean), lowered: the profile as data
      ([Effect4.Program.ProfileData]), rc.112's ([rc112]), a host's answer as one value tree
      ([answerTree]), and the judgment over a value and over a program's literals
      ([ProfileData.valueRefusal], [ProfileData.literalRefusal]). *)
  type profile_data

  val program_rc112 : profile_data
  val program_answer_tree : (Val.t, Err.t, Defect.t, fiber_id, unit) Completion.t -> Val.t

  val program_profile_data_value_refusal
    :  profile_data
    -> Val.t
    -> (Z.t list, ProfileReason.t) Located.t option

  val program_profile_data_literal_refusal
    :  profile_data
    -> program
    -> (Z.t list, ProfileReason.t) Located.t option

  (** The free rows. A count is the host's [int] (EI3); every other number is the machine's
      natural. *)

  val fibers : machine -> (fiber_id * fiber) list
  val fiber_count : machine -> int
  val trace : machine -> event list
  val trace_length : machine -> int
  val stuck_of : machine -> stuck option
  val armed_of : machine -> fiber_id list
  val next_id : machine -> Z.t
  val next_token : machine -> Z.t
  val race_count : machine -> int
  val middleware : machine -> bool
  val finished : machine -> bool

  val completed_exits
    :  machine
    -> (fiber_id * (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t) list

  val refs : machine -> Val.t list
  val next_name : machine -> Z.t
  val due_count : machine -> int
  val cell_count : machine -> int
  val scope_count : machine -> int
  val memo_map_count : machine -> int
  val memo_paths : machine -> (Z.t * (Z.t list * Z.t list list) list) list
  val f_id : fiber -> fiber_id
  val f_exit : fiber -> (Val.t, Err.t, Defect.t, fiber_id, unit) Exit.t option
  val f_parked : fiber -> parked
  val f_running : fiber -> bool
  val f_finalizing : fiber -> bool
  val f_pending_tokens : fiber -> Z.t list
  val f_observers : fiber -> observer list
  val f_children : fiber -> fiber_id list
  val f_op_count : fiber -> Z.t
  val f_max_ops : fiber -> Z.t
  val f_prevent_yield : fiber -> bool
  val f_yield_override : fiber -> bool option
  val f_context : fiber -> ctx
  val f_dispatcher : fiber -> (Z.t * int) list
end

(** {1 The engine} *)

module type ENGINE = sig
  val name : string
  val carriers : string

  type t
  type decision

  (** The one program type of the wire and every instance (`Eff_types`, the LCNF route's): a
      program crosses with no conversion. *)
  type program = NativeOp.t Eff.t

  (** {2 The tape} *)

  val evaluate : int -> decision
  val flush : decision
  val fire : int -> decision
  val yield_verdict : int -> bool -> decision

  (** [answer_async_success fiber token n] answers the parked token with
      `Completion.ofExit (Exit.success (Val.nat n))`. A constructor: the answer's ingress is
      {!ingress}'s question. *)
  val answer_async_success : int -> int -> int -> decision

  val answer_async
    :  int
    -> int
    -> (Val.t, Err.t, Defect.t, Z.t, unit) Completion.t
    -> decision
  (* [answer_async fiber token c] answers the parked token with the completion [c], a success or a
     failure. A constructor: a host driver asks {!ingress} first (EN9). *)

  val answer_async_value : int -> int -> Val.t -> decision
  (* [answer_async_value fiber token v] answers the parked token with `Completion.ofExit
     (Exit.success v)`, any value. Whether it crosses is {!ingress}'s question, and whether it
     fits the call's row is `admits`'s. *)

  val interrupt_from : int option -> int -> decision
  val install_middleware : decision
  val advance : int -> decision

  (** Exact logical milliseconds, a Lean natural. [advance] promotes a nonnegative host integer
      and raises [Invalid_argument] on a negative one, which no duration is; [advance_exact]
      takes the natural itself, past the host integer range too. *)
  val advance_exact : Z.t -> decision

  (** {2 Ingress} *)

  (** Profile support of a program at the selected profile ([rc112]): Lean's
      [ProfileData.literalRefusal], lowered. [None] when the profile supports every natural
      literal the program states; otherwise the first literal above the bound, at the address
      of its node (EN8). A host driver asks it before {!load}. *)
  val literal_refusal : program -> profile_refusal option

  (** A host's answer at ingress (decisions row 394 (1), EN9): [None] when it crosses. It is
      [Not_a_value] when its value tree ([answerTree], lowered) is no Lean value
      ([Eff_val.valid]), and [Unsupported] when Lean's profile support refuses that tree at
      the selected profile ([ProfileData.valueRefusal] at [rc112], lowered). Never [Crossing].
      A host driver asks it before {!admits}. *)
  val ingress : (Val.t, Err.t, Defect.t, Z.t, unit) Completion.t -> outside option

  (** {2 Loading} *)

  (** A program from its canonical bytes, exactly: Lean's reading, lowered
      ([Eff_codec.decode_program], `Wire.decodeProgram`). *)
  val of_bytes : string -> program option

  (* [?table] is the program's row table (`Api.Built.table`); [[]] when omitted, for a program
     with no host row. Every step reads it. *)
  val load_program : ?table:Row.t list -> program -> fuel:int -> t
  val load : ?table:Row.t list -> program -> fuel:int -> t

  (** {2 Driving} *)

  val step : t -> decision -> t

  (* Whether Lean's checked replay (`Api.replayChecked`) admits the decision here, at the
     program's row table. `step` applies a decision either way, as `Api.replay` does; a host
     driver asks `admits` first, so a reply that does not fit its row is refused. *)
  val admits : t -> decision -> bool

  (** `Api.replay`'s machine (replay (src/Effect4/Api.lean)): decisions are applied until the replay stops
      (EN4), and the rest of the tape is never read. *)
  val replay : t -> decision list -> t

  (** {!replay} beside the decisions it did NOT read: `([], …)` when the tape was spent, and
      otherwise the suffix that begins at the position the replay stopped at.  When the
      machine is stuck (`answer` = {!Refused}) the head of that suffix is the REFUSED decision
      -- Lean answers `ReplayResult.stuck why m` without applying it -- and the position of
      the refusal is `List.length tape - List.length residue`.  When the fuel ran out
      (`answer` = {!Delay}) the head is simply the next unread decision. *)
  val replay_to : t -> decision list -> t * decision list

  (** THE TAPE AXIS (EN4): `|tape| + 1` machines, the initial one first, position i equal to
      {!replay} of the first i decisions.  Past the stop the machine is PHYSICALLY the halted
      one — `a == b` is how a caller tells a repetition from a step — so a caller counting
      the positions a RUN has must use {!replay_positions} or {!replay_to} and not the length
      of this sequence (EN4b, lane P6's finding F1). *)
  val replay_steps : t -> decision list -> t Seq.t

  (** THE RUN AXIS (EN4b): the machines the replay actually visits, the initial one first,
      ending at the position `replayEval` stops in and repeating nothing.  It is
      `replay_steps` truncated to `|tape| - |residue| + 1` machines, and equal to it when the
      tape is spent. *)
  val replay_positions : t -> decision list -> t Seq.t

  (** `Api.run`'s tape, `[evaluate root; flush]` (run (src/Effect4/Api.lean)). *)
  val drive : t -> t

  val run : ?table:Row.t list -> program -> fuel:int -> t
  val run_program : ?table:Row.t list -> program -> fuel:int -> t

  (** The GENERATED `Effect4.Api.run`, unwrapped, answering only its outcome: the W1 bench
      cell, and the oracle {!run} is checked against. *)
  val api_run : ?table:Row.t list -> program -> fuel:int -> string

  (** {2 Reading -- every row free} *)

  val answer : t -> answer
  val outcome : t -> string
  val exits : t -> (int * string) list
  val root_exit : t -> string option
  val root_exit_of : t -> (Val.t, Err.t, Defect.t, Z.t, unit) Exit.t option

  (* The root's exit itself, as Lean's `Run.exit` answers it; `root_exit` renders it. *)
  val host_calls : t -> (int * int * int * Val.t) list

  (* The host calls the machine waits on: (fiber, token, the row's external position, request),
     in the order of `Effect4.Program.awaits`. *)
  val fiber_rows : t -> (int * string) list
  val fiber_count : t -> int
  val trace_rows : t -> string list
  val trace_length : t -> int

  (** The ref heap, ascending by cell key. *)
  val refs : t -> string list

  val store_row : t -> string
  val snapshot : t -> t
  val fuel : t -> int
end

(** {1 E4_engine's interface} *)

module type E4_engine = sig
  include module type of struct
    include Alphabet
  end

  (** {1 Outside the profile} *)

  (** The refusal as a report spells it: the number and its path, the value that is no Lean
      value, or the crossing's text ([Lcnf_crossing.refusal_text]). *)
  val outside_text : outside -> string

  module type INSTANCE = INSTANCE
  module type ENGINE = ENGINE

  module Make (I : INSTANCE) : ENGINE with type program = I.program

  (** {!Make} of `Api_engine_inst`: the generated engine over the substituted carriers,
      `E4_instance.Make (E4_table) (E4_trace) (E4_memo) (E4_buckets) (E4_ppath) (E4_env)
      (E4_fibers_view)`. *)
  module Fast : ENGINE
end
