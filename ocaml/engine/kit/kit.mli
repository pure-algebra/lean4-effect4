(** Kit — check and run Eff programs natively (hand-written face over generated code).

    What it is: the face of the native kit. Every behaviour behind it is Lean's, lowered by LCNF
    into the api closure ([Effect4_gen.Api_gen]): the checker ([Effect4.Run.Kit.check]), program and
    reply admission, the call tree at a budget and its runs ([Effect4.Run.Tree]), and each
    carrier's canonical image. The machine is the engine ([Kit_machine], [E4_host]). [run] is the
    one call: it picks the runner, as Lean's [Effect4.Run.atBudget] does, so a caller never asks
    which part of the language a program uses.
    Depends on: Eff_types, Effect4_gen.Api_gen (generated), Kit_machine, Yojson (the text).

    Behaviours it holds itself to, each by construction over the generated code:
    B1  The checker is Lean's: [check] answers what [Api.check] answers, a type or a located
        refusal, never both and never neither.
    B2  A run stops one of five ways: finished, waiting on a call the host has no reply for,
        refused (the host's reply does not fit the call's row), unsettled (the budget, the fuel or
        the rounds ended first: a finite probe, never a divergence), or stopped otherwise.
    B3  A program the call tree covers settles at the least budget whose run is not cut, checked
        (Lean's [settle_sound]); every other program runs on the machine.
    B4  A host is a reactor, the machine's own ([Run.Reactor]): a function of the call's row, its
        request and the host's state; [None] leaves the call waiting (decisions row 408 (1)).
    B5  Every reply is admitted at its call's row before it is applied (the session's reply
        admission, [Program.admitAnswer]); a reply that does not fit is not applied.
    B6  JSON is Lean's: yojson parses the text into the profile's tree ([Effect4.NatJson]), and
        Lean's lowered reader and printer do the rest ([ShapeDoc.readLocated],
        [ShapeDoc.printTree], [NatJson.render]). A carrier read from JSON is the carrier whose
        canonical print is the JSON, normalised ([ShapeDoc.readLocated_exact]); a refusal names
        its site and its reason. *)

(** {1 The carriers} *)

(** A program: the Eff tree over the native operations ([Effect4.Api.Program]). *)
type program = Eff_types.NativeOp.t Eff_types.Eff.t

(** How a program, or a host call, ends: a success with a value or a failure with a cause. *)
type exit =
  (Eff_types.Val.t, Eff_types.Err.t, Eff_types.Defect.t, int, unit) Eff_types.Exit.t

(** A host's answer to a call. *)
type completion =
  (Eff_types.Val.t, Eff_types.Err.t, Eff_types.Defect.t, int, unit) Eff_types.Completion.t

(** An application: its host rows, its service declarations and its named types ([SigApp]). *)
type app = Effect4_gen.Api_gen.sig_app

(** The application of these rows and services; with neither, the empty one. *)
val app
  :  ?rows:Eff_types.Row.t list
  -> ?services:(Eff_types.ServiceKey.t * Eff_types.Ty.t) list
  -> unit
  -> app

(** A success with this value. *)
val succeed : Eff_types.Val.t -> exit

(** A failure with this error value: the cause [Cause.fail (errOf v)], as a host writes one. *)
val fail : Eff_types.Val.t -> exit

(** {1 Checking} *)

(** The checker's answer: the program's type at the application ([Effect<A, E, R>]), or the
    address of the refusing node and why ([Api.check]). *)
val check
  :  app
  -> program
  -> ( Eff_types.EffTy.t
       , (int list, Effect4_gen.Api_gen.type_reason) Effect4_gen.Api_gen.located )
       result

(** Program admission ([Program.admitProgram]) beyond typing: the application's own admission
    (each row's registration and kind, its key, the service declarations) and the program's
    empty columns. [None] when admitted. Raw formation is not decided natively (the note's
    finding 4). *)
val admit : app -> program -> Effect4_gen.Api_gen.admit_refusal option

(** A type's TypeScript spelling ([Ty.render]). *)
val ty_text : Eff_types.Ty.t -> string

(** {1 Hosts} *)

(** A host: the call's row, its request and the host's state, to an answer and the next state;
    [None] leaves the call waiting. Lean's [Run.Reactor], and [E4_host]'s provider. *)
type 's reactor = Eff_types.Row.t -> Eff_types.Val.t -> 's -> (completion * 's) option

module Reactor : sig
  (** Answers no call: every call waits. *)
  val silent : unit reactor

  (** Each call takes the tape's next exit, whatever its row; an empty tape waits. *)
  val tape : exit list reactor

  (** A host by row name: each named row's function answers its calls; a row with no function,
      or a function that answers [None], waits. *)
  val by_name : (string * (Eff_types.Val.t -> exit option)) list -> unit reactor

  (** The first reactor that answers. *)
  val first : 's reactor list -> 's reactor

  (** The same reactor, counting the calls it answered. *)
  val counted : 's reactor -> ('s * int) reactor
end

(** {1 Running} *)

type reply_fault = Effect4_gen.Api_gen.reply_fault =
  | ReplyFault_answerType of Eff_types.Ty.t
  (** a success whose value is no member of the row's answer type *)
  | ReplyFault_errorType of Eff_types.Ty.t
  (** a failure with a reason outside the row's error column *)
  | ReplyFault_reservedDefect
  (** a failure carrying one of the machine's markers of malformed code *)

type stop =
  | Finished of exit (** the program ended with this exit *)
  | Waiting of int * Eff_types.Val.t
  (** the host has no reply for a call of this row with this request *)
  | Refused of int * Eff_types.Val.t * exit * reply_fault option
  (** the host's reply to this call does not fit the row: the fault, or [None] when the
          engine refused a reply the kit admits *)
  | Unsettled
  (** the budget, the fuel or the rounds ended first: a finite probe, not a divergence *)
  | Stopped of string
  (** the machine stopped otherwise: suspended on a timer, stuck, a raise *)

type step = Effect4_gen.Api_gen.step =
  | Step_called of int * Eff_types.Val.t * exit
  (** a host call: its row, its request, its reply *)
  | Step_celled of Effect4_gen.Api_gen.sync_op * Eff_types.Val.t
  (** a cell operation and its value *)

(** How one run went: its steps in order and how it stopped. The machine's trace holds its host
    calls alone; the call tree's holds its cell operations too. *)
type trace =
  { steps : step list
  ; stop : stop
  }

(** A trace's host calls, in order. *)
val calls : trace -> (int * Eff_types.Val.t * exit) list

(** A trace's replies, in call order: a reply tape that replays it. *)
val tape_of : trace -> exit list

type 's report =
  { by_tree : bool (** the call tree answered; otherwise the machine *)
  ; budget : int option (** the least budget whose tree run is not cut *)
  ; trace : trace (** the run *)
  ; state : 's (** the reactor's state at the end *)
  ; frames : trace list (** the tree's runs at budgets 0 up to [budget], when asked for *)
  ; agrees : bool option
    (** for a settled tree run: whether the machine's run of it is the same *)
  }

(** {b Run a program}: as its call tree when the tree covers it, settling at the least budget
    up to [limit] (default 1024) that does not cut it; otherwise on the machine, [limit] its
    rounds. [frames] returns the tree's runs at every budget up to the one it settled at, or up
    to [limit] when it did not. [check] (default [true]) runs a settled tree run on the machine
    too and says whether the two agree. Every reply is admitted at its row. *)
val run
  :  ?limit:int
  -> ?frames:bool
  -> ?check:bool
  -> app
  -> 's reactor
  -> 's
  -> program
  -> 's report

(** {1 Every path} *)

(** A few small members of a type under the application's named types ([Kit.samples]). *)
val samples : app -> Eff_types.Ty.t -> Eff_types.Val.t list

(** The replies a row can give, drawn from its types, each one reply admission takes. *)
val replies : app -> int -> exit list

(** Why a reply does not fit the row at this position, or [None] when it fits
    ([Kit.replyFault]). *)
val reply_fault : app -> int -> exit -> reply_fault option

(** Every path of the program's call tree at the budget, its replies drawn from the rows' types,
    the first [width]; or, for a program the tree does not cover, the address of its first node
    outside it. *)
val explore : app -> budget:int -> width:int -> program -> (trace list, int list) result

(** Whether the machine, under the trace's tape, makes the same calls and stops the same way;
    [None] for a trace the budget cut. *)
val replays : app -> program -> trace -> bool option

(** {1 JSON} *)

(** The version of the carriers' formats: the shape documents of [Effect4.Run.Kit]
    ([admitShape] to [valShape], src/Effect4/Run/Kit.lean) that {!Json} prints and reads by,
    pinned by digest in engine/test/kit/test_shapes.ml, which reads this number. The rule: a
    change to any of those shapes moves this number up by one and the test's pins with it, in
    one commit. *)
val format_version : int

module Json : sig
  (** The profile's JSON tree ([Effect4.NatJson]): a number is a natural, and a number the tree
      does not hold as one (a negative number, a fraction, a natural past the host's integers) is
      a numeral with its text, which every reader refuses at its place. *)
  type t = Effect4_gen.Api_gen.nat_json =
    | NatJson_null
    | NatJson_bool of bool
    | NatJson_nat of int
    | NatJson_numeral of string
    | NatJson_str of string
    | NatJson_arr of t list
    | NatJson_obj of (string * t) list

  (** A refusal of the profile's reader: a reason at a site ([Store.JsonRefusal]). *)
  type refusal =
    ( Effect4_gen.Api_gen.json_site
      , Effect4_gen.Api_gen.json_reason )
      Effect4_gen.Api_gen.located

  (** The tree of one JSON text, or why it is none. yojson parses it ([Yojson.Raw], so each
      number keeps its text); a yojson extension (a tuple, a variant, NaN, Infinity) or a string
      that is not UTF-8 is refused. yojson's acceptance is the text's: it also skips comments. *)
  val parse : string -> (t, string) result

  (** The tree of a yojson value whose literals are raw, as [parse] makes it. *)
  val of_raw : Yojson.Raw.t -> (t, string) result

  (** The compact text: Lean's [NatJson.render], lowered. *)
  val render : t -> string

  (** A value tree from JSON under a shape document: Lean's located reader, lowered
      ([ShapeDoc.readLocated]). *)
  val read : Effect4_gen.Api_gen.shape_doc -> t -> (Eff_types.Val.t, refusal) result

  (** A value tree as JSON under a shape document, each list family as an array: Lean's printer,
      lowered ([ShapeDoc.printTree]). *)
  val print : Effect4_gen.Api_gen.shape_doc -> Eff_types.Val.t -> t

  (** A program from its JSON print (the session tool's form), objects in any order. *)
  val program : t -> program option

  val program_json : program -> t
  val rows : t -> Eff_types.Row.t list option
  val rows_json : Eff_types.Row.t list -> t
  val services : t -> (Eff_types.ServiceKey.t * Eff_types.Ty.t) list option

  (** A reply tape: an array of exits. *)
  val exits : t -> exit list option

  val exit_json : exit -> t
  val value_json : Eff_types.Val.t -> t
  val ty_json : Eff_types.Ty.t -> t
  val eff_ty_json : Eff_types.EffTy.t -> t

  val refusal_json
    :  (int list, Effect4_gen.Api_gen.type_reason) Effect4_gen.Api_gen.located
    -> t

  val admit_json : Effect4_gen.Api_gen.admit_refusal -> t

  (** The checker's answer, then admission's: [{"status":"ok","type":…,"text":"Effect<A, E>"}],
      [{"status":"refused","refusal":…}] (typing, located) or
      [{"status":"refused","admission":…}]. *)
  val check_json : app -> program -> t

  (** How a run stopped, as an answer's fields: its "status" and what the status names. *)
  val stop_json : app -> stop -> (string * t) list

  (** A trace: how it stopped, its calls (each row by position and name) and its tape. *)
  val trace_json : app -> trace -> t

  (** A run: its trace, the budget it settled at, which runner answered, the machine's
      agreement, and the frames. *)
  val report_json : app -> 's report -> t
end

(** {1 Bytes} *)

(** A program from its canonical bytes, exactly ([Eff_wire.decode_eff_exact]). *)
val program_of_bytes : string -> program option

(** A program's canonical bytes. *)
val program_bytes : program -> string
