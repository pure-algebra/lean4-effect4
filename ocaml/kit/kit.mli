(** Kit — check, run and watch Eff programs natively (hand-written face over generated code).

    What it is: the face of the native kit. Every behaviour behind it is Lean's, lowered by LCNF
    into [Kit_gen]: the checker ([Effect4.Run.Kit.check], [Api.check]), the call tree of a
    program at a budget and its runs ([Effect4.Run.Tree], [probe], [settle], [frames]), and each
    carrier's canonical image. This module names them, gives hosts as plain closures, and reads and
    prints every carrier as JSON through its shape ([Kit_json]).
    Depends on: Eff_types, Kit_gen (generated), Kit_json.

    Behaviours it holds itself to, each by construction over the generated code:
    B1  The checker is Lean's: [check] answers what [Api.check] answers, a type or a located
        refusal, never both and never neither.
    B2  A run's stop is one of three: the program finished, the budget cut it, or a call waits on
        the host. A cut is never reported as a failure, and never as a divergence.
    B3  [settle] answers the least budget whose run is not cut, with that run, checked: the
        answer is the probe at the budget it names (Lean's [settle_sound]). Under the declared
        fact [ofProgram_approx], that run is the run at every larger budget.
    B4  A host is a function of the row's position, the request and the host's own state. [None]
        leaves the call waiting, a frontier (decisions row 408 (1)).
    B5  JSON reads exactly: a carrier read from JSON is the carrier whose value tree the JSON
        prints, or nothing. *)

(** {1 The carriers} *)

type program = Eff_types.native_op Eff_types.eff
(** A program: the Eff tree over the native operations ([Effect4.Api.Program]). *)

type exit = (Eff_types.val_, Eff_types.err, Eff_types.defect, int, unit) Eff_types.exit_
(** How a program, or a host call, ends: a success with a value or a failure with a cause. *)

type app = Kit_gen.sig_app
(** An application: its host rows, its service declarations and its named types ([SigApp]). *)

val app : ?rows:Eff_types.row list -> ?services:(Eff_types.service_key * Eff_types.ty) list -> unit -> app
(** The application of these rows and services; with neither, the empty one. *)

val succeed : Eff_types.val_ -> exit
(** A success with this value. *)

val fail : Eff_types.val_ -> exit
(** A failure with this error value: the cause [Cause.fail (errOf v)], as a host writes one. *)

(** {1 Checking} *)

val check : app -> program -> (Eff_types.eff_ty, Kit_gen.type_refusal) result
(** The checker's answer: the program's type at the application ([Effect<A, E, R>]), or the
    address of the refusing node and why ([Api.check]). *)

val admit : app -> program -> Kit_gen.admit_refusal option
(** Program admission ([Program.admitProgram]): what typing does not read, the application's own
    admission (each row's registration and kind, its key, the service declarations), the raw
    formation of the program's types and its empty columns. [None] when admitted. A row the host
    answers is asynchronous and externally registered ([Kit_author.row] writes one). *)

val ty_text : Eff_types.ty -> string
(** A type's TypeScript spelling ([Ty.render]). *)

val outside : program -> int list option
(** The address of the first node the call tree has no arm for (a fork, a scope, a service, a
    layer, a generator, a mask), in program order; [None] when the tree runs the whole program.
    Such a program runs on the machine ([Effect4.Run.runWith]). *)

(** {1 Reply admission} *)

type reply_fault = Kit_gen.reply_fault =
  | ReplyFault_answerType of Eff_types.ty  (** a success whose value is no member of the row's answer type *)
  | ReplyFault_errorType of Eff_types.ty  (** a failure with a reason outside the row's error column *)
  | ReplyFault_reservedDefect  (** a failure carrying one of the machine's markers of malformed code *)

val reply_fault : app -> int -> exit -> reply_fault option
(** Why a reply does not fit the row of its call, as the session's reply admission reads it
    ([Program.admitAnswer]); [None] when it fits. *)


(** {1 Hosts} *)

type 's host = int -> Eff_types.val_ -> 's -> (exit * 's) option
(** A host: a row's reply to a request, from the host's own state; [None] leaves the call
    waiting. *)

module Host : sig
  val silent : unit host
  (** Answers no call: every call waits. *)

  val tape : exit list host
  (** Each call takes the tape's next exit, whatever its row; an empty tape waits. *)

  val pure : (int -> Eff_types.val_ -> exit option) -> unit host
  (** A host that keeps no state. *)

  val rows : app -> (string * (Eff_types.val_ -> exit option)) list -> unit host
  (** A host by row name: each named row's function answers its calls; a row with no function,
      or a function that answers [None], waits. *)

  val first : 's host list -> 's host
  (** The first host that answers. *)

  val counted : 's host -> ('s * int) host
  (** The same host, counting the calls it answered. *)

  val guarded : app -> 's host -> 's host
  (** The same host, each reply admitted at its call's row ([reply_fault]): a reply that does not
      fit is not applied, so the call waits (decisions row 408). [wait_reason] says why. *)
end

(** {1 Runs} *)

type stop = Kit_gen.stop =
  | Stop_finished of exit  (** the program ended with this exit *)
  | Stop_cut  (** the budget ended first: a finite probe, never a divergence *)
  | Stop_waiting of int * Eff_types.val_  (** a call of this row, with this request, waits on the host *)

type step = Kit_gen.step =
  | Step_called of int * Eff_types.val_ * exit  (** a host call: row, request, the reply's exit *)
  | Step_celled of Kit_gen.sync_op * Eff_types.val_  (** a cell operation and its value *)

type 's run = 's Kit_gen.outcome = {
  steps : step list;  (** in order *)
  stop : stop;
  stores : Kit_gen.stores;  (** the cells it left *)
  state : 's;  (** the host's state it left *)
}

val probe : app -> budget:int -> 's host -> 's -> program -> 's run
(** The run of the program's call tree at the budget: every loop tests at most [budget] times,
    and calls of definitions nest at most [budget] deep. *)

type 's settled =
  | Settled of { budget : int; run : 's run }
      (** the least budget whose run is not cut, and that run: it finishes or waits *)
  | Unsettled of { limit : int; last : 's run }
      (** the run is cut at every budget up to [limit]: not yet known, never "diverges" *)

val settle : ?limit:int -> app -> 's host -> 's -> program -> 's settled
(** Probe budgets up to [limit] (default 1024) by doubling and bisection, about [2 log limit]
    probes, for the least budget whose run is not cut. *)

val frames : app -> limit:int -> 's host -> 's -> program -> 's run list
(** The run at each budget from [0] to [limit]. A frame never takes back a step of the one
    before, so a view plays the frames as one growing run. *)

val calls : 's run -> (int * Eff_types.val_ * exit) list
(** The host calls of a run, in order. *)

type wait =
  | No_answer  (** the host has no answer for the call *)
  | Refused of exit * reply_fault  (** the host's answer does not fit the call's row *)

val wait_reason : app -> 's host -> 's run -> wait option
(** Why a waiting run waits: the host (unguarded) asked again at the waiting call, from the
    state the run left; a host is a function of its state, so this is the answer it gave.
    [None] when the run does not wait. *)

(** {1 JSON} *)

module Json : sig
  type t = Eff_json_text.t

  val parse : string -> (t, string) result
  val render : t -> string

  val program : t -> program option
  (** A program from its JSON print (the session tool's form), objects in any order. *)

  val program_json : program -> t
  val rows : t -> Eff_types.row list option
  val rows_json : Eff_types.row list -> t
  val services : t -> (Eff_types.service_key * Eff_types.ty) list option
  val exits : t -> exit list option
  (** A reply tape: an array of exits. *)

  val exit_json : exit -> t
  val value_json : Eff_types.val_ -> t
  val ty_json : Eff_types.ty -> t
  val eff_ty_json : Eff_types.eff_ty -> t
  val refusal_json : Kit_gen.type_refusal -> t

  val admit_json : Kit_gen.admit_refusal -> t

  val check_json : app -> program -> t
  (** The checker's answer, then admission's: [{"status":"ok","type":…,"text":"Effect<A, E>"}],
      [{"status":"refused","refusal":…}] (typing, located) or
      [{"status":"refused","admission":…}]. *)

  val run_json : ?app:app -> ?budget:int -> 's run -> t
  (** A run: its stop, its host calls (each row by position and, with [app], by name) and, when
      known, the budget it settled at. *)

  val settled_json : ?app:app -> 's settled -> t

  val wait_json : ?app:app -> wait -> t
end

(** {1 Bytes} *)

val program_of_bytes : string -> program option
(** A program from its canonical bytes, exactly ([Eff_wire.decode_eff_exact]). *)

val program_bytes : program -> string
(** A program's canonical bytes. *)
