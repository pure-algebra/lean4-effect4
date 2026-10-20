(** A host driver over the engine: Lean's `Effect4.Run.driveFrom` (src/Effect4/Run/Basic.lean).
    The program is loaded and its root evaluated; each round answers the first host call from a
    provider, or flushes; the engine's answer is read after every step, and a reply is applied
    only when the engine admits it. The properties are e4_host.ml's header. *)

open Eff_types

type completion = (Val.t, Err.t, Defect.t, int, unit) Eff_types.Completion.t

(** The host's types. None mentions the engine, so they are declared once here and every
    instance of {!Make} re-exports them with type equalities (H12). *)
module Types : sig
  (** The host: a call's row, its request and the host's state, to a completion and the host's
      next state; [None] declines. Lean's `Run.Reactor`. *)
  type 'st provider = Row.t -> Val.t -> 'st -> (completion * 'st) option

  (** What the machine reached, read off the engine's answer ([E4_engine.answer], H10). The
      engine served is the machine after the step that reached it. *)
  type outcome =
    | Finished
    (** every fiber exited and a flush left no host call; read [E.root_exit_of] *)
    | Waiting
    (** the machine is live and settled, and a flush left no host call: a live frontier,
            never an error (the engine's [Suspended]) *)
    | Delay (** a step ran out of fuel: a live frontier, never an error *)
    | Stuck of string (** the machine is stuck: the engine's [Refused], with its reason *)

  (** Why the host stopped driving a live machine. After [Declined], [Raised], [Refused] and
      [Outside_profile] the engine and the host's state are the ones before the call, no call
      is recorded for it, and the call stays outstanding (H2, H5, H6). *)
  type host_stop =
    | Declined (** the provider answered [None] *)
    | Raised of exn
    (** the provider raised: no answer, as [Declined] (H5); never a typed failure.
            [Out_of_memory] and [Sys.Break] are raised again. *)
    | Refused (** the engine did not admit the provider's reply *)
    | Outside_profile of E4_engine.outside
    (** a reply failed the host-ingress check (EN9, H6: no Lean value, or Lean's profile
            support refused it at its path), or a step's numeric crossing refused a value and
            was not taken (H2, H9): the engine is the one before it. *)
    | Unknown_row (** a call's row position is not in the table *)
    | Out_of_rounds (** the last round was played with the machine still live *)

  (** Why the drive stopped: what the machine reached, or why the host stopped it. *)
  type stop =
    | Machine of outcome
    | Host of host_stop

  (** The stop, spelled for a report. *)
  val stop_name : stop -> string

  (** Why the program was not loaded (H8): Lean's profile support refused one of its literals
      ([Unsupported], EN8), or its loading computed a value a crossing refused ([Crossing]). *)
  type load_refusal = Load_outside_profile of E4_engine.outside

  (** One answered call: the row's external position, the request and the answer. *)
  type call =
    { row : int
    ; request : Val.t
    ; answer : completion
    }
end

include module type of struct
  include Types
end

module Make (E : E4_engine.ENGINE) : sig
  include module type of struct
    include Types
  end

  type 'st served =
    { engine : E.t
    ; state : 'st
    ; calls : call list
    ; stop : stop
    }

  (** The program loaded at [fuel] and driven under the provider from the host's [state]: the
      drive, or the loading refusal. Nothing it refuses escapes as an exception. *)
  val serve
    :  ?table:Row.t list
    -> ?rounds:int
    -> 'st provider
    -> Eff_wire.program
    -> fuel:int
    -> 'st
    -> ('st served, load_refusal) result
end
