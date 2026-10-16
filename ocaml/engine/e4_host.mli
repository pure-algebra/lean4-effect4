(** A host driver over the engine: Lean's `Effect4.Run.driveFrom` (src/Effect4/Run/Basic.lean).
    The root is evaluated; each round answers the first host call from a provider, or flushes;
    a reply is applied only when the engine admits it. The properties are e4_host.ml's header. *)

open Eff_types

type completion = (val_, err, defect, int, unit) Eff_types.completion

module Make (E : E4_engine.ENGINE) : sig
  (** The host: a call's row, its request and the host's state, to a completion and the host's
      next state; [None] declines. Lean's `Run.Reactor`. *)
  type 'st provider = row -> val_ -> 'st -> (completion * 'st) option

  (** Why the drive stopped. *)
  type stop =
    | Settled  (** a flush left no host call *)
    | Declined  (** the provider answered [None] *)
    | Refused  (** the engine did not admit the provider's reply *)
    | Unknown_row  (** a call's row position is not in the table *)
    | Out_of_rounds

  (** One answered call: the row's external position, the request and the answer. *)
  type call = { row : int; request : val_; answer : completion }

  type 'st served = { engine : E.t; state : 'st; calls : call list; stop : stop }

  val serve :
    ?table:row list -> ?rounds:int -> 'st provider -> Eff_wire.program -> fuel:int -> 'st ->
    'st served
end
