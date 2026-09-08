(* E4_diff -- the comparison as data: one projection record per engine per position, and
   the divergence list that names the first field and position at which two of them differ.

   What it is: build lane X of the engine team (docs/research/2026-09-08-engine-brief.md
   §2.1 "a differential is the evidence"; the projection of
   2026-09-08-engine-a1-state.md §6.3, p1..p13; A3 §4.2 DF-1).  It holds no semantics: a
   {!projection} is a tuple of `E4_engine.ENGINE`'s free rows, all of which are pure
   functions of a machine value (INV-TAPE-1, brief §2.4), and {!compare} is equality on
   them.

   WHY A RENDERING AND NOT A VALUE.  `Api_engine.Make(fast).event` and
   `Api_engine.Make(list).event` and `Api_gen.run_event` are THREE OCaml types -- the
   generated type group is declared inside the functor, so each application makes its own,
   and the untouched `ocaml/gen/api_gen.ml` is a fourth compilation unit entirely.  Nothing
   can compare them as values.  `E4_engine.ENGINE` therefore exposes string renderings and
   this module compares those.  The renderers print every constructor of `RunEvent`,
   `Task`, `Prim`, `FrameEvent`, `Exit`, `Cause`, `Reason`, `Val`, `Ctx`, `Observer`,
   `Parked` and `Stuck` in full; `Effect4.Program.EffName` and `Effect4.Program.EffThunk`
   print as `<name>` and `<thunk>` (lane D deviation D-D3).  "The projections are equal"
   means exactly this and nothing wider.

   THE TAPE IS ENGINE-INDEPENDENT.  {!decision} is a datum, not an engine's `decision`
   type, so ONE tape drives all three engines.  {!Of.gen_tape} builds a tape by looking at
   the machine as it runs -- every fiber id it names was minted by that machine, so no
   generated tape can reach `Stuck.unknownFiber` by accident and a stuck answer is always
   a fact about the program, never about the tape.

   Depends on: E4_engine, effect4_eff (Eff_types), stdlib.

   Behaviours:
   D1  {!compare} is reflexive-complete: `compare p p = []` for every projection, and
       `compare a b = []` implies every field of the record is equal (the comparison covers
       all thirteen).                                                     by construction
   D2  A divergence names the field, the position INSIDE the field for the list-shaped
       rows, and both sides verbatim.                                     by construction
   D3  The order of comparison is the order of the record: the cheap scalars first, so the
       FIRST divergence reported is the most diagnostic one.              by construction
   D4  Every row of a projection is free: no fuel is spent and nothing reaches the tape.
                                                                          by construction
   D5  {!Of.positions} yields `List.length tape + 1` projections, the loaded machine first
       (`E4_engine` EN4).                                                 by construction
   D6  {!Of.gen_tape} only names fiber ids and park tokens the machine has shown.
                                                                          by construction *)

(** {1 The tape, as data} *)

type decision =
  | Evaluate of int
  | Flush
  | Fire of int
  | Yield_verdict of int * bool
  | Answer_async of int * int * int  (** fiber, token, the nat the completion carries *)
  | Interrupt_from of int option * int
  | Install_middleware

val show_decision : decision -> string
val show_tape : decision list -> string

val drive_tape : decision list
(** `Api.run`'s own tape: `[Evaluate 0; Flush]` (Api.lean:171-172). *)

(** {1 The projection} *)

type projection = {
  p1_outcome : string;  (** "finished" | "frontier" | "stuck <why>" *)
  p2_stuck : string option;  (** the `Stuck` constructor, spelled *)
  p3_settled : bool;  (** the generated `settled` of the last step: `Delay` iff false *)
  p4_answer : string;  (** the four-letter alphabet, with the frontier *)
  p5_fiber_count : int;
  p6_fiber_ids : int list;  (** IN MACHINE ORDER -- the ordering law is exactly this row *)
  p7_exits : (int * string) list;
  p8_root_exit : string option;
  p9_fiber_rows : (int * string) list;  (** park, exit, observers, children, dispatcher, ctx *)
  p10_armed : string;  (** the armed owners, in arming order, as the store row spells them *)
  p11_trace_length : int;
  p12_trace_rows : string list;  (** every row, in emission order *)
  p13_store_row : string;  (** refs, cells, scopes, memo paths, nextName, due, ids, races *)
}

type divergence = {
  d_field : string;
  d_index : int option;  (** the position inside a list-shaped field *)
  d_left : string;
  d_right : string;
}

val compare : projection -> projection -> divergence list
(** [] iff the two projections are equal.  One entry per differing field, in the record's
    order; for a list-shaped field the entry names the first differing index (or the
    lengths, when one side is shorter). *)

val show_divergence : divergence -> string

(** {1 One engine's side of the comparison} *)

module type SIDE = sig
  val name : string
  val carriers : string

  type t

  val load : Eff_types.eff -> fuel:int -> t
  val step : t -> decision -> t
  val project : t -> projection

  val positions : Eff_types.eff -> fuel:int -> decision list -> projection list
  (** The projection at every position of `replay_steps`: `|tape| + 1` of them. *)

  val gen_tape : Eff_types.eff -> fuel:int -> seed:int -> max_len:int -> decision list
  (** An ADMISSIBLE tape: at each step the next decision is drawn from what this machine
      shows -- its fiber ids, its armed owners, its parked (fiber, token) pairs -- so the
      tape never names something the machine has not minted (D6).  Deterministic in
      [seed]. *)
end

module Of (E : E4_engine.ENGINE) : SIDE with type t = E.t
