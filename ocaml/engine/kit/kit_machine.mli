(** Kit_machine — run any program on the machine under a reactor (hand-written host code).

    What it is: the kit's machine runner. It runs a program on Lean's [RunMachine], made from LCNF
    ([E4_engine.Fast], [ocaml/engine/api_engine.ml]), driven by [E4_host.serve], Lean's
    [Run.driveFrom]: the root is evaluated, then each round answers the first host call from the
    reactor, or flushes, until a flush leaves no call. The engine admits each reply at its row
    before applying it. [Kit.run] uses it for every program the call tree does not cover, and to
    cross-check the tree's settled runs.
    Depends on: E4_engine, E4_host, Eff_types.

    Behaviours it holds itself to:
    M1  The decisions are [E4_host]'s (its H1 to H11).                     by construction
    M2  A fuel or round limit that ends the drive is [Out_of_fuel] or [Out_of_rounds]: a finite
        probe, never a divergence and never a failure (the machine's [Delay]).  by construction
    M3  A call's row is found by identity in the table the engine hands the reactor, so two rows
        with one name stay apart.                                          by construction
    M4  [Finished] is read only off [E4_host]'s [Machine Finished] (its H10), and a program the
        engine refuses to load (its H8) is [Stopped] with the refusal, never an escaping
        exception.                                                         by construction *)

type exit = (Eff_types.Val.t, Eff_types.Err.t, Eff_types.Defect.t, int, unit) Eff_types.Exit.t
type completion = (Eff_types.Val.t, Eff_types.Err.t, Eff_types.Defect.t, int, unit) Eff_types.Completion.t

type stop =
  | Finished of exit  (** the root ended with this exit *)
  | Waiting of int * Eff_types.Val.t  (** the reactor has no answer for this call *)
  | Refused of int * Eff_types.Val.t  (** the engine did not admit the reactor's reply to this call *)
  | Out_of_fuel  (** the machine's fuel ended first ([Delay]) *)
  | Out_of_rounds  (** the drive answered its last round of calls *)
  | Stopped of string
      (** any other end: suspended on a timer or a decision, stuck, a raise, a reply or a
          program outside the host profile *)

type 's run = { stop : stop; calls : (int * Eff_types.Val.t * exit) list; state : 's }

val run :
  ?fuel:int -> ?rounds:int -> Eff_types.Row.t list ->
  (Eff_types.Row.t -> Eff_types.Val.t -> 's -> (completion * 's) option) -> 's ->
  Eff_types.NativeOp.t Eff_types.Eff.t -> 's run
(** The program on the machine at the row table under the reactor; [fuel] defaults to 10 000 000
    machine steps and [rounds] to 100 000 host calls. *)
