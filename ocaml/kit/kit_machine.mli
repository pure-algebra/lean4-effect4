(** Kit_machine — run any program on the machine, under a kit host (hand-written host code).

    What it is: the kit's second runner. [Kit] runs a program's call tree, the meaning, on the
    sequential fragment ([Kit.outside] is [None]). This module runs every program on the machine
    itself: Lean's [RunMachine], made from LCNF ([E4_engine.Fast], [ocaml/engine/api_engine.ml]),
    driven by [E4_host.serve], Lean's [Run.driveFrom]. A kit host answers each call; the engine
    admits each reply at its row before applying it. The stops are named as [Kit]'s are.
    Depends on: Kit, E4_engine, E4_host, Eff_types.

    Behaviours it holds itself to:
    M1  The decisions are [E4_host]'s (H1 to H7): evaluate the root, then answer the first host
        call or flush, until a flush leaves no host call.          by construction
    M2  A fuel or round limit that ends the drive is [Out_of_fuel] or [Out_of_rounds]: a finite
        probe, never a divergence and never a failure (the machine's [Delay]).  by construction
    M3  On the tree's fragment, a run that both runners finish or leave waiting has the same calls
        and the same stop ([agree]); a disagreement is a finding about the machine, the meaning
        or the lowering, never noise.                               tested (test_kit T8) *)

type stop =
  | Finished of Kit.exit  (** the root ended with this exit *)
  | Waiting of int * Eff_types.val_  (** the host has no answer for this call *)
  | Refused of int * Eff_types.val_ * Kit.exit  (** the engine did not admit this reply *)
  | Out_of_fuel  (** the machine's fuel ended first ([Delay]) *)
  | Out_of_rounds  (** the drive answered its last round of calls *)
  | Stopped of string  (** any other end: suspended on a timer or a decision, stuck, a raise *)

type 's run = { stop : stop; calls : (int * Eff_types.val_ * Kit.exit) list; state : 's }

val run : ?fuel:int -> ?rounds:int -> Kit.app -> 's Kit.host -> 's -> Kit.program -> 's run
(** The program on the machine under the host; [fuel] defaults to 10 000 000 machine steps and
    [rounds] to 100 000 host calls. *)

val agree : 's Kit.run -> 't run -> bool
(** Whether a tree run and a machine run of one program finish or wait alike, with the same host
    calls: the per-run check of the session theorems ([denoteRowsB_eq_session_host]). A tree
    run that is cut agrees with nothing. *)

val json : ?app:Kit.app -> 's run -> Eff_json_text.t
