(* e4_abandon.mli — stop a live run and account for every open scope.

   THE RULING THIS FILE NEEDED (D-A3-9, the unwritten ruling of survey trap #24 / §8.4;
   Q-A3-3): Riot's `unwind` DISCARDS every effect a finalizer performs; Eio's `await_idle`
   BLOCKS under `Cancel.protect` with no fuel bound. Neither is available to us -- we cannot
   drop silently and we cannot block at a frontier. The third option, and the one taken:
   A FINALIZER FUEL BUDGET, WITH OVERRUN AS A DISTINCT OUTCOME. The budget is a profile
   field, [default_finalizer_fuel] = 1 000 command steps per scope.
   Depends on: nothing (polymorphic in the machine; the machine's own scope operations
   arrive as the {!driver} record of functions -- the same "records of functions, not
   functors" rule the scheduler follows, design §1.2.2).

   Properties (2026-09-08-engine-a3-queue-query.md §1.2.4, §2.5):
     AB1 `run` = interrupt the root, then close scopes innermost-first, running each scope's
         finalizers under `budget.finalizer_fuel` command steps. Termination is by two
         bounds and no other argument: at most `budget.max_scopes` scopes are attempted, and
         each attempt runs at most `finalizer_fuel` steps.
         [by construction; tested: abandon-order, abandon-budget]
     AB2 A finalizer that exhausts its budget is stopped, its scope is REPORTED in
         `unfinished`, and the pass continues with the next scope. It is never discarded
         silently and never waited on forever.
         [by construction; tested: abandon-budget, abandon-budget-mutation]
     AB3 ACCOUNTING (Miou's orphan discipline, survey §8.3, with reporting where Miou
         raises): `closed @ unfinished` is exactly the multiset of scopes open at entry. An
         outcome that mentions none of them is malformed; {!accounted} is the predicate.
         [by construction; tested: abandon-accounts]
     AB4 Every step `abandon` takes is a decision on the tape: `report.decisions` is the
         number the driver reported appending, so an abandoned run replays.
         [by construction (the driver reports its own count); tested: abandon-accounts]
     AB5 `abandon` is idempotent: a second call on an abandoned machine returns the first
         report. This module is a pure function, so AB5 is discharged where the first report
         is kept -- `E4_sched.abandon` stores it per machine and never runs a second pass.
         [tested: sched-abandon-idempotent]

   Refused: killing a finalizer thread, or any notion of a wall-clock timeout on a
   finalizer. The bound is FUEL -- a count of command steps, on the tape -- because a
   wall-clock bound would make which scopes closed depend on host timing, and the report is
   a fact about the run, not about the host. Refusal row A3-ABANDON-WALLCLOCK.
   Refused: discarding a scope that overran (Riot's `unwind`). Refusal row
   A3-ABANDON-DISCARD. *)

type budget = {
  finalizer_fuel : int;  (** command steps per scope *)
  max_scopes : int;  (** a bound on the close pass, so AB1 terminates *)
}

val default_finalizer_fuel : int
(** 1 000 (Q-A3-3). A named constant in the file, never [max_int] (trap #17). *)

val default_max_scopes : int
(** 1 024. A named constant in the file, never [max_int]. *)

val default_budget : budget
(** [{ finalizer_fuel = default_finalizer_fuel; max_scopes = default_max_scopes }]. *)

type report = {
  closed : int list;  (** scope keys whose finalizers all ran, in close order *)
  unfinished : int list;  (** AB2: budget exhausted, or beyond [max_scopes]; the owed closes *)
  exits : string list;  (** the accumulated exits, in close order *)
  fuel_left : int;  (** granted minus spent: [finalizer_fuel] x scopes attempted, less the
                        steps actually run *)
  decisions : int;  (** AB4: what was appended to the tape *)
}

type 'm driver = {
  interrupt : 'm -> reason:string -> 'm * int;
      (** AB1's first half: interrupt the root. Returns the machine and the number of
          decisions it appended. *)
  open_scopes : 'm -> int list;
      (** Every open scope of the machine, OUTERMOST FIRST. {!run} closes them in reverse,
          which is innermost-first. Read once, at entry: AB3's "at entry" is this list. *)
  finalizer_step : 'm -> scope:int -> ('m * string list * int) option;
      (** ONE command step of [scope]'s finalizers: the machine after the step, the exits
          that step produced, and the number of decisions it appended. [None] means the
          scope has no more finalizer work and is now closed -- a [None] costs no fuel,
          because it is the answer to "is there more", not a step. *)
}
(** What `abandon` needs of a machine. A record of functions, not a functor (design §1.2.2:
    "one machine over one carrier is the case RWO says dictionary passing handles well"). *)

val run : 'm driver -> 'm -> reason:string -> budget:budget -> 'm * report
(** [run driver m ~reason ~budget] is AB1: read the open scopes of [m], interrupt the root,
    then close the scopes innermost-first under the budget. Total: it performs at most
    [budget.max_scopes * budget.finalizer_fuel] finalizer steps and then returns.
    @raise Invalid_argument if [budget.finalizer_fuel < 0] or [budget.max_scopes < 0]. *)

val accounted : report -> at_entry:int list -> bool
(** AB3 as a predicate: [closed @ unfinished] and [at_entry] are the same multiset. *)

val to_string : report -> string
(** One line, for a receipt or a log. Not a wire format and never an identity. *)
