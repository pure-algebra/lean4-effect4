(* e4_shutdown.mli — the ordered clean-up DAG.

   Borrow: lwt-exit's `?after:` / `~loc:` / exit status / double-signal safety, plus Eio's
   `Switch.await_idle` discipline (survey #6, #7, §8.2): SEAL the hook list atomically before
   the first hook runs, run every hook under protection in REVERSE registration order,
   accumulate a raising hook's exception rather than aborting the pass, and RECURSE if a hook
   registered more work. `E4_sched.shutdown` today would otherwise be `stop` + `join`, with
   no drain, no deadline and no finaliser flush (survey §1.4, e4_host.ml:118-124).
   Depends on: nothing in the library (Unix for the host deadline, Thread for the bounded
   wait of SD5).

   Properties (2026-09-08-engine-a3-queue-query.md §1.2.4, §2.5):
     SD1 Sealed: nothing registered after `run` begins enters this pass. A hook registered
         by a running hook is picked up by the NEXT pass (SD4), never by the one in flight.
         [by construction (each pass snapshots the not-yet-attempted hooks before it starts);
         tested: shutdown-seal]
     SD2 Reverse registration order, respecting `after` edges: a topological order of the
         DAG in which the tie-break among eligible hooks is the largest registration index,
         so with no edges the order is exactly LIFO. A cycle is an `Invalid_argument` at
         `register`, not at `run` -- and cannot in fact arise, because an `after` id must
         already exist when it is named, so every edge points backwards in registration
         order. An id from another registry is the `Invalid_argument` this rule catches.
         [by construction; tested: shutdown-order]
     SD3 A raising hook is recorded in `failed` and the pass continues.
         [by construction; tested: shutdown-failed]
     SD4 Re-entrant to a fixpoint, bounded by {!max_passes}; hooks still unattempted when
         the passes run out are reported in `unfinished`, never dropped.
         [by construction; tested: shutdown-recurse]
     SD5 Deadline-bounded: hooks not reached by the deadline are REPORTED, never dropped
         silently and never waited on forever. A hook that itself blocks past the deadline
         is left running on its own thread, reported in `unfinished`, and the pass stops --
         "never waited on forever" is a property of the CALLER, and it is why a finite
         deadline runs each hook on a thread it can walk away from.
         [by construction; tested: shutdown-deadline]
     SD6 Double-signal safe: a second `run` returns the first report, exactly, and runs
         nothing again. [by construction; tested: shutdown-double-signal]

   THE DEADLINE IS AN ABSOLUTE INSTANT on `Unix.gettimeofday`'s scale, not a duration:
   `run ~deadline:(Unix.gettimeofday () +. 5.0)`. {!no_deadline} is the unbounded case. It
   is a HOST deadline and never reaches a decision (survey trap #8).

   THE EXIT CODE is Octez's published contract (survey §1.4): the code tells an operator
   whether to go and clean up leftovers. {!exit_clean} 127, {!exit_cleanup_failed} 128,
   {!exit_cleanup_unfinished} 129, {!exit_forced} 255.

   Refused: killing a hook that overran. OCaml has no thread kill, and a `Thread.exit` from
   outside is not a thing; the report says `unfinished` and the operator gets exit code 129.
   Refusal row A3-SHUTDOWN-KILL.
   Refused: a signal handler in this module. `run` is called by whoever caught the signal;
   this file installs nothing global. Refusal row A3-SHUTDOWN-SIGNAL. *)

type id
(** A registered hook. Carries its registration index, its name and its `~loc:`, and the
    registry it belongs to, so an id from another registry is refused rather than silently
    treated as "already attempted". *)

val name : id -> string
val loc : id -> string

val index : id -> int
(** The registration index, from 0. SD2's tie-break is on this. *)

val equal : id -> id -> bool

type report = {
  ran : (id * float) list;  (** in the order they ran; the float is the hook's elapsed seconds *)
  failed : (id * exn) list;  (** SD3, in the order they raised *)
  unfinished : id list;  (** SD5 and SD4, in registration order *)
  passes : int;  (** SD4: how many passes actually ran a hook *)
  exit_code : int;
}

val max_passes : int
(** SD4's bound. A named constant in the file, never [max_int] (trap #17). *)

val no_deadline : float
(** [infinity]: run every hook to completion, on this thread, however long it takes. *)

val poll_seconds : float
(** The granularity of the bounded wait of SD5. `Condition` has no timed wait, so the wait
    polls, exactly as `E4_quiescence.wait_zero_for` does. *)

val exit_clean : int
(** 127 — clean shutdown: nothing failed, nothing unfinished. *)

val exit_cleanup_failed : int
(** 128 — exited, but a clean-up hook raised. *)

val exit_cleanup_unfinished : int
(** 129 — clean-up trouble: a hook was not reached, or overran the deadline. In Octez's
    contract 129-253 is the error-with-clean-up-trouble band; we use its first code. *)

val exit_forced : int
(** 255 — forced: `run` was called with a deadline that had already passed, so no hook was
    even attempted. *)

(** {1 The process registry}

    The entry points lwt-exit shapes: one registry per process, because a clean-up DAG is a
    property of the process and not of an object. {!Registry} is the same thing with the
    state named, which is what makes two independent shutdowns testable in one process and
    what {!E4_sched.shutdown} uses for the host's own four-hook DAG. *)

val register : ?after:id list -> loc:string -> name:string -> (unit -> unit) -> id
(** Register a clean-up hook in the process registry. [~loc] is meant to be [__LOC__], so a
    hung clean-up names its own source line (lwt-exit's rule).
    @raise Invalid_argument if an id in [after] belongs to another registry, or if the
    process registry has already produced its report (SD6: the pass is over). *)

val run : deadline:float -> report
(** Run the process registry's DAG. SD1-SD6. Idempotent: the second call returns the first
    report. *)

val report : unit -> report option
(** The process registry's report, if {!run} has produced one. *)

module Registry : sig
  type t

  val create : unit -> t
  val register : t -> ?after:id list -> loc:string -> name:string -> (unit -> unit) -> id
  val run : t -> deadline:float -> report
  val report : t -> report option

  val registered : t -> id list
  (** In registration order. *)
end
