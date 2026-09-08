(* e4_logindex.mli — the indexes over the log, built incrementally as rows are appended.

   What it is: the secondary indexes the design language's reading axis needs
   (2026-09-08-design-language.md §3, §6.4-§6.6).  Every index is a `Map.Make(Int)` from an
   identity to the ASCENDING list of trace indices that mention it.  Built by folding one
   {!add} per appended row -- never by re-scanning the log.
   Measured (2026-09-08-engine-a3-queue-query.md §6.3): 14.3 M rows/s to build the by-fiber
   index at 1e6 rows, constant per row from 1e4 to 1e6.  What THIS module measures, over its
   seven identities, is in the lane receipt's bench table.
   Depends on: E4_log.

   Properties:
     X1  Incremental: `add (of_log l) e = of_log (append l e)` for the row `e` describes.
         [tested: index-incremental]
     X2  Ascending, duplicate-free: every posting list is strictly ascending.
         [by construction: rows arrive in index order and each is added once -- {!add}
         REFUSES an entry whose index is not above the last one, so the invariant is carried
         by the type's constructor and not by a convention; tested: index-ascending]
     X3  Total: every row of the log is in `by_index`, and in `by_fiber` iff it names a
         fiber.                                                     [tested: index-total]
     X4  Free: no function here reads a machine, appends a row or charges fuel
         (INV-TAPE-1, A3 §1.3.4).                                          [by construction]

   THREE CARRIER CHOICES, each because the key says so.
     `by_index`     the trace index is DENSE and MONOTONE, so the entries live in an
                    `E4_log.Vec` (the same chunked vector as the log), not in a `Map`:
                    O(1) append, O(log (n/256)) get, and one fewer balanced tree per row.
     `by_decision`  the rows of one decision are CONTIGUOUS (a decision appends a segment,
                    design-language §1.6), so a decision needs no posting list at all: the
                    segment `[from, upto)` is the answer and {!by_decision} enumerates it.
                    The segment map takes one insertion per DECISION, not one per row.
     the rest       genuinely scattered keys: `Map.Make(Int) -> int list`, the posting list
                    held descending and reversed on read, so `add` stays O(log n).

   THE ORDINALS.  `kind` is the `RunEvent` constructor ordinal -- a POSITION IN A CONTENT
   TABLE (proposal 1; CAS amendment M17), read off `ocaml/engine/api_engine.ml:174-195` and
   named here as constants so no integer literal decides anything.  Append-only: a retired
   row's ordinal is never reused and no ordinal is ever renumbered. *)

(** {1 The row alphabet} *)

(** The twenty-one `RunEvent` ordinals, in the content table's own order
    (api_engine.ml:174-195).  The three that carry a second identity are marked:
    [scheduledTask]/[ranTask] a task owner, [parkedOn]/[resumedWith] a park token,
    [scopeLinked]/[scopeClosedOnLink] a scope key.  [kind_finalizer_program] is the ONLY
    finalizer row that exists today and it carries no scope key.  [kind_unknown] is [-1]:
    a row this codec does not recognise, never a guess. *)

val kind_forked : int
val kind_started : int
val kind_scheduled_task : int
val kind_ran_task : int
val kind_yield_injected : int
val kind_parked_on : int
val kind_resumed_with : int
val kind_interrupt_recorded : int
val kind_interrupt_deferred : int
val kind_children_interrupted : int
val kind_observer_fired : int
val kind_frame : int
val kind_finalizer_program : int
val kind_scope_linked : int
val kind_scope_closed_on_link : int
val kind_race_started : int
val kind_race_launched : int
val kind_race_settled : int
val kind_context_set : int
val kind_callback : int
val kind_exited : int
val kind_unknown : int

val kind_count : int
(** 21.  The size of the content table today; it grows only at the end (X2 of the CAS
    amendments), so this constant is a floor on future tables and never a modulus. *)

val kind_name : int -> string
(** The constructor's name, or ["kind<n>"] for an ordinal this build does not know. *)

(** {1 The entry} *)

type entry = {
  index : int;  (** the trace index: the reading axis *)
  kind : int;  (** the `RunEvent` constructor ordinal, from the content table *)
  fiber : int option;
  token : int option;  (** parkedOn / resumedWith: the park protocol's identity *)
  scope : int option;  (** scopeLinked / scopeClosedOnLink *)
  task_owner : int option;  (** scheduledTask / ranTask: the fiber's queue staff *)
  decision : int;  (** which decision's segment this row falls in *)
}

val parse_run_event_row : decision:int -> int -> E4_log.row -> entry
(** The codec of the public log AS IT IS RENDERED TODAY: the rows
    `E4_engine.ENGINE.trace_rows` prints (`ocaml/engine/e4_engine.ml:472-505`), which are
    `name(arg,arg,...)` with the arguments nested by parentheses and brackets.  It reads the
    head name to a {!kind}, and the identities off the argument positions Lean declares
    (`src/Effect4/Machine/Fibers.lean:355-374`); an unrecognised head is {!kind_unknown}
    with every identity [None], never a guess.

    THE OWED ROWS ARE OWED HERE (A3 §1.3.4).  `scopeLinked`/`scopeClosedOnLink` supply the
    scope key, so `by_scope` is exact for linked fibers and PARTIAL for the rest;
    `finalizerProgram` carries fiber, finalizer and exit but NO scope, so a finalizer row is
    not joined to its scope until X2 lands `finalizerRegistered`.  `scopeOpened` and
    `scopeClosed` do not exist at all.  This function invents none of them. *)

(** {1 The index} *)

type t

val empty : t
val add : t -> entry -> t
(** Append one row's entry.  X1, X2.
    @raise Invalid_argument if [entry.index] is not greater than the last added index, or if
      [entry.decision] is below the last added decision -- both would break X2 or the
      contiguity {!segment} rests on. *)

val of_log : E4_log.t -> parse:(int -> E4_log.row -> entry) -> t
(** One pass over the log, in index order; [parse i row] must answer an entry with
    [index = i].  Use {!parse_run_event_row} for the codec above. *)

val count : t -> int

val by_index : t -> int -> entry option
val by_fiber : t -> int -> int list
val by_kind : t -> int -> int list
val by_token : t -> int -> int list
val by_scope : t -> int -> int list
val by_task_owner : t -> int -> int list
val by_decision : t -> int -> int list
(** All ascending.  X2.  {!by_decision} is {!segment} enumerated: the rows of one decision
    are contiguous, so there is no posting list to keep. *)

val fibers : t -> int list
val tokens : t -> int list
val scopes : t -> int list
val kinds : t -> int list
(** All ascending. *)

val task_owners : t -> int list

val decisions : t -> int
(** How many decisions appended at least one row, i.e. how many segments {!segment} has. *)

val decision_keys : t -> int list
(** Those decisions, ascending. *)

val segment : t -> int -> (int * int) option
(** The half-open row range [\[log_from, log_upto)] one decision appended
    (design-language §1.6: "each decision appends a segment").  [None] for a decision that
    appended nothing -- an empty segment is not a gap in the log, it is a bar line with no
    note under it. *)

val decision_of : t -> int -> int option
(** The decision whose segment row [i] falls in: `(by_index t i).decision`. *)
