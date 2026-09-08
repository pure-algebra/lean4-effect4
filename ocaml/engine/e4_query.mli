(* e4_query.mli — the read-only face of a run.  Serves the design language's reading axis.

   INV-TAPE-1 (QUERY), the invariant this API guarantees:
     Every entry point below is a PURE FUNCTION of the saved machine, the log and the tape.
     It appends no row, consumes no fuel, takes no decision and returns no new tape.
     Mechanically enforced twice: (1) no function RETURNS a `source` or a tape, so a caller
     cannot thread a mutated one -- {!of_run} is the single constructor and every other
     signature's result is a row, a list, an int, a machine or a cursor; (2) a repo gate
     (test_query.ml, `query-inv-tape-1`) rejects this file if any signature's RESULT type
     mentions `source` or `tape`, or if the module ever refers to `E4_sched.send`.
   `at`/`cursor`/`replay_steps` return a machine, but that machine is REPLAYED from the same
   tape prefix, so `tape_of (at s i) = take i (tape s)` and nothing was chosen.
   Depends on: E4_log, E4_logindex.

   THE COST MODEL for `replay_steps`.
     A checkpoint is a POINTER, not a copy: every carrier in A3 §1.1 and §1.3.1 is
     persistent, so retaining the machine at decision j costs only the words that decision's
     path-copying already allocated -- it does not copy anything, it merely prevents
     collection.  So the checkpoint interval k is a RETENTION knob:
        space  = O(n/k) retained versions, each holding O(log (store size)) words the run
                 allocated anyway; measure it as live words, not as bytes copied
        random access `at i`   = i mod k replayed decisions, <= k/2 in expectation
        sequential `cursor`    = one replayed decision per step -- the cursor keeps the last
                                 machine, so a full walk of n positions costs exactly n
                                 replays and no checkpoint lookups
        `replay_steps from upto` = (upto - from) + (from mod k) replays
     The viewer's real access pattern is the sequential walk (design-language §6.6: "a
     replay step prints one more measure"), so THE CURSOR IS THE PRIMARY ENTRY POINT and
     `at` is the convenience.  Default k = 1024 (`E4_sched.config.checkpoint_every`), which
     bounds a random access at 1023 replayed decisions, 511.5 on average, and retains one
     version per 1024.

   THE CHECKPOINT SCHEDULE IS MATERIALISED AT {!of_run}, in ONE forward pass over the tape.
   The alternative -- materialising lazily, on the first `at` that needs one -- was refused:
   it makes {!cost} depend on the access history, and {!cost} must be exact and Q3 says a
   query leaves the source unchanged.  So `of_run` replays the tape once, keeps every k-th
   machine, and from then on every number this module reports is a function of the source
   alone.  A source over an n-decision tape therefore costs n replays to build and
   1 + n/k retained machine versions to hold.

   Properties:
     Q1  Free: INV-TAPE-1(query) above.       [by type; gated; tested: query-free]
     Q2  Agreement: `at s i` equals the machine `replay program fuel (take i tape)`
         produces.  [licensed by Api.replay's agreement theorem (src/Effect4/Api.lean:156-162,
         commit 781cfbc); DIFFERENTIAL DF-3: for every corpus program and tape, `at s i` for
         every i must equal what replaying the tape prefix produces, on every projection;
         tested: query-agreement / DF-3 in test_query.ml]
     Q3  Idempotent: two calls with the same argument return equal values and leave the
         source unchanged.                    [tested: query-idempotent]
     Q4  Complete: `rows s ~from:0 ~upto:(length s)` is the whole log, with no gap.  The
         RING may gap; the LOG may not (A3 §1.2.2 S6, survey trap #15).
                                              [tested: query-complete] *)

type ('m, 'd) source

type status = {
  finished : bool;  (** every fiber has exited and the last step settled *)
  stuck : string option;  (** the `Stuck` constructor, spelled *)
  fuel_left : int;
}
(** THE ONE MACHINE PROJECTION THIS MODULE TAKES, and the one deviation from the design's
    `of_run` (lane receipt D-Q3-1).  `outcome` is a fact about the machine at the end of the
    tape and the design's `of_run` had no way to read it: the module holds `'m` abstract and
    replays it, and a query layer that decided `finished` for itself would be a second
    interpreter, which brief §1 forbids.  So the caller supplies the projection -- for the
    engine it is `E4_engine.ENGINE.answer` read off in three lines -- and this module
    combines it with what the LOG knows (the open scopes) into {!outcome}. *)

type frontier = {
  open_scopes : int list;  (** scope keys with a link row and no close row, ascending *)
  awaited : string option;
      (** INV-TAPE-2: the row the frontier names.  [None] until X2 lands the row
          (A3 §1.3.4, risk R-A3-3) -- it is `None`, NEVER A GUESS. *)
  fuel_left : int;
}

val of_run :
  log:E4_log.t ->
  index:E4_logindex.t ->
  tape:'d array ->
  replay:('m -> 'd -> 'm) ->
  initial:'m ->
  checkpoint_every:int ->
  status:('m -> status) ->
  ('m, 'd) source
(** The single constructor.  Replays the tape once to materialise the checkpoint schedule.
    @raise Invalid_argument if [checkpoint_every < 1]. *)

(** {1 The reading axis} *)

val length : ('m, 'd) source -> int
val row : ('m, 'd) source -> int -> string option
val rows : ('m, 'd) source -> from:int -> upto:int -> string list
val segment_of_decision : ('m, 'd) source -> int -> (int * int) option
val decision_of_row : ('m, 'd) source -> int -> int option
(** The two directions of design-language §1.6's "each decision appends a segment".  A bar
    line always falls between two rows and a segment boundary always falls on a row (§4.8),
    so these two are inverse on their domains. *)

(** {1 By identity} *)

val fiber_rows : ('m, 'd) source -> int -> (int * string) list
val scope_rows : ('m, 'd) source -> int -> (int * string) list
(** open / close / finalizer rows of one scope: the locking-table view (design-language
    §6.5).  Today it is the `scopeLinked` / `scopeClosedOnLink` rows only: `scopeOpened`,
    `scopeClosed` and `finalizerRegistered` need X2, and `finalizerProgram` carries no scope
    key, so a finalizer joins its scope only for a linked fiber (A3 §1.3.4). *)

val token_rows : ('m, 'd) source -> int -> (int * string) list
(** the park and the answer for one token: the hollow box and the filled box
    (design-language §2). *)

val task_rows : ('m, 'd) source -> owner:int -> (int * string) list
(** `scheduledTask` / `ranTask`: one fiber's queue staff. *)

val fibers : ('m, 'd) source -> int list
val scopes : ('m, 'd) source -> int list
val tokens : ('m, 'd) source -> int list

val open_scopes : ('m, 'd) source -> int list
(** Every scope with a link row and no close row, ascending: the empty `closed at` cells of
    the locking table (design-language §6.5).  PARTIAL until X2, as {!scope_rows} says. *)

val by_cid : ('m, 'd) source -> cid:string -> (int * string) list
(** Every row whose content address is [cid].  The address is the SHA-256 of canonical bytes
    as Lean computes them; THIS FUNCTION NEVER COMPUTES ONE (brief rule 2, survey trap #1) --
    it looks for the seal A2's writer already put in the row, as the literal text [cid].  A
    linear pass over the log: the log's codec carries no address today, so there is nothing
    to index yet and a posting list would be an empty map with a cost.  When the public
    codec gains the seal (A3 §1.3.4, "the tape in the manifest" and the Cid rows), this
    becomes one more `E4_logindex` posting list behind an unchanged signature.
    @raise Invalid_argument on an empty [cid] -- it would match every row. *)

val by_occurrence : ('m, 'd) source -> program:string -> path:int list -> (int * string) list
(** The `Occurrence {program, path}` identity (2026-09-07-cas-design.md §1), as the text
    {!occurrence_text} spells it. *)

val by_path : ('m, 'd) source -> path:int list -> (int * string) list
(** Every occurrence at this path in any program of the run, as {!path_text} spells it. *)

val path_text : int list -> string
(** [\[1;1;0\]] is ["[1 1 0]"] -- the design language's own glyph for a path
    (design-language §3).  SPACE separated and not comma separated, which is what keeps it
    apart from the engine's rendered id lists (`childrenInterrupted(0,[1,2])`). *)

val occurrence_text : program:string -> path:int list -> string
(** ["program:2ddd3c…/[1 0]"] -- design-language §3, the occurrence row. *)

(** {1 The tape and the outcome} *)

val tape : ('m, 'd) source -> 'd list
val tape_length : ('m, 'd) source -> int

val outcome : ('m, 'd) source -> [ `Finished | `Frontier of frontier | `Stuck of string ]
(** Three outcomes and one latched frontier (grill §1 Q7).  The machine half comes from the
    {!status} the caller supplied, the `open_scopes` half from the log. *)

(** {1 The machine at a position} *)

type ('m, 'd) cursor

val cursor : ('m, 'd) source -> from:int -> ('m, 'd) cursor
(** @raise Invalid_argument outside [0, tape_length]. *)

val next : ('m, 'd) cursor -> ('m * ('m, 'd) cursor) option
(** One replayed decision: the machine AFTER the cursor's next decision, and the cursor
    advanced onto it.  [None] at the end of the tape.  THE PRIMARY ENTRY POINT. *)

val current : ('m, 'd) cursor -> 'm
(** The machine at {!position}.  Free: the cursor already holds it. *)

val position : ('m, 'd) cursor -> int

val at : ('m, 'd) source -> int -> 'm
(** [i mod checkpoint_every] replayed decisions.
    @raise Invalid_argument outside [0, tape_length]. *)

val replay_steps : ('m, 'd) source -> from:int -> upto:int -> 'm list
(** `Api.replaySteps`, "the viewer's one real need" (2026-09-08-build-path.md §3 row 3).
    The machines at positions [from .. upto] INCLUSIVE, so [upto - from + 1] of them.
    Cost: [(upto - from) + (from mod k)] replays.
    @raise Invalid_argument unless [0 <= from <= upto <= tape_length]. *)

val cost : ('m, 'd) source -> from:int -> upto:int -> int
(** How many decisions the corresponding call WILL replay.  Free, and exact -- a viewer
    decides whether to ask before it asks.  [cost s ~from:i ~upto:i] is what {!at} [i]
    costs. *)

val checkpoints : ('m, 'd) source -> int list
(** The retained positions, ascending: [0, k, 2k, ...] up to the tape length. *)

val checkpoint_every : ('m, 'd) source -> int
