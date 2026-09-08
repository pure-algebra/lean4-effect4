(* e4_buckets.mli — the dispatcher: priority -> FIFO, persistent.

   What it is: the OCaml carrier of Effect4.Machine.Dispatcher
   (src/Effect4/Machine/Fibers.lean:115-155, transcribing Scheduler.ts:105-131 and :225-233).
   Buckets in strictly ascending priority; FIFO within a bucket; one drain empties the whole
   structure, so a task enqueued during a drain waits for the next one. Representation: an
   ascending assoc list of (priority, front/back list pair). The assoc list IS
   OCaml5.Lib.Map's carrier (a strictly ascending association list, Lib/Map.lean:9-14) and
   the pair IS OCaml5.Lib.Deque's carrier (its `toList`, Lib/Deque.lean:92-96) under
   to_list (f, b) = f @ List.rev b -- so every theorem in Lib/Deque.lean is a law of this
   module, not an analogy.
   Depends on: nothing (polymorphic in the task; Stdlib only).

   Properties (the Lean theorem that licenses each is in
   docs/research/2026-09-08-engine-a3-queue-query.md §2.1):
     B1  Ascending priorities, each exactly once. `priorities` is strictly increasing.
         [by construction (insert keeps the order); licensed by Buckets.drain_priority_ascending,
         Map.keys_sorted, Map.keys_nodup; tested: buckets-ascending]
     B2  FIFO within a bucket. `enqueue` appends at the tail of exactly its own priority's
         queue and leaves every other priority alone.
         [by construction; licensed by Buckets.drain_fifo_within_bucket,
         Buckets.enqueue_find_other, Deque.fifo; tested: buckets-fifo]
     B3  A drain is the concatenation of the buckets' queues, in ascending priority.
         [by construction; licensed by Buckets.drain_eq_flatten + Dispatcher.drain_projection;
         tested: buckets-drain-order]
     B4  Drained once: `drain` returns an empty dispatcher.
         [by construction; licensed by Buckets.drained_once, Dispatcher.drain_snd_empty;
         tested: buckets-drained-once]
     B5  Exactly one delivery per enqueue: one `enqueue` adds exactly one element to the next
         drain, and that element is the enqueued task.
         [by construction; licensed by Buckets.drain_enqueue_length, Buckets.drain_enqueue_mem;
         tested: buckets-exactly-once]
     B6  `enqueue` arms; `drain` disarms; `arm` arms without enqueueing and `disarm` disarms
         without touching the buckets. This half has no Lean counterpart in Buckets -- the Deep
         dispatcher's `armed : Bool` is a host fact (refusal row W4-DEQ-ARMED,
         Lib/Deque.lean:75-78) -- so it is stated here and proved nowhere. It is nevertheless
         an OBSERVATION of Effect4.Machine.Dispatcher (Fibers.lean:127,147,153) and the
         differential in test_buckets.ml checks it after every operation.
         [by construction; tested: buckets-armed]
     B7  Persistence: every operation returns a fresh value and no earlier value is changed.
         A saved machine holding a `t` holds no mutable structure (brief rule 3).
         [by construction (no mutable field, no array, no Hashtbl/Buffer/Queue);
         tested: buckets-persistent]

   Refused: amortised single-element `dequeue`. The Deep dispatcher only ever drains the whole
   snapshot (Scheduler.ts:225-233), so a front/back pair never needs its rotation amortisation
   argument -- the drain reverses each back list exactly once. Refusal row A3-BUCKETS-DEQUEUE.

   NOT refused, kept as the tripwire of R-A3-4: the Map.Make(Int) carrier is written in this
   file as {!Map_variant}, behind the same signature {!S}, and benched beside the default at
   p in {1, 4, 16, 256} by test_buckets.ml. Refusal row A3-BUCKETS-MAP therefore stands as a
   DEFAULT, not as an absence: if a program ever uses many priorities, the switch is one line
   (`include Assoc` becomes `include Map_variant` at the foot of e4_buckets.ml) and no caller
   changes. *)

type 'a t
(** A dispatcher: the buckets and the armed flag. Persistent. *)

val empty : 'a t
(** The empty dispatcher, disarmed. `Effect4.Machine.Dispatcher.empty`
    (Fibers.lean:134). *)

val is_empty : 'a t -> bool
(** No bucket holds a task. Note: an empty dispatcher may still be armed. *)

val armed : 'a t -> bool
(** "The host callback is scheduled" (Scheduler.ts:207-212). B6; not projected onto Lean. *)

val arm : 'a t -> 'a t
(** Set the armed flag without enqueueing anything: a task was scheduled on this owner's
    dispatcher and the first one arms it (`RunMachine.arm`, Fibers.lean:627-629). B6. *)

val disarm : 'a t -> 'a t
(** Clear the armed flag without touching the buckets: the host callback of this owner ran
    (`RunMachine.disarm`, Fibers.lean:632-634). B6. *)

val enqueue : 'a t -> priority:int -> 'a -> 'a t
(** `Dispatcher.enqueue` (Fibers.lean:145-147): append at the tail of `priority`'s queue,
    creating the bucket in ascending position if there is none, and arm. B1, B2, B5, B6.
    @raise Invalid_argument if [priority] is negative. *)

val drain : 'a t -> 'a list * 'a t
(** `Dispatcher.drain` / `runTasks` (Fibers.lean:151-153): the whole snapshot in ascending
    priority and FIFO within a priority, and the empty disarmed dispatcher. B3, B4. *)

val length : 'a t -> int
(** The number of tasks a drain would deliver. O(the number of queued tasks). *)

val priorities : 'a t -> int list
(** Strictly ascending. B1. *)

val to_list : 'a t -> (int * 'a list) list
(** The canonical form: ascending priority, each bucket front-to-back. This is
    `Dispatcher.bucketPairs` (Lib/Deque.lean:320-322) with each `Deque` read as its `toList`,
    and it is what a snapshot serialises. Two dispatchers with the same `to_list` and the same
    `armed` are equal. *)

val of_list : armed:bool -> (int * 'a list) list -> 'a t
(** The inverse of {!to_list}. An empty bucket is preserved, so [to_list (of_list ~armed l) = l]
    for every admissible [l].
    @raise Invalid_argument if the priorities are not strictly ascending, or if one is negative
    (the invariant is carried in the type, as `Map.wf` is in Lean; a caller that needs a
    rejection checks first -- refusal row W4-MAP-OF-ALIST-EXN). *)

(** {1 The two carriers} *)

module type S = sig
  type 'a t

  val empty : 'a t
  val is_empty : 'a t -> bool
  val armed : 'a t -> bool
  val arm : 'a t -> 'a t
  val disarm : 'a t -> 'a t
  val enqueue : 'a t -> priority:int -> 'a -> 'a t
  val drain : 'a t -> 'a list * 'a t
  val length : 'a t -> int
  val priorities : 'a t -> int list
  val to_list : 'a t -> (int * 'a list) list
  val of_list : armed:bool -> (int * 'a list) list -> 'a t
end
(** The contract both carriers meet, and the contract lane G externs
    `Effect4.Machine.Dispatcher` onto. Every law B1-B7 above is a law of BOTH. *)

module Assoc : S with type 'a t = 'a t
(** The default carrier, and the one this module's top-level functions are (D-A3-1): the
    ascending assoc list of front/back pairs. *)

module Map_variant : S
(** The tripwire carrier of R-A3-4: `Map.Make(Int)` of front/back pairs. Same laws, same
    observations -- test_buckets.ml runs every property test and the 100 000-operation
    differential against the Lean transcription over BOTH. Measured slower at every priority
    count >= 4 and every drain depth >= 8 (design §6.2), which is why it is not the default. *)
