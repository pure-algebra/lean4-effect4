(* e4_wake.mli — the one allocation-and-wake protocol: waiter list + completion + WakePhase.

   What it is: the shared core every coordination family instantiates (grill agenda §1 Q5:
   "one allocation-and-wake protocol: waiter list + completion + WakePhase : Nat +
   cancelled-waiter disposition"). Deferred is the instance that exists today
   (Stores.lean:1341-1422); Timer is the instance keyed by deadline; Queue, Semaphore, Latch
   and PubSub follow. TxRef is NOT a member -- it is its own subcalculus with retry/orElse
   (lit-siblings Q5; kcas.mli "repeatedly calls").
   Depends on: nothing (polymorphic in the completion; Stdlib.Map only).

   THE PHASE. Each cell carries `phase : int`, incremented by every completion or signal. A
   waiter records the phase it registered at. The phase is our `In_transition`
   (Eio sem_state.ml, survey §8.2): it is what tells a canceller whether the resumer already
   won.

   Properties:
     W1  Registration order. `register` appends; a completion moves waiters into the due list
         in registration order, and close/error fulfil pending waiters IN REQUEST ORDER.
         [by construction; licensed by Stores.lean:1416, deferredStore_complete_due (:1532);
         WHATWG fixture F4; tested: wake-registration-order]
     W2  Register on a settled cell answers now and queues nothing. A cell that already holds
         a completion answers `Answer c` synchronously and its waiter list is untouched.
         [by construction; licensed by DeferredStore.register (Stores.lean:1386-1393);
         WHATWG fixture F2; tested: wake-settled-register]
     W3  Completion is once. A second `complete` changes nothing and reports `Already`; the
         first clears the waiter list AND appends every waiter to the due list -- both halves,
         in one step.
         [by construction; licensed by DeferredStore.complete (Stores.lean:1407-1416);
         WHATWG fixture F5c (their shipped defect was clearing one list and not the other);
         tested: wake-complete-once]
     W4  THE CANCELLED WAITER OWES ONE WAKE. Cancelling a waiter whose recorded phase EQUALS
         the cell's phase splices it out and owes nothing. Cancelling a waiter whose recorded
         phase is LESS than the cell's phase means the resumer already consumed a wake on its
         behalf, so the cancelling step must itself perform one wake: `cancel` reports
         `Owes_wake` and hands back the next waiter to resume.
         [stated, not derivable; survey #17 / Eio sem_state.ml; tested: wake-cancel-owes]
     W4a THE SUB-CASE W4 DOES NOT NAME, decided here: if the cell's phase has advanced but NO
         waiter remains to hand the wake to, `cancel` reports `Removed`. The obligation is
         discharged vacuously -- there is no waiter, so an `Owes_wake` would name nobody. This
         is the only arm of W4 the design left open and it is recorded as a deviation in
         docs/research/2026-09-08-engine-lane-q1-delivery.md.
         [stated; tested: wake-cancel-owes]
     W5  Capture. A waiter row carries the (cell, phase) it registered at, so replacing the
         cell's contents later cannot retarget an outstanding wake.
         [by construction; WHATWG fixture F1 (transform-backpressure.contract.md:141);
         tested: wake-capture]
     W6  Coalescing. A second `signal` on a cell whose phase a waiter has already observed is
         a no-op for that waiter: at most one pending wake per (cell, waiter). The guard IS
         the phase equality; there is no separate flag.
         [by construction; tested: wake-coalesce]
     W7  Spurious wakes are permitted. The signal-then-repoll families (Queue) may wake a
         waiter that then finds the resource gone; the waiter answers `Delay` and is
         re-presented. This is the price of keeping WHICH waiter gets WHICH item on the tape
         instead of hiding it inside a payload handoff (survey §8.2 (c)).
         [stated as a permission, not a property to test; the Delay budget is DL3 below]
     W8  Wake order within a family is FIFO, fixed per family as a PROFILE FIELD, never a
         runtime choice, because it changes observable wake order (Picos `Computation`'s
         FIFO/LIFO mode is a runtime choice -- we refuse that). Refusal row A3-WAKE-MODE.
         [by construction: this file offers no mode and no comparison on waiters]

   THE DELAY ANSWER (survey #1, Riot proc_state.mli; proposal 11):
     DL1  `Delay` means "not ready, re-present the SAME row next round, do not consume the
          fiber's frame, charge no fuel for the re-presentation, emit no trace row".
     DL2  `Delay` is a STORE answer, a function of the saved store, and therefore NOT a
          decision and NOT a tape entry: INV-TAPE-1 holds because there is no choice to
          record. (Owner question Q-A3-4.)
     DL3  Re-presentation is bounded: `delay_budget` re-presentations of one (fiber, token)
          without an intervening state change is a frontier naming the row, never a silent
          spin (DB-04 forbids a silent spin). The COUNTER lives in the driver that
          re-presents the row, not in a cell -- a cell that counted re-presentations would put
          a host fact into a saved machine. This module supplies the bound and nothing else;
          test_wake.ml pins it (test: wake-delay-budget). *)

type phase = int

type waiter =
  { fiber : int
  ; token : int
  ; at_phase : phase  (** W5: captured at registration, never rewritten *)
  }

type cell_id = int

type 'a step_answer =
  | Answer of 'a  (** the row is answered now, synchronously *)
  | Park of phase  (** the fiber parks on its token; the phase it registered at *)
  | Delay  (** DL1: not ready, re-present, consume nothing *)
  | Refuse
      (** the handle is unknown: a frontier, never a hang. This is the arm probe gap G1 says
          `registerAsync` lacks today (2026-09-07-probe-stores-performance.md:265). *)

type 'a cell =
  { completion : 'a option
  ; waiters : waiter list  (** registration order *)
  ; phase : phase
  }

type 'a t
(** The cells of ONE family. Persistent. The owed resumes live in {!E4_due}, not here, so the
    family order is stated once. *)

val empty : 'a t
val alloc : 'a t -> cell_id * 'a t
val size : 'a t -> int
val get : 'a t -> cell_id -> 'a cell option

val register : 'a t -> cell_id -> fiber:int -> token:int -> 'a t * 'a step_answer
(** `_await` (Deferred.ts:173-177): answer now when the cell is settled (W2), otherwise append
    this waiter and park at the cell's current phase (W1, W5). An unknown cell is [Refuse]. *)

val cancel :
  'a t -> cell_id -> waiter -> 'a t * [ `Removed | `Owes_wake of waiter | `Unknown ]
(** `_await`'s cleanup (Deferred.ts:178-185). W4: [`Owes_wake w] means the resumer already
    consumed a wake for this waiter and [w] must be resumed by the cancelling step. W4a: with
    no waiter left to hand it to, the answer is [`Removed]. *)

val complete :
  'a t -> cell_id -> 'a -> 'a t * [ `Completed of waiter list | `Already | `Unknown ]
(** `doneUnsafe` (Deferred.ts:1648-1662): store the completion, clear the waiter list, bump
    the phase, and hand back every waiter in registration order for {!E4_due.owe_all}. W3. *)

val signal : 'a t -> cell_id -> count:int -> 'a t * waiter list
(** The signal-then-repoll shape (Queue, Semaphore): bump the phase and hand back at most
    [count] waiters from the head, without settling the cell. W6, W7. An unknown cell bumps
    nothing and hands back no waiter. A [count] below zero takes none, and still bumps the
    phase (F5a's rule: the bump is unconditional). *)

val poll : 'a t -> cell_id -> 'a option option
(** `poll` (Deferred.ts:1414-1416). A FREE ROW: no fuel, no tape, no state change. *)

val is_done : 'a t -> cell_id -> bool option
(** `isDoneUnsafe` (Deferred.ts:1382). A FREE ROW. *)

val phase_of : 'a t -> cell_id -> phase option

val waiters_of : 'a t -> cell_id -> waiter list
(** Both FREE ROWS. An unknown cell has no waiter. *)

val delay_budget : int
(** DL3. A constant in the file; the profile may lower it, never raise it. *)
