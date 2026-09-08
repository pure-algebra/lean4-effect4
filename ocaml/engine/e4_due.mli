(* e4_due.mli — the due-resume queue and the declared family order.

   What it is: the resumes the stores owe now. `RunInterp.dueResumes`
   (src/Effect4/Machine/Fibers.lean:483-485) is one `St -> List (FiberId x Nat x k) x St`
   with no composition law: with two families owing resumes the interleaving is a semantic
   choice nothing states (probe gap G2, decision D6). This module states it.

   THE FAMILY ORDER (ORD-FAM), declared here once, before Queue lands:

       0 Deferred    1 Timer    2 Memo    3 Queue
       4 Semaphore   5 Latch    6 PubSub  7 External

   `drain` is the concatenation of the families' lists in that ordinal order, each family's
   own list in registration order. Ordinals are append-only: a retired family's ordinal is
   never reused and no ordinal is ever renumbered (proposal 1; CAS amendment M17 -- an ordinal
   is a position in a content table). Deferred is 0 because `dueResumes` is
   `deferreds.drainDue` today (Stores.lean:2446-2448), so every trace the corpus already has
   stays byte-identical when the other families arrive.
   Depends on: nothing (polymorphic in the resume; Stdlib only).

   Properties:
     U1  Concatenation in ORD-FAM order: `drain t` = `pending t f0 @ pending t f1 @ ...` over
         `families`, and `families` is total, duplicate-free and ascending in `ordinal`.
         [by construction (a fixed eight-slot record, not a map); tested: due-family-order]
     U2  Registration order within a family: `owe` appends at the tail.
         [by construction (front/back pair); licensed by deferredStore_complete_due
         (Stores.lean:1416, :1532); tested: due-registration-order]
     U3  Drained once, every family: `drain` returns the empty queue.
         [by construction; licensed by DeferredStore.drainDue (Stores.lean:1419-1420);
         tested: due-drained-once]
     U4  Exactly once: every `owe`d resume is returned by exactly one `drain`.
         [by construction; tested: due-exactly-once]
     U5  Persistence, as E4_buckets' B7: no mutable field, no array, no Hashtbl/Buffer/Queue,
         so a saved machine holding a `t` holds no mutable structure (brief rule 3).
         [by construction; tested: due-persistent]

   THE MUTATION TEST (design §4.1, "swap two families in ORD-FAM"): test_due.ml runs the same
   drain under a deliberately wrong family order and asserts the observable difference, so the
   law is pinned by a test that goes red rather than by a comment. Test: due-family-order-mutation.

   Refused: a priority or a fairness rule across families. Fairness is not among the decision
   sources the tape covers (grill ruling 11); the order is fixed, declared and dull.
   Refusal row A3-DUE-FAIRNESS. *)

type family =
  | Deferred  (** ordinal 0 -- `Deferred.ts`, the only family today *)
  | Timer  (** ordinal 1 -- slice A4 *)
  | Memo  (** ordinal 2 -- the memo world's completion *)
  | Queue  (** ordinal 3 *)
  | Semaphore  (** ordinal 4 *)
  | Latch  (** ordinal 5 *)
  | PubSub  (** ordinal 6 *)
  | External  (** ordinal 7 -- X2's foreign row answers *)

val ordinal : family -> int
(** Append-only. Never renumbered, never reused. *)

val family_count : int
(** The number of families, a named constant in the file. Every ordinal is in
    [0, family_count).  *)

val families : family list
(** Every family, ascending in {!ordinal}; total, duplicate-free. U1. *)

val name : family -> string
(** The family's name, for a receipt or a test transcript. Never an identity. *)

type 'a t
(** The owed resumes of every family. Persistent. ['a] is the resume payload; in the machine
    it is `FiberId * token * answer-code`. *)

val empty : 'a t
val is_empty : 'a t -> bool

val length : 'a t -> int
(** The number of resumes a drain would deliver, over every family. *)

val owe : 'a t -> family -> 'a -> 'a t
(** Append one resume to a family's list. U2. *)

val owe_all : 'a t -> family -> 'a list -> 'a t
(** Append a list, order preserved. This is the shape a completion uses:
    `due := due ++ waiters.map ...` (Stores.lean:1416). *)

val pending : 'a t -> family -> 'a list
(** One family's owed resumes, in registration order. A free row (design §1.3.4): no fuel, no
    tape, no state change. *)

val drain : 'a t -> 'a list * 'a t
(** Every family, in ORD-FAM order, and the empty queue. U1, U3, U4. *)

val to_list : 'a t -> (family * 'a list) list
(** The canonical snapshot form: every family in ORD-FAM order, empty lists included, so the
    serialised shape does not depend on which families happen to be non-empty. *)

val drain_under : 'a t -> family list -> 'a list
(** The drain the given family order would produce, WITHOUT taking it: [drain_under t families]
    is [fst (drain t)]. It exists for one reason -- the ORD-FAM mutation test, which runs it
    under a swapped order and asserts the difference. It takes no state, so it is a free row
    and cannot be used to smuggle a fairness rule in: the machine calls {!drain}. *)
