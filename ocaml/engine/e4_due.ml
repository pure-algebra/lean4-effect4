(* e4_due.ml — the due-resume queue and the declared family order.
   The property list, ORD-FAM and the refusals are in e4_due.mli.

   THE CARRIER: a fixed EIGHT-SLOT RECORD, one front/back pair per family, and not a map from
   family to queue. That is what makes U1 hold by construction -- `drain` is a concatenation
   the type forces to mention every family exactly once, in the order the record's accessors
   are written, so a family cannot be silently missing and an order cannot be silently
   data-dependent. A map would move that guarantee to run time.

   The pair is the same deque as E4_buckets': contents = front @ List.rev back, `owe` conses
   onto back, `drain` reverses each back exactly once. `due := due ++ waiters.map ...`
   (Stores.lean:1416) is the same observation at quadratic cost. *)

type family =
  | Deferred
  | Timer
  | Memo
  | Queue
  | Semaphore
  | Latch
  | PubSub
  | External

(* ORD-FAM. Append-only: a retired family's ordinal is never reused and no ordinal is ever
   renumbered (CAS amendment M17). The match is total and has no wildcard, so adding a family
   to the type is a compile error here, in `families`, in `name` and in `slots` -- which is
   exactly where the four things a new family needs are. *)
let ordinal = function
  | Deferred -> 0
  | Timer -> 1
  | Memo -> 2
  | Queue -> 3
  | Semaphore -> 4
  | Latch -> 5
  | PubSub -> 6
  | External -> 7

let family_count = 8

let families =
  [ Deferred; Timer; Memo; Queue; Semaphore; Latch; PubSub; External ]

let name = function
  | Deferred -> "Deferred"
  | Timer -> "Timer"
  | Memo -> "Memo"
  | Queue -> "Queue"
  | Semaphore -> "Semaphore"
  | Latch -> "Latch"
  | PubSub -> "PubSub"
  | External -> "External"

(* One family's owed resumes: front @ List.rev back, in registration order. *)
type 'a q = { front : 'a list; back : 'a list }

let q_empty = { front = []; back = [] }
let q_is_empty q = match (q.front, q.back) with [], [] -> true | _ -> false
let q_to_list q = q.front @ List.rev q.back
let q_length q = List.length q.front + List.length q.back
let q_owe q x = { q with back = x :: q.back }
let q_owe_all q xs = { q with back = List.rev_append xs q.back }

type 'a t =
  { deferred : 'a q
  ; timer : 'a q
  ; memo : 'a q
  ; queue : 'a q
  ; semaphore : 'a q
  ; latch : 'a q
  ; pubsub : 'a q
  ; external_ : 'a q
  }

let empty =
  { deferred = q_empty
  ; timer = q_empty
  ; memo = q_empty
  ; queue = q_empty
  ; semaphore = q_empty
  ; latch = q_empty
  ; pubsub = q_empty
  ; external_ = q_empty
  }

let slot t = function
  | Deferred -> t.deferred
  | Timer -> t.timer
  | Memo -> t.memo
  | Queue -> t.queue
  | Semaphore -> t.semaphore
  | Latch -> t.latch
  | PubSub -> t.pubsub
  | External -> t.external_

let with_slot t f q =
  match f with
  | Deferred -> { t with deferred = q }
  | Timer -> { t with timer = q }
  | Memo -> { t with memo = q }
  | Queue -> { t with queue = q }
  | Semaphore -> { t with semaphore = q }
  | Latch -> { t with latch = q }
  | PubSub -> { t with pubsub = q }
  | External -> { t with external_ = q }

let is_empty t = List.for_all (fun f -> q_is_empty (slot t f)) families
let length t = List.fold_left (fun n f -> n + q_length (slot t f)) 0 families
let owe t f x = with_slot t f (q_owe (slot t f) x)
let owe_all t f xs = with_slot t f (q_owe_all (slot t f) xs)
let pending t f = q_to_list (slot t f)

(* U1: the concatenation, ORD-FAM order, each family in registration order. `fold_right` over
   EIGHT families, never over the resumes. *)
let drain_under t order =
  List.fold_right (fun f acc -> pending t f @ acc) order []

let drain t = (drain_under t families, empty)
let to_list t = List.map (fun f -> (f, pending t f)) families
