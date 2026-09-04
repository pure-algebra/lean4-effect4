import OCaml5.Lib.Map
import Effect4.Deep.Fibers

/-!
# `OCaml5.Lib.Deque` — `Core.Deque` and the dispatcher's priority buckets

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§2 ("the dispatcher's FIFO buckets are a `Map` keyed by priority of `Deque`s") and §4.2.
Report: `docs/research/2026-09-04-seat-w4-library-carriers.md`.

`Core.Deque.t` is a growable circular buffer with `enqueue`/`dequeue` at both ends. The carrier
is its `to_list`: the buffer's capacity, its physical index and its `Exn`/`Option` faces are not
observable in anything we claim. The dispatcher bucket structure the avatar hand-rolls is then
`Map Nat (Deque τ)` — `Buckets` below — and the four properties the avatar's scheduler rests on
are proved of it and *projected onto* `Effect4.Deep.Dispatcher`, which is the object the Deep
machine actually runs (`Effect4/Deep/Fibers.lean:114-152`, transcribing `Scheduler.ts:105-131`
and `:225-233`).

## Named properties (theorem names are stable; cite these)

FIFO, per bucket:

* `Deque.toList_enqueueBack` — `enqueue_back` appends at the tail.
* `Deque.dequeueFront_cons` — `dequeue_front` takes the head.
* `Deque.fifo` — **the FIFO law**: a `dequeue_front` after an `enqueue_back` still answers the
  older element; the new one is only reached when the deque was empty.
* `Deque.popAll_eq_toList` — draining a deque yields exactly `to_list`, in order.
* `Deque.length_enqueueBack` — one `enqueue_back` is one more element.

The dispatcher's buckets:

* `Buckets.drain_eq_flatten` — a drain is the concatenation of the buckets' lists.
* `Buckets.drain_priority_ascending` — those buckets are visited in strictly ascending priority
  (`Buckets.wf` is the invariant; `Map.keys_nodup` says a priority appears once).
* `Buckets.drain_fifo_within_bucket` — within one priority the order is the deque's, and
  `enqueue` appends at that bucket's tail.
* `Buckets.drained_once` — the drain empties the structure: a task enqueued during a drain waits
  for the next drain (`Scheduler.ts:225-233`).
* `Buckets.drain_enqueue_length` — one `enqueue` adds exactly one delivery.
* `Buckets.drain_enqueue_mem` — and that delivery is the enqueued task: **each task is delivered
  exactly once**.

The projection onto the Deep dispatcher:

* `Dispatcher.bucketPairs_enqueue` — `Effect4.Deep.Dispatcher.enqueue` *is* `Buckets.enqueue`
  through `bucketPairs`.
* `Dispatcher.enqueue_wf` — and it preserves the ascending-priority invariant, which
  `Dispatcher.empty` starts with (`Dispatcher.empty_wf`).
* `Dispatcher.drain_projection` — `Effect4.Deep.Dispatcher.drain` *is* `Buckets.drain`.
* `Dispatcher.drain_snd_empty` — the Deep dispatcher is drained once, as `Buckets` is.

Together these say the avatar may replace its hand-rolled bucket list by `Map Nat (Deque τ)`
without changing a single delivered task or its order.

## What each definition stands for

| here | OCaml / Deep | the law |
| --- | --- | --- |
| `Deque.empty` | `Core.Deque.create ()` | — |
| `Deque.enqueueBack` | `Core.Deque.enqueue_back` (= `enqueue \`back`) | `toList_enqueueBack`, `fifo` |
| `Deque.enqueueFront` | `Core.Deque.enqueue_front` | `toList_enqueueFront` |
| `Deque.dequeueFront` | `Core.Deque.dequeue_front` (the `option` face) | `dequeueFront_cons`, `fifo` |
| `Deque.dequeueBack` | `Core.Deque.dequeue_back` | `dequeueBack_snoc` |
| `Deque.length` | `Core.Deque.length` | `length_enqueueBack` |
| `Deque.toList` | `Core.Deque.to_list` (front to back) | every law above |
| `Buckets` | the avatar's priority buckets; `Effect4.Deep.Dispatcher.buckets` | the projection |
| `Buckets.enqueue` | `Effect4.Deep.Dispatcher.enqueue` (`Scheduler.ts:105-131`) | `bucketPairs_enqueue` |
| `Buckets.drain` | `Effect4.Deep.Dispatcher.drain` (`runTasks`, `Scheduler.ts:225-233`) | `drain_projection` |

## Refusals

* **`Core.Deque`'s capacity, `blit`, `Exn` face and physical mutation.** The carrier is the
  `to_list`; `dequeue_front_exn` raising on empty is the `none` of `dequeueFront`, and a caller
  that needs the exception must check first. Refusal row `W4-DEQ-CAPACITY`.
* **`armed`.** `Effect4.Deep.Dispatcher` carries `armed : Bool` — "the host callback is
  scheduled" (`Scheduler.ts:207-212`) — which is a *host* fact, not a bucket fact, and has no
  counterpart in `Buckets`. The projection therefore forgets it, and any claim about arming is
  the host's. Refusal row `W4-DEQ-ARMED`.
* **The cross-dispatcher flush order.** `Effect4/Deep/Fibers.lean:1130` records it as an
  assumption and the avatar corpus found it observable; nothing here changes that. Refusal row
  `W4-DEQ-CROSS-DISPATCHER` (the existing Deep gap).
-/

set_option autoImplicit false

namespace OCaml5.Lib

universe u v w

/-! ## `Core.Deque` -/

/-- `Core.Deque.t`, as its `to_list`: front first, back last. -/
structure Deque (τ : Type w) : Type w where
  /-- `Core.Deque.to_list`. -/
  toList : List τ
deriving DecidableEq, Repr, Inhabited

namespace Deque

variable {τ : Type w}

@[ext] theorem ext {d₁ d₂ : Deque τ} (h : d₁.toList = d₂.toList) : d₁ = d₂ := by
  cases d₁; cases d₂; cases h; rfl

/-- `Core.Deque.create ()`. -/
def empty : Deque τ := ⟨[]⟩

/-- `Core.Deque.enqueue_back`. -/
def enqueueBack (d : Deque τ) (x : τ) : Deque τ := ⟨d.toList ++ [x]⟩

/-- `Core.Deque.enqueue_front`. -/
def enqueueFront (d : Deque τ) (x : τ) : Deque τ := ⟨x :: d.toList⟩

/-- `Core.Deque.dequeue_front`, the `option` face. -/
def dequeueFront (d : Deque τ) : Option (τ × Deque τ) :=
  match d.toList with
  | [] => none
  | x :: r => some (x, ⟨r⟩)

/-- `Core.Deque.dequeue_back`, the `option` face. -/
def dequeueBack (d : Deque τ) : Option (τ × Deque τ) :=
  match d.toList.reverse with
  | [] => none
  | x :: r => some (x, ⟨r.reverse⟩)

/-- `Core.Deque.length`. -/
def length (d : Deque τ) : Nat := d.toList.length

/-- `Core.Deque.is_empty`. -/
def isEmpty (d : Deque τ) : Bool := d.toList.isEmpty

/-- Repeated `dequeue_front`, fuel-bounded. -/
def popAll : Nat → Deque τ → List τ
  | 0, _ => []
  | n + 1, d =>
    match d.dequeueFront with
    | none => []
    | some (x, d') => x :: popAll n d'

/-! ### The laws -/

@[simp] theorem toList_empty : (empty : Deque τ).toList = [] := rfl

@[simp] theorem toList_enqueueBack (d : Deque τ) (x : τ) :
    (d.enqueueBack x).toList = d.toList ++ [x] := rfl

@[simp] theorem toList_enqueueFront (d : Deque τ) (x : τ) :
    (d.enqueueFront x).toList = x :: d.toList := rfl

@[simp] theorem dequeueFront_empty : (empty : Deque τ).dequeueFront = none := rfl

theorem dequeueFront_cons (x : τ) (r : List τ) :
    (⟨x :: r⟩ : Deque τ).dequeueFront = some (x, ⟨r⟩) := rfl

theorem dequeueBack_snoc (r : List τ) (x : τ) :
    (⟨r ++ [x]⟩ : Deque τ).dequeueBack = some (x, ⟨r⟩) := by
  simp [dequeueBack]

@[simp] theorem length_enqueueBack (d : Deque τ) (x : τ) :
    (d.enqueueBack x).length = d.length + 1 := by
  simp [length, enqueueBack]

/-- **FIFO.** An `enqueue_back` never overtakes what is already queued: `dequeue_front` after it
answers the same element it would have answered before, and the new element is reached only when
the deque was empty. -/
theorem fifo (d : Deque τ) (x : τ) :
    (d.enqueueBack x).dequeueFront =
      (match d.dequeueFront with
       | some (y, d') => some (y, d'.enqueueBack x)
       | none => some (x, empty)) := by
  cases h : d.toList with
  | nil => simp [dequeueFront, enqueueBack, h, empty]
  | cons y r => simp [dequeueFront, enqueueBack, h]

/-- **A drain delivers exactly `to_list`, in order.** -/
theorem popAll_eq_toList : ∀ (n : Nat) (d : Deque τ), d.toList.length ≤ n → popAll n d = d.toList
  | 0, d, h => by
    cases hd : d.toList with
    | nil => simp [popAll]
    | cons x r => rw [hd] at h; simp at h
  | n + 1, d, h => by
    cases hd : d.toList with
    | nil => simp [popAll, dequeueFront, hd]
    | cons x r =>
      rw [hd] at h
      simp only [popAll, dequeueFront, hd]
      rw [popAll_eq_toList n ⟨r⟩ (by simp at h ⊢; omega)]

end Deque

/-! ## The dispatcher's priority buckets -/

/-- The dispatcher bucket structure: a `Map` keyed by priority of `Deque`s. This is what the
plan §2 says the avatar's hand-rolled buckets should become. -/
abbrev Buckets (τ : Type w) := Map Nat (Deque τ)

namespace Buckets

variable {τ : Type w}

/-- The empty dispatcher. -/
def empty : Buckets τ := Map.empty

/-- `Effect4.Deep.Dispatcher.enqueue` (`Scheduler.ts:105-131`): append at the tail of the
priority's bucket, creating the bucket if there is none. -/
def enqueue (b : Buckets τ) (p : Nat) (t : τ) : Buckets τ :=
  b.set p (((b.find p).getD Deque.empty).enqueueBack t)

/-- The tasks a drain delivers: every bucket's deque, in ascending priority. -/
def drainTasks (b : Buckets τ) : List τ :=
  b.fold [] (fun _ dq acc => acc ++ dq.toList)

/-- `Effect4.Deep.Dispatcher.drain` (`runTasks`, `Scheduler.ts:225-233`): the snapshot, and an
empty dispatcher. -/
def drain (b : Buckets τ) : List τ × Buckets τ := (drainTasks b, empty)

private theorem foldl_append_flatten :
    ∀ (l : List (Nat × Deque τ)) (acc : List τ),
      l.foldl (fun a (e : Nat × Deque τ) => a ++ e.2.toList) acc
        = acc ++ (l.map (·.2.toList)).flatten
  | [], acc => by simp
  | e :: r, acc => by
    simp only [List.foldl_cons, List.map_cons, List.flatten_cons]
    rw [foldl_append_flatten r (acc ++ e.2.toList)]
    simp

/-- **A drain is the concatenation of the buckets' lists**, in the map's key order. -/
theorem drain_eq_flatten (b : Buckets τ) :
    drainTasks b = (b.entries.map (·.2.toList)).flatten := by
  simp [drainTasks, Map.fold, foldl_append_flatten b.entries []]

/-- **Priorities are visited in strictly ascending order**, and each exactly once. -/
theorem drain_priority_ascending (b : Buckets τ) : strictAsc b.entries = true := b.wf

theorem drain_priority_nodup (b : Buckets τ) : b.keys.Nodup := Map.keys_nodup b

/-- **FIFO within a bucket.** `enqueue` appends at the tail of exactly its own priority's deque,
and leaves every other priority alone. -/
theorem drain_fifo_within_bucket (b : Buckets τ) (p : Nat) (t : τ) :
    (b.enqueue p t).find p = some (((b.find p).getD Deque.empty).enqueueBack t) := by
  simp [enqueue]

theorem enqueue_find_other (b : Buckets τ) (p q : Nat) (t : τ) (h : q ≠ p) :
    (b.enqueue p t).find q = b.find q := by
  simp [enqueue, Map.find_set_other _ _ _ _ h]

/-- **Drained once.** The drain hands back an empty dispatcher, so a task enqueued during the
drain waits for the next one. -/
theorem drained_once (b : Buckets τ) : (drain b).2 = empty := rfl

/-! ### Exactly one delivery per `enqueue` -/

private theorem length_flatten_insert (p : Nat) (d : Deque τ) :
    ∀ {l : List (Nat × Deque τ)}, strictAsc l = true →
      ((insertIn p d l).map (·.2.toList)).flatten.length
          + ((findIn p l).getD Deque.empty).toList.length
        = (l.map (·.2.toList)).flatten.length + d.toList.length
  | [], _ => by simp [insertIn, findIn, Deque.empty]
  | e :: r, hwf => by
    rcases LinOrd.cmp_total p e.1 with h | h | h
    · have hne : LinOrd.cmp p e.1 ≠ Ordering.eq := by rw [h]; intro hc; cases hc
      have hrest : findIn p r = none := by
        refine findIn_none_of_all_lt (fun x hx => ?_)
        exact LinOrd.cmp_trans_lt h (strictAsc_head_lt hwf x hx)
      rw [insertIn_cons_lt h, findIn_cons_ne hne, hrest]
      simp [Deque.empty]
      omega
    · rw [insertIn_cons_eq h, findIn_cons_eq h]
      simp
      omega
    · have hne : LinOrd.cmp p e.1 ≠ Ordering.eq := by rw [h]; intro hc; cases hc
      have ih := length_flatten_insert p d (l := r) (strictAsc_of_cons hwf)
      rw [insertIn_cons_gt h, findIn_cons_ne hne]
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      omega

/-- **Exactly one more delivery.** -/
theorem drain_enqueue_length (b : Buckets τ) (p : Nat) (t : τ) :
    (drainTasks (b.enqueue p t)).length = (drainTasks b).length + 1 := by
  have hfind : Map.find b p = findIn p b.entries := rfl
  have key := length_flatten_insert (τ := τ) p
    (((findIn p b.entries).getD Deque.empty).enqueueBack t) b.wf
  rw [drain_eq_flatten, drain_eq_flatten]
  show ((insertIn p (((Map.find b p).getD Deque.empty).enqueueBack t) b.entries).map
    (·.2.toList)).flatten.length = (b.entries.map (·.2.toList)).flatten.length + 1
  rw [hfind]
  simp only [Deque.toList_enqueueBack, List.length_append, List.length_cons,
    List.length_nil] at key
  omega

private theorem mem_insertIn (p : Nat) (d : Deque τ) :
    ∀ l : List (Nat × Deque τ), (p, d) ∈ insertIn p d l
  | [] => by simp [insertIn]
  | e :: r => by
    rcases LinOrd.cmp_total p e.1 with h | h | h
    · rw [insertIn_cons_lt h]; simp
    · rw [insertIn_cons_eq h]; simp
    · rw [insertIn_cons_gt h]; exact List.mem_cons_of_mem _ (mem_insertIn p d r)

/-- **And that delivery is the enqueued task.** -/
theorem drain_enqueue_mem (b : Buckets τ) (p : Nat) (t : τ) :
    t ∈ drainTasks (b.enqueue p t) := by
  rw [drain_eq_flatten]
  refine List.mem_flatten.mpr ⟨(((b.find p).getD Deque.empty).enqueueBack t).toList, ?_, ?_⟩
  · refine List.mem_map.mpr ⟨(p, ((b.find p).getD Deque.empty).enqueueBack t), ?_, rfl⟩
    exact mem_insertIn p _ b.entries
  · simp [Deque.enqueueBack]

end Buckets

/-! ## The projection onto `Effect4.Deep.Dispatcher` -/

namespace Dispatcher

open Effect4.Deep

variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}

/-- The Deep dispatcher's bucket list, read as `Buckets` entries. -/
def bucketPairs (bs : List (Bucket ν σ β ε δ ι α)) :
    List (Nat × Deque (Task ν σ β ε δ ι α)) :=
  bs.map fun b => (b.priority, ⟨b.tasks⟩)

/-- The invariant the Deep dispatcher's bucket list carries but does not state: strictly
ascending priorities. `Effect4.Deep.Dispatcher.insert` is `private`, so the invariant is
recovered here from the *reflected* unfolding equation `enqueue_unfold`, which holds by `rfl`. -/
def Wf (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) : Prop :=
  strictAsc (bucketPairs d.buckets) = true

/-- The unfolding of `Effect4.Deep.Dispatcher.enqueue` at a non-empty bucket list, which holds
definitionally even though the `insert` it calls is `private`. -/
theorem enqueue_unfold (a : Bool) (p : Nat) (t : Task ν σ β ε δ ι α)
    (b : Bucket ν σ β ε δ ι α) (rest : List (Bucket ν σ β ε δ ι α)) :
    ((Effect4.Deep.Dispatcher.mk (b :: rest) a).enqueue p t).buckets
      = (if b.priority = p then (⟨b.priority, b.tasks ++ [t]⟩ : Bucket ν σ β ε δ ι α) :: rest
         else if p < b.priority then ⟨p, [t]⟩ :: b :: rest
         else b :: ((Effect4.Deep.Dispatcher.mk rest a).enqueue p t).buckets) := rfl

theorem enqueue_unfold_nil (a : Bool) (p : Nat) (t : Task ν σ β ε δ ι α) :
    ((Effect4.Deep.Dispatcher.mk [] a).enqueue p t).buckets
      = [(⟨p, [t]⟩ : Bucket ν σ β ε δ ι α)] := rfl

private theorem findIn_none_of_lt_head (p : Nat) :
    ∀ {bs : List (Bucket ν σ β ε δ ι α)}, strictAsc (bucketPairs bs) = true →
      (∀ b ∈ bs, p < b.priority) →
      findIn p (bucketPairs bs) = none := by
  intro bs _ h
  refine findIn_none_of_all_lt (fun x hx => ?_)
  obtain ⟨b, hb, hbx⟩ := List.mem_map.mp hx
  have := h b hb
  rw [← hbx]
  exact natCmp_lt_iff.mpr this

/-- **`Effect4.Deep.Dispatcher.enqueue` is `Buckets.enqueue`.** -/
theorem bucketPairs_enqueue (a : Bool) (p : Nat) (t : Task ν σ β ε δ ι α) :
    ∀ bs : List (Bucket ν σ β ε δ ι α), strictAsc (bucketPairs bs) = true →
      bucketPairs ((Effect4.Deep.Dispatcher.mk bs a).enqueue p t).buckets
        = insertIn p (((findIn p (bucketPairs bs)).getD Deque.empty).enqueueBack t)
            (bucketPairs bs)
  | [], _ => by
    rw [enqueue_unfold_nil]
    simp [bucketPairs, insertIn, findIn, Deque.empty, Deque.enqueueBack]
  | b :: rest, hwf => by
    rw [enqueue_unfold]
    have hhead : bucketPairs (b :: rest) = (b.priority, (⟨b.tasks⟩ : Deque _))
        :: bucketPairs rest := rfl
    by_cases h1 : b.priority = p
    · subst h1
      rw [if_pos rfl, hhead]
      have hc : LinOrd.cmp b.priority b.priority = Ordering.eq := LinOrd.cmp_self _
      rw [findIn_cons_eq hc, insertIn_cons_eq hc]
      simp [bucketPairs, Deque.enqueueBack]
    · by_cases h2 : p < b.priority
      · rw [if_neg h1, if_pos h2, hhead]
        have hlt : LinOrd.cmp p b.priority = Ordering.lt := natCmp_lt_iff.mpr h2
        have hne : LinOrd.cmp p b.priority ≠ Ordering.eq := by rw [hlt]; intro hc; cases hc
        rw [findIn_cons_ne hne]
        have hrest : findIn p (bucketPairs rest) = none := by
          refine findIn_none_of_all_lt (fun x hx => ?_)
          have := strictAsc_head_lt (r := bucketPairs rest) hwf x hx
          exact LinOrd.cmp_trans_lt hlt this
        rw [hrest, insertIn_cons_lt hlt]
        simp [bucketPairs, Deque.empty, Deque.enqueueBack]
      · rw [if_neg h1, if_neg h2, hhead]
        have hgt : LinOrd.cmp p b.priority = Ordering.gt :=
          natCmp_gt_iff.mpr (by omega)
        have hne : LinOrd.cmp p b.priority ≠ Ordering.eq := by rw [hgt]; intro hc; cases hc
        rw [findIn_cons_ne hne]
        have ih := bucketPairs_enqueue a p t rest (strictAsc_of_cons hwf)
        show (b.priority, (⟨b.tasks⟩ : Deque _))
            :: bucketPairs ((Effect4.Deep.Dispatcher.mk rest a).enqueue p t).buckets = _
        rw [ih, insertIn_cons_gt hgt]

/-- **And it preserves the ascending-priority invariant.** -/
theorem enqueue_wf (a : Bool) (p : Nat) (t : Task ν σ β ε δ ι α)
    (bs : List (Bucket ν σ β ε δ ι α)) (hwf : strictAsc (bucketPairs bs) = true) :
    strictAsc (bucketPairs ((Effect4.Deep.Dispatcher.mk bs a).enqueue p t).buckets) = true := by
  rw [bucketPairs_enqueue a p t bs hwf]
  exact strictAsc_insertIn _ _ hwf

/-- `Dispatcher.empty` satisfies it. -/
theorem empty_wf : Wf (Effect4.Deep.Dispatcher.empty (ν := ν) (σ := σ) (β := β)
    (ε := ε) (δ := δ) (ι := ι) (α := α)) := rfl

/-- The Deep dispatcher, read as a `Buckets`. -/
def toBuckets (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) (h : Wf d) :
    Buckets (Task ν σ β ε δ ι α) :=
  ⟨bucketPairs d.buckets, h⟩

/-- **`Effect4.Deep.Dispatcher.enqueue` is `Buckets.enqueue`, bundled.** -/
theorem toBuckets_enqueue (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) (h : Wf d)
    (p : Nat) (t : Task ν σ β ε δ ι α) (h' : Wf (d.enqueue p t)) :
    toBuckets (d.enqueue p t) h' = (toBuckets d h).enqueue p t := by
  refine Map.ext ?_
  show bucketPairs (d.enqueue p t).buckets = _
  cases d with
  | mk bs a => exact bucketPairs_enqueue a p t bs h

/-- **`Effect4.Deep.Dispatcher.drain` is `Buckets.drain`.** -/
theorem drain_projection (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) (h : Wf d) :
    (Effect4.Deep.Dispatcher.drain d).1 = Buckets.drainTasks (toBuckets d h) := by
  rw [Buckets.drain_eq_flatten]
  show (d.buckets.map Effect4.Deep.Bucket.tasks).flatten = _
  simp only [toBuckets, bucketPairs, List.map_map]
  rfl

/-- And the Deep dispatcher is drained once, as `Buckets` is. -/
theorem drain_snd_empty (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) :
    (Effect4.Deep.Dispatcher.drain d).2 = Effect4.Deep.Dispatcher.empty := rfl

end Dispatcher

end OCaml5.Lib
