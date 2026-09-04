import Effect4.Evidence.Char.Core

/-!
# Char.Queue.Machine: carriers and step of the bounded suspend-strategy Queue

Hand-authored parts 1 and 2 of the five: the carriers and the step. Ported from
`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/EffectQueue.lean`
(`EffectQueue`, `offer`, `fail`, `shutdown`, `takeAll`, `wake`, lines 45-131) into
the label-carries-answer shape of `workshop/Char/01-model/01-queue-port-plan.md`.
Every `Queue.ts` citation below is at `effect@4.0.0-rc.112`,
`vendor/effect-4.0.0-rc.112/src/Queue.ts`, SHA-256
`dc355d1a09662ae7b023c98ad47b7fe71051becaf9d461f244c37ad0a4d3dc35`. Line numbers
are advisory; the span digests in section 02-pins are what survives a move.

| Label | `EffectQueue` operation | `Queue.ts` (rc.112) |
| --- | --- | --- |
| `offer m` | `offer cap q m`, `.accepted` and `.refused` | `offer` 645, refused 647-648, append 666 |
| `takeAll c` | `takeAll q`, `.chunk` on `opened` and `closing` | `takeAll` 1297; `takeBetweenUnsafe` 1977-1999; `releaseCapacity` 2037, finalize 2042-2046 |
| `takeExit e` | `takeAll q` and `wake q` on `done e`, `.exit e` | `takeUnsafe` 1606, the `Done` arm 1607-1609, ends 1623 |
| `takePark` | `takeAll q`, `.parked` | `scheduleReleaseTaker` 1969-1975 |
| `wake c` | `wake q`, `.chunk` | `releaseTakers` 1955-1967 |
| `fail e` | `fail q e` | `failCauseUnsafe` 1000-1015 |
| `shutdown` | `shutdown q` | `shutdown` 1191-1210, `MutableList.clear` 1196 |

Three unifications delete a case each (item 01 section 1): `wake` and `takeAll`
on `done` are the one label `takeExit`; `.parked` is a label with an empty reading
and `.interrupted` is the absence of a step; `.wouldSuspend` is the disabled step,
which keeps the B1/B2 boundary explicit. `size` (`sizeUnsafe`, `Queue.ts:1789`)
is an observation, not a verb, and is the reading's `residue`.

The one correction to the design report's step: `takeExit` clears the parked
taker, as `EffectQueue.wake`'s own `done` arm does (`EffectQueue.lean:129`).
Without it `QInv.takerLive` is false; the refutation is
`Effect4.Char.Queue.Refute.doc_step_breaks_takerLive` in `Mutants.lean`.
-/

set_option autoImplicit false

namespace Effect4.Char.Queue

open Effect4.Char

/-! ## Carriers -/

/-- The queue's status. `closing e` keeps a non-empty buffer after a failure;
`done e` is `Done` with the failure `e`; `shutdown` is `Done` with the interrupt
exit. -/
inductive QStatus where
  | opened
  | closing (err : Nat)
  | done (err : Nat)
  | shutdown
deriving DecidableEq, Repr, Inhabited

/-- The queue's state. `buffer` is oldest first; `taker` records a `takeAll`
parked on an open empty buffer. -/
structure QState where
  buffer : List Item
  status : QStatus
  taker : Bool
deriving DecidableEq, Repr, Inhabited

/-- The alphabet. Answers live in the label: `takeAll` and `wake` carry the
chunk they returned, `takeExit` the exit it returned. -/
inductive QLabel where
  | offer (item : Item)
  | takeAll (chunk : List Item)
  | takeExit (err : Nat)
  | takePark
  | wake (chunk : List Item)
  | fail (err : Nat)
  | shutdown
deriving DecidableEq, Repr, Inhabited

/-- The finite quotient of the alphabet by constructor, so a failure model is
first-order finite data. -/
inductive QKind where
  | offer | takeAll | takeExit | takePark | wake | fail | shutdown
deriving DecidableEq, Repr, Inhabited

/-- The constructor of a label. Generated from `QLabel` in the emitted tree;
hand-typed here from the item's text. -/
def qKind : QLabel → QKind
  | .offer _ => .offer
  | .takeAll _ => .takeAll
  | .takeExit _ => .takeExit
  | .takePark => .takePark
  | .wake _ => .wake
  | .fail _ => .fail
  | .shutdown => .shutdown

/-- The manifest spelling of a kind. -/
def qSpell : QKind → String
  | .offer => "offer"
  | .takeAll => "takeAll"
  | .takeExit => "takeExit"
  | .takePark => "takePark"
  | .wake => "wake"
  | .fail => "fail"
  | .shutdown => "shutdown"

/-- The alphabet morphism onto the kind quotient. -/
def queueKinds : Kinds QLabel QKind :=
  { kind := qKind
    all := [.offer, .takeAll, .takeExit, .takePark, .wake, .fail, .shutdown]
    spell := qSpell }

/-! ## The step -/

/-- The bounded suspend-strategy queue at capacity `cap`, sequential verbs only.
Total-or-disabled: `none` is a label not enabled here, never a failure. -/
def queue (cap : Nat) : Machine QState QLabel where
  init := { buffer := [], status := .opened, taker := false }
  step := fun s l =>
    match l, s.status with
    | .offer m, .opened =>
        if s.buffer.length < cap then some { s with buffer := s.buffer ++ [m] } else none
    | .offer _, _ => some s
    | .takeAll c, .opened =>
        if s.buffer ≠ [] ∧ c = s.buffer then some { s with buffer := [] } else none
    | .takeAll c, .closing e =>
        if s.buffer ≠ [] ∧ c = s.buffer then
          some { s with buffer := [], status := .done e } else none
    | .takeAll _, _ => none
    | .takeExit e, .done e' =>
        if e = e' then some { s with status := .shutdown, taker := false } else none
    | .takeExit _, _ => none
    | .takePark, .opened =>
        if s.buffer = [] ∧ !s.taker then some { s with taker := true } else none
    | .takePark, _ => none
    | .wake c, .opened =>
        if s.taker ∧ s.buffer ≠ [] ∧ c = s.buffer then
          some { s with buffer := [], taker := false } else none
    | .wake c, .closing e =>
        if s.taker ∧ s.buffer ≠ [] ∧ c = s.buffer then
          some { s with buffer := [], status := .done e, taker := false } else none
    | .wake _, _ => none
    | .fail e, .opened =>
        some (if s.buffer.isEmpty then { s with status := .done e }
              else { s with status := .closing e })
    | .fail _, _ => some s
    | .shutdown, _ => some { buffer := [], status := .shutdown, taker := false }

/-! ## The step equations

The eight theorems of `EffectQueueLaws.lean` that survive as step equations
(item 01 section 4), plus the two `wake` arms, which have no source theorem and
are stated here so every enabled arm of the step has one equation. -/

/-- `offer_admits` (`EffectQueueLaws.lean:56-61`): below capacity on an open
queue the item is appended (`Queue.ts:666`). -/
theorem queue_step_offer_admits (cap : Nat) (s : QState) (m : Item)
    (h : s.status = .opened) (hr : s.buffer.length < cap) :
    (queue cap).step s (.offer m) = some { s with buffer := s.buffer ++ [m] } := by
  simp [queue, h, hr]

/-- `offer_refused` (`EffectQueueLaws.lean:63-70`): on any non-open queue the
offer is refused and nothing changes (`Queue.ts:647-648`). -/
theorem queue_step_offer_refused (cap : Nat) (s : QState) (m : Item)
    (h : s.status ≠ .opened) :
    (queue cap).step s (.offer m) = some s := by
  cases hs : s.status with
  | opened => exact absurd hs h
  | closing e => simp [queue, hs]
  | done e => simp [queue, hs]
  | shutdown => simp [queue, hs]

/-- `takeAll_drains` (`EffectQueueLaws.lean:18-22`): on an open non-empty queue
`takeAll` returns the whole buffer and clears it (`Queue.ts:1994-1998`). -/
theorem queue_step_takeAll_opened (cap : Nat) (s : QState)
    (h : s.status = .opened) (hne : s.buffer ≠ []) :
    (queue cap).step s (.takeAll s.buffer) = some { s with buffer := [] } := by
  simp [queue, h, hne]

/-- `takeAll_closing` (`EffectQueueLaws.lean:24-29`): on a closing queue the
drain finishes it in the same step (`Queue.ts:2042-2046`). -/
theorem queue_step_takeAll_closing (cap : Nat) (s : QState) (e : Nat)
    (h : s.status = .closing e) (hne : s.buffer ≠ []) :
    (queue cap).step s (.takeAll s.buffer) = some { s with buffer := [], status := .done e } := by
  simp [queue, h, hne]

/-- `exit_after_drain` (`EffectQueueLaws.lean:43-46`), restated: on a finished
queue the stored exit is returned and the parked taker is cleared
(`Queue.ts:1607-1609`, `EffectQueue.lean:129`). -/
theorem queue_step_takeExit (cap : Nat) (s : QState) (e : Nat)
    (h : s.status = .done e) :
    (queue cap).step s (.takeExit e) = some { s with status := .shutdown, taker := false } := by
  simp [queue, h]

/-- The parked read (`EffectQueue.lean:109`, `Queue.ts:1969-1975`): on an open
empty queue with no taker, the taker parks. -/
theorem queue_step_takePark (cap : Nat) (s : QState)
    (h : s.status = .opened) (hb : s.buffer = []) (ht : s.taker = false) :
    (queue cap).step s .takePark = some { s with taker := true } := by
  simp [queue, h, hb, ht]

/-- `wake` on an open queue (`EffectQueue.lean:123-125`, `Queue.ts:1955-1967`):
the parked taker takes the buffer. -/
theorem queue_step_wake_opened (cap : Nat) (s : QState)
    (h : s.status = .opened) (ht : s.taker = true) (hne : s.buffer ≠ []) :
    (queue cap).step s (.wake s.buffer) = some { s with buffer := [], taker := false } := by
  simp [queue, h, ht, hne]

/-- `wake` on a closing queue (`EffectQueue.lean:126-128`): the parked taker
takes the kept buffer and the queue finishes. -/
theorem queue_step_wake_closing (cap : Nat) (s : QState) (e : Nat)
    (h : s.status = .closing e) (ht : s.taker = true) (hne : s.buffer ≠ []) :
    (queue cap).step s (.wake s.buffer) =
      some { s with buffer := [], status := .done e, taker := false } := by
  simp [queue, h, ht, hne]

/-- `fail_empty` (`EffectQueueLaws.lean:31-35`): a failure on an empty open
queue finishes it at once (`Queue.ts:1000-1015`). -/
theorem queue_step_fail_empty (cap : Nat) (s : QState) (e : Nat)
    (h : s.status = .opened) (hb : s.buffer = []) :
    (queue cap).step s (.fail e) = some { s with status := .done e } := by
  simp [queue, h, hb]

/-- `fail_nonempty` (`EffectQueueLaws.lean:37-41`): a failure on a non-empty
open queue keeps the buffer and closes. -/
theorem queue_step_fail_nonempty (cap : Nat) (s : QState) (e : Nat)
    (h : s.status = .opened) (hb : s.buffer ≠ []) :
    (queue cap).step s (.fail e) = some { s with status := .closing e } := by
  simp [queue, h, hb]

/-- `shutdown_clears` (`EffectQueueLaws.lean:48-49`), strengthened to name all
three fields (`Queue.ts:1191-1210`). -/
theorem queue_step_shutdown (cap : Nat) (s : QState) :
    (queue cap).step s .shutdown = some { buffer := [], status := .shutdown, taker := false } := by
  cases s.status <;> simp [queue]

end Effect4.Char.Queue
