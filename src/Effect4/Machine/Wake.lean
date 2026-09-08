import Effect4.Machine.Fiber
import Effect4.Machine.Value

/-!
# Effect4.Machine.Wake

The allocation-and-wake protocol every waiting family shares (grill Q5; the scheduler-surface
dispatch, `docs/research/2026-09-08-scheduler-surface-dispatch.md` §1–2), generic in the
family's payload: a waiter list with a phase and a coalescing batch, the mode an owed resume
is delivered in, the cancelled-waiter clause, and the sweeps a family's policy is written
with. Deferred is its first instance (`Machine/Stores.lean`: payload `Unit`, policy
`broadcast`, mode `now`); Latch (`Unit`, broadcast, scheduled), Queue's takers and offerers
(the take bounds, signal-then-repoll), Semaphore's observers (the permits wanted, a non-FIFO
sweep), Pool's waiters (a count), PubSub's subscribers and the timer's sleepers (a deadline,
fired through `due`) are its consumers.

**What it says.** A waiter carries the phase it registered at (`register`). Every wake-owing
step advances the phase: `wakeAll` (a broadcast completion, rc.112 `Deferred.ts:1655-1659`),
`wakeOne` (a signal), `wakeTake` (up to `n`, `Pool.ts:703-712`), `sweep` (a state-threaded
scan that wakes the waiters a family's step accepts and keeps the rest in order —
`Semaphore.ts:258-266`, where a large waiter is skipped and a smaller later one succeeds),
`schedule` (a batch wake, rc.112 `internal/effect.ts:5575-5590` `Latch.scheduleUnsafe`: the
pending waiters move into the batch; a second schedule while a batch is pending joins it and
posts no task — the coalescing guard). `runBatch` is the posted task's run (`flushScheduled`).
`cancel` is the cancelled-waiter clause (Eio `sem_state.ml`, survey #17): a waiter still
pending is removed and nothing is owed; a waiter no longer pending consumed a wake, so the
cancelling step owes one — `signal` families re-owe it to their next waiter, a `broadcast`
wake reached everyone (`wakeAll_cancel_owed`).

**What is proved.** `register_phase`, `delay_repoll`, `cancel_owed_iff`, `cancel_pending`, `wakeBy_none`,
`wakeBy_some`, `schedule_empty`,
`schedule_posts`, `schedule_coalesces`, `runBatch_clears`, `wakeAll_advances`,
`wakeAll_empties`, `wakeAll_cancel_owed`, `sweep_keeps_order`, `empty_quiet`.

**What is refused.** Which waiters a family wakes and with what answer is the family's policy,
written with these sweeps; the list is FIFO, a Semaphore's sweep is not (`SCHED-FB-NO-FIFO`).
The machine side of the clause is the resume guard: a resume for a fiber no longer parked on
that token is inert (`drive_resume_wrong_token`, `Machine/Clauses.lean`).
-/

set_option autoImplicit false

namespace Effect4.Machine

universe u v

/-- A cell of the Deferred store (`Deferred.ts:140-145`): allocation order. Here, below the
fiber machine, so a task can name a Deferred's waiter list. -/
structure DeferredKey where
  index : Nat
deriving DecidableEq, Repr, Inhabited

/-- The counter on a waiter list: advanced by every wake-owing step. A waiter records the phase
it registered at; "its phase has already advanced" is the clause's test. -/
abbrev WakePhase := Nat

/-- How an owed resume is delivered: `now`, inline inside the completing `sync` (rc.112
Deferred, `Deferred.ts:1655-1659`, M1); `scheduled`, posted as a task on the dispatcher
addressed by `owner` at `priority` (rc.112's `scheduleTask` sites 3–7: the Latch batch, Queue's
`releaseTakers` on the dispatcher stored at its make (`Queue.ts:455`), the permit sweep, the
Pool wake, the STM pending wake). -/
inductive WakeMode
  | now
  | scheduled (owner : FiberId) (priority : Nat)
deriving DecidableEq, Repr, Inhabited

/-- Which waiters a completion wakes, named: every one (Deferred, Latch), the head (a signal),
or a family's own sweep. The list is the same; the policy is the family's. -/
inductive WakePolicy
  | broadcast
  | signal
  | sweep
deriving DecidableEq, Repr, Inhabited

/-- The waiter list a task names: the store family by handle kind and the cell's allocation
index — the shape of a handle's code (`Machine/Handles.lean`), so every family's cell already
has a key and none needs a constructor here. -/
structure WakeKey where
  kind : HandleKind
  index : Nat
deriving DecidableEq, Repr

/-- A Deferred's list. -/
def WakeKey.deferred (cell : DeferredKey) : WakeKey := ⟨HandleKind.promise, cell.index⟩

/-- One waiter: the parked fiber, its resume token, the phase at registration, and the
family's payload (the permits a Semaphore waiter wants, a take's bounds, a sleep's deadline;
`Unit` for Deferred and Latch). -/
structure Waiter (π : Type u) where
  fiber : FiberId
  token : Nat
  phase : WakePhase
  payload : π
deriving DecidableEq, Repr

/-- A resume a store owes: the waiter, its token, the code it resumes with, and the mode. -/
structure Owed (κ : Type u) where
  waiter : FiberId
  token : Nat
  code : κ
  mode : WakeMode
deriving DecidableEq

/-- The owed resume with its code re-read in another alphabet. -/
def Owed.mapCode {κ : Type u} {κ' : Type v} (f : κ → κ') (d : Owed κ) : Owed κ' :=
  ⟨d.waiter, d.token, f d.code, d.mode⟩

theorem Owed.mapCode_waiter {κ : Type u} {κ' : Type v} (f : κ → κ') (d : Owed κ) :
    (d.mapCode f).waiter = d.waiter := rfl

theorem Owed.mapCode_token {κ : Type u} {κ' : Type v} (f : κ → κ') (d : Owed κ) :
    (d.mapCode f).token = d.token := rfl

theorem Owed.mapCode_mode {κ : Type u} {κ' : Type v} (f : κ → κ') (d : Owed κ) :
    (d.mapCode f).mode = d.mode := rfl

/-- A waiter list: the pending waiters in registration order, the batch a scheduled wake
captured and has not yet run (`Latch.scheduled`), and the phase. -/
structure WakeList (π : Type u) where
  waiters : List (Waiter π)
  batch : Option (List (Waiter π))
  phase : WakePhase
deriving DecidableEq, Repr

namespace WakeList

variable {π : Type u}

/-- No waiter, no batch, phase zero: the bottom every family's cell starts from. -/
def empty : WakeList π := ⟨[], none, 0⟩

/-- `_await`'s registration (`Deferred.ts:173-177`): appended, at the current phase. -/
def register (l : WakeList π) (fiber : FiberId) (token : Nat) (payload : π) : WakeList π :=
  { l with waiters := l.waiters ++ [⟨fiber, token, l.phase, payload⟩] }

/-- The `Delay` reply (Riot `Proc_state.step`, survey #1): a row that is not ready registers
the fiber on the list with *the row itself* as the payload, and the wake resumes the fiber
with that row — re-presented, re-polled (Queue's signal-then-repoll, `Queue.ts:1955-1975`:
`releaseTakers` resumes with `exitVoid` and the taker loops `takeBetween` again, `:1432`). The frame is
not consumed: the fiber parks on a fresh token and its `current` stays the row. A spurious
wake is permitted by construction, since the repoll may park again at the advanced phase. -/
def delay (l : WakeList π) (fiber : FiberId) (token : Nat) (row : π) : WakeList π :=
  l.register fiber token row

/-- Whether this waiter is still pending. -/
def pending (l : WakeList π) (fiber : FiberId) (token : Nat) : Bool :=
  l.waiters.any fun w => w.fiber = fiber && w.token = token

/-- The cancelled-waiter clause. A pending waiter is spliced out, order preserved
(`Deferred.ts:178-185`), and nothing is owed. A waiter no longer pending — its phase advanced,
the resumer won — consumed a wake that is now nobody's, so the cancelling step owes one:
answered `true` for the family to re-owe under its policy. -/
def cancel (l : WakeList π) (fiber : FiberId) (token : Nat) : WakeList π × Bool :=
  if l.pending fiber token then
    ({ l with waiters := l.waiters.filter fun w => !(w.fiber = fiber && w.token = token) }, false)
  else (l, true)

/-- A broadcast completion: every pending waiter woken, in order; the phase advances. -/
def wakeAll (l : WakeList π) : List (Waiter π) × WakeList π :=
  (l.waiters, { l with waiters := [], phase := l.phase + 1 })

/-- A signal: the head waiter woken; the phase advances only when someone is woken. -/
def wakeOne (l : WakeList π) : Option (Waiter π) × WakeList π :=
  match l.waiters with
  | [] => (none, l)
  | w :: rest => (some w, { l with waiters := rest, phase := l.phase + 1 })

/-- Up to `n` waiters woken, in order (`Pool.wakeWaiters`, `Pool.ts:700-712`). -/
def wakeTake (l : WakeList π) (n : Nat) : List (Waiter π) × WakeList π :=
  match l.waiters.take n with
  | [] => ([], l)
  | woken => (woken, { l with waiters := l.waiters.drop n, phase := l.phase + 1 })

/-- A family's choice of one waiter — the timer's earliest deadline, first registered among
equals (`testing/TestClock.ts:337`, `SleepOrder`): the chosen waiter is woken and removed and
the phase advances; a choice of `none` wakes nothing and changes nothing. The chooser sees
the list in registration order, so "first among equals" is its own decision, never the
list's. -/
def wakeBy [DecidableEq π] (l : WakeList π) (choose : List (Waiter π) → Option (Waiter π)) :
    Option (Waiter π) × WakeList π :=
  match choose l.waiters with
  | none => (none, l)
  | some w => (some w, { l with waiters := l.waiters.erase w, phase := l.phase + 1 })

/-- A family's sweep (`Semaphore.releaseUnsafe`, `Semaphore.ts:258-266`): the waiters scanned in
order with a family state; each the step accepts is woken and the state moves on, each it
declines stays, in order; the scan stops when `stop` says the state has nothing left. -/
def sweepWith {σ : Type v} (step : σ → Waiter π → Option σ) (stop : σ → Bool) :
    σ → List (Waiter π) → List (Waiter π) × List (Waiter π) × σ
  | s, [] => ([], [], s)
  | s, w :: rest =>
    if stop s then ([], w :: rest, s)
    else
      match step s w with
      | some s' =>
        let r := sweepWith step stop s' rest
        (w :: r.1, r.2.1, r.2.2)
      | none =>
        let r := sweepWith step stop s rest
        (r.1, w :: r.2.1, r.2.2)

/-- The sweep on a list: the woken, the list with the rest (the phase advanced when anyone
woke), and the family state after. -/
def sweep {σ : Type v} (l : WakeList π) (step : σ → Waiter π → Option σ) (stop : σ → Bool)
    (s : σ) : List (Waiter π) × WakeList π × σ :=
  let r := sweepWith step stop s l.waiters
  (r.1, { l with waiters := r.2.1, phase := if r.1.isEmpty then l.phase else l.phase + 1 },
    r.2.2)

/-- A scheduled batch wake (`Latch.scheduleUnsafe`, `internal/effect.ts:5575-5590`): with no
pending waiter nothing happens; with no pending batch the waiters move into a new batch and
a task must be posted (`true`); with one pending they join it and no task is posted — the
coalescing guard. The phase advances whenever waiters move. -/
def schedule (l : WakeList π) : WakeList π × Bool :=
  match l.waiters with
  | [] => (l, false)
  | _ =>
    match l.batch with
    | none => ({ l with waiters := [], batch := some l.waiters, phase := l.phase + 1 }, true)
    | some b =>
      ({ l with waiters := [], batch := some (b ++ l.waiters), phase := l.phase + 1 }, false)

/-- The posted task runs (`flushScheduled`, `:5591-5598`): the batch, cleared. -/
def runBatch (l : WakeList π) : List (Waiter π) × WakeList π :=
  (l.batch.getD [], { l with batch := none })

/-- The list owes nothing: no pending waiter, no pending batch. -/
def Quiet (l : WakeList π) : Prop := l.waiters = [] ∧ l.batch = none

theorem empty_quiet : Quiet (empty : WakeList π) := ⟨rfl, rfl⟩

/-- A choice of nothing changes nothing. -/
theorem wakeBy_none [DecidableEq π] (l : WakeList π) (choose : List (Waiter π) → Option (Waiter π))
    (h : choose l.waiters = none) : l.wakeBy choose = (none, l) := by
  simp only [wakeBy, h]

/-- A chosen waiter is woken: it is the answer, the list loses it (a sublist, order kept) and the
phase advances. -/
theorem wakeBy_some [DecidableEq π] (l : WakeList π) (choose : List (Waiter π) → Option (Waiter π))
    (w : Waiter π) (h : choose l.waiters = some w) :
    (l.wakeBy choose).1 = some w ∧ (l.wakeBy choose).2.waiters = l.waiters.erase w ∧
      (l.wakeBy choose).2.phase = l.phase + 1 ∧ (l.wakeBy choose).2.waiters.Sublist l.waiters := by
  simp only [wakeBy, h]
  exact ⟨trivial, trivial, trivial, List.erase_sublist⟩

theorem register_phase (l : WakeList π) (fiber : FiberId) (token : Nat) (payload : π) :
    (l.register fiber token payload).waiters = l.waiters ++ [⟨fiber, token, l.phase, payload⟩] :=
  rfl

/-- A delayed row is registered as the waiter's payload, at the current phase: what the wake
re-presents. -/
theorem delay_repoll (l : WakeList π) (fiber : FiberId) (token : Nat) (row : π) :
    (l.delay fiber token row).waiters = l.waiters ++ [⟨fiber, token, l.phase, row⟩] := rfl

/-- The clause: a wake is owed exactly when the waiter is no longer pending. -/
theorem cancel_owed_iff (l : WakeList π) (fiber : FiberId) (token : Nat) :
    (l.cancel fiber token).2 = !(l.pending fiber token) := by
  unfold cancel
  split <;> simp_all

/-- A pending waiter's cancel removes it and owes nothing. -/
theorem cancel_pending (l : WakeList π) (fiber : FiberId) (token : Nat)
    (h : l.pending fiber token = true) :
    l.cancel fiber token =
      ({ l with waiters := l.waiters.filter fun w => !(w.fiber = fiber && w.token = token) },
        false) := by
  unfold cancel
  simp [h]

theorem schedule_empty (l : WakeList π) (h : l.waiters = []) : l.schedule = (l, false) := by
  unfold schedule
  simp [h]

/-- The first schedule posts the task and captures the waiters. -/
theorem schedule_posts (l : WakeList π) (h : l.waiters ≠ []) (hb : l.batch = none) :
    l.schedule =
      ({ l with waiters := [], batch := some l.waiters, phase := l.phase + 1 }, true) := by
  unfold schedule
  cases hw : l.waiters with
  | nil => exact absurd hw h
  | cons w rest => simp [hb]

/-- A schedule while a batch is pending joins it and posts nothing. -/
theorem schedule_coalesces (l : WakeList π) (b : List (Waiter π)) (h : l.waiters ≠ [])
    (hb : l.batch = some b) :
    l.schedule =
      ({ l with waiters := [], batch := some (b ++ l.waiters), phase := l.phase + 1 }, false) := by
  unfold schedule
  cases hw : l.waiters with
  | nil => exact absurd hw h
  | cons w rest => simp [hb, ← hw]

theorem runBatch_clears (l : WakeList π) : (l.runBatch).2.batch = none := rfl

theorem wakeAll_advances (l : WakeList π) : (l.wakeAll).2.phase = l.phase + 1 := rfl

theorem wakeAll_empties (l : WakeList π) : (l.wakeAll).2.waiters = [] := rfl

/-- After a broadcast wake, a woken waiter's cancel owes a wake (the clause fires) and that
waiter was among the woken: a broadcast lost nothing, since the wake reached every waiter. -/
theorem wakeAll_cancel_owed (l : WakeList π) (w : Waiter π) (hw : w ∈ l.waiters) :
    ((l.wakeAll).2.cancel w.fiber w.token).2 = true ∧ w ∈ (l.wakeAll).1 := by
  refine ⟨?_, hw⟩
  rw [cancel_owed_iff]
  simp [wakeAll, pending]

/-- A sweep keeps the declined waiters in their order: the kept list is a sublist of the
scanned one, and the woken and the kept together are all of it. -/
theorem sweep_keeps_order {σ : Type v} (step : σ → Waiter π → Option σ) (stop : σ → Bool) :
    ∀ (s : σ) (ws : List (Waiter π)),
      (sweepWith step stop s ws).2.1.Sublist ws ∧ (sweepWith step stop s ws).1.Sublist ws
  | _, [] => ⟨List.Sublist.refl _, List.Sublist.refl _⟩
  | s, w :: rest => by
    unfold sweepWith
    split
    · exact ⟨List.Sublist.refl _, List.nil_sublist _⟩
    · split
      · next s' _ =>
        obtain ⟨hk, hw⟩ := sweep_keeps_order step stop s' rest
        exact ⟨hk.cons w, hw.cons_cons w⟩
      · obtain ⟨hk, hw⟩ := sweep_keeps_order step stop s rest
        exact ⟨hk.cons_cons w, hw.cons w⟩

end WakeList

end Effect4.Machine
