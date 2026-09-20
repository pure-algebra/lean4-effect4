import Effect4.Machine.Wake
import Effect4.Data.ClockMillis
import Effect4.Laws.Auto.Obligations
set_option linter.unusedVariables false

/-!
# The timer store — the logical clock and its sleeps (A4)

**What it is.** rc.112's clock as a store on the wake protocol (`Machine/Wake.lean`). The
*shape* is `TestClock`'s (`testing/TestClock.ts:249-253`, `:327-338`, `:345-375`): a timestamp
that moves only when the host says so, a table of sleeps ordered by deadline then registration
(`SleepOrder`, `:337`), and an `adjust` that fires every due sleep in that order, staging the
clock at each fired deadline and letting fibers run between fires (`yieldNow` after each
latch opens, `:366`). The *meaning* of a registration is the live clock's
(`internal/effect.ts:6052-6066`, `ClockImpl.sleepMillis`): a cancelled sleep is removed
(`clearTimeout`, `:6063`) — `TestClock` keeps its entry (`:178-185` of the timer note, refusal
R2), and this store does not model that. `sleep 0` and `sleep ∞` never reach the store
(`:6054-6055`: `yieldNow` and `never` are programs, decided at the row).

**Representation.** `now : ClockMillis` (ms), the pending sleeps as a `WakeList ClockMillis` whose payload is
the deadline (registration order is the list's, the earliest deadline is the family's choice,
`WakeList.wakeBy`), and `target : Option ClockMillis`, an advance in progress — `TestClock.run` holds
its `endTimestamp` under `runSemaphore.withPermits(1)` (`:345`, `:375`), and so does this store
between the fires of one `advance`. There is no `due` list: a fired sleep is owed *to the
machine* (`RunInterp.clockStep`), which resumes the sleeper inline (`WakeMode.now`, as a
Deferred's completion does) and flushes the dispatchers before the next fire. rc.112 opens a
latch there (`latch.openUnsafe()`, `:365`), whose `flushScheduled` posts the resume; that
posted spelling is Latch's to land (`WakeMode.scheduled` on the sleeper's dispatcher), and
until then the fire is the family's `now` — the same fibers run, in the same order, before
the next fire.

**What is proved.** `empty_wf`, `sleep_wf`, `cancel_wf`, `dueMin_mem`, `dueMin_le`,
`dueMin_min`, `dueMin_none_of_late`, `dueMin_first`, `fireNext_none`, `fireNext_now`,
`fireNext_owed`, `fireNext_wf`, `clockStep_finish`, `clockStep_owed`, `clockStep_wf`,
`cancel_pending`.

**Refusal rows** (`Test/Counterexamples/REGISTER.md`): `TIMER-FB-SET-TIME` (no `setTime`: the
clock never moves backwards, R1), `TIMER-FB-KEPT-CANCEL` (a cancelled sleep is removed, not
kept, R2), `TIMER-FB-INFINITE` (`sleep ∞` is not a deadline).
-/

namespace Effect4.Machine

universe u

/-- The logical clock and its pending sleeps; see the module header. -/
structure TimerStore where
  /-- `currentTimestamp` (`testing/TestClock.ts:257`), in milliseconds. -/
  now : ClockMillis
  /-- `sleeps` (`:249-253`): the parked fiber, its token, its phase, its deadline. -/
  wake : WakeList ClockMillis
  /-- An advance in progress: the `endTimestamp` of the running `adjust` (`:355`). -/
  target : Option ClockMillis
deriving DecidableEq

namespace TimerStore

/-- The clock at zero, nothing pending, no advance in progress (`new Date(0)`, `:257`). -/
def empty : TimerStore := ⟨0, WakeList.empty, none⟩

/-- `sleep(d)` with `0 < d` (`:327-338`; live `:6057-6062`): registered at its deadline, in
registration order. -/
def sleep (self : TimerStore) (fiber : FiberId) (token : Nat) (millis : ClockMillis) : TimerStore :=
  { self with wake := self.wake.register fiber token (self.now + millis) }

/-- `clearTimeout` (`internal/effect.ts:6063`): the sleep removed. The clause's owed wake
(`WakeList.cancel`) is the sleeper's own fire, which reached nobody else: nothing to re-owe. -/
def cancel (self : TimerStore) (fiber : FiberId) (token : Nat) : TimerStore :=
  { self with wake := (self.wake.cancel fiber token).1 }

/-- The family's choice (`SleepOrder`, `:337`): among the sleeps due at `target`, the earliest
deadline; among equal deadlines the first registered — the list is in registration order and
a later waiter replaces the choice only when strictly earlier. -/
def dueMin (target : ClockMillis) : List (Waiter ClockMillis) → Option (Waiter ClockMillis)
  | [] => none
  | w :: rest =>
    match dueMin target rest with
    | none => if w.payload ≤ target then some w else none
    | some m => if w.payload ≤ target && w.payload ≤ m.payload then some w else some m

/-- One fire of `TestClock.run`'s loop (`:361-367`): the least due sleep is popped, the clock
staged at its deadline, and its resume owed inline (`latch.openUnsafe()`; see the header).
`none` when nothing is due at `target`. -/
def fireNext {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ) :
    Option (Owed κ) × TimerStore :=
  match self.wake.wakeBy (dueMin target) with
  | (none, _) => (none, self)
  | (some w, wake) =>
    (some ⟨w.fiber, w.token, resume, WakeMode.now⟩, { self with now := w.payload, wake := wake })

/-- The staged loop's one step, `advance (by millis)` as the machine drives it: the first step
fixes the end (`now + millis`, `:355`, `:378`) and keeps it until the loop finishes; each step
fires the least due sleep, or, with nothing due, sets the clock to the end
(`advanceTo(endTimestamp)`, `:368`) and clears the advance. -/
def clockStep {κ : Type u} (self : TimerStore) (millis : ClockMillis) (resume : κ) :
    Option (Owed κ) × TimerStore :=
  let target := self.target.getD (self.now + millis)
  match self.fireNext target resume with
  | (some owed, s) => (some owed, { s with target := some target })
  | (none, s) => (none, { s with now := target, target := none })

/-- Every pending deadline is at or after the clock: a sleep is registered ahead of `now`, a
fire stages the clock at the least deadline, a finish moves it below what is not due. -/
def WF (self : TimerStore) : Prop := ∀ w ∈ self.wake.waiters, self.now ≤ w.payload

/-- Nothing pending, no advance in progress. -/
def Quiet (self : TimerStore) : Prop := self.wake.Quiet ∧ self.target = none

instance (self : TimerStore) : Decidable self.WF := by unfold WF; infer_instance

def M1Clock.empty_wf : ProofGraph.Obligation (empty.WF) := ⟨⟩
#proof_wanted M1Clock.empty_wf

def M1Clock.empty_quiet : ProofGraph.Obligation (empty.Quiet) := ⟨⟩
#proof_wanted M1Clock.empty_quiet

def M1Clock.sleep_wf {self : TimerStore} (h : self.WF) (fiber : FiberId) (token : Nat) (millis : ClockMillis) : ProofGraph.Obligation ((self.sleep fiber token millis).WF) := ⟨⟩
#proof_wanted M1Clock.sleep_wf

def M1Clock.cancel_wf {self : TimerStore} (h : self.WF) (fiber : FiberId) (token : Nat) : ProofGraph.Obligation ((self.cancel fiber token).WF) := ⟨⟩
#proof_wanted M1Clock.cancel_wf

def M1Clock.cancel_pending (self : TimerStore) (fiber : FiberId) (token : Nat) : ProofGraph.Obligation ((self.cancel fiber token).wake.pending fiber token = false) := ⟨⟩
#proof_wanted M1Clock.cancel_pending

def M1Clock.dueMin_none_of_late (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)), dueMin target l = none → ∀ w ∈ l, target < w.payload) := ⟨⟩
#proof_wanted M1Clock.dueMin_none_of_late

def M1Clock.dueMin_mem (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)) (m : Waiter ClockMillis), dueMin target l = some m → m ∈ l) := ⟨⟩
#proof_wanted M1Clock.dueMin_mem

def M1Clock.dueMin_le (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)) (m : Waiter ClockMillis), dueMin target l = some m → m.payload ≤ target) := ⟨⟩
#proof_wanted M1Clock.dueMin_le

def M1Clock.dueMin_min (target : ClockMillis) : ProofGraph.Obligation (∀ (l : List (Waiter ClockMillis)) (m : Waiter ClockMillis), dueMin target l = some m →
      ∀ x ∈ l, x.payload ≤ target → m.payload ≤ x.payload) := ⟨⟩
#proof_wanted M1Clock.dueMin_min

def M1Clock.dueMin_first (target : ClockMillis) (w : Waiter ClockMillis) (rest : List (Waiter ClockMillis))
    (hw : w.payload ≤ target) (hrest : ∀ x ∈ rest, w.payload ≤ x.payload) : ProofGraph.Obligation (dueMin target (w :: rest) = some w) := ⟨⟩
#proof_wanted M1Clock.dueMin_first

def M1Clock.fireNext_none {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ)
    (h : dueMin target self.wake.waiters = none) : ProofGraph.Obligation (self.fireNext target resume = (none, self)) := ⟨⟩
#proof_wanted M1Clock.fireNext_none

def M1Clock.fireNext_now {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ) (w : Waiter ClockMillis)
    (h : dueMin target self.wake.waiters = some w) : ProofGraph.Obligation ((self.fireNext target resume).1 = some ⟨w.fiber, w.token, resume, WakeMode.now⟩ ∧
      (self.fireNext target resume).2.now = w.payload ∧
      (self.fireNext target resume).2.wake.waiters = self.wake.waiters.erase w) := ⟨⟩
#proof_wanted M1Clock.fireNext_now

def M1Clock.fireNext_owed {κ : Type u} (self : TimerStore) (target : ClockMillis) (resume : κ) (o : Owed κ)
    (h : (self.fireNext target resume).1 = some o) : ProofGraph.Obligation (o.code = resume ∧ o.mode = WakeMode.now) := ⟨⟩
#proof_wanted M1Clock.fireNext_owed

def M1Clock.fireNext_wf {κ : Type u} {self : TimerStore} (hwf : self.WF) (target : ClockMillis) (resume : κ) : ProofGraph.Obligation ((self.fireNext target resume).2.WF) := ⟨⟩
#proof_wanted M1Clock.fireNext_wf

def M1Clock.clockStep_finish {κ : Type u} (self : TimerStore) (millis : ClockMillis) (resume : κ)
    (h : dueMin (self.target.getD (self.now + millis)) self.wake.waiters = none) : ProofGraph.Obligation (self.clockStep millis resume =
      (none, { self with now := self.target.getD (self.now + millis), target := none })) := ⟨⟩
#proof_wanted M1Clock.clockStep_finish

def M1Clock.clockStep_owed {κ : Type u} (self : TimerStore) (millis : ClockMillis) (resume : κ) (o : Owed κ)
    (h : (self.clockStep millis resume).1 = some o) : ProofGraph.Obligation (o.code = resume ∧ o.mode = WakeMode.now) := ⟨⟩
#proof_wanted M1Clock.clockStep_owed

def M1Clock.clockStep_wf {κ : Type u} {self : TimerStore} (hwf : self.WF) (millis : ClockMillis) (resume : κ) : ProofGraph.Obligation ((self.clockStep millis resume).2.WF) := ⟨⟩
#proof_wanted M1Clock.clockStep_wf

end TimerStore
end Effect4.Machine
