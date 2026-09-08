import Effect4.Machine.Wake

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

**Representation.** `now : Nat` (ms), the pending sleeps as a `WakeList Nat` whose payload is
the deadline (registration order is the list's, the earliest deadline is the family's choice,
`WakeList.wakeBy`), and `target : Option Nat`, an advance in progress — `TestClock.run` holds
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
  now : Nat
  /-- `sleeps` (`:249-253`): the parked fiber, its token, its phase, its deadline. -/
  wake : WakeList Nat
  /-- An advance in progress: the `endTimestamp` of the running `adjust` (`:355`). -/
  target : Option Nat
deriving DecidableEq

namespace TimerStore

/-- The clock at zero, nothing pending, no advance in progress (`new Date(0)`, `:257`). -/
def empty : TimerStore := ⟨0, WakeList.empty, none⟩

/-- `sleep(d)` with `0 < d` (`:327-338`; live `:6057-6062`): registered at its deadline, in
registration order. -/
def sleep (self : TimerStore) (fiber : FiberId) (token : Nat) (millis : Nat) : TimerStore :=
  { self with wake := self.wake.register fiber token (self.now + millis) }

/-- `clearTimeout` (`internal/effect.ts:6063`): the sleep removed. The clause's owed wake
(`WakeList.cancel`) is the sleeper's own fire, which reached nobody else: nothing to re-owe. -/
def cancel (self : TimerStore) (fiber : FiberId) (token : Nat) : TimerStore :=
  { self with wake := (self.wake.cancel fiber token).1 }

/-- The family's choice (`SleepOrder`, `:337`): among the sleeps due at `target`, the earliest
deadline; among equal deadlines the first registered — the list is in registration order and
a later waiter replaces the choice only when strictly earlier. -/
def dueMin (target : Nat) : List (Waiter Nat) → Option (Waiter Nat)
  | [] => none
  | w :: rest =>
    match dueMin target rest with
    | none => if w.payload ≤ target then some w else none
    | some m => if w.payload ≤ target && w.payload ≤ m.payload then some w else some m

/-- One fire of `TestClock.run`'s loop (`:361-367`): the least due sleep is popped, the clock
staged at its deadline, and its resume owed inline (`latch.openUnsafe()`; see the header).
`none` when nothing is due at `target`. -/
def fireNext {κ : Type u} (self : TimerStore) (target : Nat) (resume : κ) :
    Option (Owed κ) × TimerStore :=
  match self.wake.wakeBy (dueMin target) with
  | (none, _) => (none, self)
  | (some w, wake) =>
    (some ⟨w.fiber, w.token, resume, WakeMode.now⟩, { self with now := w.payload, wake := wake })

/-- The staged loop's one step, `advance (by millis)` as the machine drives it: the first step
fixes the end (`now + millis`, `:355`, `:378`) and keeps it until the loop finishes; each step
fires the least due sleep, or, with nothing due, sets the clock to the end
(`advanceTo(endTimestamp)`, `:368`) and clears the advance. -/
def clockStep {κ : Type u} (self : TimerStore) (millis : Nat) (resume : κ) :
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

theorem empty_wf : empty.WF := by intro w hw; cases hw

theorem empty_quiet : empty.Quiet := ⟨WakeList.empty_quiet, rfl⟩

theorem sleep_wf {self : TimerStore} (h : self.WF) (fiber : FiberId) (token millis : Nat) :
    (self.sleep fiber token millis).WF := by
  intro w hw
  simp only [sleep, WakeList.register_phase, List.mem_append, List.mem_singleton] at hw
  rcases hw with hw | rfl
  · exact h w hw
  · exact Nat.le_add_right _ _

theorem cancel_wf {self : TimerStore} (h : self.WF) (fiber : FiberId) (token : Nat) :
    (self.cancel fiber token).WF := by
  intro w hw
  unfold cancel WakeList.cancel at hw
  split at hw
  · exact h w (List.mem_filter.mp hw).1
  · exact h w hw

/-- A cancelled sleep is no longer pending. -/
theorem cancel_pending (self : TimerStore) (fiber : FiberId) (token : Nat) :
    (self.cancel fiber token).wake.pending fiber token = false := by
  unfold cancel WakeList.cancel
  split
  · simp only [WakeList.pending, List.any_eq_true, List.mem_filter, Bool.not_eq_eq_eq_not,
      Bool.not_true, Bool.and_eq_false_imp, decide_eq_true_eq, decide_eq_false_iff_not]
    simp
    intro x _ h hf ht
    exact h.elim (fun h => h hf) (fun h => h ht)
  · rename_i h
    simpa using h

/-- With no choice, every deadline is past the target. -/
theorem dueMin_none_of_late (target : Nat) :
    ∀ (l : List (Waiter Nat)), dueMin target l = none → ∀ w ∈ l, target < w.payload
  | [], _, _, hw => nomatch hw
  | w :: rest, h, x, hx => by
    cases hr : dueMin target rest with
    | none =>
      simp only [dueMin, hr] at h
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Nat.lt_of_not_le (by intro hle; simp [hle] at h)
      · exact dueMin_none_of_late target rest hr x hx
    | some m =>
      simp only [dueMin, hr] at h
      split at h <;> simp at h

theorem dueMin_mem (target : Nat) :
    ∀ (l : List (Waiter Nat)) (m : Waiter Nat), dueMin target l = some m → m ∈ l
  | [], _, h => nomatch h
  | w :: rest, m, h => by
    cases hr : dueMin target rest with
    | none =>
      simp only [dueMin, hr] at h
      split at h
      · rcases Option.some.inj h with rfl
        exact List.mem_cons_self
      · exact nomatch h
    | some m' =>
      simp only [dueMin, hr] at h
      split at h
      · rcases Option.some.inj h with rfl
        exact List.mem_cons_self
      · rcases Option.some.inj h with rfl
        exact List.mem_cons_of_mem _ (dueMin_mem target rest _ hr)

theorem dueMin_le (target : Nat) :
    ∀ (l : List (Waiter Nat)) (m : Waiter Nat), dueMin target l = some m → m.payload ≤ target
  | [], _, h => nomatch h
  | w :: rest, m, h => by
    cases hr : dueMin target rest with
    | none =>
      simp only [dueMin, hr] at h
      split at h
      · rcases Option.some.inj h with rfl
        assumption
      · exact nomatch h
    | some m' =>
      simp only [dueMin, hr] at h
      split at h
      · rename_i hc
        rcases Option.some.inj h with rfl
        exact (by simpa using hc : _ ∧ _).1
      · rcases Option.some.inj h with rfl
        exact dueMin_le target rest _ hr

/-- The choice is the least due deadline. -/
theorem dueMin_min (target : Nat) :
    ∀ (l : List (Waiter Nat)) (m : Waiter Nat), dueMin target l = some m →
      ∀ x ∈ l, x.payload ≤ target → m.payload ≤ x.payload
  | [], _, h => nomatch h
  | w :: rest, m, h => by
    intro x hx hxt
    cases hr : dueMin target rest with
    | none =>
      simp only [dueMin, hr] at h
      split at h
      · rcases Option.some.inj h with rfl
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact absurd hxt (Nat.not_le.mpr (dueMin_none_of_late target rest hr x hx))
      · exact nomatch h
    | some m' =>
      simp only [dueMin, hr] at h
      have ih := dueMin_min target rest m' hr
      split at h
      · rename_i hc
        rcases Option.some.inj h with rfl
        have hc' := (by simpa using hc : _ ∧ _)
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_refl _
        · exact Nat.le_trans hc'.2 (ih x hx hxt)
      · rename_i hc
        rcases Option.some.inj h with rfl
        rcases List.mem_cons.mp hx with rfl | hx
        · exact Nat.le_of_lt (Nat.lt_of_not_le fun hle => by simp [hxt, hle] at hc)
        · exact ih x hx hxt

/-- Equal deadlines fire in registration order: a due head that no later waiter beats is the
choice. -/
theorem dueMin_first (target : Nat) (w : Waiter Nat) (rest : List (Waiter Nat))
    (hw : w.payload ≤ target) (hrest : ∀ x ∈ rest, w.payload ≤ x.payload) :
    dueMin target (w :: rest) = some w := by
  cases hr : dueMin target rest with
  | none => simp [dueMin, hr, hw]
  | some m => simp [dueMin, hr, hw, hrest m (dueMin_mem target rest m hr)]

theorem fireNext_none {κ : Type u} (self : TimerStore) (target : Nat) (resume : κ)
    (h : dueMin target self.wake.waiters = none) : self.fireNext target resume = (none, self) := by
  simp [fireNext, WakeList.wakeBy, h]

/-- A fire stages the clock at the fired deadline, owes the sleeper its resume posted on its own
dispatcher, and removes exactly that sleep. -/
theorem fireNext_now {κ : Type u} (self : TimerStore) (target : Nat) (resume : κ) (w : Waiter Nat)
    (h : dueMin target self.wake.waiters = some w) :
    (self.fireNext target resume).1 = some ⟨w.fiber, w.token, resume, WakeMode.now⟩ ∧
      (self.fireNext target resume).2.now = w.payload ∧
      (self.fireNext target resume).2.wake.waiters = self.wake.waiters.erase w := by
  simp [fireNext, WakeList.wakeBy, h]

/-- Whatever a fire owes resumes with the given code, inline. -/
theorem fireNext_owed {κ : Type u} (self : TimerStore) (target : Nat) (resume : κ) (o : Owed κ)
    (h : (self.fireNext target resume).1 = some o) : o.code = resume ∧ o.mode = WakeMode.now := by
  cases hd : dueMin target self.wake.waiters with
  | none => rw [fireNext_none self target resume hd] at h; cases h
  | some w =>
    rw [(fireNext_now self target resume w hd).1] at h
    cases Option.some.inj h
    exact ⟨rfl, rfl⟩

theorem fireNext_wf {κ : Type u} {self : TimerStore} (hwf : self.WF) (target : Nat) (resume : κ) :
    (self.fireNext target resume).2.WF := by
  cases h : dueMin target self.wake.waiters with
  | none => rw [fireNext_none self target resume h]; exact hwf
  | some w =>
    intro x hx
    rw [(fireNext_now self target resume w h).2.2] at hx
    rw [(fireNext_now self target resume w h).2.1]
    have hxl : x ∈ self.wake.waiters := List.mem_of_mem_erase hx
    by_cases hxt : x.payload ≤ target
    · exact dueMin_min target _ w h x hxl hxt
    · exact Nat.le_trans (dueMin_le target _ w h) (Nat.le_of_lt (Nat.lt_of_not_le hxt))

/-- With nothing due, the step finishes: the clock at the end, no advance in progress. -/
theorem clockStep_finish {κ : Type u} (self : TimerStore) (millis : Nat) (resume : κ)
    (h : dueMin (self.target.getD (self.now + millis)) self.wake.waiters = none) :
    self.clockStep millis resume =
      (none, { self with now := self.target.getD (self.now + millis), target := none }) := by
  simp [clockStep, fireNext_none self _ resume h]

/-- Whatever a step owes resumes with the given code, inline. -/
theorem clockStep_owed {κ : Type u} (self : TimerStore) (millis : Nat) (resume : κ) (o : Owed κ)
    (h : (self.clockStep millis resume).1 = some o) : o.code = resume ∧ o.mode = WakeMode.now := by
  simp only [clockStep] at h
  rcases hfx : self.fireNext (self.target.getD (self.now + millis)) resume with ⟨o', s⟩
  rw [hfx] at h
  cases o' with
  | none => simp at h
  | some o' =>
    simp only [Option.some.injEq] at h
    subst h
    exact fireNext_owed self _ resume o' (by rw [hfx])

theorem clockStep_wf {κ : Type u} {self : TimerStore} (hwf : self.WF) (millis : Nat) (resume : κ) :
    (self.clockStep millis resume).2.WF := by
  cases h : dueMin (self.target.getD (self.now + millis)) self.wake.waiters with
  | none =>
    rw [clockStep_finish self millis resume h]
    intro x hx
    exact Nat.le_of_lt (dueMin_none_of_late _ _ h x hx)
  | some w =>
    have hf := fireNext_wf hwf (self.target.getD (self.now + millis)) resume
    have h1 := (fireNext_now self (self.target.getD (self.now + millis)) resume w h).1
    simp only [clockStep]
    rcases hfx : self.fireNext (self.target.getD (self.now + millis)) resume with ⟨o, s⟩
    rw [hfx] at hf h1
    simp only at h1
    subst h1
    exact hf

end TimerStore

end Effect4.Machine
