import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.Keeps
import Effect4.Laws.Effects.Protocol

/-!
# Machine.Lift — invariants through commands, decisions and replay

The invariant, world order, interpreter and machine instances are parameters. The command
lift carries the pending queue, and the decision lift also carries the tasks drained by a
fire but not yet executed. Its answer premise applies after preparation and the first resume.
Replay requires admission only for the decisions it applies before stopping.

The frame law retains a halting alternative: a settling halt may drop the pending suffix.
The machine-only specialization packages the edits outside the command loop. Concrete
invariants and native prefix reachability live with their users, outside this module.
-/

set_option autoImplicit false

namespace Effect4.Machine.Lift

open Effect4 Effect4.Machine
open Effect4.Laws.Effects (WorldOrder)

universe u v w

/-- The order with one world: for facts about the machine alone. -/
def unitOrder : WorldOrder Unit := ⟨fun _ _ => True, fun _ => trivial, fun _ _ => trivial⟩

section Loop

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w}

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] [FiberCore ν β ε δ ι α κ φ]
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem stuck_none_of_not {m : RunMachine ν σ β ε δ ι α χ St κ φ η}
    (hs : ¬ m.stuck.isSome = true) : m.stuck = none := by
  cases h : m.stuck with
  | none => rfl
  | some why => exact absurd (by rw [h]; rfl) hs

/-- The per-command premise: a command run on a machine that is not stuck keeps the
invariant, at some later world. `rest` is universally quantified. -/
def StepKeeps (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop) :
    Prop :=
  ∀ w m c rest, m.stuck = none → I w m (c :: rest) →
    ∃ w', o.le w w' ∧ I w' (driveStep interp m c rest).1 (driveStep interp m c rest).2

/-- **Lift 1, the command loop.** One fact per command gives the fact for `driveState` at every
fuel, machine and pending list, at some later world. -/
theorem driveState_lift (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (step : StepKeeps o interp I) :
    ∀ (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
      (cmds : List (Cmd ν σ β ε δ ι α κ)), I w m cmds →
      ∃ w', o.le w w' ∧
        I w' (driveState interp fuel m cmds).1 (driveState interp fuel m cmds).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro w m cmds h
    exact ⟨w, o.refl w, by rw [driveState_zero]; exact h⟩
  | succ fuel ih =>
    intro w m cmds h
    cases cmds with
    | nil => exact ⟨w, o.refl w, by rw [driveState_nil]; exact h⟩
    | cons c rest =>
      rw [driveState_succ_cons]
      by_cases hs : m.stuck.isSome = true
      · rw [if_pos hs]
        exact ⟨w, o.refl w, h⟩
      · rw [if_neg hs]
        obtain ⟨w₁, le₁, h₁⟩ := step w m c rest (stuck_none_of_not hs) h
        obtain ⟨w₂, le₂, h₂⟩ := ih w₁ _ _ h₁
        exact ⟨w₂, o.trans le₁ le₂, h₂⟩

/-- The premise exactly as the brief states it (no stuck guard); it implies `StepKeeps`. -/
theorem driveState_lift_of (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (step : ∀ w m c rest, I w m (c :: rest) →
      ∃ w', o.le w w' ∧ I w' (driveStep interp m c rest).1 (driveStep interp m c rest).2)
    (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) (h : I w m cmds) :
    ∃ w', o.le w w' ∧ I w' (driveState interp fuel m cmds).1 (driveState interp fuel m cmds).2 :=
  driveState_lift o interp I (fun w m c rest _ hi => step w m c rest hi) fuel w m cmds h

/-- The machine-only form (`W := Unit`): the guard's shape. -/
theorem driveState_lift_unit (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (step : ∀ m c rest, m.stuck = none → I m (c :: rest) →
      I (driveStep interp m c rest).1 (driveStep interp m c rest).2)
    (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
    (h : I m cmds) : I (driveState interp fuel m cmds).1 (driveState interp fuel m cmds).2 := by
  obtain ⟨_, _, h'⟩ := driveState_lift unitOrder interp (fun _ m cmds => I m cmds)
    (fun _ m c rest hs hi => ⟨(), trivial, step m c rest hs hi⟩) fuel () m cmds h
  exact h'

/-- **The equality form.** A projection every non-stuck command leaves alone is left alone by
the loop: the lift at "equal to the start value". -/
theorem driveState_keeps {P : Sort w} (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (proj : RunMachine ν σ β ε δ ι α χ St κ φ η → P)
    (step : ∀ c rest m, m.stuck = none → proj (driveStep interp m c rest).1 = proj m)
    (fuel : Nat) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    Keeps proj (fun m => (driveState interp fuel m cmds).1) := fun m =>
  driveState_lift_unit interp (fun m' _ => proj m' = proj m)
    (fun m' c rest hs h => (step c rest m' hs).trans h) fuel m cmds rfl

/-- The tree's `Keeps` of every command is the premise of `driveState_keeps`. -/
theorem driveState_keeps_of_keeps {P : Sort w} (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (proj : RunMachine ν σ β ε δ ι α χ St κ φ η → P)
    (step : ∀ c rest, Keeps proj (fun m => (driveStep interp m c rest).1))
    (fuel : Nat) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    Keeps proj (fun m => (driveState interp fuel m cmds).1) :=
  driveState_keeps interp proj (fun c rest m _ => step c rest m) fuel cmds

/-- A kept proposition is a kept-true fact: the `Keeps` of a `Prop` projection gives the
invariant premise (one direction of its equation). -/
theorem stepKeeps_of_keeps (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (P : RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (step : ∀ c rest, Keeps P (fun m => (driveStep interp m c rest).1)) :
    StepKeeps unitOrder interp (fun _ m _ => P m) :=
  fun _ m c rest _ h => ⟨(), trivial, (step c rest m).mpr h⟩

end Loop

/-! ## The frame law: a command never reads the commands after it -/

section Frame

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-- The same machine, and the old residue followed by the suffix; or, on a halt, both
residues empty (`settle`'s stuck arm returns `[]`, `Machine/Fibers.lean:1825-1826`). -/
def Framed (s : List (Cmd ν σ β ε δ ι α κ))
    (r r' : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) : Prop :=
  r'.1 = r.1 ∧ (r'.2 = r.2 ++ s ∨ (r.2 = [] ∧ r'.2 = [] ∧ r.1.stuck.isSome = true))

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem settle_append (id : FiberId) (rest s : List (Cmd ν σ β ε δ ι α κ))
    (it : Iter ν σ β ε δ ι α χ St κ φ η) :
    Framed s (settle id rest it) (settle id (rest ++ s) it) := by
  unfold settle Framed
  split
  · exact ⟨rfl, Or.inl (by simp only [List.append_assoc])⟩
  · exact ⟨rfl, Or.inl (by simp only [List.append_assoc])⟩
  · split
    · exact ⟨rfl, Or.inl (by simp only [List.append_assoc])⟩
    · exact ⟨rfl, Or.inl (by simp only [List.append_assoc])⟩
  · exact ⟨rfl, Or.inl (by simp only [List.append_assoc])⟩
  · exact ⟨rfl, Or.inl (by simp only [List.append_assoc])⟩
  · exact ⟨rfl, Or.inr ⟨rfl, rfl, rfl⟩⟩

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] [FiberCore ν β ε δ ι α κ φ]
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem framed_append (s : List (Cmd ν σ β ε δ ι α κ))
    (r : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    Framed s r (r.1, r.2 ++ s) := ⟨rfl, Or.inl rfl⟩

/-- **The frame law.** Generic in the machine instance: every arm of `driveStep` returns its
new commands in front of `rest` untouched, or a halting `settle` drops the residue. -/
theorem driveStep_append (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (c : Cmd ν σ β ε δ ι α κ)
    (rest s : List (Cmd ν σ β ε δ ι α κ)) :
    Framed s (driveStep interp m c rest) (driveStep interp m c (rest ++ s)) := by
  cases c with
  | evaluate id =>
    simp only [driveStep]
    repeat' split
    all_goals exact framed_append _ _
  | loop id yielding =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · exact settle_append _ _ _ _
  | deliver id yielding =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · exact settle_append _ _ _ _
  | resume id token answer =>
    simp only [driveStep]
    repeat' split
    all_goals exact framed_append _ _
  | launch raceId =>
    simp only [driveStep]
    repeat' split
    all_goals exact framed_append _ _
  | enrollRace raceId child =>
    simp only [driveStep]
    split
    · split
      · rw [← List.append_assoc]
        exact framed_append _ _
      · exact framed_append _ _
    · exact framed_append _ _
  | registrationDone raceId yielding =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · split
      · exact framed_append _ _
      · split
        · exact settle_append _ _ _ _
        · exact settle_append _ _ _ _
  | interruptTarget target who extra =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · rw [← List.append_assoc]
      exact framed_append _ _
  | afterInterrupt host yielding kind =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · exact settle_append _ _ _ _
  | raceCancel raceId host yielding remaining visited =>
    simp only [driveStep]
    repeat' split
    all_goals exact framed_append _ _
  | trackChild parent child =>
    simp only [driveStep]
    repeat' split
    all_goals exact framed_append _ _
  | observe id exit observer =>
    simp only [driveStep]
    rw [← List.append_assoc]
    exact framed_append _ _
  | exitDone id =>
    simp only [driveStep]
    split <;> exact framed_append _ _
  | closeParAwait host yielding fibers =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · exact settle_append _ _ _ _
  | link mode scope target interruptor extra =>
    simp only [driveStep]
    rw [← List.append_assoc]
    exact framed_append _ _
  | finish id exit =>
    simp only [driveStep]
    split
    · exact framed_append _ _
    · rw [← List.append_assoc]
      exact framed_append _ _
  | drainDue =>
    simp only [driveStep]
    rw [← List.append_assoc]
    exact framed_append _ _
  | wake list phase =>
    exact framed_append _ _

end Frame

/-! ## Lift 2: one decision -/

section Decision

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w}

/-- The invariant a decision runs its loops under: `J` always; while the machine runs, the
queue fact `I` and the snapshot fact `O` about the tasks a `fire` has drained and not yet run
(`Machine/Fibers.lean:2036-2043`: the snapshot is held by the fold, outside both the machine
and the queue). -/
def Guarded (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop)
    (ts : List (Machine.Task ν σ β ε δ ι α κ)) :
    W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop :=
  fun w m cmds => J w m ∧ (m.stuck = none → I w m cmds ∧ O w m ts)

/-- The fiber is parked at this token: the only case in which an answer resumes it
(`Machine/Fibers.lean:1865-1878`). -/
def ParkedAt (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) (token : Nat) : Prop :=
  ∃ f, m.fiber? id = some f ∧ f.parked = .withGuard token

/-- The machine an `interruptFrom` decision builds before its loop
(`Machine/Fibers.lean:2125-2133`). -/
def interruptEdit (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (who : Option FiberId)
    (extra : ReasonAnnotations α) (target : FiberId) (t : RunFiber ν σ β ε δ ι α χ κ φ) :
    RunMachine ν σ β ε δ ι α χ St κ φ η :=
  let r := interruptRecord interp who extra t
  let m₁ := m.emit [RunEvent.interruptRecorded who target]
  let m₂ := if core.deferredInterrupt r.1.frame && r.1.running then
    m₁.emit [RunEvent.interruptDeferred target] else m₁
  m₂.update r.1

/-- **The decision premises.** One per command (with the snapshot carried), one per loop
entry, and one per edit a decision makes outside the command loop: the dispatcher drained and
disarmed (`:2042-2043`), the `ranTask` event (`:2030`), `yieldVerdict`'s modify (`:2117-2118`),
the interrupt record (`:2125-2133`), the middleware latch (`:2135`), `clockStep` (`:2072-2075`)
and `prepareAnswer` (`:2123-2124`). `A` is the decision's admission (an `AnswerOk`); only the
answer premise reads it. -/
structure DecisionLift (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop)
    (A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop) :
    Prop where
  step : ∀ ts, StepKeeps o interp (Guarded J I O ts)
  nil : ∀ w m, O w m []
  evaluate : ∀ w m id, J w m → m.stuck = none → I w m [Cmd.evaluate id, Cmd.drainDue]
  drain : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner f, J w m →
    m.fiber? owner = some f →
    J w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      O w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
        (f.dispatcher.drain).1
  ran : ∀ w m owner (t : Machine.Task ν σ β ε δ ι α κ), J w m →
    J w (m.emit [RunEvent.ranTask owner t])
  task : ∀ w m owner (t : Machine.Task ν σ β ε δ ι α κ) ts, J w m → m.stuck = none →
    O w m (t :: ts) →
    I w (m.emit [RunEvent.ranTask owner t]) (taskCmds t) ∧
      O w (m.emit [RunEvent.ranTask owner t]) ts
  skip : ∀ w m (t : Machine.Task ν σ β ε δ ι α κ) ts, O w m (t :: ts) → O w m ts
  yield : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) id (v : Bool), J w m →
    J w (m.modify id fun f => { f with yieldOverride := some v })
  interrupt : ∀ w m who extra target t, J w m → m.fiber? target = some t →
    J w (interruptEdit interp m who extra target t)
  middleware : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
    J w { m with middlewareInstalled := true }
  /-- A store edit may need a later world when the world's invariant follows the store. -/
  clockNone : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis st, J w m →
    m.stuck = none → interp.clockStep millis m.state = (none, st) →
    ∃ w', o.le w w' ∧ J w' { m with state := st }
  clockSome : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis owed st, J w m →
    m.stuck = none → interp.clockStep millis m.state = (some owed, st) →
    ∃ w', o.le w w' ∧ J w' (drainOwed { m with state := st } [owed]).1 ∧
      ((drainOwed { m with state := st } [owed]).1.stuck = none →
        I w' (drainOwed { m with state := st } [owed]).1
          ((drainOwed { m with state := st } [owed]).2 ++ [Cmd.drainDue]))
  /-- An answer on a running machine: after `prepareAnswer` and the `resume` it enqueues, the
  loop invariant holds (the guard runs that first command by hand, `AnswerDecision.lean:94-112`;
  `answer_of_split` builds this from a queue fact at the entry). A halted machine keeps its
  store (`prepareAsyncAnswer`, `Machine/Fibers.lean:2103`), so it needs no premise. -/
  answer : ∀ w m id token answer, J w m → m.stuck = none → A w m (.answerAsync id token answer) →
    ∃ w', o.le w w' ∧ Guarded J I O [] w'
      (driveStep interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue]).1
      (driveStep interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue]).2

/-- **The fold premises.** The eight premises of `DecisionLift` that the fold lifts below read: the
command premise with the snapshot carried, the empty snapshot, and the edits a `fire` and an
`advance` make outside the command loop (`Machine/Fibers.lean`: the dispatcher drained and disarmed,
`:2042-2043`; the `ranTask` event, `:2030`; a snapshot task queued or skipped; `clockStep` and the
owed resume, `:2072-2076`). Every decision lift is one (`FoldLift.ofDecisionLift`). The converse
fails: the guard's `Held` is a fold lift whose `interrupt` premise is false, so no decision lift
carries it (`Test/Program/GuardFoldLift.lean`). -/
structure FoldLift (o : WorldOrder W) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop) :
    Prop where
  step : ∀ ts, StepKeeps o interp (Guarded J I O ts)
  nil : ∀ w m, O w m []
  drain : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner f, J w m →
    m.fiber? owner = some f →
    J w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      O w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
        (f.dispatcher.drain).1
  ran : ∀ w m owner (t : Machine.Task ν σ β ε δ ι α κ), J w m →
    J w (m.emit [RunEvent.ranTask owner t])
  task : ∀ w m owner (t : Machine.Task ν σ β ε δ ι α κ) ts, J w m → m.stuck = none →
    O w m (t :: ts) →
    I w (m.emit [RunEvent.ranTask owner t]) (taskCmds t) ∧
      O w (m.emit [RunEvent.ranTask owner t]) ts
  skip : ∀ w m (t : Machine.Task ν σ β ε δ ι α κ) ts, O w m (t :: ts) → O w m ts
  /-- A store edit may need a later world when the world's invariant follows the store. -/
  clockNone : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis st, J w m →
    m.stuck = none → interp.clockStep millis m.state = (none, st) →
    ∃ w', o.le w w' ∧ J w' { m with state := st }
  clockSome : ∀ w (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis owed st, J w m →
    m.stuck = none → interp.clockStep millis m.state = (some owed, st) →
    ∃ w', o.le w w' ∧ J w' (drainOwed { m with state := st } [owed]).1 ∧
      ((drainOwed { m with state := st } [owed]).1.stuck = none →
        I w' (drainOwed { m with state := st } [owed]).1
          ((drainOwed { m with state := st } [owed]).2 ++ [Cmd.drainDue]))

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem not_isSome_of_none {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (hs : m.stuck = none) :
    ¬ m.stuck.isSome = true := by
  rw [hs]
  exact Bool.false_ne_true

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem isSome_of_ne_none {m : RunMachine ν σ β ε δ ι α χ St κ φ η} (hs : ¬ m.stuck = none) :
    m.stuck.isSome = true := by
  cases h : m.stuck with
  | none => exact absurd h hs
  | some why => rfl

/-- One command is the loop at fuel 1 on a running machine. -/
theorem driveState_one (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (c : Cmd ν σ β ε δ ι α κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) (hs : m.stuck = none) :
    driveState interp 1 m (c :: rest) = driveStep interp m c rest := by
  rw [driveState_succ_cons, if_neg (not_isSome_of_none hs), driveState_zero]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
/-- Parking is decided by the fiber table, without choice. -/
theorem parkedAt_em (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) (token : Nat) :
    ParkedAt m id token ∨ ¬ ParkedAt m id token := by
  cases hf : m.fiber? id with
  | none =>
    refine Or.inr ?_
    rintro ⟨f, h, _⟩
    rw [hf] at h
    cases h
  | some f =>
    cases hp : f.parked with
    | notParked =>
      refine Or.inr ?_
      rintro ⟨g, h, hg⟩
      rw [hf] at h
      cases h
      rw [hp] at hg
      cases hg
    | withGuard p =>
      by_cases he : p = token
      · exact Or.inl ⟨f, hf, by rw [hp, he]⟩
      · refine Or.inr ?_
        rintro ⟨g, h, hg⟩
        rw [hf] at h
        cases h
        rw [hp] at hg
        cases hg
        exact he rfl

/-- An answer to a fiber not parked at that token is a no-op command (`Machine/Fibers.lean:1865-1878`). -/
theorem inert_resume (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) (token : Nat) (code : κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) (h : ¬ ParkedAt m id token) :
    driveStep interp m (.resume id token code) rest = (m, rest) := by
  simp only [driveStep]
  split
  · rfl
  · rename_i t ht
    split
    · rename_i parkedToken hp
      split
      · rename_i heq
        exact absurd ⟨t, ht, by rw [hp, heq]⟩ h
      · rfl
    · rfl

theorem interruptFrom_eq (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (who : Option FiberId)
    (extra : ReasonAnnotations α) (target : FiberId) :
    stepDecisionState interp fuel m (.interruptFrom who extra target) =
      (match m.fiber? target with
       | none => (m, true)
       | some t =>
         if (interruptRecord interp who extra t).2 then
           ((driveState interp fuel (interruptEdit interp m who extra target t)
               [Cmd.evaluate target, Cmd.drainDue]).1,
             settled (driveState interp fuel (interruptEdit interp m who extra target t)
               [Cmd.evaluate target, Cmd.drainDue]))
         else (interruptEdit interp m who extra target t, true)) := rfl


/-- The answer premise from a split on parking: a parked fiber's `resume` enters the queue
under `I` and runs as a command; an inert one is a no-op (`inert_resume`) and only
`[drainDue]` remains. The live-answer premise is imposed on the prepared machine. -/
theorem answer_of_split {o : WorldOrder W} {interp : RunInterp ν σ β ε δ ι α χ St κ}
    {J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
    {I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}
    {O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop}
    (step : StepKeeps o interp (Guarded J I O [])) (nil : ∀ w m, O w m [])
    (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) (token : Nat)
    (answer : Completion β ε δ ι α) (hs : m.stuck = none)
    (split : ∃ w', o.le w w' ∧ J w' { m with state := (prepareAsyncAnswer interp m id token answer).1 } ∧
      (ParkedAt m id token →
        I w' { m with state := (prepareAsyncAnswer interp m id token answer).1 }
          [Cmd.resume id token (prepareAsyncAnswer interp m id token answer).2, Cmd.drainDue]) ∧
      (¬ ParkedAt m id token →
        I w' { m with state := (prepareAsyncAnswer interp m id token answer).1 } [Cmd.drainDue])) :
    ∃ w', o.le w w' ∧ Guarded J I O [] w'
      (driveStep interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue]).1
      (driveStep interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue]).2 := by
  obtain ⟨w₁, le₁, hj₁, parked, inert⟩ := split
  rcases parkedAt_em m id token with hp | hp
  · obtain ⟨w₂, le₂, hg⟩ := step w₁ { m with state := (prepareAsyncAnswer interp m id token answer).1 }
      _ _ hs ⟨hj₁, fun _ => ⟨parked hp, nil _ _⟩⟩
    exact ⟨w₂, o.trans le₁ le₂, hg⟩
  · rw [inert_resume interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
      id token _ _ hp]
    exact ⟨w₁, le₁, hj₁, fun _ => ⟨inert hp, nil _ _⟩⟩

variable {o : WorldOrder W} {interp : RunInterp ν σ β ε δ ι α χ St κ}
variable {J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
variable {I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}
variable {O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop}
variable {A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop}

/-- Every decision lift is a fold lift: the eight fields the fold lifts read. -/
theorem FoldLift.ofDecisionLift (h : DecisionLift o interp J I O A) : FoldLift o interp J I O :=
  ⟨h.step, h.nil, h.drain, h.ran, h.task, h.skip, h.clockNone, h.clockSome⟩

/-- The command loop keeps `Guarded` from the command premise alone. -/
theorem FoldLift.loop_lift (h : FoldLift o interp J I O) (ts : List (Machine.Task ν σ β ε δ ι α κ))
    (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m) (hi : m.stuck = none → I w m cmds ∧ O w m ts) :
    ∃ w', o.le w w' ∧ Guarded J I O ts w' (driveState interp fuel m cmds).1
      (driveState interp fuel m cmds).2 :=
  driveState_lift o interp (Guarded J I O ts) (h.step ts) fuel w m cmds ⟨hj, hi⟩

/-- A loop entered with no snapshot keeps `J`. -/
theorem FoldLift.loop_entry (h : FoldLift o interp J I O) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m)
    (hi : m.stuck = none → I w m cmds) :
    ∃ w', o.le w w' ∧ J w' (driveState interp fuel m cmds).1 := by
  obtain ⟨w', le, hj', _⟩ := loop_lift h [] fuel w m cmds hj (fun hs => ⟨hi hs, h.nil w m⟩)
  exact ⟨w', le, hj'⟩

/-- A dispatcher snapshot run task by task (`fireStep`), the snapshot fact carried. -/
theorem FoldLift.fireFold_lift (h : FoldLift o interp J I O) (fuel : Nat) (owner : FiberId) :
    ∀ (tasks : List (Machine.Task ν σ β ε δ ι α κ)) (w : W)
      (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × Bool),
      J w acc.1 → (acc.1.stuck = none → O w acc.1 tasks) →
      ∃ w', o.le w w' ∧ J w' (tasks.foldl (fireStep interp fuel owner) acc).1
  | [], w, _, hj, _ => ⟨w, o.refl w, hj⟩
  | t :: ts, w, acc, hj, ho => by
    rw [List.foldl_cons]
    by_cases hb : acc.2 = true
    · have hstep : fireStep interp fuel owner acc t =
          ((driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t)).1,
            settled (driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t))) := by
        unfold fireStep
        rw [if_pos hb]
      rw [hstep]
      obtain ⟨w₁, le₁, hj₁, hi₁⟩ := loop_lift h ts fuel w (acc.1.emit [RunEvent.ranTask owner t])
        (taskCmds t) (h.ran w acc.1 owner t hj) (fun hs => h.task w acc.1 owner t ts hj hs (ho hs))
      obtain ⟨w₂, le₂, hj₂⟩ := fireFold_lift h fuel owner ts w₁
        ((driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t)).1,
          settled (driveState interp fuel (acc.1.emit [RunEvent.ranTask owner t]) (taskCmds t)))
        hj₁ (fun hs => (hi₁ hs).2)
      exact ⟨w₂, o.trans le₁ le₂, hj₂⟩
    · have hstep : fireStep interp fuel owner acc t = acc := by
        unfold fireStep
        rw [if_neg hb]
      rw [hstep]
      exact fireFold_lift h fuel owner ts w acc hj (fun hs => h.skip w acc.1 t ts (ho hs))

/-- One `fire`: the dispatcher drained and disarmed, then its snapshot run. -/
theorem FoldLift.fireState_lift (h : FoldLift o interp J I O) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) (hj : J w m) :
    ∃ w', o.le w w' ∧ J w' (fireState interp fuel m owner).1 := by
  unfold fireState
  split
  · exact ⟨w, o.refl w, hj⟩
  · rename_i f hf
    obtain ⟨hj₀, ho₀⟩ := h.drain w m owner f hj hf
    exact fireFold_lift h fuel owner _ w _ hj₀ (fun _ => ho₀)

/-- A flush: rounds of `fire` over the armed dispatchers. -/
theorem FoldLift.flushAllState_lift (h : FoldLift o interp J I O) (fuel : Nat) :
    ∀ (rounds : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
      ∃ w', o.le w w' ∧ J w' (flushAllState interp fuel rounds m).1
  | 0, w, _, hj => ⟨w, o.refl w, hj⟩
  | rounds + 1, w, m, hj => by
    simp only [flushAllState]
    split
    · exact ⟨w, o.refl w, hj⟩
    · rename_i owner _ _
      split
      · exact ⟨w, o.refl w, hj⟩
      · obtain ⟨w₁, le₁, hj₁⟩ := fireState_lift h fuel w m owner hj
        split
        · obtain ⟨w₂, le₂, hj₂⟩ := flushAllState_lift h fuel rounds w₁ _ hj₁
          exact ⟨w₂, o.trans le₁ le₂, hj₂⟩
        · exact ⟨w₁, le₁, hj₁⟩

/-- An `advance`: rounds of `clockStep`, the owed resume through the loop, then a flush. -/
theorem FoldLift.advanceState_lift (h : FoldLift o interp J I O) (fuel : Nat)
    (millis : ClockMillis) :
    ∀ (rounds : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
      ∃ w', o.le w w' ∧ J w' (advanceState interp fuel millis rounds m).1
  | 0, w, _, hj => ⟨w, o.refl w, hj⟩
  | rounds + 1, w, m, hj => by
    simp only [advanceState]
    split
    · exact ⟨w, o.refl w, hj⟩
    · rename_i hs
      split
      · rename_i st hc
        exact h.clockNone w m millis st hj (stuck_none_of_not hs) hc
      · rename_i owed st hc
        obtain ⟨w₁, le₁, hj₁, hi₁⟩ := h.clockSome w m millis owed st hj (stuck_none_of_not hs) hc
        obtain ⟨w₂, le₂, hj₂⟩ := loop_entry h fuel w₁ _ _ hj₁ hi₁
        split
        · obtain ⟨w₃, le₃, hj₃⟩ := flushAllState_lift h fuel fuel w₂ _ hj₂
          split
          · obtain ⟨w₄, le₄, hj₄⟩ := advanceState_lift h fuel millis rounds w₃ _ hj₃
            exact ⟨w₄, o.trans (o.trans (o.trans le₁ le₂) le₃) le₄, hj₄⟩
          · exact ⟨w₃, o.trans (o.trans le₁ le₂) le₃, hj₃⟩
        · exact ⟨w₂, o.trans le₁ le₂, hj₂⟩

/-! The decision-lift forms below keep their names and statements; each is its fold-lift form
through `FoldLift.ofDecisionLift`. -/

theorem loop_lift (h : DecisionLift o interp J I O A) (ts : List (Machine.Task ν σ β ε δ ι α κ))
    (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m) (hi : m.stuck = none → I w m cmds ∧ O w m ts) :
    ∃ w', o.le w w' ∧ Guarded J I O ts w' (driveState interp fuel m cmds).1
      (driveState interp fuel m cmds).2 :=
  (FoldLift.ofDecisionLift h).loop_lift ts fuel w m cmds hj hi

theorem loop_entry (h : DecisionLift o interp J I O A) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m)
    (hi : m.stuck = none → I w m cmds) :
    ∃ w', o.le w w' ∧ J w' (driveState interp fuel m cmds).1 :=
  (FoldLift.ofDecisionLift h).loop_entry fuel w m cmds hj hi

theorem fireFold_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (owner : FiberId) :
    ∀ (tasks : List (Machine.Task ν σ β ε δ ι α κ)) (w : W)
      (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × Bool),
      J w acc.1 → (acc.1.stuck = none → O w acc.1 tasks) →
      ∃ w', o.le w w' ∧ J w' (tasks.foldl (fireStep interp fuel owner) acc).1 :=
  (FoldLift.ofDecisionLift h).fireFold_lift fuel owner

theorem fireState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) (hj : J w m) :
    ∃ w', o.le w w' ∧ J w' (fireState interp fuel m owner).1 :=
  (FoldLift.ofDecisionLift h).fireState_lift fuel w m owner hj

theorem flushAllState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) :
    ∀ (rounds : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
      ∃ w', o.le w w' ∧ J w' (flushAllState interp fuel rounds m).1 :=
  (FoldLift.ofDecisionLift h).flushAllState_lift fuel

theorem advanceState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (millis : ClockMillis) :
    ∀ (rounds : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η), J w m →
      ∃ w', o.le w w' ∧ J w' (advanceState interp fuel millis rounds m).1 :=
  (FoldLift.ofDecisionLift h).advanceState_lift fuel millis

/-- **Lift 2, one decision.** From the command premise and one premise per edit outside the
loop, every decision keeps `J`, at some later world, when its admission `A` holds. -/
theorem stepDecisionState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (d : RunDecision ν σ β ε δ ι α)
    (hj : J w m) (ha : A w m d) :
    ∃ w', o.le w w' ∧ J w' (stepDecisionState interp fuel m d).1 := by
  cases d with
  | fire owner => exact fireState_lift h fuel w m owner hj
  | flush => exact flushAllState_lift h fuel fuel w m hj
  | evaluate id => exact loop_entry h fuel w m _ hj (h.evaluate w m id hj)
  | yieldVerdict id v => exact ⟨w, o.refl w, h.yield w m id v hj⟩
  | answerAsync id token answer =>
    cases fuel with
    | zero => exact ⟨w, o.refl w, hj⟩
    | succ fuel =>
      show ∃ w', o.le w w' ∧ J w' (driveState interp (fuel + 1)
        { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        [Cmd.resume id token (prepareAsyncAnswer interp m id token answer).2, Cmd.drainDue]).1
      by_cases hs : m.stuck = none
      · rw [driveState_succ_cons, if_neg (not_isSome_of_none hs)]
        obtain ⟨w₁, le₁, hg₁⟩ := h.answer w m id token answer hj hs ha
        obtain ⟨w₂, le₂, hj₂, _⟩ := loop_lift h [] fuel w₁ _ _ hg₁.1 hg₁.2
        exact ⟨w₂, o.trans le₁ le₂, hj₂⟩
      · have hkeep : prepareAsyncAnswer interp m id token answer =
            (m.state, interp.answerCode answer) := by
          unfold prepareAsyncAnswer
          rw [if_pos (isSome_of_ne_none hs)]
        rw [hkeep, driveState_stuck interp (fuel + 1) { m with state := m.state } _
          (isSome_of_ne_none (m := { m with state := m.state }) hs)]
        exact ⟨w, o.refl w, hj⟩
  | interruptFrom who extra target =>
    rw [interruptFrom_eq]
    split
    · exact ⟨w, o.refl w, hj⟩
    · rename_i t ht
      have hj₁ := h.interrupt w m who extra target t hj ht
      split
      · exact loop_entry h fuel w _ _ hj₁ (h.evaluate w _ target hj₁)
      · exact ⟨w, o.refl w, hj₁⟩
  | installMiddleware => exact ⟨w, o.refl w, h.middleware w m hj⟩
  | advance millis => exact advanceState_lift h fuel millis fuel w m hj

end Decision

/-! ## Replay -/

section Replay

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w}

/-- The decisions replay applies, each admitted at the machine it meets. Replay stops at a
halted machine and at the first decision whose loop runs out of fuel
(`Machine/Fibers.lean:2188-2200`); decisions after that are never applied and impose nothing. -/
def AdmittedReplay (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop)
    (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) :
    RunMachine ν σ β ε δ ι α χ St κ φ η → List (RunDecision ν σ β ε δ ι α) → Prop
  | _, [] => True
  | m, d :: tape => m.stuck = none → (∀ w, J w m → A w m d) ∧
      ((stepDecisionState interp fuel m d).2 = true →
        AdmittedReplay J A interp fuel (stepDecisionState interp fuel m d).1 tape)

theorem replayEval_nil_machine (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : (replayEval interp fuel [] m).machine = m := by
  simp only [replayEval]
  split
  · rfl
  · split
    · rfl
    · rfl

/-- **Lift 3, replay** (the reference `replayR`, `Laws/Program/RuntimeR.lean:51-54`). -/
theorem replayEval_lift (o : WorldOrder W) (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop)
    (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (pres : ∀ w m d, m.stuck = none → J w m → A w m d →
      ∃ w', o.le w w' ∧ J w' (stepDecisionState interp fuel m d).1) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      J w m → AdmittedReplay J A interp fuel m tape →
      ∃ w', o.le w w' ∧ J w' (replayEval interp fuel tape m).machine
  | [], w, m, hj, _ => ⟨w, o.refl w, by rw [replayEval_nil_machine]; exact hj⟩
  | d :: tape, w, m, hj, adm => by
    simp only [replayEval]
    split
    · exact ⟨w, o.refl w, hj⟩
    · rename_i hs
      obtain ⟨hA, hrest⟩ := adm hs
      obtain ⟨w₁, le₁, hj₁⟩ := pres w m d hs hj (hA w hj)
      split
      · rename_i hr
        obtain ⟨w₂, le₂, hj₂⟩ := replayEval_lift o J A interp fuel pres tape w₁ _ hj₁ (hrest hr)
        exact ⟨w₂, o.trans le₁ le₂, hj₂⟩
      · exact ⟨w₁, le₁, hj₁⟩

end Replay

/-! ## A fact through a folded history

The history form of the lifts above, for any state type and step: a fact every admitted step
keeps holds after the whole fold, at a later world. The guard's prefix replay
(`executePrefix`, `Laws/Program/Guard/Core.lean`) is its user. Moved here from
`Laws/Program/Guard/Core.lean` on 2026-10-01, beside the other lifts. -/

section History

variable {W : Type w} {M : Type u} {X : Type v}

/-- Every history step is admitted at the state it actually meets, for every world that
satisfies the invariant at that state. -/
def Admitted (J : W → M → Prop) (A : W → M → X → Prop) (step : M → X → M) :
    M → List X → Prop
  | _, [] => True
  | m, x :: xs => (∀ w, J w m → A w m x) ∧ Admitted J A step (step m x) xs

/-- A fact kept by every admitted step holds after the whole folded history, at a later
world. This is the history form of the machine lift. -/
theorem foldl_lift (o : WorldOrder W) (J : W → M → Prop)
    (A : W → M → X → Prop) (step : M → X → M)
    (pres : ∀ w m x, J w m → A w m x → ∃ w', o.le w w' ∧ J w' (step m x)) :
    ∀ (xs : List X) (w : W) (m : M), J w m → Admitted J A step m xs →
      ∃ w', o.le w w' ∧ J w' (xs.foldl step m)
  | [], w, _, hj, _ => ⟨w, o.refl w, hj⟩
  | x :: xs, w, m, hj, ⟨hx, hxs⟩ => by
    obtain ⟨w₁, le₁, hj₁⟩ := pres w m x hj (hx w hj)
    obtain ⟨w₂, le₂, hj₂⟩ := foldl_lift o J A step pres xs w₁ (step m x) hj₁ hxs
    exact ⟨w₂, o.trans le₁ le₂, hj₂⟩

/-- A history whose every step is admitted at every state the invariant holds of is admitted
along the run it makes. -/
theorem admitted_of_forall (J : W → M → Prop) (A : W → M → X → Prop) (step : M → X → M) :
    ∀ (xs : List X), (∀ x ∈ xs, ∀ w m, J w m → A w m x) → ∀ m, Admitted J A step m xs
  | [], _, _ => trivial
  | x :: xs, h, m =>
    ⟨fun w hj => h x (List.mem_cons_self ..) w m hj,
      admitted_of_forall J A step xs (fun y hy => h y (List.mem_cons_of_mem _ hy)) (step m x)⟩

/-- When admission imposes no condition, every history is admitted. -/
theorem admitted_true (J : W → M → Prop) (step : M → X → M) (xs : List X) (m : M) :
    Admitted J (fun _ _ _ => True) step m xs :=
  admitted_of_forall J (fun _ _ _ => True) step xs (fun _ _ _ _ _ => trivial) m

end History

/-! ## Facts about the machine alone -/

section MachineFact

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-- The edits outside the loop, each keeping a machine fact `P`. -/
structure MachineEdits (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (P : RunMachine ν σ β ε δ ι α χ St κ φ η → Prop) : Prop where
  drain : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner f, P m → m.fiber? owner = some f →
    P ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
  ran : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner (t : Machine.Task ν σ β ε δ ι α κ),
    P m → P (m.emit [RunEvent.ranTask owner t])
  yield : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) id (v : Bool), P m →
    P (m.modify id fun f => { f with yieldOverride := some v })
  interrupt : ∀ m who extra target t, P m → m.fiber? target = some t →
    P (interruptEdit interp m who extra target t)
  middleware : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η), P m →
    P { m with middlewareInstalled := true }
  clock : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) millis, P m → m.stuck = none →
    P { m with state := (interp.clockStep millis m.state).2 }
  owed : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owed, P m → P (drainOwed m [owed]).1
  prepare : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) id token answer, P m →
    P { m with state := (prepareAsyncAnswer interp m id token answer).1 }

/-- **Decision level** for a machine fact: the decision lift at `W := Unit`, `I := P`,
no snapshot fact and no admission. -/
theorem machineFact_stepDecision (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (P : RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (step : ∀ m c rest, m.stuck = none → P m → P (driveStep interp m c rest).1)
    (edits : MachineEdits interp P) (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (d : RunDecision ν σ β ε δ ι α) (hp : P m) : P (stepDecisionState interp fuel m d).1 := by
  have lift : DecisionLift unitOrder interp (fun _ m => P m) (fun _ m _ => P m)
      (fun _ _ _ => True) (fun _ _ _ => True) :=
    { step := fun _ _ m c rest hs h =>
        ⟨(), trivial, step m c rest hs h.1, fun _ => ⟨step m c rest hs h.1, trivial⟩⟩
      nil := fun _ _ => trivial
      evaluate := fun _ _ _ hp _ => hp
      drain := fun _ m owner f hp hf => ⟨edits.drain m owner f hp hf, trivial⟩
      ran := fun _ m owner t hp => edits.ran m owner t hp
      task := fun _ m owner t _ hp _ _ => ⟨edits.ran m owner t hp, trivial⟩
      skip := fun _ _ _ _ _ => trivial
      yield := fun _ m id v hp => edits.yield m id v hp
      interrupt := fun _ m who extra target t hp hf => edits.interrupt m who extra target t hp hf
      middleware := fun _ m hp => edits.middleware m hp
      clockNone := fun _ m millis st hp hs hc => by
        have h := edits.clock m millis hp hs
        rw [hc] at h
        exact ⟨(), trivial, h⟩
      clockSome := fun _ m millis owed st hp hs hc => by
        have h := edits.clock m millis hp hs
        rw [hc] at h
        exact ⟨(), trivial, edits.owed _ owed h, fun _ => edits.owed _ owed h⟩
      answer := fun _ m id token answer hp hs _ => by
        have hq := edits.prepare m id token answer hp
        have hr := step { m with state := (prepareAsyncAnswer interp m id token answer).1 }
          (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue] hs hq
        exact ⟨(), trivial, hr, fun _ => ⟨hr, trivial⟩⟩ }
  obtain ⟨_, _, h⟩ := stepDecisionState_lift lift fuel () m d hp trivial
  exact h

end MachineFact

end Effect4.Machine.Lift
