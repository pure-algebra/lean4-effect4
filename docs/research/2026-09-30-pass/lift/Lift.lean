import Effect4.Laws.Machine.Approximation
import Effect4.Laws.Machine.Keeps
import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Program.Guard.Decision
import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Api.TraceOrigin

/-!
# Research.Pass.Lift — one lift for facts every step keeps (probe)

Generic in the machine instance: every theorem here quantifies over the machine's type
parameters, its `FiberCore` and `FiberEvaluator` instances and the interpreter. The world
order is the tree's own `WorldOrder` (`Laws/Effects/Protocol.lean:30`), whose `hostOrder`
instance is M6's `World.leHost` (`Laws/Program/Typed/Validity.lean:121`).

Three lifts, kept apart (origin-ledger plan §4):
1. the command loop (`driveState_lift`), from one fact per command;
2. one decision (`stepDecisionState_lift`), from 1 plus one fact per edit outside the loop;
3. a whole run (`foldl_lift`/`reachable_lift` for the native prefix, `replayEval_lift`/
   `rreachable_lift` for the reference replay).

Beside them, the frame law (`driveStep_append`). Then three instances, each checked against the
tree's own statements: the guard (`driverContract_of_lift`, `guardState_steppedBy_of_lift`,
`guardState_reachable_of_lift`), M6 (`m6_stepKeeps`, `m6_decision_preserves`, the repaired
capstone `m6_capstone`, the typed-layer `m6_capstone_admitted`), and the fork-ledger trace
agreement as a `Keeps` (`ledger_driveState`, `ledger_stepDecision`, `reachable_agrees_of`).
Red controls are in `Controls.lean`.
-/

set_option autoImplicit false

namespace Research.Pass.Lift

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
residues empty (`settle`'s stuck arm returns `[]`, `Machine/Fibers.lean:1798-1799`). -/
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
new commands in front of `rest` untouched, except a halt, which drops everything. -/
theorem driveStep_append (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (c : Cmd ν σ β ε δ ι α κ)
    (rest s : List (Cmd ν σ β ε δ ι α κ)) :
    Framed s (driveStep interp m c rest) (driveStep interp m c (rest ++ s)) := by
  cases c <;> simp only [driveStep]
  all_goals (repeat' split)
  all_goals first
    | exact settle_append _ _ _ _
    | exact framed_append _ _
    | (rw [← List.append_assoc]; exact framed_append _ _)

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
(`Machine/Fibers.lean:2009-2016`: the snapshot is held by the fold, outside both the machine
and the queue). -/
def Guarded (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop)
    (ts : List (Machine.Task ν σ β ε δ ι α κ)) :
    W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop :=
  fun w m cmds => J w m ∧ (m.stuck = none → I w m cmds ∧ O w m ts)

/-- The fiber is parked at this token: the only case in which an answer resumes it
(`Machine/Fibers.lean:1838-1851`). -/
def ParkedAt (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (id : FiberId) (token : Nat) : Prop :=
  ∃ f, m.fiber? id = some f ∧ f.parked = .withGuard token

/-- The machine an `interruptFrom` decision builds before its loop
(`Machine/Fibers.lean:2098-2106`). -/
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
disarmed (`:2015-2016`), the `ranTask` event (`:2003`), `yieldVerdict`'s modify (`:2090-2091`),
the interrupt record (`:2098-2106`), the middleware latch (`:2108`), `clockStep` (`:2045-2048`)
and `prepareAnswer` (`:2096-2097`). `A` is the decision's admission (an `AnswerOk`); only the
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
  /-- A store edit may need a later world: M6's world follows the store exactly
  (`WorldValid.state`, `Typed/Validity.lean:27`). -/
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
  store (`prepareAsyncAnswer`, `Machine/Fibers.lean:2076`), so it needs no premise. -/
  answer : ∀ w m id token answer, J w m → m.stuck = none → A w m (.answerAsync id token answer) →
    ∃ w', o.le w w' ∧ Guarded J I O [] w'
      (driveStep interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue]).1
      (driveStep interp { m with state := (prepareAsyncAnswer interp m id token answer).1 }
        (.resume id token (prepareAsyncAnswer interp m id token answer).2) [Cmd.drainDue]).2

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

/-- An answer to a fiber not parked at that token is a no-op command (`Machine/Fibers.lean:1838-1851`). -/
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
`[drainDue]` remains. This is the shape M6's `AnswerOk` supports (finding F2). -/
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

theorem loop_lift (h : DecisionLift o interp J I O A) (ts : List (Machine.Task ν σ β ε δ ι α κ))
    (fuel : Nat) (w : W) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m) (hi : m.stuck = none → I w m cmds ∧ O w m ts) :
    ∃ w', o.le w w' ∧ Guarded J I O ts w' (driveState interp fuel m cmds).1
      (driveState interp fuel m cmds).2 :=
  driveState_lift o interp (Guarded J I O ts) (h.step ts) fuel w m cmds ⟨hj, hi⟩

theorem loop_entry (h : DecisionLift o interp J I O A) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) (hj : J w m)
    (hi : m.stuck = none → I w m cmds) :
    ∃ w', o.le w w' ∧ J w' (driveState interp fuel m cmds).1 := by
  obtain ⟨w', le, hj', _⟩ := loop_lift h [] fuel w m cmds hj (fun hs => ⟨hi hs, h.nil w m⟩)
  exact ⟨w', le, hj'⟩

theorem fireFold_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (owner : FiberId) :
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

theorem fireState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (w : W)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) (hj : J w m) :
    ∃ w', o.le w w' ∧ J w' (fireState interp fuel m owner).1 := by
  unfold fireState
  split
  · exact ⟨w, o.refl w, hj⟩
  · rename_i f hf
    obtain ⟨hj₀, ho₀⟩ := h.drain w m owner f hj hf
    exact fireFold_lift h fuel owner _ w _ hj₀ (fun _ => ho₀)

theorem flushAllState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) :
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

theorem advanceState_lift (h : DecisionLift o interp J I O A) (fuel : Nat) (millis : ClockMillis) :
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

/-! ## Lift 3: a whole run -/

section History

variable {W : Type w} {M : Type u} {X : Type v}

/-- Every step of a history is admitted at the state it actually meets: for every world that
types that state. With an admission that ignores the world this is just "each step meets `A`". -/
def Admitted (J : W → M → Prop) (A : W → M → X → Prop) (step : M → X → M) : M → List X → Prop
  | _, [] => True
  | m, x :: xs => (∀ w, J w m → A w m x) ∧ Admitted J A step (step m x) xs

/-- **Lift 3, a folded history** (the native `executePrefix`, `Guard/Core.lean:27-29`). -/
theorem foldl_lift (o : WorldOrder W) (J : W → M → Prop) (A : W → M → X → Prop)
    (step : M → X → M) (pres : ∀ w m x, J w m → A w m x → ∃ w', o.le w w' ∧ J w' (step m x)) :
    ∀ (xs : List X) (w : W) (m : M), J w m → Admitted J A step m xs →
      ∃ w', o.le w w' ∧ J w' (xs.foldl step m)
  | [], w, _, hj, _ => ⟨w, o.refl w, hj⟩
  | x :: xs, w, m, hj, ⟨hx, hxs⟩ => by
    obtain ⟨w₁, le₁, hj₁⟩ := pres w m x hj (hx w hj)
    obtain ⟨w₂, le₂, hj₂⟩ := foldl_lift o J A step pres xs w₁ (step m x) hj₁ hxs
    exact ⟨w₂, o.trans le₁ le₂, hj₂⟩

/-- With no admission, every history is admitted. -/
theorem admitted_true (J : W → M → Prop) (step : M → X → M) :
    ∀ (xs : List X) (m : M), Admitted J (fun _ _ _ => True) step m xs
  | [], _ => trivial
  | _ :: xs, _ => ⟨fun _ _ => trivial, admitted_true J step xs _⟩

end History

section Replay

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w}

/-- The decisions replay applies, each admitted at the machine it meets. Replay stops at a
halted machine and at the first decision whose loop runs out of fuel
(`Machine/Fibers.lean:2161-2174`); decisions after that are never applied and impose nothing. -/
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

/-! ## Instance 1: the guard's `DriverContract` (native machine, `W := Unit`) -/

section GuardLoop

open Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.RegistrationQueue

/-- The guard's loop invariant (`Guard/Contract.lean:10-14`). -/
def guardI (p : NativeEff) (table : RowTable) (m : NativeMachine) (cmds : List NCmd) : Prop :=
  GuardState m ∧ GuardQueue p table m cmds ∧ RegistrationQueue cmds

/-- `DriverContract.invariant`, from the loop lift and `driveStep_invariants`. -/
theorem guard_invariant (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      letI := evaluatorFor p table
      let result := driveState (interpOf p table) fuel m commands
      GuardState result.1 ∧ GuardQueue p table result.1 result.2 ∧ RegistrationQueue result.2 := by
  intro fuel m commands state queue registration
  letI := evaluatorFor p table
  exact driveState_lift_unit (interpOf p table) (guardI p table)
    (fun m c rest _ h => driveStep_invariants p table m c rest h.1 h.2.1 h.2.2)
    fuel m commands ⟨state, queue, registration⟩

/-- `DriverContract.reserved`: the same lift at the invariant with the frame fact beside it. -/
theorem guard_reserved (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (keys : List GuardKey),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      ReservedKeys m keys →
      letI := evaluatorFor p table
      ReservedKeys (driveState (interpOf p table) fuel m commands).1 keys := by
  intro fuel m commands keys state queue registration reserved
  letI := evaluatorFor p table
  exact (driveState_lift_unit (interpOf p table)
    (fun m cmds => guardI p table m cmds ∧ ReservedKeys m keys)
    (fun m c rest _ h => ⟨driveStep_invariants p table m c rest h.1.1 h.1.2.1 h.1.2.2,
      reservedKeys_driveStep p table m c rest h.1.1 h.1.2.1 keys h.2⟩)
    fuel m commands ⟨⟨state, queue, registration⟩, reserved⟩).2

theorem guard_interrupted (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd) (fiber : FiberId),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      InterruptedAt m fiber →
      letI := evaluatorFor p table
      InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber := by
  intro fuel m commands fiber state queue registration before
  letI := evaluatorFor p table
  exact (driveState_lift_unit (interpOf p table)
    (fun m cmds => guardI p table m cmds ∧ InterruptedAt m fiber)
    (fun m c rest _ h => ⟨driveStep_invariants p table m c rest h.1.1 h.1.2.1 h.1.2.2,
      interruptedAt_driveStep p table m c rest h.1.1 fiber h.2⟩)
    fuel m commands ⟨⟨state, queue, registration⟩, before⟩).2

theorem guard_request (p : NativeEff) (table : RowTable) :
    ∀ (fuel : Nat) (m : NativeMachine) (commands : List NCmd)
      (fiber : FiberId) (token : Nat) (request : NativeOp × Val),
      GuardState m → GuardQueue p table m commands → RegistrationQueue commands →
      requestOf m fiber token = some request →
      letI := evaluatorFor p table
      requestOf (driveState (interpOf p table) fuel m commands).1 fiber token = some request ∨
        InterruptedAt (driveState (interpOf p table) fuel m commands).1 fiber := by
  intro fuel m commands fiber token request state queue registration before
  letI := evaluatorFor p table
  refine (driveState_lift_unit (interpOf p table)
    (fun m cmds => guardI p table m cmds ∧
      (requestOf m fiber token = some request ∨ InterruptedAt m fiber))
    (fun m c rest _ h => ⟨driveStep_invariants p table m c rest h.1.1 h.1.2.1 h.1.2.2, ?_⟩)
    fuel m commands ⟨⟨state, queue, registration⟩, Or.inl before⟩).2
  rcases h.2 with kept | interrupted
  · exact requestOrInterrupted_driveStep p table m c rest h.1.1 h.1.2.1 fiber token request kept
  · exact Or.inr (interruptedAt_driveStep p table m c rest h.1.1 fiber interrupted)

/-- **The guard's contract is an instance.** All four fields of `DriverContract` come from the
one loop lift, each at its own invariant, with the guard's per-command lemmas as premises. -/
theorem driverContract_of_lift (p : NativeEff) (table : RowTable) : DriverContract p table :=
  ⟨guard_invariant p table, guard_reserved p table, guard_request p table,
    guard_interrupted p table⟩

end GuardLoop

/-! ## Instance 2: M6 (reference machine; the world is `Typed.World` under `hostOrder`) -/

section M6

open Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- `QueueOk` is a statement about each command, so it splits over an append. -/
theorem queueOk_append (root : ProgramSource) (w : Typed.World) (a b : List RCmd) :
    QueueOk root w (a ++ b) ↔ QueueOk root w a ∧ QueueOk root w b := by
  unfold QueueOk
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left b hc), fun c hc => h c (List.mem_append_right a hc)⟩
  · intro h c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.1 c hc
    · exact h.2 c hc

/-- The loop invariant of M6: the typed state and a typed queue (`Typed/Assembly.lean:93-97`). -/
def m6I (root : ProgramSource) (rootTy : EffTy) (w : Typed.World) (m : RState) (cmds : List RCmd) : Prop :=
  TypedState root rootTy w m ∧ QueueOk root w cmds

/-- The snapshot fact of M6: the drained tasks' commands are a typed queue. -/
def m6O (root : ProgramSource) (w : Typed.World) (_ : RState)
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann RProgram)) : Prop :=
  QueueOk root w (ts.flatMap taskCmds)

/-- **M6's per-command obligations are the loop lift's premise, exactly.** -/
theorem m6_stepKeeps (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ cmd, StepPreserves root rootTy cmd) :
    letI := termEvaluatorFor root.program
    StepKeeps hostOrder (interpR root.program) (m6I root rootTy) := by
  letI := termEvaluatorFor root.program
  intro w m c rest _ h
  exact steps c w m rest h.1 h.2

/-- The ledger's 18 `step_*` obligations (`Typed/Assembly.lean:161-215`), one per `Cmd`
constructor, are together exactly the lift's premise `∀ cmd, StepPreserves root rootTy cmd`. -/
theorem m6_steps_of_ledger (root : ProgramSource) (rootTy : EffTy)
    (evaluate : ∀ id, StepPreserves root rootTy (.evaluate id))
    (loop : ∀ id yielding, StepPreserves root rootTy (.loop id yielding))
    (deliver : ∀ id yielding, StepPreserves root rootTy (.deliver id yielding))
    (finish : ∀ id exit, StepPreserves root rootTy (.finish id exit))
    (resume : ∀ id token code, StepPreserves root rootTy (.resume id token code))
    (launch : ∀ race, StepPreserves root rootTy (.launch race))
    (enrollRace : ∀ race child, StepPreserves root rootTy (.enrollRace race child))
    (registrationDone : ∀ race yielding, StepPreserves root rootTy (.registrationDone race yielding))
    (interruptTarget : ∀ target who extra, StepPreserves root rootTy (.interruptTarget target who extra))
    (afterInterrupt : ∀ host yielding kind, StepPreserves root rootTy (.afterInterrupt host yielding kind))
    (raceCancel : ∀ race host yielding remaining visited,
      StepPreserves root rootTy (.raceCancel race host yielding remaining visited))
    (trackChild : ∀ parent child, StepPreserves root rootTy (.trackChild parent child))
    (observe : ∀ fiber exit observer, StepPreserves root rootTy (.observe fiber exit observer))
    (exitDone : ∀ fiber, StepPreserves root rootTy (.exitDone fiber))
    (closeParAwait : ∀ host yielding fibers, StepPreserves root rootTy (.closeParAwait host yielding fibers))
    (link : ∀ mode scope target interruptor extra,
      StepPreserves root rootTy (.link mode scope target interruptor extra))
    (drainDue : StepPreserves root rootTy .drainDue)
    (wake : ∀ list phase, StepPreserves root rootTy (.wake list phase)) :
    ∀ cmd, StepPreserves root rootTy cmd
  | .evaluate id => evaluate id
  | .loop id yielding => loop id yielding
  | .deliver id yielding => deliver id yielding
  | .finish id exit => finish id exit
  | .resume id token code => resume id token code
  | .launch race => launch race
  | .enrollRace race child => enrollRace race child
  | .registrationDone race yielding => registrationDone race yielding
  | .interruptTarget target who extra => interruptTarget target who extra
  | .afterInterrupt host yielding kind => afterInterrupt host yielding kind
  | .raceCancel race host yielding remaining visited => raceCancel race host yielding remaining visited
  | .trackChild parent child => trackChild parent child
  | .observe fiber exit observer => observe fiber exit observer
  | .exitDone fiber => exitDone fiber
  | .closeParAwait host yielding fibers => closeParAwait host yielding fibers
  | .link mode scope target interruptor extra => link mode scope target interruptor extra
  | .drainDue => drainDue
  | .wake list phase => wake list phase

/-- One of the 18, checked against the ledger's declaration by the kernel. -/
example (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat) (code : RProgram) :
    ProofGraph.Obligation (StepPreserves root rootTy (.resume id token code)) :=
  M6Ledger.step_resume root rootTy id token code

/-- M6's loop, from the 18 per-command obligations. -/
theorem m6_driveState (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ cmd, StepPreserves root rootTy cmd) (fuel : Nat) (w : Typed.World) (m : RState)
    (cmds : List RCmd) (ht : TypedState root rootTy w m) (hq : QueueOk root w cmds) :
    letI := termEvaluatorFor root.program
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' (driveState (interpR root.program) fuel m cmds).1 ∧
      QueueOk root w' (driveState (interpR root.program) fuel m cmds).2 := by
  letI := termEvaluatorFor root.program
  exact driveState_lift hostOrder (interpR root.program) (m6I root rootTy)
    (m6_stepKeeps root rootTy steps) fuel w m cmds ⟨ht, hq⟩

/-- **The snapshot comes free.** Because every `StepPreserves` quantifies over the whole pending
list, the frame law lets the drained snapshot ride as a suffix of it: the same 18 obligations
carry a `fire` decision's snapshot to the new world. No transport lemma for `ResumeOk` is needed
(it has none, `Typed/Contracts.lean:71-74`). -/
theorem m6_stepFrame (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ cmd, StepPreserves root rootTy cmd)
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann RProgram)) :
    letI := termEvaluatorFor root.program
    StepKeeps hostOrder (interpR root.program)
      (Guarded (TypedState root rootTy) (m6I root rootTy) (m6O root) ts) := by
  letI := termEvaluatorFor root.program
  intro w m c rest hs h
  obtain ⟨⟨ht, hq⟩, ho⟩ := h.2 hs
  have hq' : QueueOk root w (c :: (rest ++ ts.flatMap taskCmds)) := by
    rw [← List.cons_append]
    exact (queueOk_append root w _ _).mpr ⟨hq, ho⟩
  obtain ⟨w', le, ht', hq''⟩ := steps c w m (rest ++ ts.flatMap taskCmds) ht hq'
  obtain ⟨hm, hres⟩ := driveStep_append (interpR root.program) m c rest (ts.flatMap taskCmds)
  rw [hm] at ht'
  refine ⟨w', le, ht', fun hs' => ?_⟩
  rcases hres with hres | ⟨_, _, hstuck⟩
  · rw [hres] at hq''
    obtain ⟨hq₁, hq₂⟩ := (queueOk_append root w' _ _).mp hq''
    exact ⟨⟨ht', hq₁⟩, hq₂⟩
  · rw [hs'] at hstuck
    cases hstuck

/-- `TypedState` reads the fibers, races, store and token counter only (`RunMachineOk`,
generated at `Typed/State.lean:26`; `WorldValid`, `Typed/Validity.lean:19-34`), so an edit of
the trace or of the middleware latch keeps it at the same world. -/
theorem m6_ran (root : ProgramSource) (rootTy : EffTy) (w : Typed.World) (m : RState)
    (owner : FiberId) (t : Machine.Task EffName EffThunk Val Err Defect FiberId Ann RProgram)
    (h : TypedState root rootTy w m) :
    TypedState root rootTy w (m.emit [RunEvent.ranTask owner t]) := by
  obtain ⟨hv, hok, hpark⟩ := h
  exact ⟨⟨hv.ids, hv.fibers, hv.heap, hv.promises, hv.tokens, hv.tokenBound, hv.tokenTargets,
    hv.state, hv.wf, hv.cells, hv.fiberClosed, hv.heapClosed, hv.promiseClosed, hv.tokenClosed,
    hv.root⟩, ⟨hok.c0, hok.c1, hok.c2⟩, hpark⟩

theorem m6_middleware (root : ProgramSource) (rootTy : EffTy) (w : Typed.World) (m : RState)
    (h : TypedState root rootTy w m) :
    TypedState root rootTy w { m with middlewareInstalled := true } := by
  obtain ⟨hv, hok, hpark⟩ := h
  exact ⟨⟨hv.ids, hv.fibers, hv.heap, hv.promises, hv.tokens, hv.tokenBound, hv.tokenTargets,
    hv.state, hv.wf, hv.cells, hv.fiberClosed, hv.heapClosed, hv.promiseClosed, hv.tokenClosed,
    hv.root⟩, ⟨hok.c0, hok.c1, hok.c2⟩, hpark⟩

/-- The facts a decision needs outside the command loop, for M6. Eight edits; two are proved
above (`m6_ran`, `m6_middleware`), six remain. With the 18 per-command obligations they replace
`decision_preserves`. The store edits (`clockNone`, `clockSome`, `answer`) may move to a later
world, because the world follows the store (`WorldValid.state`). The answer fact needs its
typing only when the fiber is parked at that token, which is what `AnswerOk` gives. -/
structure M6Edits (root : ProgramSource) (rootTy : EffTy) : Prop where
  drain : ∀ w (m : RState) owner f, TypedState root rootTy w m → m.fiber? owner = some f →
    TypedState root rootTy w ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      QueueOk root w ((f.dispatcher.drain).1.flatMap taskCmds)
  yield : ∀ w (m : RState) id (v : Bool), TypedState root rootTy w m →
    TypedState root rootTy w (m.modify id fun f => { f with yieldOverride := some v })
  interrupt : ∀ w (m : RState) who extra target t, TypedState root rootTy w m →
    m.fiber? target = some t →
    TypedState root rootTy w (interruptEdit (interpR root.program) m who extra target t)
  clockNone : ∀ w (m : RState) millis st, TypedState root rootTy w m → m.stuck = none →
    (interpR root.program).clockStep millis m.state = (none, st) →
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' { m with state := st }
  clockSome : ∀ w (m : RState) millis owed st, TypedState root rootTy w m → m.stuck = none →
    (interpR root.program).clockStep millis m.state = (some owed, st) →
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' (drainOwed { m with state := st } [owed]).1 ∧
      QueueOk root w' (drainOwed { m with state := st } [owed]).2
  answer : ∀ w (m : RState) id token answer, TypedState root rootTy w m → m.stuck = none →
    AnswerOk w m (.answerAsync id token answer) →
    ∃ w', w.leHost w' ∧
      TypedState root rootTy w' { m with state := (prepareAsyncAnswer (interpR root.program) m id token answer).1 } ∧
      (ParkedAt m id token →
        Contracts.ResumeOk (TypedProg root) w' id token
          (prepareAsyncAnswer (interpR root.program) m id token answer).2)

theorem queueOk_drainDue (root : ProgramSource) (w : Typed.World) :
    QueueOk root w [Cmd.drainDue] := by
  intro c hc
  rw [List.mem_singleton] at hc
  subst hc
  trivial

theorem queueOk_evaluate (root : ProgramSource) (w : Typed.World) (id : FiberId) :
    QueueOk root w [Cmd.evaluate id, Cmd.drainDue] := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl <;> trivial

theorem queueOk_resume (root : ProgramSource) (w : Typed.World) (id : FiberId) (token : Nat)
    (code : RProgram) (h : Contracts.ResumeOk (TypedProg root) w id token code) :
    QueueOk root w [Cmd.resume id token code, Cmd.drainDue] := by
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · exact h
  · trivial

theorem m6O_nil (root : ProgramSource) (w : Typed.World) (m : RState) : m6O root w m [] := by
  intro c hc
  simp only [List.flatMap_nil, List.not_mem_nil] at hc

/-- M6's premise bundle for the decision lift. -/
theorem m6_decisionLift (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ cmd, StepPreserves root rootTy cmd) (edits : M6Edits root rootTy) :
    letI := termEvaluatorFor root.program
    DecisionLift hostOrder (interpR root.program) (TypedState root rootTy) (m6I root rootTy)
      (m6O root) (fun w m d => AnswerOk w m d) := by
  letI := termEvaluatorFor root.program
  refine
    { step := m6_stepFrame root rootTy steps
      nil := m6O_nil root
      evaluate := fun w m id ht _ => ⟨ht, queueOk_evaluate root w id⟩
      drain := fun w m owner f ht hf => edits.drain w m owner f ht hf
      ran := fun w m owner t ht => m6_ran root rootTy w m owner t ht
      task := fun w m owner t ts ht _ ho => by
        have ho' : QueueOk root w (taskCmds t ++ ts.flatMap taskCmds) := by
          simpa only [m6O, List.flatMap_cons] using ho
        obtain ⟨h₁, h₂⟩ := (queueOk_append root w _ _).mp ho'
        exact ⟨⟨m6_ran root rootTy w m owner t ht, h₁⟩, h₂⟩
      skip := fun w m t ts ho => by
        have ho' : QueueOk root w (taskCmds t ++ ts.flatMap taskCmds) := by
          simpa only [m6O, List.flatMap_cons] using ho
        exact ((queueOk_append root w _ _).mp ho').2
      yield := fun w m id v ht => edits.yield w m id v ht
      interrupt := fun w m who extra target t ht hf => edits.interrupt w m who extra target t ht hf
      middleware := fun w m ht => m6_middleware root rootTy w m ht
      clockNone := fun w m millis st ht hs hc => edits.clockNone w m millis st ht hs hc
      clockSome := fun w m millis owed st ht hs hc => by
        obtain ⟨w', le, ht', hq'⟩ := edits.clockSome w m millis owed st ht hs hc
        exact ⟨w', le, ht', fun _ =>
          ⟨ht', (queueOk_append root w' _ _).mpr ⟨hq', queueOk_drainDue root w'⟩⟩⟩
      answer := fun w m id token answer ht hs ha => by
        obtain ⟨w', le, ht', hres⟩ := edits.answer w m id token answer ht hs ha
        exact answer_of_split (m6_stepFrame root rootTy steps []) (m6O_nil root)
          w m id token answer hs
          ⟨w', le, ht', fun hp => ⟨ht', queueOk_resume root w' id token _ (hres hp)⟩,
            fun _ => ⟨ht', queueOk_drainDue root w'⟩⟩ }

/-- `decision_preserves`'s statement, copied from `Typed/Assembly.lean:218-222`. -/
def DecisionPreservesStmt (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) : Prop :=
  ∀ w m, TypedState root rootTy w m → AnswerOk w m d →
    ∃ w', w.leHost w' ∧ TypedState root rootTy w'
      (letI := termEvaluatorFor root.program
       stepDecisionState (interpR root.program) fuel m d).1

/-- The obligation's statement is this one, by definition (checked by the kernel). -/
example (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    ProofGraph.Obligation (DecisionPreservesStmt root rootTy fuel d) :=
  M6Ledger.decision_preserves root rootTy fuel d

/-- **`decision_preserves` is an instance of the decision lift**: it follows from the 18
per-command obligations and the eight edit facts. -/
theorem m6_decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (d : Api.Decision) (steps : ∀ cmd, StepPreserves root rootTy cmd)
    (edits : M6Edits root rootTy) : DecisionPreservesStmt root rootTy fuel d := by
  intro w m ht ha
  letI := termEvaluatorFor root.program
  exact stepDecisionState_lift (m6_decisionLift root rootTy steps edits) fuel w m d ht ha

/-! ### The M6 repair: count only runs that apply no host answer -/

/-- The decision that carries a host answer. -/
def isAnswer : Api.Decision → Bool
  | .answerAsync _ _ _ => true
  | _ => false

/-- Reachability over tapes with no host answer (host-answers note §4). -/
def RReachableNoAnswer (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, (∀ d ∈ tape, isAnswer d = false) ∧ m = (replayR root.program fuel tape).machine

theorem rreachableNoAnswer_rreachable (root : ProgramSource) (fuel : Nat) (m : RState)
    (h : RReachableNoAnswer root fuel m) : RReachable root fuel m :=
  let ⟨tape, _, hm⟩ := h
  ⟨tape, hm⟩

/-- `AnswerOk` imposes nothing on a decision that is not an answer. -/
theorem answerOk_of_not_answer (w : Typed.World) (m : RState) :
    ∀ d, isAnswer d = false → AnswerOk w m d
  | .answerAsync _ _ _, h => by cases h
  | .fire _, _ => trivial
  | .flush, _ => trivial
  | .evaluate _, _ => trivial
  | .yieldVerdict _ _, _ => trivial
  | .interruptFrom _ _ _, _ => trivial
  | .installMiddleware, _ => trivial
  | .advance _, _ => trivial

/-- `typedState_load`'s statement, copied from `Typed/Assembly.lean:148-150`. -/
def LoadStmt (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) : Prop :=
  Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel)

example (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (LoadStmt root rootTy fuel compileFuel) :=
  M3bAssembly.typedState_load root rootTy fuel compileFuel

/-- A tape whose decisions all meet a world-free admission is admitted along any replay. -/
theorem admittedReplay_of_forall {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ] [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
    {W : Type w} (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (P : RunDecision ν σ β ε δ ι α → Prop) (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      (∀ d ∈ tape, P d) → AdmittedReplay J (fun _ _ d => P d) interp fuel m tape
  | [], _, _ => trivial
  | d :: tape, _, h => fun _ =>
    ⟨fun _ _ => h d (List.mem_cons_self ..),
      fun _ => admittedReplay_of_forall J P interp fuel tape _
        (fun d' hd' => h d' (List.mem_cons_of_mem d hd'))⟩

/-- The repaired capstone's statement: `typedState_reachable` with answer-free reachability. -/
def CapstoneRepaired (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    RReachableNoAnswer root fuel m → ∃ w, TypedState root rootTy w m

/-- **The repaired capstone, derived.** From `typedState_load` at `compileFuel := fuel` (what
`replayR` loads with, `RuntimeR.lean:51-54`) and `decision_preserves` for decisions that are
not answers, by the replay lift. Every hypothesis is explicit. -/
theorem m6_capstone (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (load : LoadStmt root rootTy fuel fuel)
    (dec : ∀ d, isAnswer d = false → DecisionPreservesStmt root rootTy fuel d) (m : RState) :
    CapstoneRepaired root rootTy fuel m := by
  intro hty hclosed hreach
  obtain ⟨tape, hna, hm⟩ := hreach
  obtain ⟨w₀, h₀⟩ := load hty hclosed
  letI := termEvaluatorFor root.program
  obtain ⟨w, _, hw⟩ := replayEval_lift hostOrder (fun w m => TypedState root rootTy w m)
    (fun _ _ d => isAnswer d = false) (interpR root.program) fuel
    (fun w m d _ ht hn => dec d hn w m ht (answerOk_of_not_answer w m d hn))
    tape w₀ (loadR root.program fuel fuel) h₀
    (admittedReplay_of_forall _ (fun d => isAnswer d = false) (interpR root.program) fuel tape _ hna)
  subst hm
  exact ⟨w, hw⟩

/-- The capstone from the whole ledger: `typedState_load`, the 18 per-command obligations and
the eight edit facts. -/
theorem m6_capstone_of_steps (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (load : LoadStmt root rootTy fuel fuel) (steps : ∀ cmd, StepPreserves root rootTy cmd)
    (edits : M6Edits root rootTy) (m : RState) : CapstoneRepaired root rootTy fuel m :=
  m6_capstone root rootTy fuel load
    (fun d _ => m6_decision_preserves root rootTy fuel d steps edits) m


/-- The capstone from the ledger's `decision_preserves`, quantified over every decision as the
ledger states it. -/
theorem m6_capstone_of_ledger (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (load : LoadStmt root rootTy fuel fuel)
    (dec : ∀ d, DecisionPreservesStmt root rootTy fuel d) (m : RState) :
    CapstoneRepaired root rootTy fuel m :=
  m6_capstone root rootTy fuel load (fun d _ => dec d) m

/-- **Lift 3 at the reference machine** (`RReachable`'s replay, `Typed/Assembly.lean:75-76`):
an invariant of the loaded term machine that every admitted decision keeps holds on the machine
of every admitted tape. -/
theorem rreachable_lift {W : Type w} (root : ProgramSource) (fuel : Nat) (o : WorldOrder W)
    (J : W → RState → Prop) (A : W → RState → Api.Decision → Prop)
    (load : ∃ w, J w (loadR root.program fuel fuel))
    (pres : ∀ w m d, m.stuck = none → J w m → A w m d →
      ∃ w', o.le w w' ∧ J w'
        (letI := termEvaluatorFor root.program
         stepDecisionState (interpR root.program) fuel m d).1)
    (tape : List Api.Decision)
    (adm : letI := termEvaluatorFor root.program
      AdmittedReplay J A (interpR root.program) fuel (loadR root.program fuel fuel) tape) :
    ∃ w, J w (replayR root.program fuel tape).machine := by
  obtain ⟨w₀, h₀⟩ := load
  letI := termEvaluatorFor root.program
  obtain ⟨w, _, hw⟩ := replayEval_lift o J A (interpR root.program) fuel pres tape w₀ _ h₀ adm
  exact ⟨w, hw⟩


/-- Admission is monotone in the admission predicate. -/
theorem admittedReplay_mono {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ] [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
    {W : Type w} (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (A A' : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop)
    (h : ∀ w m d, A w m d → A' w m d) (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) :
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      AdmittedReplay J A interp fuel m tape → AdmittedReplay J A' interp fuel m tape
  | [], _, _ => trivial
  | _ :: tape, _, adm => fun hs =>
    ⟨fun w hj => h _ _ _ ((adm hs).1 w hj),
      fun hr => admittedReplay_mono J A A' h interp fuel tape _ ((adm hs).2 hr)⟩

/-- The typed layer's reachability: every host answer a tape applies meets `AnswerOk` at the
machine it meets, in every world that types that machine. -/
def RReachableAdmitted (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, (letI := termEvaluatorFor root.program
    AdmittedReplay (TypedState root rootTy) (fun w m d => AnswerOk w m d) (interpR root.program)
      fuel (loadR root.program fuel fuel) tape) ∧
    m = (replayR root.program fuel tape).machine

/-- The no-answer repair is the special case: a tape with no answer is admitted. -/
theorem noAnswer_admitted (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState)
    (h : RReachableNoAnswer root fuel m) : RReachableAdmitted root rootTy fuel m := by
  obtain ⟨tape, hna, hm⟩ := h
  letI := termEvaluatorFor root.program
  exact ⟨tape, admittedReplay_mono _ _ _ (fun w m d hd => answerOk_of_not_answer w m d hd) _ fuel
    tape _ (admittedReplay_of_forall _ (fun d => isAnswer d = false) _ fuel tape _ hna), hm⟩

/-- **The typed-layer capstone**: with `decision_preserves` as the ledger states it (every
decision, under `AnswerOk`), every machine an admitted tape reaches is typed. -/
theorem m6_capstone_admitted (root : ProgramSource) (rootTy : EffTy) (fuel : Nat)
    (load : LoadStmt root rootTy fuel fuel)
    (dec : ∀ d, DecisionPreservesStmt root rootTy fuel d) (m : RState)
    (hty : Api.typeOf root.program root.table = some rootTy) (hclosed : ClosedEff rootTy)
    (hreach : RReachableAdmitted root rootTy fuel m) : ∃ w, TypedState root rootTy w m := by
  obtain ⟨tape, adm, hm⟩ := hreach
  obtain ⟨w₀, h₀⟩ := load hty hclosed
  letI := termEvaluatorFor root.program
  obtain ⟨w, _, hw⟩ := replayEval_lift hostOrder (fun w m => TypedState root rootTy w m)
    (fun w m d => AnswerOk w m d) (interpR root.program) fuel
    (fun w m d _ ht ha => dec d w m ht ha) tape w₀ (loadR root.program fuel fuel) h₀ adm
  subst hm
  exact ⟨w, hw⟩

/-- Red control, tied to this file's predicate: the plan review's refuting tape
(`Controls.lean` C4) applies a host answer, so the repaired reachability does not count it. -/
theorem reviewTape_refused :
    ¬ ∀ d ∈ ([Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (.nat 42)))] :
      List Api.Decision), isAnswer d = false := by
  decide

/-- An answer-free tape is admitted. -/
theorem evaluateTape_admitted : ∀ d ∈ ([Api.evaluate] : List Api.Decision), isAnswer d = false := by
  decide

end M6

/-! ## Lift 3 at the native machine: `Guard.Reachable` -/

section NativeHistory

open Effect4.Program Effect4.Program.Guard

variable {W : Type w}

/-- **The history lift over the native reachability** (`Guard/Core.lean:31-34`): an invariant
of the loaded machine that every admitted decision keeps holds on every admitted prefix. -/
theorem reachable_lift (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (o : WorldOrder W)
    (J : W → NativeMachine → Prop) (A : W → NativeMachine → Nat × NativeDecision → Prop)
    (load : ∃ w, J w (Api.load p compileFuel answers))
    (pres : ∀ w m fuel d, J w m → A w m (fuel, d) →
      ∃ w', o.le w w' ∧ J w' (steppedBy p fuel table m d))
    (history : Prefix)
    (adm : Admitted J A (fun m s => steppedBy p s.1 table m s.2) (Api.load p compileFuel answers)
      history) :
    ∃ w, J w (executePrefix p table (Api.load p compileFuel answers) history) := by
  obtain ⟨w₀, h₀⟩ := load
  obtain ⟨w, _, hw⟩ := foldl_lift o J A (fun m s => steppedBy p s.1 table m s.2)
    (fun w m s hj ha => pres w m s.1 s.2 hj ha) history w₀ _ h₀ adm
  exact ⟨w, hw⟩

/-- The machine-only form, with no admission: every reachable machine keeps the fact. -/
theorem reachable_lift_unit (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (J : NativeMachine → Prop)
    (load : J (Api.load p compileFuel answers))
    (pres : ∀ m fuel d, J m → J (steppedBy p fuel table m d)) (m : NativeMachine)
    (reachable : Reachable p table compileFuel answers m) : J m := by
  obtain ⟨history, rfl⟩ := reachable
  obtain ⟨_, hw⟩ := reachable_lift p table compileFuel answers unitOrder (fun _ m => J m)
    (fun _ _ _ => True) ⟨(), load⟩ (fun _ m fuel d hj _ => ⟨(), trivial, pres m fuel d hj⟩)
    history (admitted_true _ _ history _)
  exact hw

end NativeHistory

/-! ## Instance 3: the fork-ledger trace agreement, a `Keeps` -/

section Trace

open Effect4.Api.TraceFacts

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-- The plan's agreement `forkedOf m.trace = forkLedger m`, for any ledger projection
(origin-ledger plan §5, user 1). -/
def LedgerAgrees (ledger : RunMachine ν σ β ε δ ι α χ St κ φ η → List (FiberId × FiberId × Bool))
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop :=
  forkedOf m.trace = ledger m

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
/-- Today's `Agrees` is the agreement at the fiber-origin projection. -/
theorem ledgerAgrees_originForks (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    LedgerAgrees originForks m = Agrees m := rfl

/-- **Loop level.** A `Keeps` of the agreement per command is a `Keeps` of the loop. -/
theorem ledger_driveState (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (ledger : RunMachine ν σ β ε δ ι α χ St κ φ η → List (FiberId × FiberId × Bool))
    (step : ∀ c rest, Keeps (LedgerAgrees ledger) (fun m => (driveStep interp m c rest).1))
    (fuel : Nat) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    Keeps (LedgerAgrees ledger) (fun m => (driveState interp fuel m cmds).1) :=
  driveState_keeps_of_keeps interp _ step fuel cmds

/-- The edits outside the loop, each keeping a machine fact `P` (for the ledger user,
`P := LedgerAgrees forkLedger`). -/
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

/-- The ledger user at decision level: per-command `Keeps` of the agreement and the eight
edit facts give the agreement after every decision. -/
theorem ledger_stepDecision (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (ledger : RunMachine ν σ β ε δ ι α χ St κ φ η → List (FiberId × FiberId × Bool))
    (step : ∀ c rest, Keeps (LedgerAgrees ledger) (fun m => (driveStep interp m c rest).1))
    (edits : MachineEdits interp (LedgerAgrees ledger)) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (d : RunDecision ν σ β ε δ ι α)
    (h : LedgerAgrees ledger m) : LedgerAgrees ledger (stepDecisionState interp fuel m d).1 :=
  machineFact_stepDecision interp _ (fun m c rest _ hp => (step c rest m).mpr hp) edits fuel m d h


omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
/-- A `ranTask` event is not a fork event, and `emit` leaves the fibers alone. -/
theorem agrees_ran (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId)
    (t : Machine.Task ν σ β ε δ ι α κ) (h : Agrees m) :
    Agrees (m.emit [RunEvent.ranTask owner t]) := by
  show forkedOf (m.trace ++ [RunEvent.ranTask owner t]) = originForks m
  rw [Effect4.Api.forkedOf_append]
  show forkedOf m.trace ++ [] = originForks m
  rw [List.append_nil]
  exact h

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem agrees_state (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (s : St) (h : Agrees m) :
    Agrees { m with state := s } := h

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] core
  [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem agrees_middleware (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (h : Agrees m) :
    Agrees { m with middlewareInstalled := true } := h

/-- With today's origin field, the edits left to prove are exactly the four that rewrite a fiber
through `update`: they keep the agreement only while fiber ids are distinct (`Controls.lean`
C3). With the ledger off the fiber, `update` cannot reach the record. -/
structure AgreesUpdates (interp : RunInterp ν σ β ε δ ι α χ St κ) : Prop where
  drain : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owner f, Agrees m → m.fiber? owner = some f →
    Agrees ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
  yield : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) id (v : Bool), Agrees m →
    Agrees (m.modify id fun f => { f with yieldOverride := some v })
  interrupt : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) who extra target t, Agrees m →
    m.fiber? target = some t → Agrees (interruptEdit interp m who extra target t)
  owed : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) owed, Agrees m → Agrees (drainOwed m [owed]).1

omit [FiberEvaluator ν σ β ε δ ι α χ St κ φ η] in
theorem agrees_edits (interp : RunInterp ν σ β ε δ ι α χ St κ) (u : AgreesUpdates (η := η) interp) :
    MachineEdits interp (fun m : RunMachine ν σ β ε δ ι α χ St κ φ η => Agrees m) :=
  { drain := u.drain
    ran := fun m owner t h => agrees_ran m owner t h
    yield := u.yield
    interrupt := u.interrupt
    middleware := fun m h => agrees_middleware m h
    clock := fun m _ h _ => agrees_state m _ h
    owed := u.owed
    prepare := fun m _ _ _ h => agrees_state m _ h }

end Trace

section TraceNative

open Effect4.Program Effect4.Program.Guard Effect4.Api.TraceFacts

/-- **History level, today's obligations.** `M1Trace.reachable_agrees` follows from
`load_agrees` and `step_agrees` (whose reachability premise rides in the invariant). -/
theorem reachable_agrees_of (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann))
    (load : Agrees (Api.load program compileFuel answers))
    (step : ∀ m, Reachable program table compileFuel answers m → Agrees m →
      ∀ fuel decision, Agrees (steppedBy program fuel table m decision))
    (m : NativeMachine) (reachable : Reachable program table compileFuel answers m) :
    forkedOf m.trace = originForks m :=
  (reachable_lift_unit program table compileFuel answers
    (fun m => Reachable program table compileFuel answers m ∧ Agrees m)
    ⟨reachable_load program table compileFuel answers, load⟩
    (fun m fuel d h => ⟨reachable_step h.1 fuel d, step m h.1 h.2 fuel d⟩) m reachable).2

/-- The obligations' statements are these (checked by the kernel). -/
example (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (reachable : Reachable program table compileFuel answers m) (agrees : Agrees m)
    (fuel : Nat) (decision : NativeDecision) :
    ProofGraph.Obligation (Agrees (steppedBy program fuel table m decision)) :=
  Effect4.Api.TraceFacts.M1Trace.step_agrees program table compileFuel answers m reachable agrees
    fuel decision

example (program : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (reachable : Reachable program table compileFuel answers m) :
    ProofGraph.Obligation (forkedOf m.trace = originForks m) :=
  Effect4.Api.TraceFacts.M1Trace.reachable_agrees program table compileFuel answers m reachable

end TraceNative

/-! ## Instance 1, decision and history level: the guard's `guardState_steppedBy` -/

section GuardDecision

open Effect4.Program Effect4.Program.Guard Effect4.Program.Guard.RegistrationQueue
open Effect4.Program.Guard.OuterDriver

/-- The guard's snapshot fact, as its fire fold carries it (`OuterDriver.lean:95-110`): the
drained tasks' keys stay reserved, and they carry no race site. -/
def guardO (m : NativeMachine) (ts : List NTask) : Prop :=
  ReservedKeys m (ts.flatMap taskKeys) ∧ ∀ t ∈ ts, taskRaceSites t = []

/-- The guard's premise bundle, every field from a lemma the guard already has. -/
theorem guard_decisionLift (p : NativeEff) (table : RowTable) :
    letI := evaluatorFor p table
    DecisionLift unitOrder (interpOf p table) (fun _ m => GuardState m)
      (fun _ m cmds => guardI p table m cmds) (fun _ m ts => guardO m ts) (fun _ _ _ => True) := by
  letI := evaluatorFor p table
  exact
    { step := fun ts _ m c rest hs h => by
        obtain ⟨⟨st, q, r⟩, keys, sites⟩ := h.2 hs
        have next := driveStep_invariants p table m c rest st q r
        exact ⟨(), trivial, next.1, fun _ =>
          ⟨next, reservedKeys_driveStep p table m c rest st q _ keys, sites⟩⟩
      nil := fun _ m => ⟨reservedKeys_nil m, fun t ht => by cases ht⟩
      evaluate := fun _ m id st _ =>
        ⟨st, LocalDecision.guardQueue_evaluate_drainDue p table m id,
          ⟨True.intro, True.intro, True.intro⟩⟩
      drain := fun _ m owner f st hf => by
        have lookup : m.fiber? f.id = some f := by
          simpa only [fiber_id_of_lookup hf] using hf
        have clear := clearDispatcher_preserved st f lookup
        have before := clear.trans (Preserved.disarm clear.state owner)
        have member := List.mem_of_find?_eq_some hf
        have keys := reservedKeys_subset (reservedKeys_fiber (f := f) st member) (dispatcher_keys f)
        exact ⟨before.state, before.reserved _ keys, dispatcher_sites st f member⟩
      ran := fun _ m owner t st => guardState_emit st _
      task := fun _ m owner t ts st _ ho => by
        obtain ⟨keys, sites⟩ := ho
        have em := Preserved.emit st [RunEvent.ranTask owner t]
        have keysT : ReservedKeys m (taskKeys t) := reservedKeys_subset keys (List.subset_append_left ..)
        have keysTs : ReservedKeys m (ts.flatMap taskKeys) :=
          reservedKeys_subset keys (List.subset_append_right ..)
        exact ⟨⟨em.state, taskCmds_guardQueue p table _ t (em.reserved _ keysT)
            (sites t (List.mem_cons_self ..)), taskCmds_registration t⟩,
          em.reserved _ keysTs, fun t' ht' => sites t' (List.mem_cons_of_mem _ ht')⟩
      skip := fun _ m t ts ho =>
        ⟨reservedKeys_subset ho.1 (List.subset_append_right ..),
          fun t' ht' => ho.2 t' (List.mem_cons_of_mem _ ht')⟩
      yield := fun _ m id v st => LocalDecision.guardState_yieldVerdict p table 0 m id v st
      interrupt := fun _ m who extra target t st ht => by
        have saved : m.fiber? t.id = some t := by simpa only [fiber_id_of_lookup ht] using ht
        exact LocalDecision.guardState_interruptBeforeLoop p table m target t who extra st saved
      middleware := fun _ m st => LocalDecision.guardState_installMiddleware p table 0 m st
      clockNone := fun _ m millis st' st _ hc => by
        have h := (clockStep_preserved p table m millis st).state
        rw [hc] at h
        exact ⟨(), trivial, h⟩
      clockSome := fun _ m millis owed st' st _ hc => by
        have facts := clockStep_owed_facts p table m millis owed (by rw [hc])
        have changed := clockStep_preserved p table m millis st
        rw [hc] at changed
        have oldKeys : ReservedKeys m (taskKeys (.resume owed.waiter owed.token owed.code)) := by
          apply reservedKeys_subset (reservedKeys_internal m st)
          intro key hk
          have eq := List.mem_singleton.mp hk
          exact eq ▸ facts.1
        have hd : drainOwed { m with state := st' } [owed] =
            ({ m with state := st' }, [Cmd.resume owed.waiter owed.token owed.code]) := by
          simp only [drainOwed, facts.2.2]
        rw [hd]
        exact ⟨(), trivial, changed.state, fun _ => ⟨changed.state,
          taskCmds_guardQueue p table _ (.resume owed.waiter owed.token owed.code)
            (changed.reserved _ oldKeys) facts.2.1,
          taskCmds_registration (.resume owed.waiter owed.token owed.code)⟩⟩
      answer := fun _ m id token answer st _ _ => by
        have st' := AnswerDecision.guardState_prepareAsyncAnswer p table m id token answer st
        have sites := (AnswerDecision.prepareAsyncAnswer_shape p table m id token answer).2.2
        have next := guardState_driveStep_resume p table
          { m with state := (prepareAsyncAnswer (interpOf p table) m id token answer).1 } id token
          (prepareAsyncAnswer (interpOf p table) m id token answer).2 [Cmd.drainDue] st' sites
        have q := AnswerDecision.guardQueue_resume_from_tail p table
          { m with state := (prepareAsyncAnswer (interpOf p table) m id token answer).1 } id token
          (prepareAsyncAnswer (interpOf p table) m id token answer).2 [Cmd.drainDue] st'
          (AnswerDecision.guardQueue_drainDue p table _)
        have r := AnswerDecision.registrationQueue_resume_result p table
          { m with state := (prepareAsyncAnswer (interpOf p table) m id token answer).1 } id token
          (prepareAsyncAnswer (interpOf p table) m id token answer).2 [Cmd.drainDue]
          ⟨True.intro, True.intro⟩
        exact ⟨(), trivial, next, fun _ => ⟨⟨next, q, r⟩, reservedKeys_nil _, fun t ht => by cases ht⟩⟩ }

/-- `guardState_steppedBy` (`Guard/Decision.lean:11-34`), from the decision lift. -/
theorem guardState_steppedBy_of_lift (p : NativeEff) (table : RowTable) (fuel : Nat)
    (m : NativeMachine) (d : NativeDecision) (state : GuardState m) :
    GuardState (steppedBy p fuel table m d) := by
  letI := evaluatorFor p table
  obtain ⟨_, _, h⟩ := stepDecisionState_lift (guard_decisionLift p table) fuel () m d state trivial
  exact h

/-- `guardState_reachable` (`Guard/Decision.lean:74-79`), from the history lift. -/
theorem guardState_reachable_of_lift (p : NativeEff) (table : RowTable) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (m : NativeMachine)
    (reachable : Reachable p table compileFuel answers m) : GuardState m :=
  reachable_lift_unit p table compileFuel answers GuardState (guardState_load p compileFuel answers)
    (fun m fuel d st => guardState_steppedBy_of_lift p table fuel m d st) m reachable

end GuardDecision

end Research.Pass.Lift

#print axioms Research.Pass.Lift.stuck_none_of_not
#print axioms Research.Pass.Lift.driveState_lift
#print axioms Research.Pass.Lift.driveState_lift_of
#print axioms Research.Pass.Lift.driveState_lift_unit
#print axioms Research.Pass.Lift.driveState_keeps
#print axioms Research.Pass.Lift.driveState_keeps_of_keeps
#print axioms Research.Pass.Lift.stepKeeps_of_keeps
#print axioms Research.Pass.Lift.settle_append
#print axioms Research.Pass.Lift.framed_append
#print axioms Research.Pass.Lift.driveStep_append
#print axioms Research.Pass.Lift.not_isSome_of_none
#print axioms Research.Pass.Lift.isSome_of_ne_none
#print axioms Research.Pass.Lift.parkedAt_em
#print axioms Research.Pass.Lift.inert_resume
#print axioms Research.Pass.Lift.interruptFrom_eq
#print axioms Research.Pass.Lift.answer_of_split
#print axioms Research.Pass.Lift.loop_lift
#print axioms Research.Pass.Lift.loop_entry
#print axioms Research.Pass.Lift.fireFold_lift
#print axioms Research.Pass.Lift.fireState_lift
#print axioms Research.Pass.Lift.flushAllState_lift
#print axioms Research.Pass.Lift.advanceState_lift
#print axioms Research.Pass.Lift.stepDecisionState_lift
#print axioms Research.Pass.Lift.foldl_lift
#print axioms Research.Pass.Lift.admitted_true
#print axioms Research.Pass.Lift.replayEval_nil_machine
#print axioms Research.Pass.Lift.replayEval_lift
#print axioms Research.Pass.Lift.guard_invariant
#print axioms Research.Pass.Lift.guard_reserved
#print axioms Research.Pass.Lift.guard_interrupted
#print axioms Research.Pass.Lift.guard_request
#print axioms Research.Pass.Lift.driverContract_of_lift
#print axioms Research.Pass.Lift.queueOk_append
#print axioms Research.Pass.Lift.m6_stepKeeps
#print axioms Research.Pass.Lift.m6_steps_of_ledger
#print axioms Research.Pass.Lift.m6_driveState
#print axioms Research.Pass.Lift.m6_stepFrame
#print axioms Research.Pass.Lift.queueOk_drainDue
#print axioms Research.Pass.Lift.queueOk_evaluate
#print axioms Research.Pass.Lift.queueOk_resume
#print axioms Research.Pass.Lift.m6O_nil
#print axioms Research.Pass.Lift.m6_ran
#print axioms Research.Pass.Lift.m6_middleware
#print axioms Research.Pass.Lift.m6_decisionLift
#print axioms Research.Pass.Lift.m6_decision_preserves
#print axioms Research.Pass.Lift.rreachableNoAnswer_rreachable
#print axioms Research.Pass.Lift.answerOk_of_not_answer
#print axioms Research.Pass.Lift.admittedReplay_of_forall
#print axioms Research.Pass.Lift.m6_capstone
#print axioms Research.Pass.Lift.m6_capstone_of_steps
#print axioms Research.Pass.Lift.m6_capstone_of_ledger
#print axioms Research.Pass.Lift.rreachable_lift
#print axioms Research.Pass.Lift.admittedReplay_mono
#print axioms Research.Pass.Lift.noAnswer_admitted
#print axioms Research.Pass.Lift.m6_capstone_admitted
#print axioms Research.Pass.Lift.reviewTape_refused
#print axioms Research.Pass.Lift.evaluateTape_admitted
#print axioms Research.Pass.Lift.reachable_lift
#print axioms Research.Pass.Lift.reachable_lift_unit
#print axioms Research.Pass.Lift.ledgerAgrees_originForks
#print axioms Research.Pass.Lift.ledger_driveState
#print axioms Research.Pass.Lift.machineFact_stepDecision
#print axioms Research.Pass.Lift.ledger_stepDecision
#print axioms Research.Pass.Lift.agrees_ran
#print axioms Research.Pass.Lift.agrees_state
#print axioms Research.Pass.Lift.agrees_middleware
#print axioms Research.Pass.Lift.agrees_edits
#print axioms Research.Pass.Lift.reachable_agrees_of
#print axioms Research.Pass.Lift.guard_decisionLift
#print axioms Research.Pass.Lift.guardState_steppedBy_of_lift
#print axioms Research.Pass.Lift.guardState_reachable_of_lift
