import Effect4.Laws.Machine.LiftMachineFact

/-!
Concepts: reactive-scheduling R9, store-typing R4, and scope-lifetime-finalization R11.
Question: the four application answer-flow goals need jointly retained frames and queued replies.
Consumers: the crews' saved-answer invariant and Timeout's numeric phase invariant.
Reach: the existing command driver and scheduler, with a separate proof world for the added fact.
The local command proof reads both old queue assertions and produces both new assertions.
This construction assumes no independently preserved answer-class queue.
It establishes no application predicate, progress, or host agreement by itself.
-/
set_option autoImplicit false
namespace Effect4.Machine.Lift
open Effect4 Effect4.Machine Effect4.Laws.Effects
universe u v w z
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [FiberEvaluator ν σ β ε δ ι α χ St κ φ η]
variable {W : Type w} {V : Type z}
variable {o : WorldOrder W} {p : WorldOrder V}
variable {interp : RunInterp ν σ β ε δ ι α χ St κ}
variable {J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
variable {I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}
variable {O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop}
variable {A : W → RunMachine ν σ β ε δ ι α χ St κ φ η → RunDecision ν σ β ε δ ι α → Prop}
variable {P : V → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop}
variable {Q : V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop}
variable {R : V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop}

/-- The base and added proof worlds advance together without identifying their data. -/
def pairOrder (o : WorldOrder W) (p : WorldOrder V) : WorldOrder (W × V) where
  le a b := o.le a.1 b.1 ∧ p.le a.2 b.2
  refl a := ⟨o.refl a.1, p.refl a.2⟩
  trans first second := ⟨o.trans first.1 second.1, p.trans first.2 second.2⟩

/-- An added scheduler fact may use the base's source and ownership facts.
Its pending-command and drained-task assertions advance jointly with its machine assertion. -/
structure CoupledFold (p : WorldOrder V) (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (J : W → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (I : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (O : W → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop)
    (P : V → RunMachine ν σ β ε δ ι α χ St κ φ η → Prop)
    (Q : V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (R : V → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Machine.Task ν σ β ε δ ι α κ) → Prop) : Prop where
  step : ∀ ts w v m c rest, m.stuck = none → Guarded J I O ts w m (c :: rest) →
    Guarded P Q R ts v m (c :: rest) → ∃ v', p.le v v' ∧
      Guarded P Q R ts v' (driveStep interp m c rest).1 (driveStep interp m c rest).2
  nil : ∀ v m, R v m []
  drain : ∀ w v m owner f, J w m → P v m → m.fiber? owner = some f →
    P v ((m.update {f with dispatcher := f.dispatcher.drain.2}).disarm owner) ∧
      R v ((m.update {f with dispatcher := f.dispatcher.drain.2}).disarm owner) f.dispatcher.drain.1
  ran : ∀ w v m owner task, J w m → P v m → P v (m.emit [.ranTask owner task])
  task : ∀ w v m owner task tasks, J w m → P v m → m.stuck = none →
    O w m (task :: tasks) → R v m (task :: tasks) →
    Q v (m.emit [.ranTask owner task]) (taskCmds task) ∧ R v (m.emit [.ranTask owner task]) tasks
  skip : ∀ v m task tasks, R v m (task :: tasks) → R v m tasks
  clockNone : ∀ w v m millis state, J w m → P v m → m.stuck = none →
    interp.clockStep millis m.state = (none, state) →
    ∃ v', p.le v v' ∧ P v' {m with state}
  clockSome : ∀ w v m millis owed state, J w m → P v m → m.stuck = none →
    interp.clockStep millis m.state = (some owed, state) →
    ∃ v', p.le v v' ∧ P v' (drainOwed {m with state} [owed]).1 ∧
      ((drainOwed {m with state} [owed]).1.stuck = none →
        Q v' (drainOwed {m with state} [owed]).1
          ((drainOwed {m with state} [owed]).2 ++ [.drainDue]))

/-- The joint local facts extend the existing scheduler lift, including each actual queue cut. -/
theorem FoldLift.withCoupledFact (base : FoldLift o interp J I O)
    (facts : CoupledFold p interp J I O P Q R) :
    FoldLift (pairOrder o p) interp
      (fun w m => J w.1 m ∧ P w.2 m)
      (fun w m commands => I w.1 m commands ∧ Q w.2 m commands)
      (fun w m tasks => O w.1 m tasks ∧ R w.2 m tasks) := by
  constructor
  · intro tasks world m command rest running held
    have old : Guarded J I O tasks world.1 m (command :: rest) :=
      ⟨held.1.1, fun live => ⟨(held.2 live).1.1, (held.2 live).2.1⟩⟩
    have extra : Guarded P Q R tasks world.2 m (command :: rest) :=
      ⟨held.1.2, fun live => ⟨(held.2 live).1.2, (held.2 live).2.2⟩⟩
    obtain ⟨next, advanced, kept⟩ := base.step tasks world.1 m command rest running old
    obtain ⟨later, moved, retained⟩ := facts.step tasks world.1 world.2 m command rest running old extra
    exact ⟨(next, later), ⟨advanced, moved⟩, ⟨kept.1, retained.1⟩,
      fun live => ⟨⟨(kept.2 live).1, (retained.2 live).1⟩,
        ⟨(kept.2 live).2, (retained.2 live).2⟩⟩⟩
  · intro world m
    exact ⟨base.nil world.1 m, facts.nil world.2 m⟩
  · intro world m owner fiber held found
    have kept := base.drain world.1 m owner fiber held.1 found
    have retained := facts.drain world.1 world.2 m owner fiber held.1 held.2 found
    exact ⟨⟨kept.1, retained.1⟩, kept.2, retained.2⟩
  · intro world m owner task held
    exact ⟨base.ran world.1 m owner task held.1,
      facts.ran world.1 world.2 m owner task held.1 held.2⟩
  · intro world m owner task tasks held running snapshot
    have kept := base.task world.1 m owner task tasks held.1 running snapshot.1
    have retained := facts.task world.1 world.2 m owner task tasks held.1 held.2 running snapshot.1 snapshot.2
    exact ⟨⟨kept.1, retained.1⟩, kept.2, retained.2⟩
  · intro world m task tasks snapshot
    exact ⟨base.skip world.1 m task tasks snapshot.1, facts.skip world.2 m task tasks snapshot.2⟩
  · intro world m millis state held running clock
    obtain ⟨next, advanced, kept⟩ := base.clockNone world.1 m millis state held.1 running clock
    obtain ⟨later, moved, retained⟩ := facts.clockNone world.1 world.2 m millis state held.1 held.2 running clock
    exact ⟨(next, later), ⟨advanced, moved⟩, kept, retained⟩
  · intro world m millis owed state held running clock
    obtain ⟨next, advanced, kept, queued⟩ := base.clockSome world.1 m millis owed state held.1 running clock
    obtain ⟨later, moved, retained, pending⟩ := facts.clockSome world.1 world.2 m millis owed state held.1 held.2 running clock
    exact ⟨(next, later), ⟨advanced, moved⟩, ⟨kept, retained⟩,
      fun live => ⟨queued live, pending live⟩⟩

/-- Decision entry adds its outside edits and the prepared first reply to the coupled fold. -/
structure CoupledDecision : Prop extends CoupledFold p interp J I O P Q R where
  evaluate : ∀ w v m id, J w m → P v m → m.stuck = none → Q v m [.evaluate id, .drainDue]
  yield : ∀ w v m id verdict, J w m → P v m →
    P v (m.modify id fun fiber => {fiber with yieldOverride := some verdict})
  interrupt : ∀ w v m who extra target fiber, J w m → P v m → m.fiber? target = some fiber →
    P v (interruptEdit interp m who extra target fiber)
  middleware : ∀ w v m, J w m → P v m → P v {m with middlewareInstalled := true}
  answer : ∀ w v m id token answer, J w m → P v m → m.stuck = none →
    A w m (.answerAsync id token answer) → ∃ v', p.le v v' ∧
      Guarded P Q R [] v'
        (driveStep interp {m with state := (prepareAsyncAnswer interp m id token answer).1}
          (.resume id token (prepareAsyncAnswer interp m id token answer).2) [.drainDue]).1
        (driveStep interp {m with state := (prepareAsyncAnswer interp m id token answer).1}
          (.resume id token (prepareAsyncAnswer interp m id token answer).2) [.drainDue]).2

/-- The existing decision producer carries the added machine and queue assertions jointly. -/
theorem DecisionLift.withCoupledFact (base : DecisionLift o interp J I O A)
    (facts : CoupledDecision (p := p) (interp := interp) (J := J) (I := I) (O := O)
      (A := A) (P := P) (Q := Q) (R := R)) :
    DecisionLift (pairOrder o p) interp
      (fun w m => J w.1 m ∧ P w.2 m)
      (fun w m commands => I w.1 m commands ∧ Q w.2 m commands)
      (fun w m tasks => O w.1 m tasks ∧ R w.2 m tasks)
      (fun w m decision => A w.1 m decision) := by
  have fold := (FoldLift.ofDecisionLift base).withCoupledFact facts.toCoupledFold
  refine {
    step := fold.step, nil := fold.nil, drain := fold.drain, ran := fold.ran,
    task := fold.task, skip := fold.skip, clockNone := fold.clockNone, clockSome := fold.clockSome,
    evaluate := ?_, yield := ?_, interrupt := ?_, middleware := ?_, answer := ?_ }
  · intro world m id held running
    exact ⟨base.evaluate world.1 m id held.1 running,
      facts.evaluate world.1 world.2 m id held.1 held.2 running⟩
  · intro world m id verdict held
    exact ⟨base.yield world.1 m id verdict held.1,
      facts.yield world.1 world.2 m id verdict held.1 held.2⟩
  · intro world m who extra target fiber held found
    exact ⟨base.interrupt world.1 m who extra target fiber held.1 found,
      facts.interrupt world.1 world.2 m who extra target fiber held.1 held.2 found⟩
  · intro world m held
    exact ⟨base.middleware world.1 m held.1, facts.middleware world.1 world.2 m held.1 held.2⟩
  · intro world m id token answer held running admitted
    obtain ⟨next, advanced, kept⟩ := base.answer world.1 m id token answer held.1 running admitted
    obtain ⟨later, moved, retained⟩ := facts.answer world.1 world.2 m id token answer held.1 held.2 running admitted
    exact ⟨(next, later), ⟨advanced, moved⟩, ⟨kept.1, retained.1⟩,
      fun live => ⟨⟨(kept.2 live).1, (retained.2 live).1⟩,
        ⟨(kept.2 live).2, (retained.2 live).2⟩⟩⟩
end Effect4.Machine.Lift
