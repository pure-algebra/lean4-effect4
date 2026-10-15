import Effect4.Laws.Machine.AnswerFlowGhostCommands

/-!
Concept: reactive-scheduling R9 and store-typing R4.
Consumer: Atomic and Timeout active coupled command producers.
Strict application assertions belong to the joint contextual premise and postcondition.
The existing command theorem carries a trivial auxiliary frame assertion.
This adapter supplies no application transition premise.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Machine
universe u v z x
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α)
  (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α)]
variable {V : Type z} {Context : Type x}

/-- One actual command transition retains its machine, queue and snapshot at the same proof world. -/
structure JointCommands (order : Effect4.Laws.Effects.WorldOrder V)
    (interp : RunInterp ν σ β ε δ ι α χ St)
    (Ready : V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop)
    (Premise : Context → V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α →
      List (Cmd ν σ β ε δ ι α) → Prop)
    (Post : Context → V → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) → Prop) : Prop where
  idle : ∀ context ghost m c rest, Premise context ghost m c rest → Ready ghost m c →
    Post context ghost m rest
  fixed : ∀ context ghost m c rest, Premise context ghost m c rest → Ready ghost m c →
    ghostAdvancing c = false →
    Post context ghost (driveStep interp m c rest).1 (driveStep interp m c rest).2
  iteration : ∀ context ghost m (f : RunFiber ν σ β ε δ ι α χ) y rest,
    Premise context ghost m (.loop f.id y) rest → Ready ghost m (.loop f.id y) →
    m.fiber? f.id = some f →
    ∃ next, order.le ghost next ∧
      Post context next (Machine.settle f.id rest (Machine.iteration interp m f y)).1
        (Machine.settle f.id rest (Machine.iteration interp m f y)).2
  deliver : ∀ context ghost m (f : RunFiber ν σ β ε δ ι α χ) y rest,
    Premise context ghost m (.deliver f.id y) rest → Ready ghost m (.deliver f.id y) →
    m.fiber? f.id = some f →
    ∃ next, order.le ghost next ∧
      Post context next (Machine.settle f.id rest (FiberEvaluator.evaluate interp m f y)).1
        (Machine.settle f.id rest (FiberEvaluator.evaluate interp m f y)).2
  entrant : ∀ context ghost m raceId (race : Race ν σ β ε δ ι α (Prim ν σ β ε δ ι α)) code more
    (host : RunFiber ν σ β ε δ ι α χ) rest,
    Premise context ghost m (.launch raceId) rest → Ready ghost m (.launch raceId) →
    m.race? raceId = some race → race.programs = code :: more →
    race.state.accepted.isSome = false → m.fiber? race.host = some host →
    ∃ next, order.le ghost next ∧
      Post context next (driveStep interp m (.launch raceId) rest).1
        (driveStep interp m (.launch raceId) rest).2

/-- The frame-only auxiliary assertion is vacuous; strict application facts remain contextual. -/
theorem Commands.trivial (interp : RunInterp ν σ β ε δ ι α χ St)
    (Ready : RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop) :
    Commands interp Ready (fun (_ : Unit) _ _ => True) (fun _ _ => ()) := by
  constructor
  all_goals intros
  all_goals aesop (rule_sets := [Effect4.Fibers]) (add norm simp [Flows, IterFlows])

variable {order : Effect4.Laws.Effects.WorldOrder V}
variable {interp : RunInterp ν σ β ε δ ι α χ St}
variable {Ready : V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop}
variable {Premise : Context → V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α →
  List (Cmd ν σ β ε δ ι α) → Prop}
variable {Post : Context → V → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) → Prop}

/-- Contextual application producers reuse the existing command census without a frame-only closure premise. -/
theorem JointCommands.toGhost (facts : JointCommands order interp Ready Premise Post) :
    GhostCommands order interp Ready (fun _ (_ : Unit) _ _ => True) (fun _ _ _ => ()) Premise Post where
  administrative ghost := Commands.trivial interp _
  idle context ghost m c rest premise ready _ := facts.idle context ghost m c rest premise ready
  fixed context ghost m c rest premise ready fixed _ := facts.fixed context ghost m c rest premise ready fixed
  iteration context ghost m fiber yielding rest premise ready _ found := by
    obtain ⟨next, moved, post⟩ := facts.iteration context ghost m fiber yielding rest premise ready found
    exact ⟨next, moved, ⟨fun _ _ => True.intro, True.intro⟩, post⟩
  deliver context ghost m fiber yielding rest premise ready _ found := by
    obtain ⟨next, moved, post⟩ := facts.deliver context ghost m fiber yielding rest premise ready found
    exact ⟨next, moved, ⟨fun _ _ => True.intro, True.intro⟩, post⟩
  entrant context ghost m raceId race code more host rest premise ready _ found programs accepted hostFound := by
    obtain ⟨next, moved, post⟩ := facts.entrant context ghost m raceId race code more host rest
      premise ready found programs accepted hostFound
    exact ⟨next, moved, (fun _ _ => True.intro), True.intro, post⟩

/-- The actual postcondition and world movement share one witness through the existing command theorem. -/
theorem JointCommands.step (facts : JointCommands order interp Ready Premise Post)
    (context : Context) (ghost : V) (machine : RunMachine ν σ β ε δ ι α χ St)
    (command : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α))
    (premise : Premise context ghost machine command rest) (ready : Ready ghost machine command) :
    ∃ next, order.le ghost next ∧ Post context next
      (driveStep interp machine command rest).1 (driveStep interp machine command rest).2 := by
  obtain ⟨next, moved, flowing, post⟩ := facts.toGhost.step context ghost machine command rest
    premise ready (fun _ _ => True.intro)
  exact ⟨next, moved, post⟩

end Effect4.Machine.AnswerFlow
