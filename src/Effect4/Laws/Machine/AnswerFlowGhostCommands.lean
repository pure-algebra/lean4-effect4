import Effect4.Laws.Machine.AnswerFlowRun
import Effect4.Laws.Machine.LiftCoupledFact

/-!
Concepts: reactive-scheduling R9, store-typing R4, scope-lifetime-finalization R11 and reactive-scheduling R10.
Question: Atomic request stages and Timeout phases need a common external proof world.
Consumer: their coupled machine, queue and detached-task assertions.
Fixed-world commands use the existing command theorem.
Only evaluation and race entry choose a later proof world.
Each choice retains its flow and application postcondition together.
This adapter establishes no application phase or progress statement.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Machine
universe u v w z x
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable [FiberEvaluator ν σ β ε δ ι α χ St (Prim ν σ β ε δ ι α)
  (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α)]
variable {World : Type w} {V : Type z} {Context : Type x}
variable {interp : RunInterp ν σ β ε δ ι α χ St}
variable {Ready Ready' : RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop}
variable {G : World → FiberId → FrameFiber ν σ β ε δ ι α → Prop}
variable {worldOf : St → FiberId → World}

/-- A stronger command premise reuses every existing command producer. -/
theorem Commands.restrict (facts : Commands interp Ready G worldOf)
    (stronger : ∀ m c, Ready' m c → Ready m c) : Commands interp Ready' G worldOf where
  iteration m f y ready := facts.iteration m f y (stronger m _ ready)
  deliver m f y ready := facts.deliver m f y (stronger m _ ready)
  interruption := facts.interruption
  resume m id token code f ready := facts.resume m id token code f (stronger m _ ready)
  entrant m raceId race code more host ready := facts.entrant m raceId race code more host (stronger m _ ready)
  settleRace m raceId y race f exit ready := facts.settleRace m raceId y race f exit (stronger m _ ready)
  parkRace m raceId y race f ready := facts.parkRace m raceId y race f (stronger m _ ready)
  afterInterrupt m host y kind f ready := facts.afterInterrupt m host y kind f (stronger m _ ready)
  closePar m host y fibers f ready := facts.closePar m host y fibers f (stronger m _ ready)
  exitChildren m id exit f ready := facts.exitChildren m id exit f (stronger m _ ready)
  publish := facts.publish
  cleared := facts.cleared
  link := facts.link
  drop := facts.drop
  due := facts.due
  wake := facts.wake

/-- These existing commands can advance an application's external proof world. -/
def ghostAdvancing : Cmd ν σ β ε δ ι α → Bool
  | .loop _ _ | .deliver _ _ | .launch _ => true
  | _ => false

/-- The frame flow and the application postcondition share one returned proof world.
`Context` can retain the actual detached snapshot and the base driver's proof world.
`Premise` can read their joint machine and queue assertions.
`Post` can retain the new machine, queue and the same detached snapshot together. -/
structure GhostCommands (order : Effect4.Laws.Effects.WorldOrder V)
    (interp : RunInterp ν σ β ε δ ι α χ St)
    (Ready : V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop)
    (G : V → World → FiberId → FrameFiber ν σ β ε δ ι α → Prop)
    (worldOf : V → St → FiberId → World)
    (Premise : Context → V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α →
      List (Cmd ν σ β ε δ ι α) → Prop)
    (Post : Context → V → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) → Prop) : Prop where
  administrative : ∀ ghost, Commands interp
    (fun m c => Ready ghost m c ∧ ghostAdvancing c = false) (G ghost) (worldOf ghost)
  idle : ∀ context ghost m c rest, Premise context ghost m c rest → Ready ghost m c →
    Flows (G ghost) (worldOf ghost) m → Post context ghost m rest
  fixed : ∀ context ghost m c rest, Premise context ghost m c rest → Ready ghost m c →
    ghostAdvancing c = false → Flows (G ghost) (worldOf ghost) m →
    Post context ghost (driveStep interp m c rest).1 (driveStep interp m c rest).2
  iteration : ∀ context ghost m (f : RunFiber ν σ β ε δ ι α χ) y rest,
    Premise context ghost m (.loop f.id y) rest → Ready ghost m (.loop f.id y) →
    Flows (G ghost) (worldOf ghost) m → m.fiber? f.id = some f →
    ∃ next, order.le ghost next ∧
      IterFlows (G next) (worldOf next) (Machine.iteration interp m f y) ∧
      Post context next (Machine.settle f.id rest (Machine.iteration interp m f y)).1
        (Machine.settle f.id rest (Machine.iteration interp m f y)).2
  deliver : ∀ context ghost m (f : RunFiber ν σ β ε δ ι α χ) y rest,
    Premise context ghost m (.deliver f.id y) rest → Ready ghost m (.deliver f.id y) →
    Flows (G ghost) (worldOf ghost) m → m.fiber? f.id = some f →
    ∃ next, order.le ghost next ∧
      IterFlows (G next) (worldOf next) (FiberEvaluator.evaluate interp m f y) ∧
      Post context next (Machine.settle f.id rest (FiberEvaluator.evaluate interp m f y)).1
        (Machine.settle f.id rest (FiberEvaluator.evaluate interp m f y)).2
  entrant : ∀ context ghost m raceId (race : Race ν σ β ε δ ι α (Prim ν σ β ε δ ι α)) code more
    (host : RunFiber ν σ β ε δ ι α χ) rest,
    Premise context ghost m (.launch raceId) rest → Ready ghost m (.launch raceId) →
    Flows (G ghost) (worldOf ghost) m → m.race? raceId = some race → race.programs = code :: more →
    race.state.accepted.isSome = false → m.fiber? race.host = some host →
    ∃ next, order.le ghost next ∧ Flows (G next) (worldOf next) m ∧
      G next (worldOf next m.state ⟨m.nextId⟩) ⟨m.nextId⟩
        (RunFiber.make ⟨m.nextId⟩ code true (interp.budgetOf host.context) host.context :
          RunFiber ν σ β ε δ ι α χ).frame ∧
      Post context next (driveStep interp m (.launch raceId) rest).1
        (driveStep interp m (.launch raceId) rest).2

variable {order : Effect4.Laws.Effects.WorldOrder V}
variable {ReadyV : V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α → Prop}
variable {GV : V → World → FiberId → FrameFiber ν σ β ε δ ι α → Prop}
variable {worldOfV : V → St → FiberId → World}
variable {Premise : Context → V → RunMachine ν σ β ε δ ι α χ St → Cmd ν σ β ε δ ι α →
  List (Cmd ν σ β ε δ ι α) → Prop}
variable {Post : Context → V → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) → Prop}

/-- The existing command proof handles fixed worlds; the three advancing cases retain one joint witness. -/
theorem GhostCommands.step (facts : GhostCommands order interp ReadyV GV worldOfV Premise Post)
    (context : Context) (ghost : V) (m : RunMachine ν σ β ε δ ι α χ St)
    (c : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α))
    (premise : Premise context ghost m c rest) (ready : ReadyV ghost m c)
    (held : Flows (GV ghost) (worldOfV ghost) m) :
    ∃ next, order.le ghost next ∧ Flows (GV next) (worldOfV next) (driveStep interp m c rest).1 ∧
      Post context next (driveStep interp m c rest).1 (driveStep interp m c rest).2 := by
  cases advancing : ghostAdvancing c with
  | false =>
    exact ⟨ghost, order.refl ghost,
      (facts.administrative ghost).step m c rest ⟨ready, advancing⟩ held,
      facts.fixed context ghost m c rest premise ready advancing held⟩
  | true =>
    cases c
    case loop id y =>
      cases found : m.fiber? id with
      | none =>
        refine ⟨ghost, order.refl ghost, ?_, ?_⟩
        · simpa only [driveStep, found] using held
        · simpa only [driveStep, found] using facts.idle context ghost m (.loop id y) rest premise ready held
      | some fiber =>
        have key := RunMachine.id_of_fiber? found
        subst key
        obtain ⟨next, moved, flowing, post⟩ := facts.iteration context ghost m fiber y rest premise ready held found
        refine ⟨next, moved, ?_, ?_⟩
        · simpa only [driveStep, found] using
            (Flows.settle (facts.administrative next).interruption fiber.id rest _ flowing)
        · simpa only [driveStep, found] using post
    case deliver id y =>
      cases found : m.fiber? id with
      | none =>
        refine ⟨ghost, order.refl ghost, ?_, ?_⟩
        · simpa only [driveStep, found] using held
        · simpa only [driveStep, found] using facts.idle context ghost m (.deliver id y) rest premise ready held
      | some fiber =>
        have key := RunMachine.id_of_fiber? found
        subst key
        obtain ⟨next, moved, flowing, post⟩ := facts.deliver context ghost m fiber y rest premise ready held found
        refine ⟨next, moved, ?_, ?_⟩
        · simpa only [driveStep, found] using
            (Flows.settle (facts.administrative next).interruption fiber.id rest _ flowing)
        · simpa only [driveStep, found] using post
    case launch raceId =>
      cases raceFound : m.race? raceId with
      | none =>
        refine ⟨ghost, order.refl ghost, ?_, ?_⟩
        · simpa only [driveStep, raceFound] using held
        · simpa only [driveStep, raceFound] using facts.idle context ghost m (.launch raceId) rest premise ready held
      | some race =>
        cases programs : race.programs with
        | nil =>
          refine ⟨ghost, order.refl ghost, ?_, ?_⟩
          · simpa only [driveStep, raceFound, programs] using held
          · simpa only [driveStep, raceFound, programs] using facts.idle context ghost m (.launch raceId) rest premise ready held
        | cons code more =>
          cases accepted : race.state.accepted.isSome with
          | true =>
            refine ⟨ghost, order.refl ghost, ?_, ?_⟩
            · simpa only [driveStep, raceFound, programs, accepted, Bool.false_eq_true, ↓reduceIte] using held
            · simpa only [driveStep, raceFound, programs, accepted, Bool.false_eq_true, ↓reduceIte] using
                facts.idle context ghost m (.launch raceId) rest premise ready held
          | false =>
            cases hostFound : m.fiber? race.host with
            | none =>
              refine ⟨ghost, order.refl ghost, ?_, ?_⟩
              · simpa only [driveStep, raceFound, programs, accepted, hostFound, Bool.false_eq_true, ↓reduceIte] using held
              · simpa only [driveStep, raceFound, programs, accepted, hostFound, Bool.false_eq_true, ↓reduceIte] using
                  facts.idle context ghost m (.launch raceId) rest premise ready held
            | some host =>
              obtain ⟨next, moved, oldFlow, childFlow, post⟩ := facts.entrant context ghost m raceId race code more host rest
                premise ready held raceFound programs accepted hostFound
              refine ⟨next, moved, ?_, post⟩
              have launched := Flows.launchEntrant interp raceId m host code (race.nextSite.getD []) oldFlow childFlow
              simp only [driveStep, raceFound, programs, accepted, hostFound]
              generalize launchEntrant interp raceId m host code (race.nextSite.getD []) = pair at launched ⊢
              obtain ⟨spawned, child⟩ := pair
              exact launched.fields rfl rfl
    all_goals cases advancing

/-- The original command facts instantiate the adapter with a constant proof world.
Consumer: existing frame-only command clients retain their current premises and behavior. -/
theorem Commands.toGhost (facts : Commands interp Ready G worldOf) :
    GhostCommands Lift.unitOrder interp (fun (_ : Unit) m c => Ready m c)
      (fun (_ : Unit) => G) (fun (_ : Unit) => worldOf)
      (fun (_ : Unit) (_ : Unit) m c (_ : List (Cmd ν σ β ε δ ι α)) => Ready m c)
      (fun (_ : Unit) (_ : Unit) (_ : RunMachine ν σ β ε δ ι α χ St)
        (_ : List (Cmd ν σ β ε δ ι α)) => True) := by
  refine { administrative := ?_, idle := ?_, fixed := ?_, iteration := ?_, deliver := ?_, entrant := ?_ }
  · intro ghost
    exact facts.restrict (fun _ _ ready => ready.1)
  · intro context ghost m c rest premise ready held
    exact True.intro
  · intro context ghost m c rest premise ready fixed held
    exact True.intro
  · intro context ghost m fiber y rest premise ready held found
    exact ⟨(), Lift.unitOrder.refl (), facts.iteration m fiber y ready held found, True.intro⟩
  · intro context ghost m fiber y rest premise ready held found
    exact ⟨(), Lift.unitOrder.refl (), facts.deliver m fiber y ready held found, True.intro⟩
  · intro context ghost m raceId race code more host rest premise ready held raceFound programs accepted hostFound
    exact ⟨(), Lift.unitOrder.refl (), held,
      facts.entrant m raceId race code more host ready held raceFound programs hostFound, True.intro⟩

end Effect4.Machine.AnswerFlow
