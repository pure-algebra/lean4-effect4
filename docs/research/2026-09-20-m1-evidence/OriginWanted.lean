import Effect4.Laws.Machine.Book
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Auto.Obligations

/-! Phase A pending statements, recorded before the origin/site repair proofs.
This snapshot is a pending ledger only; Phase B must establish the live gate. -/
namespace Effect4.Machine.PhaseA.OriginWanted
open Effect4 Effect4.Machine
set_option linter.unusedSectionVars false
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

def spawn_eq (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat := [])  : ProofGraph.Obligation (
    spawn interp m parent program options site =
      ({ m with fibers := m.fibers ++ [spawnChild interp m parent program options site], nextId := m.nextId + 1 }.emit
          [RunEvent.forked parent.id ⟨m.nextId⟩ options.daemon],
        parent, ⟨m.nextId⟩)) := ⟨⟩
#proof_wanted spawn_eq

def spawnChild_fields (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat := [])  : ProofGraph.Obligation (
    (spawnChild interp m parent program options site).id = ⟨m.nextId⟩ ∧
      (spawnChild interp m parent program options site).context = parent.context ∧
      (spawnChild interp m parent program options site).frame.interruptible =
        (match options.maskMode with
          | Supervision.MaskMode.interruptible => true
          | Supervision.MaskMode.uninterruptible => false
          | Supervision.MaskMode.inherit => parent.frame.interruptible) ∧
      (spawnChild interp m parent program options site).observers = [] ∧
      (spawnChild interp m parent program options site).origin = .forked parent.id options.daemon site) := ⟨⟩
#proof_wanted spawnChild_fields

def spawn_untracked (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat := [])  : ProofGraph.Obligation (
    (spawn interp m parent program options site).2.1 = parent) := ⟨⟩
#proof_wanted spawn_untracked

def drive_launch_runs (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (raceId : Nat) (rest : List (Cmd ν σ β ε δ ι α))
    (race : Race ν σ β ε δ ι α) (program : Prim ν σ β ε δ ι α) (more : List (Prim ν σ β ε δ ι α))
    (host : RunFiber ν σ β ε δ ι α χ)
    (_hs : m.stuck = none) (_hr : m.race? raceId = some race)
    (_hp : race.programs = program :: more) (_hacc : race.state.accepted = none)
    (_hh : m.fiber? race.host = some host)  : ProofGraph.Obligation (
    drive interp (fuel + 1) m (Cmd.launch raceId :: rest) =
      (let l := launchEntrant interp raceId m host program (race.nextSite.getD [])
       drive interp fuel
         ((l.1.updateRace { race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1]) }).emit [RunEvent.raceLaunched raceId l.2])
         (Cmd.evaluate l.2 :: Cmd.enrollRace raceId l.2 :: Cmd.launch raceId :: rest))) := ⟨⟩
#proof_wanted drive_launch_runs

def withFiber_fork (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat := [])  : ProofGraph.Obligation (
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.fork program options site) =
      (let m' := if options.daemon then m else { m with middlewareInstalled := true }
       let s := spawn interp m' f program options site
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_,
        t.2.2 ++ (if options.daemon then [] else [Cmd.trackChild f.id s.2.2])⟩)) := ⟨⟩
#proof_wanted withFiber_fork

def withFiber_forkIn (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat := [])  : ProofGraph.Obligation (
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkIn program options scope site) =
      (let s := spawn interp m f program { options with daemon := true } site
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_,
        t.2.2 ++ [Cmd.link Supervision.ScopeMode.forkIn scope s.2.2 (some t.2.1.id)
          (interp.stackAnnotations t.2.1.id)]⟩)) := ⟨⟩
#proof_wanted withFiber_forkIn

def withFiber_forkScoped_ambient (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (scope : Nat)
    (_h : interp.ambientScope f.context = some scope) (site : List Nat := [])  : ProofGraph.Obligation (
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options site) =
      (let s := spawn interp m f program { options with daemon := true } site
       let t := start s.1 s.2.1 s.2.2 options.startImmediately
       ⟨t.1, { t.2.1 with frame := { t.2.1.frame with
          current := Prim.success (interp.fiberValue s.2.2) } },
        yielding, Outcome.continue_,
        t.2.2 ++ [Cmd.link Supervision.ScopeMode.forkIn scope s.2.2 (some t.2.1.id)
          (interp.stackAnnotations t.2.1.id)]⟩)) := ⟨⟩
#proof_wanted withFiber_forkScoped_ambient

def withFiber_forkScoped_none (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions)
    (_h : interp.ambientScope f.context = none) (site : List Nat := [])  : ProofGraph.Obligation (
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.forkScoped program options site) =
      ⟨m, { f with frame := { f.frame with
          current := Prim.failure (Cause.die interp.missingScope) } },
        yielding, Outcome.continue_, []⟩) := ⟨⟩
#proof_wanted withFiber_forkScoped_none

def launchEntrant_eq (interp : RunInterp ν σ β ε δ ι α χ St) (raceId : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (host : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (site : List Nat := [])  : ProofGraph.Obligation (
    launchEntrant interp raceId m host program site =
      (let s := spawn interp m host program ⟨true, true, Supervision.MaskMode.interruptible⟩ site
       (s.1, s.2.2))) := ⟨⟩
#proof_wanted launchEntrant_eq

def withFiber_raceAll (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (entrants : List (Prim ν σ β ε δ ι α)) (site : Option (List Nat) := none)  : ProofGraph.Obligation (
    evaluatePrim.withFiber interp m f yielding (WithFiberAction.raceAll entrants site) =
      (let raceId := m.nextRace
       let token := m.nextToken
       let m := { m with nextRace := m.nextRace + 1, nextToken := m.nextToken + 1 }
       let race : Race ν σ β ε δ ι α :=
         ⟨raceId, f.id, token,
           { Supervision.RaceAllState.initial [] with remaining := entrants.length }, false, entrants,
           false, site⟩
       let m := { m with races := m.races ++ [race] }
       ⟨m.emit [RunEvent.raceStarted raceId f.id entrants.length],
        { f with frame := { f.frame with current := interp.parkCode (ParkKind.race raceId) } },
        yielding, Outcome.continue_, []⟩)) := ⟨⟩
#proof_wanted withFiber_raceAll

variable {κ₁ φ₁ κ₂ φ₂ : Type (max u v)}
variable [core₁ : FiberCore ν β ε δ ι α κ₁ φ₁] [core₂ : FiberCore ν β ε δ ι α κ₂ φ₂]
variable {C : κ₁ → κ₂ → Prop} {S : φ₁ → φ₂ → Prop}

def fiberMeans_origin {f₁ : RunFiber ν σ β ε δ ι α χ κ₁ φ₁}
    {f₂ : RunFiber ν σ β ε δ ι α χ κ₂ φ₂} (_h : FiberMeans C S f₁ f₂)  : ProofGraph.Obligation (
    f₁.origin = f₂.origin) := ⟨⟩
#proof_wanted fiberMeans_origin

end Effect4.Machine.PhaseA.OriginWanted
