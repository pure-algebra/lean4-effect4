import Effect4.Laws.Program.Simulation.Fibers
import Effect4.Laws.Auto.Obligations

/-! Phase A pending statements, frozen before reference-origin compilation maintenance.
The live Phase B ledger and proof census remain required. -/
namespace Effect4.Program.Sched.PhaseA.ReferenceOriginWanted
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
set_option linter.unusedSectionVars false
variable {root : NativeEff} {f₁ : FRun} {f₂ : RFiber}

def FMeans_origin (_h : FMeans root f₁ f₂)  : ProofGraph.Obligation (
    f₁.origin = f₂.origin) := ⟨⟩
#proof_wanted FMeans_origin

def FMeans_mk' (_hid : f₁.id = f₂.id) (_hpk : f₁.parked = f₂.parked)
    (_hctx : f₁.context = f₂.context) (_hrun : f₁.running = f₂.running)
    (_hpend : f₁.pending = f₂.pending) (_hfin : f₁.finalizing = f₂.finalizing)
    (_hex : f₁.exit = f₂.exit) (_hoc : f₁.currentOpCount = f₂.currentOpCount)
    (_hmo : f₁.maxOpsBeforeYield = f₂.maxOpsBeforeYield) (_hpy : f₁.preventYield = f₂.preventYield)
    (_hyo : f₁.yieldOverride = f₂.yieldOverride) (_hobs : f₁.observers = f₂.observers)
    (_hch : f₁.children = f₂.children)
    (_hdisp : DispatcherMeans (CodeMeans root) f₁.dispatcher f₂.dispatcher)
    (_hS : Means root f₁.frame f₂.frame) (_horigin : f₁.origin = f₂.origin)  : ProofGraph.Obligation (
    FMeans root f₁ f₂) := ⟨⟩
#proof_wanted FMeans_mk'

def fmeans_make (root : NativeEff) (id : FiberId) {c₁ : NCode} {c₂ : RProgram}
    (_hc : CodeMeans root c₁ c₂) (flag : Bool) (budget : Nat × Bool) (ctx : Ctx) (origin : Origin := .root)  : ProofGraph.Obligation (
    FMeans root (RunFiber.make id c₁ flag budget ctx origin) (RunFiber.make id c₂ flag budget ctx origin)) := ⟨⟩
#proof_wanted fmeans_make

def raceMeans_nextSite {r₁ : FRace} {r₂ : RRace} (_h : RaceMeans (CodeMeans root) r₁ r₂)  : ProofGraph.Obligation (
    r₁.nextSite = r₂.nextSite) := ⟨⟩
#proof_wanted raceMeans_nextSite

def raceMeans_mk' {r₁ : FRace} {r₂ : RRace} (_hid : r₁.id = r₂.id) (_hhost : r₁.host = r₂.host)
    (_htok : r₁.token = r₂.token) (_hst : r₁.state = r₂.state) (_hsettled : r₁.settled = r₂.settled)
    (_hreg : r₁.registering = r₂.registering) (_hprog : ListRel (CodeMeans root) r₁.programs r₂.programs)
    (_hsite : r₁.nextSite = r₂.nextSite)  : ProofGraph.Obligation (
    RaceMeans (CodeMeans root) r₁ r₂) := ⟨⟩
#proof_wanted raceMeans_mk'

end Effect4.Program.Sched.PhaseA.ReferenceOriginWanted
