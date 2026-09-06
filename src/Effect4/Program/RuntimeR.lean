import Effect4.Program.EvaluateR
import Effect4.Api

/-!
# Running terms on the shared scheduler

Packet: `Test/contracts/program-runtime-r.contract.md`; batteries and receipts:
`Test/Program/RuntimeR{Contract,AxiomReport}.lean`. These definitions instantiate
the existing decision loop, sufficiency test and observation. The equations
below pin that instantiation, and sufficient command budgets have the same
observation by the existing generic theorem. The initial term/unfolding budget
is fixed in that statement. R5 and general frame/term simulation are still
owed (`RSTEP-FB-SIMULATION`); no claim is made about an external host.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

abbrev RReplay := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit

/-- `Api.load` with the bounded term in place of compiled frame code. -/
def loadR (program : NativeEff) (fuel : Nat) (choices : List Bool := []) : RState :=
  { (RunMachine.empty Stores.empty : RState) with
    fibers := [RunFiber.make Api.root (denoteR program fuel program (rootPoint fuel choices)) true
      (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }

def obsR (m : RState) : Obs := obs m

/-- The same Completion data and decision alphabet as `Api.replay`. -/
def replayR (program : NativeEff) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool := []) : RReplay :=
  replayEval (interpR program fuel) fuel tape (loadR program fuel choices)

/-- The code budget stays fixed when comparing command budgets. -/
def SufficientR (program : NativeEff) (codeFuel commandFuel : Nat) (m : RState)
    (tape : List Api.Decision) : Bool := Suffices (interpR program codeFuel) commandFuel tape m

def BehR (program : NativeEff) (codeFuel commandFuel : Nat) (m : RState)
    (tape : List Api.Decision) (h : SufficientR program codeFuel commandFuel m tape = true) : Obs :=
  Beh (interpR program codeFuel) m tape commandFuel h

theorem loadR_current (e : NativeEff) (fuel : Nat) (choices : List Bool) :
    (loadR e fuel choices).fibers.map (fun f => f.frame.current) =
      [denoteR e fuel e (rootPoint fuel choices)] := rfl

theorem obsR_load (e : NativeEff) (fuel : Nat) (choices : List Bool) :
    obsR (loadR e fuel choices) = ⟨[(Api.root, none)], Stores.empty⟩ := rfl

theorem interpR_answerCode (e : NativeEff) (fuel : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    (interpR e fuel).answerCode answer = denoteCompletion answer := rfl

theorem interpR_body (e : NativeEff) (fuel : Nat) (body : Body) :
    bodyR (interpR e fuel) body = denoteBody e fuel body := by
  cases body <;> rfl

theorem evaluateR_pure (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) :
    evaluateR interp m (answerR f (.pure ex)) yielding =
      deliverR interp m (answerR f (.pure ex)) yielding ex := rfl

theorem evaluateR_frontier (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (reason : FrontierReason) (at_ : ResumePoint) (k : ExitV → RProgram) :
    evaluateR interp m (answerR f (.vis (.inr (.frontier reason at_)) k)) yielding =
      ⟨m, answerR f (.vis (.inr (.frontier reason at_)) k), yielding, .continue_, []⟩ := rfl

/-- The store answer waits for due resumes before the shared loop delivers it. -/
theorem evaluateR_store (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : SyncOp) (k : Val → RProgram) (state : Stores) (value : Val)
    (h : syncOpStep op m.state = some (state, value)) :
    evaluateR interp m (answerR f (.vis (.inl op) k)) yielding =
      ⟨{ m with state }, answerValueR (saveValueR (answerR f (.vis (.inl op) k)) k) value,
        yielding, .answered, [.drainDue]⟩ := by
  simp only [evaluateR, answerR, h]

/-- A malformed store request keeps the existing sync fallback. -/
theorem evaluateR_store_missing (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : SyncOp) (k : Val → RProgram) (h : syncOpStep op m.state = none) :
    evaluateR interp m (answerR f (.vis (.inl op) k)) yielding =
      ⟨m, answerValueR (saveValueR (answerR f (.vis (.inl op) k)) k) .unit,
        yielding, .answered, []⟩ := by
  simp only [evaluateR, answerR, h]

theorem BehR_fuel_irrelevant (e : NativeEff) (codeFuel n n' : Nat) (m : RState)
    (tape : List Api.Decision) (h : SufficientR e codeFuel n m tape = true)
    (h' : SufficientR e codeFuel n' m tape = true) :
    BehR e codeFuel n m tape h = BehR e codeFuel n' m tape h' :=
  Beh_fuel_irrelevant (interpR e codeFuel) m tape n n' h h'

end Effect4.Program.Sched
