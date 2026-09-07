import Effect4.Program.EvaluateR
import Effect4.Api

/-!
# Running terms on the shared scheduler

Packet: `Test/contracts/program-runtime-r.contract.md`; batteries and receipts:
`Test/Program/RuntimeR{Contract,AxiomReport}.lean`. These definitions instantiate
the existing decision loop, sufficiency test and observation. The equations
below pin that instantiation, and sufficient command budgets have the same
observation by the existing generic theorem. The loaded term and its compile
budget are fixed in that statement. R5 and general frame/term simulation are
still owed (`RSTEP-FB-SIMULATION`); no claim is made about an external host.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

abbrev RReplay := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit

/-- `Api.load` with the structural term in place of compiled frame code. -/
def loadR (program : NativeEff) (fuel : Nat) (choices : List Bool := []) : RState :=
  { (RunMachine.empty Stores.empty : RState) with
    fibers := [RunFiber.make Api.root (denoteR program program (rootPoint fuel choices)) true
      (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }

def obsR (m : RState) : Obs := obs m

/-- The same Completion data and decision alphabet as `Api.replay`. -/
def replayR (program : NativeEff) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool := []) : RReplay :=
  replayEval (interpR program) fuel tape (loadR program fuel choices)

/-- The loaded term stays fixed when comparing command budgets. -/
def SufficientR (program : NativeEff) (commandFuel : Nat) (m : RState)
    (tape : List Api.Decision) : Bool := Suffices (interpR program) commandFuel tape m

def BehR (program : NativeEff) (commandFuel : Nat) (m : RState)
    (tape : List Api.Decision) (h : SufficientR program commandFuel m tape = true) : Obs :=
  Beh (interpR program) m tape commandFuel h

theorem loadR_current (e : NativeEff) (fuel : Nat) (choices : List Bool) :
    (loadR e fuel choices).fibers.map (fun f => f.frame.current) =
      [denoteR e e (rootPoint fuel choices)] := rfl

theorem obsR_load (e : NativeEff) (fuel : Nat) (choices : List Bool) :
    obsR (loadR e fuel choices) = ⟨[(Api.root, none)], Stores.empty⟩ := rfl

theorem interpR_answerCode (e : NativeEff) (answer : Completion Val Err Defect FiberId Ann) :
    (interpR e).answerCode answer = denoteCompletion answer := rfl

theorem interpR_body (e : NativeEff) (body : Body) :
    bodyR (interpR e) body = denoteBody e body := by
  cases body <;> rfl

theorem evaluateR_pure (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool) (ex : ExitV) :
    evaluateR interp m (answerR f (.pure ex)) yielding =
      deliverR interp m (answerR f (.pure ex)) yielding ex := rfl

theorem evaluateR_frontier (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (reason : FrontierReason) (at_ : Point) (k : ExitV → RProgram) :
    evaluateR interp m (answerR f (.vis (.inr (.frontier reason at_)) k)) yielding =
      ⟨m, answerR f (.vis (.inr (.frontier reason at_)) k), yielding, .continue_, []⟩ := rfl

/-- The store answer waits for due resumes before the shared loop delivers it; the
continuation is installed directly, with no saved slot. -/
theorem evaluateR_store (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : SyncOp) (k : Val → RProgram) (state : Stores) (value : Val)
    (h : syncOpStep op m.state = some (state, value)) :
    evaluateR interp m (answerR f (.vis (.inl op) k)) yielding =
      ⟨{ m with state }, answerR (answerR f (.vis (.inl op) k)) (k value),
        yielding, .answered, [.drainDue]⟩ := by
  simp only [evaluateR, answerR, h]

/-- A malformed store request keeps the existing sync fallback. -/
theorem evaluateR_store_missing (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : SyncOp) (k : Val → RProgram) (h : syncOpStep op m.state = none) :
    evaluateR interp m (answerR f (.vis (.inl op) k)) yielding =
      ⟨m, answerR (answerR f (.vis (.inl op) k)) (k .unit), yielding, .answered, []⟩ := by
  simp only [evaluateR, answerR, h]

/-- The checkpoint that returns code installs its continuation for the next counted step. -/
theorem evaluateR_suspend (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (p : Point) (k : Val → RProgram) :
    evaluateR interp m (answerR f (.vis (.inr (.suspend p)) k)) yielding =
      ⟨m, answerR (answerR f (.vis (.inr (.suspend p)) k)) (k .unit), yielding, .continue_, []⟩ := rfl

/-- A pure thunk's value goes through the `answered` phase, owing nothing. -/
theorem evaluateR_sync (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (v : Val) (k : Val → RProgram) :
    evaluateR interp m (answerR f (.vis (.inr (.sync v)) k)) yielding =
      ⟨m, answerR (answerR f (.vis (.inr (.sync v)) k)) (k v), yielding, .answered, []⟩ := rfl

theorem BehR_fuel_irrelevant (e : NativeEff) (n n' : Nat) (m : RState)
    (tape : List Api.Decision) (h : SufficientR e n m tape = true)
    (h' : SufficientR e n' m tape = true) :
    BehR e n m tape h = BehR e n' m tape h' :=
  Beh_fuel_irrelevant (interpR e) m tape n n' h h'

end Effect4.Program.Sched
