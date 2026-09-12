import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Machine.Book
import Effect4.Laws.Program.Means
import Effect4.Laws.Program.Simulation.Drive
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Api

/-!
# Running terms on the shared scheduler

Packet: `Test/contracts/program-runtime-r.contract.md`; batteries and receipts:
`Test/Program/RuntimeR{Contract,AxiomReport}.lean`, `Test/Program/SimulationContract.lean`.
These definitions instantiate the existing decision loop, sufficiency test and
observation. The equations below pin that instantiation, and sufficient command
budgets have the same observation by the existing generic theorem. The loaded
term and its compile budget are fixed in that statement.

The last two sections are P3 and P4 (2026-09-07). `run_eq_ref` is the general
frame/term judgment: on every program the compiler admits, every compile budget,
every command budget, every `Completion` tape and every choice list, the frame
machine's replay and the term reference's replay have the same classification,
the same observation (every fiber's exit and the whole stores) and the same
sufficiency receipt. It is `Machine.Book`'s generic replay theorem at the native
alphabets, with `StepAgrees` discharged in `Simulation/Drive.lean`. `straight_ref`
is P4: on the straight fragment at the budget `run_eq_meaning` already names, the
term reference finishes with the meaning's exit and stores, and that budget is
proved sufficient (`straight_sufficient`), so the fixed-bound R5 statement holds.
No claim is made about an external host: the pinned rc.112 evidence is the finite
tables of the probes (`RSTEP-FB-HOST`).
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

abbrev RReplay := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores RProgram RSaved Unit

/-- `Api.load` with the structural term in place of compiled frame code. -/
def loadR (program : NativeEff) (fuel : Nat) (choices : List Bool := [])
    (compileFuel : Nat := fuel) : RState :=
  { (RunMachine.empty Stores.empty : RState) with
    fibers := [RunFiber.make Api.root (denoteR program program (rootPoint compileFuel choices)) true
      (stores.budgetOf emptyCtx) emptyCtx]
    nextId := 1 }

def obsR (m : RState) : Obs := obs m

/-- The same Completion data and decision alphabet as `Api.replay`. -/
def replayR (program : NativeEff) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool := []) (compileFuel : Nat := fuel) : RReplay :=
  letI := termEvaluatorFor program
  replayEval (interpR program) fuel tape (loadR program fuel choices compileFuel)

/-- The loaded term stays fixed when comparing command budgets. -/
def SufficientR (program : NativeEff) (commandFuel : Nat) (m : RState)
    (tape : List Api.Decision) : Bool :=
  letI := termEvaluatorFor program
  Suffices (interpR program) commandFuel tape m

def BehR (program : NativeEff) (commandFuel : Nat) (m : RState)
    (tape : List Api.Decision) (h : SufficientR program commandFuel m tape = true) : Obs :=
  letI := termEvaluatorFor program
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
      prepareIterR (deliverR interp m (answerR f (.pure ex)) yielding ex) := rfl

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
  simp only [evaluateR, evaluateRawR, prepareIterR, prepareR, answerR, h]

/-- A malformed store request keeps the existing sync fallback. -/
theorem evaluateR_store_missing (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (op : SyncOp) (k : Val → RProgram) (h : syncOpStep op m.state = none) :
    evaluateR interp m (answerR f (.vis (.inl op) k)) yielding =
      ⟨m, answerR (answerR f (.vis (.inl op) k)) (k .unit), yielding, .answered, []⟩ := by
  simp only [evaluateR, evaluateRawR, prepareIterR, prepareR, answerR, h]

/-- The checkpoint returns its continuation, completing stateful callback and
construction glue before the next counted step. The continuation is arbitrary. -/
theorem evaluateR_suspend (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (p : Point) (k : Val → RProgram) :
    evaluateR interp m (answerR f (.vis (.inr (.suspend p)) k)) yielding =
      prepareIterR ⟨m, answerR (answerR f (.vis (.inr (.suspend p)) k))
        (k .unit), yielding, .continue_, []⟩ := rfl

/-- A pure thunk's value goes through the `answered` phase, owing nothing. -/
theorem evaluateR_sync (interp : RInterp) (m : RState) (f : RFiber) (yielding : Bool)
    (v : Val) (k : Val → RProgram) :
    evaluateR interp m (answerR f (.vis (.inr (.sync v)) k)) yielding =
      ⟨m, answerR (answerR f (.vis (.inr (.sync v)) k)) (k v), yielding, .answered, []⟩ := rfl

theorem BehR_fuel_irrelevant (e : NativeEff) (n n' : Nat) (m : RState)
    (tape : List Api.Decision) (h : SufficientR e n m tape = true)
    (h' : SufficientR e n' m tape = true) :
    BehR e n m tape h = BehR e n' m tape h' := by
  letI := termEvaluatorFor e
  exact Beh_fuel_irrelevant (interpR e) m tape n n' h h'

/-! ## P3: the frame machine and the term reference agree on every tape

The book (`Machine/Book.lean`) lifts one obligation about `driveStep`, `StepAgrees`,
through the command loop, every decision and every tape; `Simulation/Drive.lean`
discharges it at the native alphabets and `Simulation/Actions.lean` the two hook
obligations. The loaded machines are related by the introduction lemma
`compile_intro`: the compiled root code means the denoted term, and the empty
bookkeeping is the same on both sides. The relation holds on every fiber, race,
queued task and residual command, so the classification, the whole observation and
both sufficiency receipts agree. -/

abbrev FReplay := ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- How a replay ended, read off either instance. -/
def classify {κ φ η : Type} :
    ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores κ φ η → Api.Outcome
  | .finished _ => .finished
  | .frontier _ _ => .frontier
  | .stuck why _ => .stuck why

/-- The loaded frame machine carries the invariant: empty stores, no park. -/
theorem load_ok (e : NativeEff) (fuel : Nat) (choices : List Bool) :
    MachineOk StoresOk (Api.load e fuel choices) :=
  ⟨storesOk_empty, fun f hf => by
    rw [List.mem_singleton.mp hf]
    exact pendingOk_make _ _ _ _ _⟩

/-- The two loads are in the book: the compiled root means the denoted root. -/
theorem load_rel (e : NativeEff) (fuel : Nat) (choices : List Bool) :
    BMeans e (Api.load e fuel choices) (loadR e fuel choices) :=
  BMeans.mk' (ListRel.cons (fmeans_make e Api.root (compile_intro e fuel choices) true _ _) ListRel.nil)
    ListRel.nil rfl rfl rfl rfl rfl rfl rfl

/-- Every tape replays to related results, at any compile budget and any command budget. -/
theorem replay_rel (e : NativeEff) (cfuel fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool) :
    letI := evaluatorFor e
    letI := termEvaluatorFor e
    ReplayRel (CodeMeans e) (Means e)
      (replayEval (interpOf e) fuel tape (Api.load e cfuel choices))
      (replayEval (interpR e) fuel tape (loadR e cfuel choices)) := by
  letI := evaluatorFor e
  letI := termEvaluatorFor e
  exact book_replayEval (interpOf e) (interpR e) (stepAgrees e) (hooksAgree_of e) fuel tape _ _
    (load_ok e cfuel choices) (load_rel e cfuel choices)

theorem replayRel_classify_obs {e : NativeEff} {r₁ : FReplay} {r₂ : RReplay}
    (h : ReplayRel (CodeMeans e) (Means e) r₁ r₂) :
    classify r₁ = classify r₂ ∧ obs r₁.machine = obs r₂.machine := by
  cases r₁ <;> cases r₂ <;> first
    | exact (h : False).elim
    | exact ⟨rfl, bookMeans_obs h⟩
    | exact ⟨rfl, bookMeans_obs h.2⟩
    | exact ⟨congrArg Api.Outcome.stuck h.1, bookMeans_obs h.2⟩

theorem replay_outcome (e : NativeEff) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool) :
    (Api.replay e fuel tape choices).outcome =
      classify (replayEval (evaluator := evaluatorFor e) (interpOf e) fuel tape
        (Api.load e fuel choices)) := by
  unfold Api.replay
  split <;> rename_i heq <;> rw [heq] <;> rfl

theorem replay_machine (e : NativeEff) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool) :
    (Api.replay e fuel tape choices).machine =
      (replayEval (evaluator := evaluatorFor e) (interpOf e) fuel tape
        (Api.load e fuel choices)).machine := by
  unfold Api.replay
  split <;> rename_i heq <;> rw [heq] <;> rfl

/-- **`run_eq_ref`.** The frame machine's replay and the term reference's replay of the
same program, at the same compile and command budget, on the same `Completion` tape and
choices, end the same way and observe the same thing: every fiber's exit and the whole
stores. No premise: the relation is inhabited at the load and preserved by every command.
Nothing is said about an external host.

**At the empty table, with no oracle answers** (DI-57). `Api.replay` takes a `RowTable` and a
list of external answers; this theorem takes neither, so both stay at their defaults — the
empty table and the empty oracle. It is an internal agreement on that fragment and it does not
extend to a run with external rows: the reference lacks external registration, the answer's
conversion and allocation, the prepared answer, and a way to select its evaluator. The
table-aware proposition is filed verbatim, with those four gaps at their `file:line`, in
`Test/contracts/machine-scheduler-core.contract.md`, "Table-aware agreement (DI-57)"; its
proof is a later slice. -/
theorem run_eq_ref (e : NativeEff) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool := []) :
    (Api.replay e fuel tape choices).outcome = classify (replayR e fuel tape choices) ∧
      obs (Api.replay e fuel tape choices).machine = obsR (replayR e fuel tape choices).machine := by
  rw [replay_outcome, replay_machine]
  exact replayRel_classify_obs (replay_rel e fuel fuel tape choices)

/-- Both sufficiency receipts agree, at any compile budget and any command budget. -/
theorem suffices_eq_ref (e : NativeEff) (cfuel fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool) :
    letI := evaluatorFor e
    Suffices (interpOf e) fuel tape (Api.load e cfuel choices) =
      SufficientR e fuel (loadR e cfuel choices) tape := by
  letI := evaluatorFor e
  letI := termEvaluatorFor e
  exact book_suffices (interpOf e) (interpR e) (stepAgrees e) (hooksAgree_of e) fuel tape _ _
    (load_ok e cfuel choices) (load_rel e cfuel choices)

/-- The behaviour form of `run_eq_ref`: under either receipt the observations are one. -/
theorem beh_eq_ref (e : NativeEff) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool)
    (h₁ : letI := evaluatorFor e; Suffices (interpOf e) fuel tape (Api.load e fuel choices) = true)
    (h₂ : SufficientR e fuel (loadR e fuel choices) tape = true) :
    letI := evaluatorFor e
    Beh (interpOf e) (Api.load e fuel choices) tape fuel h₁ =
      BehR e fuel (loadR e fuel choices) tape h₂ :=
  (replayRel_classify_obs (replay_rel e fuel fuel tape choices)).2

/-- The root's exit read on related machines. -/
theorem BMeans.exitOf {root : NativeEff} {m₁ : FMachine} {m₂ : RState} (h : BMeans root m₁ m₂)
    (id : FiberId) : (m₁.fiber? id).bind RunFiber.exit = (m₂.fiber? id).bind RunFiber.exit := by
  rcases h.fiber?_cases id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
  · rw [h₁, h₂]
    rfl
  · rw [h₁, h₂]
    exact hf.exit

/-- The root exits agree on every tape. -/
theorem run_eq_ref_exit (e : NativeEff) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool := []) :
    (Api.replay e fuel tape choices).exit =
      ((replayR e fuel tape choices).machine.fiber? Api.root).bind RunFiber.exit := by
  unfold Api.Run.exit
  rw [replay_machine]
  exact BMeans.exitOf (ReplayRel.machine (replay_rel e fuel fuel tape choices)) Api.root

/-! ## P4: the straight fragment on the reference, at the fixed budget

`run_eq_meaning` (`Agreement/Machine.lean`) already runs the frame machine on the straight
fragment at the budget `fuel` with `depth e ≤ fuel` and `2 * steps e + 6 ≤ fuel`, and
`replay_Mexit` names the finished machine. Through `run_eq_ref` the term reference finishes
at the same budget with the same observation: the root's exit is the meaning's and the
stores are the meaning's, and no other fiber exists. `Suffices_of_replay_terminal` makes the
requested budget sufficient on the frame side, and `suffices_eq_ref` carries the receipt
across, so the fixed-bound statement needs no existential budget. -/

open Effect4.Program.Agreement in
/-- The observation of the finished straight run: the root's exit and the stores. -/
theorem obs_Mexit (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : obs (Mexit root ex fr s k tr nt) = ⟨[(Api.root, some ex)], s⟩ := rfl

open Effect4.Program.Agreement in
/-- **P4, the straight corollary.** On the straight fragment, at the budget of
`run_eq_meaning`, the term reference finishes, its only fiber is the root with the
meaning's exit, and its stores are the meaning's. -/
theorem straight_ref (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    classify (replayR e fuel [Api.evaluate, Api.flush]) = .finished ∧
      obsR (replayR e fuel [Api.evaluate, Api.flush]).machine =
        ⟨[(Api.root, some (meaning e [] Stores.empty).1)], (meaning e [] Stores.empty).2⟩ := by
  have hpl : Plain e = true := by rw [Plain_eq_Straight]; exact hs
  obtain ⟨fr, k', tr', nt', hrep⟩ := replay_Mexit e fuel hpl hd hfuel
  have h := replayRel_classify_obs (replay_rel e fuel fuel [Api.evaluate, Api.flush] [])
  rw [hrep] at h
  exact ⟨h.1.symm, h.2.symm⟩

open Effect4.Program.Agreement in
/-- **P4, the fixed budget.** The budget `run_eq_meaning` names is sufficient for the term
reference too: the frame replay is terminal there, and the receipts agree. -/
theorem straight_sufficient (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    SufficientR e fuel (loadR e fuel) [Api.evaluate, Api.flush] = true := by
  letI := evaluatorFor e
  have hpl : Plain e = true := by rw [Plain_eq_Straight]; exact hs
  obtain ⟨fr, k', tr', nt', hrep⟩ := replay_Mexit e fuel hpl hd hfuel
  rw [← suffices_eq_ref e fuel fuel [Api.evaluate, Api.flush] []]
  refine Suffices_of_replay_terminal (interpOf e) fuel _ _ ?_
  rw [hrep]
  rfl

/-- **P4, the behaviour form.** At the fixed budget the reference's behaviour is the
meaning: the root's exit and the stores, with no other fiber. -/
theorem straight_beh (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : Effect4.Program.Agreement.depth e ≤ fuel)
    (hfuel : 2 * Effect4.Program.Agreement.steps e + 6 ≤ fuel) :
    BehR e fuel (loadR e fuel) [Api.evaluate, Api.flush] (straight_sufficient e fuel hs hd hfuel) =
      ⟨[(Api.root, some (meaning e [] Stores.empty).1)], (meaning e [] Stores.empty).2⟩ :=
  (straight_ref e fuel hs hd hfuel).2

end Effect4.Program.Sched
