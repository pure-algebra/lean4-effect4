import Effects.Algebra.Sum
import Effects.Flow.Alphabet
import Effects.Trace
import Effect4.Semantics.Runs
import Effect4.Semantics.Fuel

/-!
# Semantics.Denotation

Owner: the algebraic meaning of an admitted first-order flow (packet D1 of
`docs/research/2026-09-03-reification-plan.md`, specified in
`docs/research/2026-09-03-algebra-denotation.md` §1).

A `CheckedFlow` denotes a `Program` over a signature sum. The left summand is
the flow's own alphabet, embedded through `Alphabet.toFamily` at the constant
denotation `Val`; the right summand announces the decisions the tape has
already made, answering `Unit` because the branch is fixed before the operation
is performed. The runner of `Effect4/Semantics/Runs.lean` is then
`interpret` of that program under a handler that is a `Handler.sum`.

Two facts shape everything here.

* **The denotation is tape-indexed and fuel-free.** `Program` is inductive, so
  every root-to-leaf path is finite, while an admitted flow may cycle. The tape
  is the termination measure: `(tape.length, (raw.reachSet block).length)`
  decreases at every step, the second component exactly by `CyclesWF`. This is
  the only thing admission buys `denote`, and `fun tape => denote flow tape v`
  is the relational denotation DB-03 asks for.
* **`done` and `frontier` have no producer in the algebra.**
  `Effects.Trace.Event` has nine constructors and `Family.Service.traced`
  writes three of them. `decide` is recovered by the decision summand; the
  outcome rows are not operations at all, they are a function of the result the
  denotation returns, so they are supplied by `outcomeRows` and appended by
  `close`. `interpretRun` is that composite and is the right-hand side of T1.
-/

universe uTy uOp

namespace Effect4.Flow

open Effects
open Effects.RawFlow (reachSet_length_lt_of_edge)
open Effects.Trace (Val)

/-! ## The signature -/

/-- The flow alphabet as a named-operation family, at the constant denotation
`Val`: every request and every answer is a wire value, which is exactly what
`FlowService.handle` already promised. -/
abbrev Fam (alphabet : FlowAlphabet Ty) : Family :=
  alphabet.toAlphabet.toFamily (fun _ => Val)

/-- The signature of the flow's own operations. -/
abbrev Sig (alphabet : FlowAlphabet Ty) : Signature := (Fam alphabet).toSignature

/-- The decision summand. The answer is `Unit`, not `Bool`: the tape has already
fixed the branch, so the operation carries the observation and nothing else.
Keeping it an operation (rather than returning the `decide` rows as data) is
what lets both summands write the same log. -/
abbrev DecSig : Signature.{0, 0} := ⟨DecisionId × Bool, fun _ => Unit⟩

/-- What a flow run performs: its alphabet, plus the decisions it announces. -/
abbrev FullSig (alphabet : FlowAlphabet Ty) : Signature := Sig alphabet ⊕ₛ DecSig

/-- A `FlowService` is already a `Family.Service` for `Fam`; the `pure` flag is a
tracing policy and stays out of the signature. -/
def FlowService.toService {alphabet : FlowAlphabet Ty} {M : Type → Type}
    (service : FlowService alphabet M) : (Fam alphabet).Service M :=
  service.handle

/-! ## The fuelled denotation -/

/-- The denotation with fuel, structural on fuel, mirroring `loop` and `plan`
case for case. The `0` case yields the fuel frontier, as `loop` does; the
`frontier` row it also emits is an outcome row and is supplied by `close`. -/
def denoteFuel {alphabet : FlowAlphabet Ty} :
    Nat → RawFlow Ty → BlockId → Env → Tape → Program (FullSig alphabet) (RunResult × Tape)
  | 0, _, block, _, tape => .pure (.frontier (.fuel block), tape)
  | fuel + 1, raw, block, env, tape =>
    match lookupBlock raw block with
    | none => .pure (.frontier (.stuck block), tape)
    | some current =>
      match plan alphabet current env tape with
      | .stuck => .pure (.frontier (.stuck current.id), tape)
      | .ret value => .pure (.done value, tape)
      | .jump target env' => denoteFuel fuel raw target env' tape
      | .perform op request target env' =>
          .vis (.inl ⟨op, request⟩) fun answer : Val =>
            denoteFuel fuel raw target (env' ++ [answer]) tape
      | .exhausted site => .pure (.frontier (.unansweredDecision site), tape)
      | .mismatch expected actual => .pure (.refusal expected actual, tape)
      | .choose site branch target env' rest =>
          .vis (.inr (site, branch)) fun _ => denoteFuel fuel raw target env' rest
      | .performCatch op request target env' _ _ =>
          .vis (.inl ⟨op, request⟩) fun answer : Val =>
            denoteFuel fuel raw target (env' ++ [answer]) tape

/-! ## The interpreting handler -/

/-- The traced service the runner actually uses. `Family.Service.traced` logs
unconditionally; the runner suppresses `op` and `answer` for the operations
`FlowService.pure` marks as atoms (`Runs.lean`, `step`), so the guard is part of
the service and not of the signature. -/
def tracedFlowService [Monad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) :
    (Fam alphabet).Service (RunM M) :=
  fun op request log =>
    service.handle op request >>= fun answer =>
      pure (answer,
        if service.pure op then log
        else log ++ [.op (nameOf op) request, .answer (nameOf op) answer])

/-- The decision summand logs one `decide` row and answers `Unit`. -/
def decisionHandler [Monad M] : Handler DecSig (RunM M) :=
  ⟨fun site => emit (.decide site.1.value site.2)⟩

/-- The handler T1 interprets under: the guarded traced service on the left, the
decision logger on the right. -/
def traceHandler [Monad M] {alphabet : FlowAlphabet Ty} (service : FlowService alphabet M)
    (nameOf : alphabet.Op → String) : Handler (FullSig alphabet) (RunM M) :=
  (tracedFlowService service nameOf).toHandler.sum decisionHandler

/-! ## The outcome rows -/

/-- The rows the runner appends when a run ends. `done` and `frontier` have no
former in `Family.Service.traced` and are not operations of any summand: they
are a function of the result the denotation returns. `stuck` and both refusals end a
run silently (`Runs.lean`, `step`). -/
def outcomeRows : RunResult → Effect4.Trace.Log
  | .done value => [.done (.success value)]
  | .failed error => [.done (.failure error)]
  | .frontier (.fuel _) => [.frontier]
  | .frontier (.unansweredDecision _) => [.frontier]
  | .frontier (.stuck _) => []
  | .refusedSite _ _ => []
  | .refusedValue _ => []

@[scoped simp] theorem outcomeRows_refusal (expected actual : DecisionId) :
    outcomeRows (.refusal expected actual) = [] := by
  unfold RunResult.refusal; split <;> rfl

/-- Append the outcome rows of a finished run. -/
def close [Monad M] (result : RunResult × Tape) : RunM M (RunResult × Tape) :=
  fun log => pure (result, log ++ outcomeRows result.1)

/-- The runner read through the algebra: interpret the denotation under
`traceHandler`, then append the outcome rows. -/
def interpretRun [Monad M] {alphabet : FlowAlphabet Ty} (service : FlowService alphabet M)
    (nameOf : alphabet.Op → String) (program : Program (FullSig alphabet) (RunResult × Tape)) :
    RunM M (RunResult × Tape) :=
  interpret (traceHandler service nameOf) program >>= close

/-! ## T1: the runner is `interpret` of the fuelled denotation

One induction on fuel, generalised over block, environment, tape and log.

`Signature.sum` is a plain definition upstream, so `(FullSig a).Answer (.inl o)`
does not reduce to `Val` at the transparency `rw` and `simp` match at. The two
`rfl` lemmas below are therefore stated in the goal's own spelling: they are the
only place that reduction is needed. -/

theorem close_run [Monad M] (result : RunResult × Tape) (log : Effect4.Trace.Log) :
    (close (M := M) result).run log = pure (result, log ++ outcomeRows result.1) := rfl

theorem traceHandler_run_inl [Monad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (op : alphabet.Op) (request : Val) (log : Effect4.Trace.Log) :
    ((traceHandler service nameOf).handle (Sum.inl ⟨op, request⟩)).run log =
      service.handle op request >>= fun answer =>
        pure (answer,
          if service.pure op then log
          else log ++ [.op (nameOf op) request, .answer (nameOf op) answer]) := rfl

theorem traceHandler_run_inr [Monad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (site : DecisionId) (branch : Bool) (log : Effect4.Trace.Log) :
    ((traceHandler service nameOf).handle (Sum.inr (site, branch))).run log =
      pure ((), log ++ [.decide site.value branch]) := rfl

theorem interpretRun_pure [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (result : RunResult × Tape) :
    interpretRun service nameOf (.pure result) = close result := by
  simp [interpretRun, interpret]

theorem interpretRun_vis [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (operation : (FullSig alphabet).Op)
    (next : (FullSig alphabet).Answer operation → Program (FullSig alphabet) (RunResult × Tape)) :
    interpretRun service nameOf (.vis operation next) =
      (traceHandler service nameOf).handle operation >>= fun answer =>
        interpretRun service nameOf (next answer) := by
  simp [interpretRun, interpret, bind_assoc]

/-- Interpreting one alphabet operation: the service runs, and the two rows are
appended unless the operation is a pure atom. -/
theorem interpretRun_run_perform [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (op : alphabet.Op) (request : Val)
    (next : Val → Program (FullSig alphabet) (RunResult × Tape)) (log : Effect4.Trace.Log) :
    (interpretRun service nameOf (Program.vis (Sum.inl ⟨op, request⟩) next)).run log =
      service.handle op request >>= fun answer =>
        (interpretRun service nameOf (next answer)).run
          (if service.pure op then log
           else log ++ [.op (nameOf op) request, .answer (nameOf op) answer]) := by
  refine Eq.trans (congrArg (fun p : RunM M (RunResult × Tape) => p.run log)
    (interpretRun_vis service nameOf (Sum.inl ⟨op, request⟩) next)) ?_
  refine Eq.trans (StateT.run_bind _ _ _) ?_
  show (service.handle op request >>= fun answer =>
      (pure (answer,
        if service.pure op then log
        else log ++ [Effects.Trace.Event.op (nameOf op) request,
          Effects.Trace.Event.answer (nameOf op) answer]) : M (Val × Effect4.Trace.Log))) >>=
      (fun p => (interpretRun service nameOf (next p.1)).run p.2) = _
  rw [bind_assoc]
  exact bind_congr fun answer => pure_bind _ _

/-- Interpreting one decision: the branch the tape fixed is logged and the
answer is `()`. -/
theorem interpretRun_run_choose [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (site : DecisionId) (branch : Bool)
    (next : Unit → Program (FullSig alphabet) (RunResult × Tape)) (log : Effect4.Trace.Log) :
    (interpretRun service nameOf (Program.vis (Sum.inr (site, branch)) next)).run log =
      (interpretRun service nameOf (next ())).run (log ++ [.decide site.value branch]) := by
  refine Eq.trans (congrArg (fun p : RunM M (RunResult × Tape) => p.run log)
    (interpretRun_vis service nameOf (Sum.inr (site, branch)) next)) ?_
  refine Eq.trans (StateT.run_bind _ _ _) ?_
  show (pure ((), log ++ [Effects.Trace.Event.decide site.value branch]) :
      M (Unit × Effect4.Trace.Log)) >>= _ = _
  exact pure_bind _ _

/-- T1. The Flow runner, at every fuel, is `interpret` of the fuelled
denotation under the trace handler, closed by the outcome rows. -/
theorem loop_eq_interpretRun [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (raw : RawFlow Ty) (service : FlowService alphabet M) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log),
      (loop alphabet raw service nameOf fuel block env tape).run log =
        (interpretRun service nameOf (denoteFuel fuel raw block env tape)).run log := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape log
      simp [loop, denoteFuel, interpretRun_pure, close_run, outcomeRows, emit_run]
  | succ fuel ih =>
      intro block env tape log
      simp only [loop, denoteFuel]
      cases found : lookupBlock raw block with
      | none => simp [interpretRun_pure, close_run, outcomeRows, StateT.run_pure]
      | some current =>
          simp only []
          cases planned : plan alphabet current env tape with
          | stuck =>
              simp [step, planned, interpretRun_pure, close_run, outcomeRows]
          | ret value =>
              simp [step, planned, interpretRun_pure, close_run, outcomeRows, emit_run]
          | jump target env' =>
              simp only [step, planned, pure_bind]
              exact ih target env' tape log
          | exhausted site =>
              simp [step, planned, interpretRun_pure, close_run, outcomeRows, emit_run]
          | mismatch expected actual =>
              simp [step, planned, interpretRun_pure, close_run, outcomeRows_refusal]
          | perform op request target env' =>
              dsimp only
              refine Eq.trans ?_ (interpretRun_run_perform service nameOf op request
                (fun answer => denoteFuel fuel raw target (env' ++ [answer]) tape) log).symm
              simp only [step, planned, StateT.run_bind, StateT.run_lift,
                bind_assoc, pure_bind]
              refine bind_congr (m := M) fun answer => ?_
              cases pureOp : service.pure op with
              | false => simpa [emit_run] using ih target (env' ++ [answer]) tape _
              | true => simpa [emit_run] using ih target (env' ++ [answer]) tape log
          | choose site branch target env' rest =>
              dsimp only
              refine Eq.trans ?_ (interpretRun_run_choose service nameOf site branch
                (fun _ => denoteFuel fuel raw target env' rest) log).symm
              simp only [step, planned, StateT.run_bind, StateT.run_pure, emit_run, pure_bind]
              exact ih target env' rest _
          | performCatch op request target env' onError errorEnv =>
              dsimp only
              refine Eq.trans ?_ (interpretRun_run_perform service nameOf op request
                (fun answer => denoteFuel fuel raw target (env' ++ [answer]) tape) log).symm
              simp only [step, planned, StateT.run_bind, StateT.run_lift,
                bind_assoc, pure_bind]
              refine bind_congr (m := M) fun answer => ?_
              cases pureOp : service.pure op with
              | false => simpa [emit_run] using ih target (env' ++ [answer]) tape _
              | true => simpa [emit_run] using ih target (env' ++ [answer]) tape log

/-- T1 at the public face. -/
theorem runTape_eq_interpretRun [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (fuel : Nat) (flow : CheckedFlow alphabet) (service : FlowService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (runTape fuel flow service nameOf tape input).run log =
      (interpretRun service nameOf
        (denoteFuel fuel flow.erase flow.erase.entry [input] tape)).run log :=
  loop_eq_interpretRun flow.erase service nameOf fuel flow.erase.entry [input] tape log

/-! ## The log is a writer

Both summands only append, and what an operation appends does not depend on
what is already there. `interpret_log_append` lifts that from one operation to a
whole program; without it every case of a run-level receipt drags
`List.append_assoc` behind it, and a receipt taken from `[]` cannot be moved to
a run in progress. -/

/-- A handler into the run monad writes: what an operation appends does not
depend on the prefix already in the log. -/
def WritesLog [Monad M] {S : Signature.{u, 0}} (handler : Handler S (RunM M)) : Prop :=
  ∀ (operation : S.Op) (before log : Effect4.Trace.Log),
    (handler.handle operation).run (before ++ log) =
      (handler.handle operation).run log >>= fun result => pure (result.1, before ++ result.2)

/-- Both summands of the trace handler write. -/
theorem traceHandler_writesLog [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) :
    WritesLog (traceHandler service nameOf) := by
  intro operation before log
  cases operation with
  | inl operation =>
      obtain ⟨op, request⟩ := operation
      refine Eq.trans (traceHandler_run_inl service nameOf op request (before ++ log)) ?_
      refine Eq.trans ?_ (congrArg (fun z : M (Val × Effect4.Trace.Log) =>
        z >>= fun result => (pure (result.1, before ++ result.2) : M (Val × Effect4.Trace.Log)))
        (traceHandler_run_inl service nameOf op request log)).symm
      rw [bind_assoc]
      refine bind_congr fun answer => ?_
      rw [pure_bind]
      cases service.pure op <;> simp
  | inr operation =>
      obtain ⟨site, branch⟩ := operation
      refine Eq.trans (traceHandler_run_inr service nameOf site branch (before ++ log)) ?_
      refine Eq.trans ?_ (congrArg (fun z : M (Unit × Effect4.Trace.Log) =>
        z >>= fun result => (pure (result.1, before ++ result.2) : M (Unit × Effect4.Trace.Log)))
        (traceHandler_run_inr service nameOf site branch log)).symm
      rw [pure_bind, List.append_assoc]

/-- The log is a writer: running a program on a log already holding `before`
appends `before` to whatever the same program writes from `log`. -/
theorem interpret_log_append [Monad M] [LawfulMonad M] {S : Signature.{u, 0}}
    {handler : Handler S (RunM M)} (writes : WritesLog handler) {A : Type}
    (before : Effect4.Trace.Log) :
    ∀ (program : Program S A) (log : Effect4.Trace.Log),
      (interpret handler program).run (before ++ log) =
        (interpret handler program).run log >>= fun result => pure (result.1, before ++ result.2) := by
  intro program
  induction program with
  | pure value =>
      intro log
      show (pure (value, before ++ log) : M (A × Effect4.Trace.Log)) = _
      rw [show ((interpret handler (Program.pure value)).run log
          : M (A × Effect4.Trace.Log)) = pure (value, log) from rfl, pure_bind]
  | vis operation next ih =>
      intro log
      refine Eq.trans (StateT.run_bind _ _ _) ?_
      refine Eq.trans ?_ (congrArg (fun z : M (A × Effect4.Trace.Log) =>
        z >>= fun result => (pure (result.1, before ++ result.2) : M (A × Effect4.Trace.Log)))
        (StateT.run_bind (handler.handle operation)
          (fun answer => interpret handler (next answer)) log)).symm
      rw [writes operation before log, bind_assoc, bind_assoc]
      refine bind_congr fun result => ?_
      rw [pure_bind]
      exact ih result.1 result.2

/-- The receipt form: a run from any log is the run from `[]` with that log in
front. -/
theorem interpret_log_of_nil [Monad M] [LawfulMonad M] {S : Signature.{u, 0}}
    {handler : Handler S (RunM M)} (writes : WritesLog handler) {A : Type}
    (program : Program S A) (log : Effect4.Trace.Log) :
    (interpret handler program).run log =
      (interpret handler program).run [] >>= fun result => pure (result.1, log ++ result.2) := by
  simpa using interpret_log_append writes log program []

/-! ## The fuel-free denotation

The measure is lexicographic: `(tape.length, (raw.reachSet block).length)`. A
`choose` shortens the tape (`Tape.read_answered_length`, through `plan_shape`);
a `jump` or a `perform` travels a declared non-`choose` edge, and `CyclesWF`
makes the reachable set strictly smaller across such an edge. Admission enters
`denote` here and nowhere else. -/

/-- A `jump` leaves its block along a declared non-`choose` edge. -/
theorem edgeNoChoose_of_plan_jump {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {block : BlockId} {current : RawBlock Ty} (found : lookupBlock raw block = some current)
    {env : Env} {tape : Tape} {target : BlockId} {env' : Env}
    (planned : plan alphabet current env tape = .jump target env') :
    EdgeNoChoose raw block target := by
  have shaped := plan_shape alphabet current env tape
  rw [planned] at shaped
  exact ⟨current, List.mem_of_find?_eq_some found, lookupBlock_id found, shaped.1, shaped.2⟩

/-- A `perform` leaves its block along a declared non-`choose` edge. -/
theorem edgeNoChoose_of_plan_perform {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {block : BlockId} {current : RawBlock Ty} (found : lookupBlock raw block = some current)
    {env : Env} {tape : Tape} {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
    (planned : plan alphabet current env tape = .perform op request target env') :
    EdgeNoChoose raw block target := by
  have shaped := plan_shape alphabet current env tape
  rw [planned] at shaped
  exact ⟨current, List.mem_of_find?_eq_some found, lookupBlock_id found, shaped.1, shaped.2⟩

/-- A `performCatch` leaves its block along a declared non-`choose` edge: the
plain runner's service cannot fail, so the value edge is the only one it
travels. -/
theorem edgeNoChoose_of_plan_performCatch {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {block : BlockId} {current : RawBlock Ty} (found : lookupBlock raw block = some current)
    {env : Env} {tape : Tape} {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
    {onError : BlockId} {errorEnv : Env}
    (planned : plan alphabet current env tape
      = .performCatch op request target env' onError errorEnv) :
    EdgeNoChoose raw block target := by
  have shaped := plan_shape alphabet current env tape
  rw [planned] at shaped
  exact ⟨current, List.mem_of_find?_eq_some found, lookupBlock_id found, shaped.1, shaped.2.1⟩

/-- A `performCatch`'s *failure* edge is a declared non-`choose` edge too: a
caught failure continues in the graph rather than ending the run. -/
theorem edgeNoChoose_of_plan_performCatch_error {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    {block : BlockId} {current : RawBlock Ty} (found : lookupBlock raw block = some current)
    {env : Env} {tape : Tape} {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
    {onError : BlockId} {errorEnv : Env}
    (planned : plan alphabet current env tape
      = .performCatch op request target env' onError errorEnv) :
    EdgeNoChoose raw block onError := by
  have shaped := plan_shape alphabet current env tape
  rw [planned] at shaped
  exact ⟨current, List.mem_of_find?_eq_some found, lookupBlock_id found, shaped.1, shaped.2.2⟩

/-- A `choose` consumes exactly one tape entry. -/
theorem tape_length_of_plan_choose {alphabet : FlowAlphabet Ty} {current : RawBlock Ty}
    {env : Env} {tape : Tape} {site : DecisionId} {branch : Bool} {target : BlockId}
    {env' : Env} {rest : Tape}
    (planned : plan alphabet current env tape = .choose site branch target env' rest) :
    rest.length + 1 = tape.length := by
  have shaped := plan_shape alphabet current env tape
  rw [planned] at shaped
  exact shaped

set_option linter.unusedVariables false in
/-- The fuel-free denotation of an admitted flow, walked from `block`. -/
def denoteGo {alphabet : FlowAlphabet Ty} (raw : RawFlow Ty) (cycles : CyclesWF raw)
    (block : BlockId) (env : Env) (tape : Tape) : Program (FullSig alphabet) (RunResult × Tape) :=
  match found : lookupBlock raw block with
  | none => .pure (.frontier (.stuck block), tape)
  | some current =>
    match planned : plan alphabet current env tape with
    | .stuck => .pure (.frontier (.stuck current.id), tape)
    | .ret value => .pure (.done value, tape)
    | .jump target env' => denoteGo raw cycles target env' tape
    | .perform op request target env' =>
        .vis (.inl ⟨op, request⟩) fun answer : Val =>
          denoteGo raw cycles target (env' ++ [answer]) tape
    | .exhausted site => .pure (.frontier (.unansweredDecision site), tape)
    | .mismatch expected actual => .pure (.refusal expected actual, tape)
    | .choose site branch target env' rest =>
        .vis (.inr (site, branch)) fun _ => denoteGo raw cycles target env' rest
    | .performCatch op request target env' _ _ =>
        .vis (.inl ⟨op, request⟩) fun answer : Val =>
          denoteGo raw cycles target (env' ++ [answer]) tape
  termination_by (tape.length, (raw.reachSet block).length)
  decreasing_by
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (edgeNoChoose_of_plan_jump found planned))
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (edgeNoChoose_of_plan_perform found planned))
    · exact Prod.Lex.left _ _ (by have := tape_length_of_plan_choose planned; omega)
    · exact Prod.Lex.right _ (reachSet_length_lt_of_edge cycles
        (edgeNoChoose_of_plan_performCatch found planned))

/-- The denotation of an admitted flow against a decision tape. Admission is
used for exactly one thing: `CyclesWF`, the termination measure. -/
def denote {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet) (tape : Tape) (input : Val) :
    Program (FullSig alphabet) (RunResult × Tape) :=
  denoteGo flow.erase (erase_wf flow).cycles flow.erase.entry [input] tape

/-! ## T2: the allotted fuel is enough

`Effect4/Semantics/Fuel.lean` proved the budget invariant `LoopBudget` for the
runner. The denotation walks the same graph with the same tape, so the same
invariant carries the same induction; nothing about the pigeonhole is reproved
here. -/

/-- One layer of `denoteGo`, with the block already resolved. -/
theorem denoteGo_eq {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} (cycles : CyclesWF raw)
    {block : BlockId} {current : RawBlock Ty} (found : lookupBlock raw block = some current)
    (env : Env) (tape : Tape) :
    denoteGo (alphabet := alphabet) raw cycles block env tape =
      match plan alphabet current env tape with
      | .stuck => .pure (.frontier (.stuck current.id), tape)
      | .ret value => .pure (.done value, tape)
      | .jump target env' => denoteGo raw cycles target env' tape
      | .perform op request target env' =>
          .vis (.inl ⟨op, request⟩) fun answer : Val =>
            denoteGo raw cycles target (env' ++ [answer]) tape
      | .exhausted site => .pure (.frontier (.unansweredDecision site), tape)
      | .mismatch expected actual => .pure (.refusal expected actual, tape)
      | .choose site branch target env' rest =>
          .vis (.inr (site, branch)) fun _ => denoteGo raw cycles target env' rest
      | .performCatch op request target env' _ _ =>
          .vis (.inl ⟨op, request⟩) fun answer : Val =>
            denoteGo raw cycles target (env' ++ [answer]) tape := by
  rw [denoteGo]
  split
  · rename_i noBlock
    rw [found] at noBlock
    exact absurd noBlock (by simp)
  · rename_i other same
    rw [found] at same
    obtain rfl : current = other := Option.some.inj same
    split <;> rename_i planned <;> rw [planned]

/-- A non-`choose` step: the block just left joins the duplicate-free segment,
and `CyclesWF` keeps the target out of it. -/
theorem segmentBudget {raw : RawFlow Ty} {block target : BlockId} {tape : Tape}
    {visited : List BlockId} {fuel : Nat} {current : RawBlock Ty} (cycles : CyclesWF raw)
    (found : lookupBlock raw block = some current)
    (budget : LoopBudget raw block tape visited (fuel + 1))
    (edge : EdgeNoChoose raw block target) :
    LoopBudget raw target tape (block :: visited) fuel where
  nodup := List.nodup_cons.mpr ⟨budget.fresh, budget.nodup⟩
  fresh := by
    intro inSegment
    have reachBack : ReachableNoChoose raw target block := by
      rcases List.mem_cons.mp inSegment with eq | inVisited
      · cases eq; exact .refl _
      · exact budget.reaches target inVisited
    exact cycles block target edge reachBack
  declared := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mem_blockIds_of_lookup found
    · exact budget.declared x hx
  reaches := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .step (.refl _) edge
    · exact .step (budget.reaches x hx) edge
  covers := by
    have covers := budget.covers
    simp only [List.length_cons]
    omega

/-- A `choose` step: one tape entry is consumed, which buys back the whole
block table the restarted segment may spend. -/
theorem decisionBudget {raw : RawFlow Ty} {block target : BlockId} {tape rest : Tape}
    {visited : List BlockId} {fuel : Nat} {current : RawBlock Ty}
    (found : lookupBlock raw block = some current)
    (budget : LoopBudget raw block tape visited (fuel + 1))
    (consumed : rest.length + 1 = tape.length) :
    LoopBudget raw target rest [] fuel where
  nodup := List.nodup_nil
  fresh := List.not_mem_nil
  declared := fun _ hx => absurd hx List.not_mem_nil
  reaches := fun _ hx => absurd hx List.not_mem_nil
  covers := by
    have bound := budget.segment_lt found
    have covers := budget.covers
    have expand : (tape.length + 1) * raw.blocks.length
        = (rest.length + 1) * raw.blocks.length + raw.blocks.length := by
      rw [← consumed]
      simp [Nat.add_mul]
    simp only [List.length_nil]
    omega

/-- T2, generalised over the budget. Under `LoopBudget` the fuelled denotation
is already the fuel-free one: the fuel is never spent to zero. -/
theorem denoteFuel_eq_denoteGo {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (visited : List BlockId)
      (current : RawBlock Ty), lookupBlock raw block = some current →
      env.length = current.params.length →
      LoopBudget raw block tape visited fuel →
      denoteFuel (alphabet := alphabet) fuel raw block env tape
        = denoteGo raw wf.cycles block env tape := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape visited current found _ budget
      exfalso
      have bound := budget.segment_lt found
      have covers := budget.covers
      have pos : raw.blocks.length ≤ (tape.length + 1) * raw.blocks.length :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega
  | succ fuel ih =>
      intro block env tape visited current found sized budget
      have bound := budget.segment_lt found
      have mem : current ∈ raw.blocks := List.mem_of_find?_eq_some found
      have idEq : current.id = block := lookupBlock_id found
      have plannedSized := plan_checked wf mem sized tape
      rw [denoteGo_eq wf.cycles found]
      simp only [denoteFuel, found]
      generalize planEq : plan alphabet current env tape = p at plannedSized ⊢
      cases plannedSized with
      | ret value => rfl
      | exhausted site => rfl
      | mismatch expected actual => rfl
      | jump targetBlock foundTarget sizedTarget =>
          rename_i target env'
          have edge : EdgeNoChoose raw block target :=
            edgeNoChoose_of_plan_jump found planEq
          exact ih target env' tape (block :: visited) targetBlock foundTarget sizedTarget
            (segmentBudget wf.cycles found budget edge)
      | perform targetBlock foundTarget sizedTarget =>
          rename_i op request target env'
          have edge : EdgeNoChoose raw block target :=
            edgeNoChoose_of_plan_perform found planEq
          refine congrArg (@Program.vis (FullSig alphabet) (RunResult × Tape)
            (Sum.inl ⟨op, request⟩)) (funext fun answer => ?_)
          exact ih target (env' ++ [answer]) tape (block :: visited) targetBlock foundTarget
            (by simp [← sizedTarget]) (segmentBudget wf.cycles found budget edge)
      | choose targetBlock foundTarget sizedTarget =>
          rename_i site branch target env' rest
          have consumed : rest.length + 1 = tape.length := tape_length_of_plan_choose planEq
          refine congrArg (@Program.vis (FullSig alphabet) (RunResult × Tape)
            (Sum.inr (site, branch))) (funext fun _ => ?_)
          exact ih target env' rest [] targetBlock foundTarget sizedTarget
            (decisionBudget found budget consumed)
      | performCatch targetBlock errorBlock foundTarget sizedTarget foundError sizedError =>
          rename_i op request target env' onError errorEnv
          have edge : EdgeNoChoose raw block target :=
            edgeNoChoose_of_plan_performCatch found planEq
          refine congrArg (@Program.vis (FullSig alphabet) (RunResult × Tape)
            (Sum.inl ⟨op, request⟩)) (funext fun answer => ?_)
          exact ih target (env' ++ [answer]) tape (block :: visited) targetBlock foundTarget
            (by simp [← sizedTarget]) (segmentBudget wf.cycles found budget edge)

/-- T2. Given the fuel `fuelFor` allots (or more), the fuelled denotation is the
denotation. -/
theorem denoteFuel_eq_denote {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (tape : Tape) (input : Val) {fuel : Nat} (enough : fuelFor flow.erase tape ≤ fuel) :
    denoteFuel (alphabet := alphabet) fuel flow.erase flow.erase.entry [input] tape
      = denote flow tape input := by
  have wf := erase_wf flow
  have entry := wf.entry
  unfold EntryWF at entry
  cases found : lookupBlock flow.erase flow.erase.entry with
  | none => rw [found] at entry; cases entry
  | some current =>
      rw [found] at entry
      have sized : ([input] : Env).length = current.params.length := by rw [entry]; rfl
      exact denoteFuel_eq_denoteGo wf fuel flow.erase.entry [input] tape [] current found sized
        { nodup := List.nodup_nil
          fresh := List.not_mem_nil
          declared := fun _ hx => absurd hx List.not_mem_nil
          reaches := fun _ hx => absurd hx List.not_mem_nil
          covers := by simpa [fuelFor] using enough }

/-! ## The runner is `interpret` of the denotation -/

/-- T1 and T2 together: at the allotted fuel the runner is `interpret` of the
fuel-free denotation, closed by the outcome rows. -/
theorem runTape_eq_interpretRun_denote [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    {fuel : Nat} (flow : CheckedFlow alphabet) (service : FlowService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (enough : fuelFor flow.erase tape ≤ fuel) :
    (runTape fuel flow service nameOf tape input).run log =
      (interpretRun service nameOf (denote flow tape input)).run log := by
  rw [runTape_eq_interpretRun, denoteFuel_eq_denote flow tape input enough]

/-- The default run, read through the algebra. -/
theorem runDefault_eq_interpretRun_denote [Monad M] [LawfulMonad M] {alphabet : FlowAlphabet Ty}
    (flow : CheckedFlow alphabet) (service : FlowService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (runDefault flow service nameOf tape input).run log =
      ((·.1) <$> interpretRun service nameOf (denote flow tape input)).run log := by
  unfold runDefault run
  simp only [StateT.run_map]
  rw [runTape_eq_interpretRun_denote flow service nameOf tape input log (Nat.le_refl _)]

/-- The corollary D1 owes. The direct proof landed first as
`Effect4.Flow.runDefault_finishes` (`Effect4/Semantics/Fuel.lean`, the
`LoopBudget` invariant this packet also uses for T2); this is its name in the
denotation packet, and with T2 it says the denotation `runDefault` interprets is
the fuel-free one. -/
theorem runDefault_no_fuel_frontier {σ : Type} {alphabet : FlowAlphabet Ty}
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val)
    (log : Effect4.Trace.Log) (s : σ) :
    (((runDefault flow service nameOf tape input).run log).run s).1.1.exhausted = false :=
  runDefault_finishes flow service nameOf tape input log s

/-! The denotation lane's scoped simp set: the interpreter's two equations and
the rows a finished run appends. `scoped` keeps it opt-in (survey finding
L17). -/

attribute [scoped simp] interpretRun_pure interpretRun_vis close_run

end Effect4.Flow
