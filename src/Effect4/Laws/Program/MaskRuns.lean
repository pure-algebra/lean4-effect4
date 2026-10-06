import Effect4.Laws.Machine.MaskRuns
import Effect4.Api

/-!
# Laws.Program.MaskRuns — the saved mask's chain along a run of a compiled program

`Laws/Machine/MaskRuns.lean` lifts the chain `FrameFiber.MaskChain` to runs of the fiber
machine. Its statements over a command take one premise on the evaluator, `EvaluatorKeepsMask`,
and its placed theorem `Machine.saved_mask_chain_runs` is at the frame evaluator `evaluatePrim`.

A run of a compiled program uses another evaluator. `Api.replay` (`src/Effect4/Api.lean`) runs
`replayEval` at the interpreter `interpOf program table`, under the instance
`evaluatorFor program table`, whose evaluation is `evaluateNative`
(`src/Effect4/Program/Compile.lean`). So the general form alone does not cover such a run. This
module gives the premise for that evaluator, and the lift at the compiled program's interpreter.

* **The native evaluator meets the premise** (`evaluateNative_keepsMask`). Its scoped entry
  writes the context and the code. Its scoped exit pops through `getCont`, which keeps the
  chain. Every other arm is `evaluatePrim` at the interpreter of the evaluation.
* **The lift at the compiled program's interpreter** (`compiled_mask_chain_runs`): each replay
  of a decision tape keeps the invariant `MaskRuns`, at a table of start flags that grows at
  its end. It is the placed statement.
* **The same at the program interface** (`Api.load_maskRuns`, `Api.replay_maskRuns`). A loaded
  machine holds the invariant at the table of its root. So does each machine that `Api.replay`
  reaches, at a table that starts with the root's flag. It takes no premise: no typing of the
  program, no check of the table and no admission of a decision.

Placement (AGENTS.md, Trust):

- concept `scope-lifetime-finalization` (`docs/core/semantics.md` §2.3), requirement R11. The
  proposed registry claim is `saved-mask-chain-runs`, and its pointer is
  `compiled_mask_chain_runs`. `Machine.saved_mask_chain_runs` is its general form, at the frame
  evaluator;
- reach: every program, row table, decision tape and fuel, at the native evaluator. A fiber is
  live while its `exit` is `none`;
- it does not establish the bracket of a region, a flag or a stack of an exited fiber as a state
  invariant, a cleanup's multiplicity, a delivery, a budget or liveness. It gives no agreement
  with a target and no law of a host. `Api.runSync` and the run API's journal have no statement
  here. An invariant is not progress;
- consumers: the bracket's law, then the waiting wrapper under a masked caller, Semaphore's
  protected permit and Pool's `use`, which read the law at the program interface.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 Effect4.Machine Effect4.FrameFiber

/-- **The native evaluator meets the evaluator's premise.** `enterScoped` writes the context and
the code. `exitScoped` pops through `getCont`, which keeps the chain (`getCont_maskChain`), and
then it writes the context and the code. Every other arm is `evaluatePrim` at the interpreter of
the evaluation (`evaluatePrim_keepsMask`).

A step of `compiled_mask_chain_runs`. It reads the three definitions of
`src/Effect4/Program/Compile.lean` as they stand. -/
@[semantics "scope-lifetime-finalization"]
theorem evaluateNative_keepsMask (root : NativeEff) (table : RowTable)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (y : Bool) :
    IterKeepsMask m f (evaluateNative root m f y table) := by
  unfold evaluateNative
  split
  · split
    · unfold enterScoped
      exact ⟨MaskAged.refl m, MaskLater.refl f, rfl, fun _ h => nomatch h⟩
    · exact evaluatePrim_keepsMask _ m f y
  · unfold exitScoped
    dsimp only
    split
    · split
      · exact ⟨MaskAged.refl m,
          ⟨rfl, fun live => live, fun _ base valid => getCont_maskChain base f.frame _ _ _ valid⟩,
          rfl, fun _ h => nomatch h⟩
      · split <;> exact ⟨MaskAged.refl m,
          ⟨rfl, fun live => live, fun _ base valid => getCont_maskChain base f.frame _ _ _ valid⟩,
          rfl, fun _ h => nomatch h⟩
    · exact evaluatePrim_keepsMask _ m f y
  · unfold exitScoped
    dsimp only
    split
    · split
      · exact ⟨MaskAged.refl m,
          ⟨rfl, fun live => live, fun _ base valid => getCont_maskChain base f.frame _ _ _ valid⟩,
          rfl, fun _ h => nomatch h⟩
      · split <;> exact ⟨MaskAged.refl m,
          ⟨rfl, fun live => live, fun _ base valid => getCont_maskChain base f.frame _ _ _ valid⟩,
          rfl, fun _ h => nomatch h⟩
    · exact evaluatePrim_keepsMask _ m f y
  · exact evaluatePrim_keepsMask _ m f y

/-- **Each live fiber of a run of a compiled program holds the saved mask's chain at its start
flag** (the proposed registry claim `saved-mask-chain-runs`; concept
`scope-lifetime-finalization`, requirement R11). It is the placed statement of the claim: the
lift of `saved_mask_pop_discipline` to runs, at the compiled program's interpreter
`interpOf root table` and under the native evaluator `evaluatorFor root table`. A printed form
of the statement hides that instance.

Its general form is `Machine.saved_mask_chain_runs`, at the frame evaluator. This statement is
`Machine.replayEval_maskRuns` at the native evaluator's premise `evaluateNative_keepsMask`.

Reach: every program, row table, decision tape and fuel, from each machine that holds the
invariant. It asks for no typing, no admission and no premise on the table.

It does not establish the bracket of a region, a flag or a stack of an exited fiber as a state
invariant, a cleanup's multiplicity, a delivery, a budget or liveness. An invariant is not
progress.

Its consumers are the bracket's law, then the waiting wrapper under a masked caller,
Semaphore's protected permit and Pool's `use`. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem compiled_mask_chain_runs (root : NativeEff) (table : RowTable) (fuel : Nat)
    (tape : List (RunDecision EffName EffThunk Val Err Defect FiberId Ann)) (bases : List Bool)
    (m : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (kept : MaskRuns bases m) :
    ∃ bases', bases <+: bases' ∧ MaskRuns bases'
      (replayEval (evaluator := evaluatorFor root table) (interpOf root table) fuel tape
        m).machine :=
  letI := evaluatorFor root table
  replayEval_maskRuns (interpOf root table) (fun m f y => evaluateNative_keepsMask root table m f y)
    fuel tape bases m kept

end Effect4.Program

namespace Effect4.Api

open Effect4 Effect4.Machine Effect4.Program

/-- **A loaded machine holds the invariant at the table of its root.** `Api.load` starts the root
at flag true, over an empty stack. A step of `replay_maskRuns`. -/
@[semantics "scope-lifetime-finalization"]
theorem load_maskRuns (program : Program) (compileFuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) :
    MaskRuns [true] (load program compileFuel answers) := by
  refine ⟨rfl, ?_⟩
  intro f mem
  have same := List.mem_singleton.mp mem
  subst same
  exact ⟨true, rfl, fun _ => rfl⟩

/-- **Each machine that `Api.replay` reaches holds the invariant**, at a table that starts with
the root's flag. So each of its live fibers holds the chain at its start flag. It is
`compiled_mask_chain_runs` at the loaded machine, and it takes no premise: `Api.replay` is the
raw entry, which types no program and checks no table.

Its consumers read the law at the program interface: the bracket's law, then the protected
permit and Pool's `use`. It states nothing of `Api.runSync`, whose flush of the root's dispatcher
is no decision of a tape. -/
@[semantics "scope-lifetime-finalization"]
theorem replay_maskRuns (program : Program) (fuel : Nat) (tape : List Decision)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (compileFuel : Nat) :
    ∃ bases, [true] <+: bases ∧
      MaskRuns bases (replay program fuel tape answers table compileFuel).machine := by
  have reached := compiled_mask_chain_runs program table fuel tape [true]
    (load program compileFuel answers) (load_maskRuns program compileFuel answers)
  unfold replay
  split
  · rename_i m result
    rw [result] at reached
    exact reached
  · rename_i why m result
    rw [result] at reached
    exact reached
  · rename_i why m result
    rw [result] at reached
    exact reached

end Effect4.Api
