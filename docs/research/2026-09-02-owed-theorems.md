# The two theorems the trace lane owed

Worktree `.claude/worktrees/agent-a7d1f74bf61e7c52b`, branch
`worktree-agent-a7d1f74bf61e7c52b`, base `5e349d8`, merged `12b8ad2`
(P-T9b/P-T11). Nothing committed.

## 1. The allotted fuel always suffices — proved

`Effect4/Semantics/Fuel.lean`, a new module imported by `Effect4.lean` beside
`Effect4.Semantics.Runs`.

`fuelFor raw tape = (tape.length + 1) * raw.blocks.length + 1`. Its docstring
argued informally that between two decisions no block repeats. The argument is
now the `LoopBudget` invariant carried through `loop`:

```
structure LoopBudget (raw) (block) (tape) (visited) (fuel) : Prop where
  nodup     : visited.Nodup
  fresh     : block ∉ visited
  declared  : ∀ x ∈ visited, x ∈ raw.blocks.map RawBlock.id
  reaches   : ∀ x ∈ visited, ReachableNoChoose raw x block
  covers    : (tape.length + 1) * raw.blocks.length + 1 ≤ fuel + visited.length
```

`visited` is the segment of blocks already stepped through since the last
decision. `LoopBudget.segment_lt` turns `nodup`, `fresh` and `declared` into
`visited.length + 1 ≤ raw.blocks.length` — the segment can never have walked
every declared block. That single inequality pays for both moves:

* a non-`choose` step spends one fuel and appends the current block to
  `visited`, so `covers` is preserved verbatim. Freshness of the new block is
  where `CyclesWF` enters: the step produces `EdgeNoChoose raw block next`, and
  if `next` were already in `block :: visited` the invariant would hand back
  `ReachableNoChoose raw next block`, which `wf.cycles` refuses;
* a `choose` step consumes one tape entry and resets `visited` to `[]`. The
  budget drops by a whole `raw.blocks.length`, and `segment_lt` says the reset
  gives back at least that much minus one.

At `fuel = 0` the invariant is contradictory, so the fuel frontier is
unreachable.

Two new lemmas feed it: `plan_shape` (a `jump`/`perform` plan travels a
declared non-`choose` successor edge, a `choose` plan consumes exactly one tape
entry — what `PlanSized` forgets, and needing no well-formedness) and
`step_progress` (the same, read off one step over `StateT σ Id`).

**Statement proved** (exactly the one asked for):

```lean
theorem run_fuelFor_finishes {σ : Type} {alphabet : FlowAlphabet Ty}
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val)
    (log : Effect4.Trace.Log) (s : σ) :
    (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s)
      .1.1.exhausted = false
```

Three cheap corollaries: `runDefault_finishes`; `run_fuel_ge_finishes` (any
larger fuel also finishes, by `run_fuel_mono`); and

```lean
theorem run_fuelFor_answered … :
  (∃ value, result = .done value) ∨
  (∃ site,  result = .frontier (.unansweredDecision site)) ∨
  (∃ expected actual, result = .refused expected actual)
```

— with `run_checked_not_stuck` and `run_not_failed`, an admitted run at the
allotted fuel ends in exactly one of three ways. **The tape, not the fuel, is
the only remaining live frontier.** `run_not_failed` had to be proved along the
way: the P-T7 merge added `RunResult.failed` for the region runner, and the
plain runner's `step` has no shape that produces it.

Nothing was reformulated away from the brief; the work is stated on `loop`
under `LoopBudget` and specialised to `run`, as the brief anticipated.

### Axioms

```
Effect4.Flow.lookupBlock_id                 [propext]
Effect4.Flow.mem_blockIds_of_lookup         [propext, Quot.sound]
Effect4.Flow.plan_shape                     [propext]
Effect4.Flow.step_progress                  [propext, Quot.sound]
Effect4.Flow.LoopBudget.segment_lt          [propext, Quot.sound]
Effect4.Flow.loop_budget_not_exhausted      [propext, Quot.sound]
Effect4.Flow.loop_fuelFor_not_exhausted     [propext, Quot.sound]
Effect4.Flow.run_fuelFor_finishes           [propext, Quot.sound]
Effect4.Flow.runDefault_finishes            [propext, Quot.sound]
Effect4.Flow.run_fuel_ge_finishes           [propext, Quot.sound]
Effect4.Flow.step_not_failed                [propext, Quot.sound]
Effect4.Flow.loop_not_failed                [propext, Quot.sound]
Effect4.Flow.run_not_failed                 [propext, Quot.sound]
Effect4.Flow.run_fuelFor_answered           [propext, Quot.sound]
```

`List.Nodup.length_le_of_subset` is in scope but carries `Classical.choice`, so
the pigeonhole step is reproved by structural induction, as `Effects.RawFlow`
does privately for its own saturation bound.

## 2. The structured form agrees with the dispatch form — half proved

`Effect4/Target/TypeScript/StructureLaws.lean`.

`TypeScript.Structure.emitWith` is owned by the pinned package, so its laws are
stated in Effect4 over its definitions and Effect4's `structuredShapes`. The
property is label well-scoping: `wellScoped blocks loops` (a mutual structural
recursion over `Stmt`, `List Stmt` and the `switch` arms, exactly as the
package's own `BEq` is) says every `break l` sits inside a `label l:` and every
`continue l` inside an `l: while (true)`; `scopedGen` is a function boundary and
resets both scopes.

**Proved**:

```lean
theorem emitWith_wellScoped {g : Structure.Graph} {body}
    (closed : GraphClosed g) (scopedBody : BodyScoped body) {out}
    (emitted : Structure.emitWith g structuredShapes body = some out) :
    wellScopedList (blockLabels g) [] out = true
```

Read: **every `continue l` is inside its `while l`; every `break l` names a
block label of the graph.** The `continue` half is outright; the `break` half is
proved only up to naming, and the permissive initial block list is where the gap
sits, visibly.

Both hypotheses are discharged for Effect4's own lowering, so nothing hangs:
`graphOf_closed` (successors of `Flow.graphOf` are `position`s, hence in range)
and `lowerBlockWith_wellScoped` (`lowerBlockWith` emits a `return`, a `const`, a
`let`, an `if` and parameter moves, and reaches the transfers only through
`transfer`). Together:

```lean
theorem structuredBody_wellScoped (rows) (table) (blocks) (entry) {out}
    (emitted : Flow.structuredBody rows table blocks entry = some out) :
    wellScopedList (blockLabels (Flow.graphOf blocks entry)) [] out = true
```

### Why the `continue` half is reachable and the `break` half is not

`Structure.dominates g a b` is *defined* as a fuel-bounded walk from `b` up the
`idom` chain looking for `a`, and that is the same chain `emitNode`'s recursion
descends. So the guard `emitNode` puts on every `continue` is exactly the fact
the proof needs, and no theorem about what dominance *means* is required — nor
is `reducible g`. `dominates_step` and `dominates_entry` are the whole of it.

A `break L<t>` is different. It is in scope only if `t` is a merge child of some
ancestor `a` of the current node **and** `t` is folded after the child of `a` on
the path down. That needs (1) `Structure.idom t` to lie on the `idom` chain of
every predecessor of `t` — correctness of the Cooper–Harvey–Kennedy iteration in
`Structure.idoms` — and (2) a forward edge's target to come later in
`Structure.rpo` than its source. Both are properties of `typescript`-package
algorithms Effect4 cannot edit and cannot derive without verifying.
`BreakScopedStatement` records the exact remaining statement
(`wellScopedList [] []`).

### That this is the defect's half, and receipts for the other

Row `E4-TARGET-CE-013` was an entry that is its own loop header emitted without
a wrapping loop, leaving `continue W0` unbound. `emitWith_wellScoped` is false
for that emission: the base case of the induction supplies the entry's loop
scope from precisely the `if isLoopHeader g g.entry then [shapes.loop …]`
wrapper.

`Effect4Test/Target/TypeScript/StructureLawsContract.lean` pins the predicate
both ways (`label W1: { continue W1 }` is refused) and runs the *strict*
predicate `wellScopedList [] []` — which demands the enclosing `label` — on the
swap loop, the label-free chain and an entry-loop-header flow: finite evidence
for the `break` half on the packet's own graphs.

### The agreement theorem itself

Out of reach here, and its exact statement is written into
`test/contracts/flow-structured-lowering.contract.md`: a control-flow
interpreter `exec` over the emitted statement skeleton with a label stack, node
bodies abstracted to `step : Nat → Choice → Option Nat`, a marker statement per
node, and the claim that `exec (emitWith …)` produces the same node sequence as
the graph walk `Effect4.Flow.loop` produces. Its proof needs (1) and (2) above
as well — a `break L<t>` must be shown to *land* at `t` — plus the interpreter
and its unwinding lemmas. The well-scoping law is its first half.

### Axioms

```
Effect4.Target.Structured.wellScoped                    [propext]
Effect4.Target.Structured.wellScopedList                [propext]
Effect4.Target.Structured.wellScopedList_append         [propext]
Effect4.Target.Structured.wellScopedList_of_forall      [propext]
Effect4.Target.Structured.dominates_step                [propext]
Effect4.Target.Structured.dominates_entry               [propext]
Effect4.Target.Structured.mem_succs_of_mem_preds        [propext, Quot.sound]
Effect4.Target.Structured.exists_pred_of_transferTarget [propext, Quot.sound]
Effect4.Target.Structured.lt_size_of_transferTarget     [propext, Quot.sound]
Effect4.Target.Structured.loops_of_child                [propext]
Effect4.Target.Structured.emitNode_wellScoped           [propext, Quot.sound]
Effect4.Target.Structured.mem_blockLabels               [propext, Quot.sound]
Effect4.Target.Structured.emitWith_wellScoped           [propext, Quot.sound]
Effect4.Target.Structured.paramMove_wellScoped          [propext, Quot.sound]
Effect4.Target.Structured.graphOf_closed                [propext, Quot.sound]
Effect4.Target.Structured.lowerBlockWith_wellScoped     [propext, Classical.choice, Quot.sound]
Effect4.Target.Structured.structuredBody_wellScoped     [propext, Classical.choice, Quot.sound]
```

The emission law is `String`-free and at the ceiling. The two exceptions are the
discharges whose *statements* name `Flow.lowerBlockWith` and
`Flow.structuredBody`; those already reach `Classical.choice` through Lean's
UTF-8 folds (they spell `a<block>` and compare TypeScript type names), so a
theorem about their output inherits it. They are admitted by **exact
declaration**, not by module, in `Effect4Test/Audit/AxiomGate.lean`, whose
staleness check drops the entry the day it is no longer needed. Also reproved by
hand: `List.findIdx?`'s range bound.

## Commands and results

```
lake build Effect4                                                  green (119 jobs)
lake env lean Effect4Test/Flow/RunnerContract.lean                  green
lake env lean Effect4Test/Flow/RunnerAxiomReport.lean               green
lake env lean Effect4Test/Counterexamples/Flow/Runner.lean          green
lake env lean Effect4Test/Target/TypeScript/StructuredLowerContract.lean    green
lake env lean Effect4Test/Target/TypeScript/StructureLawsContract.lean      green
lake env lean Effect4Test/Target/TypeScript/StructureLawsAxiomReport.lean   green
lake env lean Effect4Test/Audit/AxiomGate.lean                      green
./scripts/test-trust-gate.sh                                        PASS (exit 0)
```

`lake build Effect4Test` stops at `Effect4Test.Protocol.ByteParserContract`,
red on the merge base too (verified by stashing this work) and declared in
`test/fixtures/trust-gate/known-red.txt` with
`Effect4Test.Concurrency.RaceRepresentativeContract`; the gate excises both.

The gate was run twice. The first run earned its keep: it rejected a
`structuredStmts` helper in the new battery — a *test* declaration reaching
`Classical.choice` because it wrapped `Flow.lowerStructured`. The wrapper was
removed and the second run passed.

## What remains

| Obligation | Where |
| --- | --- |
| `BreakScopedStatement` — every `break L<t>` inside `label L<t>:` | needs `Structure.idoms` and `Structure.rpo` correctness in `lean4-typescript` |
| structured/dispatch trace agreement | needs the interpreter above, plus the same two package facts |
| `Effect4Test.Protocol.ByteParserContract` red | pre-existing on the merge base; unrelated to this work |
