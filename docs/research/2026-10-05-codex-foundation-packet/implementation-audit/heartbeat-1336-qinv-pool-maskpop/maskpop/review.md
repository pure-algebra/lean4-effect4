# MASKPOP battery and PUB receipt review

No new actionable mismatch appears in the frozen sources or retained outputs.
MASKPOP has its local proof, battery, and documentation on its branch.
Its final receipt and main-line integration remain pending at this cut.
PUB's final receipt is merged and preserves its proof boundaries.

## Frozen scope

MASKPOP is `e925a8d6c6d497b6e4d44dd04c399a0f4fd5e371` in `/Users/pooks/Dev/lean4-effect4-qsteps`.
Main is `d4ea8243826e2d5e5b3750007df009d80c4b8741`.
The active edit to MASKPOP's design note is excluded.
The monitor runs file comparisons and saved-log parsing only.
It executes no project command, Lean, compiler, runtime, or generator.

## MASKPOP delta

The law module is byte-identical to the reviewed proof commit `12d7703d`.
The six statements, fixed base, alternating restoring frames, universes, and empty-scratch premise therefore remain unchanged.
Commit `86335bd1` adds `Test.Machine.MaskDiscipline` and its required `Test.All` import.
Commit `e925a8d6` adds the architecture row and role.

The battery uses actual `FrameFiber` operations at the `Nat` alphabets.
It covers the brief's five positive rows: empty stacks, restoring frames, nested chains, pending causes, and masking finalizers.
The nested and finalizer controls observe continuation stopping, pushed-frame order, and the resulting flag and stack.
An existing `popFrom_asyncFinalizer_pops_its_push` theorem supplies the named visit-order instance.

The finite sweep pins 4,681 stacks and 22,408 chain-satisfying states.
Its domain has depth at most four over eight chosen frames, both flags and bases, and pending/deferred interrupt choices.
It checks both demands, both skip choices, carried causes, frame exit, and both entries.
These are constructed states; this battery does not establish their reachability.

Five red classes target the intended properties.
They remove a restoration hook, omit a finalizer's restoring frame, vary the base, remove alternation, or remove the scratch premise.
The retained mutation run additionally rejects all 77 changed commands, with no errors outside those commands.
This is saved seat evidence, not a monitor rerun.

The battery pins all six theorem fields, its polymorphic signature, axioms, and derived `proved` status with zero next goals.
Saved narrow build: 198 jobs, success.
Saved final default build: 992 jobs, success; 742 modules and 87,797 declarations pass the axiom and closure checks.
It reports 24 planned goals and 11 dependents, with no other declaration reaching `sorryAx`.
The displayed build counts belong to this seat's base; they are not a comparison with newer main.
Saved documentation checks pass; the wrong-path control fails at the changed row.

No MASKPOP receipt exists in the frozen seat commit.
That commit is not an ancestor of frozen main.
The main registry consequently still describes the helper as proposed; coordinator integration owns that update.

## Next connection, already outside this slice

The next consumer is the R11 run-level part of `saved-mask-restoration`, through `Machine.Lift`.
Reuse `StepKeeps`, `driveState_lift`, and then the applicable `DecisionLift` and replay rules in `src/Effect4/Laws/Machine/Lift.lean`.
The concrete missing premise relates each fiber's base and chain to its pending commands and externally initiated edits.
An unrestricted predicate over every fiber and arbitrary command is not established.

`frameExitState_maskChain` supplies the frame-exit boundary.
`ensure_maskChain` covers hook pushes, and `passPushed_ensure_stack_nil` supplies the empty-scratch fact needed by the recursive pop.
The latter is a reusable frame equation; its possible move into `Machine/Frames.lean` remains a coordinator choice.

The eventual observation is the chain at the same base, then flag equality when the relevant stacks agree.
A positive control should follow an admitted region entry through its exit boundary.
A red control should retain the forbidden arbitrary-command case at `Cmd.exitDone`.
Completed exits, whole brackets, cleanup multiplicity, delivery, budget sufficiency, and liveness remain excluded.
No new proof or parallel implementation is proposed here.

## PUB receipt

`040fde77` adds only `docs/research/2026-10-06-seat-PUB-receipt.md` over `1d10d8aa`.
That receipt is byte-identical through merge `bc0ee4c1` and frozen main.
Six engine and face files remain identical to the previously reviewed `f9f24092` versions.
The new default concepts label the two Laws modules; they do not establish new semantic properties.

The receipt correctly states seven one-store-step attempt laws and five typing statements.
It retains `FirstProfile`, `Requested`, injective-table, capture, `MessageTy`, and caller-term premises.
It explicitly leaves whole-run agreement and the shared wrappers' own typing statements open.
The string-literal and hint-type restrictions remain visible.
Its host comparison retains first-sight numbering and the recorder's late-observer limit.

Saved final evidence matches the receipt: 990-job build; 1,754 passing engine lines, zero failures, and 47 Queue checks.
Saved truth generation reports 52 agreeing programs and one signed divergence.
The truth, cases, fixture-generation, and documentation logs report success.
These are retained seat runs, not new monitor executions.
Lean-to-engine evidence remains the five finite root-exit comparisons reviewed earlier.
Full Fast-versus-Ref report equality is a separate comparison.
The receipt states no general compiler, host, scheduling, or public-wrapper theorem.
