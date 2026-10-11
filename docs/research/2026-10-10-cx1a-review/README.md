# CX1a review: scope laws and retained cleanup

**The landed CX1a scope laws pass this independent review.**
The memo probe identifies an additional stored-state consumer of the context change.
Claude aligns that consumer in the working tree during this review; verification of that working change remains pending.
The delayed cleanup control passes, including capture of an allocated handle.

## Review checkpoint

- Reviewed commit: `f00008eeaef00b67fe93cfd0327754c9f42694ee`.
- Previous receipt: `ddab43db64c83bac44f0b83a952989825ae6aa43`, directory `docs/research/2026-10-10-cx-lexical-review`.
- Review branch: `codex/review-cx1a-scope`.
- Changed files: this directory only.
- Role: independent scope-law review and CX1b migration support.
- Evidence: Lean checks and a cycle-aware axiom gate, recorded by `verification.json` and the logs.
- Limits: no production repair, full sweep, TypeScript check, external-runtime comparison, merge, or push.

The review reuses the attached isolated worktree.
`source-diff.log` confirms that its production sources match the reviewed commit.
Two GPT-6.1 Sol reviewers inspect the scope laws and stored-state consumers independently.
They perform source review; the parent runs the retained probes and audit.

The bounded Claude session read verifies the primary checkout as its working directory.
Claude is migrating point admission, row-table transport, and the denotation arms.
The session reports remaining compilation errors during that migration.
This is work in progress, with no CX1b landing claimed.
`working-snapshot.json` records the inspected file hashes separately from the frozen build.

## Landed scope laws

`ScopeControls.lean` reads the actual laws in `src/Effect4/Laws/Program/Typed/Scope.lean`.
The concrete program forwards a parameter through a second definition.
The checks distinguish each body's parameters, the main program, and intermediate spine nodes.
They retain invalid-address and missing-premise controls.

`scopeParams_child` requires a program node at the parent address.
`scopeParams_below` also excludes a definition block.
`scopeParams_body` requires both the body path and its declaration.
A successful scope lookup alone does not prove node existence.
These are scope facts; they give no theorem about running a closure.

`Signature.withParams_param` now requires the outer operation to be outside the domain.
That premise excludes the earlier empty-list counterexample.
This review compiles the landed proof and a concrete reader, closing the earlier source-only verification limitation.
The law identifies the parameter and its normalized row; it does not provide parameter formation.

`Audit.log` records every declaration of the landed Scope module within `[propext, Quot.sound]`.
The recorded scope goals have no remaining planned-goal dependency.
The review controls pass the same audit separately.
This does not close `invoke_arm`, `param_arm`, or the typed-run claim during CX1b and CX2.

## Additional memo-state consumer

`storePre` in `src/Effect4/Laws/Program/Typed/Residual.lean` now reads a path's scope in the working tree.
Its changed branches are `memoGet`, `memoBuild`, and `memoComplete`.
`memo-premises.diff` retains the inspected change.

`LayerCellTyped` in `src/Effect4/Laws/Program/Typed/Adequacy.lean` reads the global source signature at the first inspection.
`MemoTableTyped` uses that condition for every stored entry.
`memo-owner.txt` retains the inspected definition.

The admitted program in `MemoControls.lean` builds an `effectDiscard` layer inside a parameterized definition.
That layer calls its parameter.
The global layer check refuses the call, while the signature extended by its parameter admits it.
A checked example proves that the old `LayerCellTyped` then holds for every world and cell.
Its failed checker premise makes it vacuous at this layer.
The closed-layer control confirms that the global check is not always refusing.

The practical consequence is a missing connection between the new memo preconditions and the stored cell's declared columns.
The affected consumers are `memoBuild_world`, `memoGet_implements`, and `memoComplete_implements`, all in `Typed/Adequacy.lean`.
This is a demonstrated migration obligation, not a landed runtime failure.

At the closing inspection, Claude changes `LayerCellTyped` to use `root.scopeSig layer`, matching the three memo-row checks.
`memo-owner-revised.diff` retains that change.
The session reports the corresponding three Adequacy failures before the edit, then starts another build.
This is a source-level resolution of the checker-input mismatch, pending an independently checked landing.
The retained probe records the old condition's vacuity at the pinned source.
That example must become a rejection control when the revised condition lands.
The known cross-scope reference issue remains separate.

Use one shared checked-layer judgment for the memo row preconditions and the memo-table invariant.
Its context must follow the chosen solution to the existing cross-scope reference issue.
Replacing the global signature with a path-derived signature alone does not resolve that issue.
When checking reused layer code in different parameter contexts, establish stable memo-cell columns or retain the necessary context evidence with the entry.
Do not infer equal columns from an equal code address.
The probe establishes only the mismatch between the two checker inputs; it does not choose a new memo-key representation.

## Cleanup after the invoking definition returns

`CleanupControls.lean` reuses the resource rows in `tools/TestSupport/AcquireHandle.lean`.
The main program acquires a handle and passes a closing program into a definition.
That definition registers cleanup and returns.
The main program then reads the handle, and its outer scope finally runs the retained closing program.

The fixed reply tape supplies acquisition, reading, and closing answers in that order.
The finite run returns the read value and retains the recorded allocation.
The program typing checker refuses the parameter's unit argument where the captured handle belongs.
Leaving the closing reply unanswered keeps the run at a live frontier with the allocation retained.

These checks exercise the stored parameter stack and caller environment through delayed cleanup.
They give CX1b a concrete acceptance program for `CaptureTyped` and its later-world consumers.
They do not prove arbitrary world extension, termination, outside-host agreement, or a general cleanup law.

## Smallest consolidation after the migration

The new `spineParams` follows the same body spine as `Part.bodyAt` in `src/Effect4/Program/Typing/Parts.lean`.
`Part.bodyAt_sig` in `src/Effect4/Laws/Program/Typing/Parts.lean` currently returns an unspecified parameter list.
A bridge could identify that list with the scope lookup:

```lean
Part.bodyAt sig decls bodies path = some (part, rest) →
  part.sig = sig.withParams (spineParams decls path)
```

This is a proposal, not a landed theorem.
Its concept is `initial-algebras-folds`; its property is the existing whole-program replacement connection.
Its proposed consumers are `Sketch.sigAt_extends` and agreement between editing and scope lookup, serving R14.
The premise is a successful part lookup at a body spine.
It establishes signature agreement only, with no claim about runtime redirects or host behavior.

Keep this law beside the existing part-signature law.
It should remove duplicated scope reasoning from editor and host-reader callers.
It should add no requirement to module authors.
Do not generalize it through `withDefs []` without the existing outside-domain premise for calls.

## Open items and next action

The prior cross-scope layer-reference counterexample remains open at this checkpoint.
The migration must keep normalized requests, expanded site programs, and formed parameter declarations.
The saved loop, generator, capture, and memo conditions must use the same context contract.
The substitution and bounded unfolding slices remain deferred; this review does not count them as regressions.

Before closing CX1b, verify the revised `LayerCellTyped` and its three consumers with the chosen context contract.
Then reuse these probes with the existing forwarding and fork controls.
Before closing CX2, audit the actual invocation and parameter proofs and their downstream dependency graph.

## Reproduction

Run the following in the isolated worktree:

```sh
python3 docs/research/2026-10-10-cx1a-review/verify.py
```

The script serializes the narrow build and the Lean probes with `LEAN_NUM_THREADS=3`.
The command logs and `verification.json` retain the exact commands, results, and source hashes.
`PLAN.md` places each checked obligation before its proof.

Captured diff context and the source excerpt retain their original whitespace.
`evidence-whitespace.log` records those findings.
`diff-check.log` checks every other staged file.
