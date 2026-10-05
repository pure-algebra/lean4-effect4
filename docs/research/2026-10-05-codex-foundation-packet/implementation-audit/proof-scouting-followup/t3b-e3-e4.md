# T3b E3/E4 bounded source review

No new actionable defect was found in the reviewed committed path.

## Scope and evidence

The worktree is `/Users/pooks/Dev/lean4-effect4-t3b`.
The reviewed range starts at `0ab2ef09` and ends at `7c678efaf5645270830d622f541d1b936a380d6c`.
E3 is `e112352f587e52b2ae3ccd2b88719d06ab067f0b`.
E4 is `861397bf0f927e90eff500cfb137bc95da984644`; `7c678efa` is the following coordinator merge.

This is source reading, supported by retained commit receipts. No build, generator, model, or runtime probe was run.
The active F edits in `Test/Dogfood/P4RateLimiter.lean` and `ocaml/engine/test/test_engine.ml` are excluded.

The brief and design are `docs/research/2026-10-04-claude-lead/state-any-type-plan.md`, T3b, and `docs/research/2026-10-04-seat-T3b-design.md`.
The detailed E3 and E4 commit messages provide the retained receipts.

## Checked source path

1. `NativeOp.binder?`, `ScopedOp NativeOp`, and `NativeOp.syncOpOf` in `src/Effect4/Program/Native.lean` use one binder at the current environment length.
   The request remains in the outer environment. All eight store operations receive the carried term and the exact captured environment.
   `Test/Program/ScopedOpContract.lean` checks capture, binder level, weakening, and a deliberately incorrect weakening.

2. `bindTerm_keeps` in `src/Effect4/Laws/Program/Template.lean` preserves every existing request binding.
   `bindTerm_termMaps` in `src/Effect4/Laws/Program/Typed/Denotation.lean` requires `EnvTyped`, successful term binding, and equivalent declared cell types.
   It uses `termMaps_of_typed` with the extended world and current cell value.
   The seed binding for A remains unchanged when the result match derives B.
   `syncRow_typed` now receives `EnvTyped` explicitly and constructs the operation with that environment.
   The modify result and replacement cell are assigned to the correct columns.
   The missing-A branch uses uninhabitance of `never`; it does not establish progress from an inhabited missing binding.

3. `syncOpOf_keys` in `src/Effect4/Laws/Program/Handles/Term.lean` bounds operation handles by request handles plus captured handles.
   Its consumer `compileEff_keys` in `src/Effect4/Laws/Program/Handles/Compile.lean` joins the request bound with `Point.env_keys_subset`.
   Captured handles are therefore included in the compiled-path invariant.

4. `ocaml/engine/externs.txt` declares `SyncOp.env` as the environment carrier `E.t`.
   `sh_ref_step` in `ocaml/engine/tools/api_engine_prelude.ml` evaluates the term at `E.snoc env a`.
   `ts/eff/read.ts` and `ts/eff/ingest/ck.ts` independently move the face's current-value variable to the node's environment length.
   Both remain bounded by the admitted face table.

## Retained verification and limits

`pRefUpdateCapture` and `pRefUpdateLevel` in `Test/Program/CompileContract.lean` retain expected values 15 and 6.
The wrong in-scope level yields 11; the out-of-scope level is refused by typing and yields unit in the untyped execution control.
E4 records the same controls on both generated OCaml engine carriers.

E3 records a successful Lean build and axiom gate.
E4 records successful Lean, OCaml, TypeScript, generator, target, and reader-corpus checks.
These are retained author receipts, not independently repeated verification.

The design explicitly retains T5 work for arbitrary term printing, binder-term annotations, and known prelude shape limits.
The current source review makes no universal generated-TypeScript execution claim.
No repair is proposed from this bounded review.
