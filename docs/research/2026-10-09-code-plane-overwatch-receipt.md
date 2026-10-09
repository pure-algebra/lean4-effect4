# Generated TypeScript module overwatch

Fix the shared type-only builtin inventory before treating the new emitter as usable for string-map answers.
The emitter imports `Readonly` and `Record` from a prelude that exports neither name.
A caller returning an empty or populated map therefore fails target compilation.

## Checkpoint and ownership

Previous main review: `4a596d5bbcda7d38964735a250471a014484e1a1`.
Reviewed main: `82f199b7017e2b4c72880b4fc754b56d01508724`.
The relevant landing is `2688f310`, the code plane and generated module emitter.
The review branch is `codex/overwatch-code-plane`, in the attached `module-design-review` worktree.
The `codex/authoring-branches` implementation remains at `0e4f21d1`, outside the reviewed main history.
Its earlier TypeScript branch and form-selection checks remain separate evidence.

The primary changes since the previous review concern the view, generated code and documentation.
No library module, core program declaration, shared step law or form table changes in that range.
The current rulings in rows 330, 331, 332, 335 and 336 retain their existing scope.
The known Channel, handle-header and CK reader findings remain unchanged.
This receipt does not repeat them as new findings.

The bounded Claude session read confirms its repository and current visual styling task.
Its session is `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50`.
The read excludes internal thinking fields.
Claude edits the look, motion and output paths during this review.
Those working changes remain separate from the pinned landing.
This review changes no production file, owner ruling or implementation session.
No full sweep, merge, push or message to Claude runs.

## CP-01: map answers produce invalid imports

`Types.ofNormalized` in `src/Effect4/Codegen/Types.lean` prints string maps as `Readonly<Record<string, value>>`.
`SourceBindings.builtins` in `src/Effect4/Codegen/SourceBindings.lean` omits both utility types.
`freeNames` and `importsOf` in `tools/Tools/Code/Module.lean` therefore treat both as unresolved prelude imports.
The same omissions make the structured module's binding check refuse it.

The finite probe generates five callers through the real `generate` function.
Scalar, map lookup and map keys callers pass target compilation.
Empty-map and populated-map answers produce four `TS2305` diagnostics.
A copied-output control removes only the two utility-type imports.
All five copied callers then pass the same strict compiler check.
The program bodies and answer annotations remain byte-identical in that control.
The production source stays unchanged.

The smallest repair adds both names as type-only globals in the shared binding inventory.
Keep value-space uses and shadowing subject to their existing checks.
Add map-answer controls to the module emitter and shared binding battery.
Do not patch the emitter with another independent list of global names.

A normal authoring caller already reaches the affected answer column:

```lean
Authoring.succeed
  (Authoring.mapSet Authoring.mapEmpty (Authoring.str "k") (Authoring.nat 7))
```

## CP-02: the generated check label exceeds its evidence

`generate` invokes `admitModule` on the structured module before `moduleText` renders it.
It discards the reconstructed program and reports that the module reads back to its original program.
The generated header and driver index also describe the module as written.
This call alone checks neither emitted-text parsing nor equality with the original input.
The relevant paths are `tools/Tools/Code/Module.lean` and `tools/Drivers/Emit.lean`.

The independent finite probe compares reconstructed programs with their inputs on the existing corpus.
All seven admitted programs match their inputs.
The existing `pScope` refusal remains, as the landing receipt records.
No accepted wrong-program example is found.
The smallest wording repair labels structured-module admission directly.
A stronger claim must retain an explicit input-equality check and separately identify emitted-text parser evidence.

## CP-03: layout recovery permits different tokens

`undo_layout` in `tools/Tools/Code/Doc.lean` reconstructs flat text from retained break metadata.
An arbitrary `Doc.line` may hold different non-whitespace text in its two alternatives.
The retained counter-control has flat text `a + b` and laid-out text `a -\nb`.
Its metadata still undoes to `a + b`.
The theorem remains valid; the document's whitespace-only summary needs a narrower domain.

The reviewed TypeScript builders retain their punctuation at breaks.
No actual TypeScript layout defect is found.
Scope that summary to those builders, or state a separate token-preserving break predicate with an actual consumer.
Do not silently strengthen the generic theorem.
`Ts.flat_expr` still connects the existing TypeScript expression representation to the pinned house printer.
The formatter introduces no second program representation.
The isolated `ifCase` change uses ordinary calls and arrows, requiring no new formatter case.

## Reproduced evidence and limits

The evidence directory is `docs/research/2026-10-09-code-plane-overwatch/`.
`checkpoint.json` records reviewed commits, source hashes, current findings and unchanged boundaries.
`Probe.lean` contains the five callers, corpus equality checks and layout counter-control.
`check-target.py` reproduces the target failure and copied-output control without installing packages.
The replay folder retains its second run and exact compiler inputs.

| Check | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Tools.Code.Module` | Passes, 163 jobs |
| `LEAN_NUM_THREADS=3 lake env lean --run Probe.lean OUT/target` | Five callers, seven admitted corpus equalities and the custom-break controls run |
| Original generated map files | Four `TS2305` diagnostics under tsgo `7.0.0-dev.20260629.1` and Effect `4.0.0-rc.112` |
| Copied import-only control | All five callers compile with strict checking and unused-name checks |
| Replay script | Reproduces the same failure and positive control |
| Two independent GPT-6.1 Sol reviews | Inspect imports and proof scope separately; parent reproduces their concrete probes |

From the review worktree, with a fresh output directory:

```sh
LEAN_NUM_THREADS=3 lake env lean --run docs/research/2026-10-09-code-plane-overwatch/Probe.lean OUT/target
python3 docs/research/2026-10-09-code-plane-overwatch/check-target.py --evidence OUT --install /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules
```

No theorem statement or proof body changes in this review.
The scoped build is not a new axiom gate run.
The landing records `undo_layout` at `propext` and `Quot.sound`, and `Ts.flat_expr` reaching `Classical.choice` through the renderer.
This review checks those statements' scope and keeps the recorded trust distinction.
The finite target checks establish no runtime behavior, whole-module simulation or general source admission property.

Four copied helper inputs retain their existing final blank line.
Their bytes match `harness/truth/control.ts`; whitespace checking excludes only that recorded EOF condition.
