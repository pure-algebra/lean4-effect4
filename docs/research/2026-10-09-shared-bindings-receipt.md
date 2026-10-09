# Shared binding inventory: repair receipt

CP-01 is repaired in the shared inventory, without a new author option or an emitter exception.
The change does not overlap Claude's TypeScript algebra or renderer work.
The branch is `codex/shared-bindings` in the isolated review worktree.
Nothing is merged or pushed.

## Commits and ownership

- Base: `ecba8f5dddf0183f0c14e0c4bc3d9619d0d330d1`.
- Implementation head: `b5ea022d558822751d416035113d7215722c94d1`.
- Reviewed primary head: `89dd732ae21d358777783a75b003e4f9279f1322`.

The current design pointer is `docs/research/2026-10-09-view-algebra-audit.md`.
Claude lands its generated TypeScript fold at `89dd732a` and starts `tools/Tools/Code/TsAlgebra.lean`.
The recent commits and the bounded session tail identify that work before this repair proceeds.
The session's working directory is `/Users/pooks/Dev/lean4-effect4`.
Its identifier is `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50`.
No message is sent to Claude.

## Change and consumer

`SourceBindings.builtins` now supplies `Readonly` and `Record` as types with no value capability.
Its path is `src/Effect4/Codegen/SourceBindings.lean`.
`Types.ofTy` already emits those names for string maps in `src/Effect4/Codegen/Types.lean`.
The missing entries previously made `Tools.Code.importsOf` request nonexistent prelude exports.
Both empty and populated map programs now use the actual global types.

`ClassTable.takenNames` consumes the same inventory in `src/Effect4/Codegen/ClassTable.lean`.
Its duplicate literals disappear.
Source inspection confirms its resulting name sequence retains the same order and multiplicity for every export name and row list.
The existing payload-class tests still refuse both colliding tags.

The changed production files are those two inventory consumers.
`Test/Codegen/SourceBindingsContract.lean` adds map projections and controls for values, imports, unknown names and local masking.
`harness/codegen-bindings/Emit.lean` checks five real callers through the existing generator.
`harness/codegen-bindings/run.py` compiles their unmodified output and deliberately failing controls.
The plan, audit source and evidence directory retain the remaining files.
The commit's explicit path list records every retained input and result.

## Proof placement and limits

The concept is translation and simulation, at the source-binding part of R10.
No theorem statement, proof body or semantics registry entry changes.
`check_iff`, `validate_iff` and `Checked.use_binding` remain the binding judgment's laws.
Their path is `src/Effect4/Laws/Codegen/SourceBindings.lean`.
`admitModule_bound` consumes that judgment in `src/Effect4/Laws/Codegen/Admit.lean`.
`checkSourceBindings_iff` exposes it in `src/Effect4/Laws/Api/Codegen.lean`.
The slice changes the selected ambient environment, with the same conservative lexical rules.

The scoped compiled audit checks 494 declarations in eight named modules.
Every audited declaration stays within `propext` and `Quot.sound`.
The audit also checks forbidden declaration shapes, core/law import separation and the changed battery's proof style.
`Test.Codegen.DataTypes` contains guards alone, so the narrow build checks it separately.
An initial missing audit dependency and the corrected empty-target selection remain recorded.
No whole-tree axiom gate or sweep runs.

The target evidence is finite compilation evidence under tsgo `7.0.0-dev.20260629.1` and Effect `4.0.0-rc.112`.
The harness separately checks structured-module admission and equality with each original program.
It checks the exact expected files and their inclusion in the compiler's inputs.
It refuses missing, aliased or extra TypeScript files, and empty source text.
These checks establish no target execution, emitted-text read-back or general simulation theorem.

## Reproduced checks

The directory is `docs/research/2026-10-09-shared-bindings-evidence/`.
`target-check-hardened/results.json` retains the final compiler commands, outputs and source hashes.
The earlier run retains the same five callers before the harness's file-coverage repair.
Both runs' output hashes are verified after execution.

| Command or control | Result |
| --- | --- |
| New map guards before the repair | Both map projection guards fail; the other new controls pass |
| Narrow dependent build | Passes, 384 jobs |
| Scoped compiled audit | Passes, 494 declarations across eight modules |
| Five generated callers | Structured-module admission and original-program equality pass |
| Five unmodified emitted files | Strict target checking and unused-name checks pass |
| False imports added to both map files | Four `TS2305` errors, exactly |
| `Readonly` and `Record` used as values | Two `TS2693` errors, exactly |
| Two independent Sol investigations | Confirm the shared owner and the disjoint algebra work |
| Independent final repair review | No actionable finding after the file-coverage check is tightened |

The exact narrow commands are:

```sh
LEAN_NUM_THREADS=3 lake build Test.Codegen.SourceBindingsContract Test.Codegen.PayloadClasses Test.Codegen.DataTypes Effect4.Laws.Codegen.Admit Effect4.Laws.Api.Codegen Tools.Code.Module
LEAN_NUM_THREADS=3 lake build ProofGraph.Audit ProofGraph.Axioms ProofGraph.ProofStyle
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-09-shared-bindings-audit.lean
python3 harness/codegen-bindings/run.py --install /Users/pooks/Dev/lean4-effect4/ts/eff/node_modules --out OUT --skip-build
```

Use a fresh `OUT` directory.
The harness installs no dependency.
Four copied helper files retain their existing final blank line, recorded in `whitespace.json`.
Every other staged path passes the ordinary whitespace check.

## Next complementary slice

Keep Claude's renderer and layout migration with Claude.
The binding inventory already feeds import planning, lexical checks and class-name checks.
The next consolidation can express the existing binding traversal through the generated TypeScript fold.
That requires a core-usable algebra, rather than a core import from the tools library.
Its inherited environment must retain pending names, ordered declaration activation and type or value availability.
A flat collection of free names would lose those rules.

`TsFold` currently covers expressions, statements and object entries.
Types and parameters remain payloads, and module declarations lie outside that family.
Keep their existing checks until a separately placed agreement obligation covers their migration.
CK and OXC retain their independent recognition and refusal order.
Their shared reserved identifiers already come from `TsGen.emitWire` through `wire.gen.ts`.
No second generated keyword list is needed.

CP-02 and CP-03 of the earlier code-plane receipt remain evidence-scope findings outside this repair.
The generator's header still describes a stronger reading claim than its structured check alone establishes.
The generic document's undo law still recovers retained flat text, without a general token-preservation premise.
Claude's active algebra work may change the latter implementation.
The next review must inspect that landing before repeating the finding.
