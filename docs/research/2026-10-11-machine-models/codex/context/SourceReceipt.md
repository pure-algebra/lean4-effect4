# Typed context source checkpoint

The source slice compiles and its repaired CE001 controls pass.
The general type-order and semantic membership proof migration remains open.
Do not interpret this checkpoint as the context requirement's final proof.

Base: `78ac5dc1ee28f2c6ca7c74d2d034fc80f92ffacf`.
The commit containing this receipt is the source checkpoint head.
The coordinator owns root imports, registries and the later behaviour sweep.

## Placement and reach

Concept: context-environment, R9; source admission and native compilation.
The reader serves the proposed `typed-context-read` claim, role preservation of promised service membership.
The provider serves the proposed `provide-context-row` claim, role preservation of the required row.
The type order serves subtyping-algebra, R14, and semantic membership weakening.
`PLAN.md` places these obligations before this implementation.
No new planned goal enters this slice.

`Ty.contextOf` carries a canonical key row.
`Ty.sub_contextOf` proves the contravariant subset equation for all rows.
The generated equality, folds and canonical image include that constructor.
The context source reader requires every promised key and refuses undeclared carriers.
The context provider removes supplied keys from the body's required row.
A legacy context handle spelling cannot supply that row evidence.
The executable value check reads context shape and promised key presence.
Its check does not establish service value typing or world membership.
That stronger membership proof remains in the next slice.

`compileEff` follows existing `updateContextAt`, `updateThenK`, `bodyThen` and `restoreCtx` producers.
The new reader compiles to the existing native context getter.
The provider merges supplied services and restores the previous context.
The compiler retains the pinned immediate-exit shortcut.
Native context get and set operations retain their meanings.
No second program representation or evaluator pass enters the tree.

## CE001 controls

`Test.Counterexamples.Program.ContextReset` refuses retired raw setter and reader heads.
The canonical decoder refuses their old tags, 12 and 13.
The battery retains the exact legacy witness in `ContextReset.legacy.lean.txt`.
The witness is evidence, not a translated program.

A reader records its exact promised requirement row.
An undeclared service carrier refuses.
A legacy context spelling refuses as provider evidence.
Both repaired provider programs receive closed rows and pass program admission.
Finite `Provision.runNative` checks return the enclosing service values, 1 and 2.
The unchanged service-region control returns 1.
These finite runs establish no whole-history context invariant.

## Commands and results

Every Lake command uses `LEAN_NUM_THREADS=3`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Program.Admission Effect4.Program.Typing.Annotate Effect4.Program.Compile` | passed, 72 jobs |
| `lake build Effect4.Program.Provision Test.Counterexamples.Program.ContextReset` | passed after namespace repairs; final focused run passed, 96 jobs |
| `lake env lean --run tools/Effect4Gen/Driver.lean --group Program --check` | canonical output and projection guard passed |
| `lake env lean --run tools/Effect4Gen/Driver.lean --group Binders --check` | generated module passed; projection guard refused because this group contains no shape declaration |
| final narrow build over CE001, source leaves, Schema leaves and generated fragments | passed, 114 jobs |
| `lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/SourceAudit.lean` | 10439 declarations within `[propext, Quot.sound]`; zero goals and zero modulo goals |
| `git diff --check` | passed |

`SourceAudit.lean` enumerates every audited changed module.
The final narrow build targets follow.

```text
Test.Counterexamples.Program.ContextReset
Effect4.Program.Typing.Annotate
Effect4.Program.TyNormal
Effect4.Program.Polarity
Effect4.Program.TyFoldExtras
Effect4.Program.Authoring.Lifts
Effect4.Program.Scoped
Effect4.Program.Binders
Effect4.Schema.Bridge
Effect4.Schema.Codec
Effect4.Laws.Program.FragmentLooped
Effect4.Laws.Program.FragmentRows
Effect4.Laws.Program.FragmentLoopedRows
```

## Generated source and open migration

Ty uses tag 28, the context region uses tag 32, and the context reader uses tag 18.
Retired action tags remain reserved.
The binder input gives the provider one child with no new binding.
The LayerView input names the canonical row leaf.
Canonical service key instances precede the newly context-bearing type instance.
Every changed generated file comes from its existing producer.
The existing straight execution fragments explicitly refuse the new provider.
No fragment silently widens.

The full derived scheduler stops at the deferred `Codegen.Types` constructor case.
`ProjectionProposal.md` records that exact central repair and its static key meaning.
Automatic approval review rejects the delegated target edit; that file remains untouched.
The generated TyView must gain the ordered-row payload rule.
The coordinator approves changing its helper decompositions to name that rule.
Outward subtype, order and Fits claims retain their statements.
No frozen contract mentions the affected decomposition names in the checked search.

Semantic `Fits`, layer result types, typed admission and native source provenance still need exhaustive migration.
A six-line semantic membership draft stays uncommitted; it is not part of this audit.
TypeScript ingestion, LCNF, OCaml and the reached behaviour gates remain deferred.
B6 needs the existing installation and restoration phases described in the plan.
No behaviour gate or broad root build is claimed.
No push occurs.

## Changed source paths

- `Test/Counterexamples/Program/ContextReset.lean`
- `src/Effect4/Laws/Program/FragmentLooped.lean`
- `src/Effect4/Laws/Program/FragmentLoopedRows.lean`
- `src/Effect4/Laws/Program/FragmentRows.lean`
- `src/Effect4/Program/Authoring/Lifts.lean`
- `src/Effect4/Program/Binders.lean`
- `src/Effect4/Program/Checker.lean`
- `src/Effect4/Program/Columns.lean`
- `src/Effect4/Program/Compile.lean`
- `src/Effect4/Program/Eff.lean`
- `src/Effect4/Program/Fold.lean`
- `src/Effect4/Program/Fragment.lean`
- `src/Effect4/Program/LayerView.lean`
- `src/Effect4/Program/NodeLenses.lean`
- `src/Effect4/Program/Polarity.lean`
- `src/Effect4/Program/Provision.lean`
- `src/Effect4/Program/Scoped.lean`
- `src/Effect4/Program/SigApp.lean`
- `src/Effect4/Program/Ty.lean`
- `src/Effect4/Program/TyCore.lean`
- `src/Effect4/Program/TyEq.lean`
- `src/Effect4/Program/TyFoldExtras.lean`
- `src/Effect4/Program/TyNormal.lean`
- `src/Effect4/Program/Typed.lean`
- `src/Effect4/Program/Typing.lean`
- `src/Effect4/Program/Typing/Annotate.lean`
- `src/Effect4/Schema/Bridge.lean`
- `src/Effect4/Schema/Codec.lean`
- `src/Effect4/Store/Domain/Derived/Program.lean`
- `tools/Effect4Gen/Fragments.lean`
- `tools/Effect4Gen/LayerView.lean`
- `tools/Effect4Gen/binders.json`
- `tools/Effect4Gen/guards/binders.lean`
- `tools/Effect4Gen/guards/fold.lean`
- `tools/Effect4Gen/manifest.json`
- `tools/Effect4Gen/wire-tags.json`

The source diff adds 605 lines and removes 400 lines.
The counts exclude the uncommitted semantic membership draft and this research evidence.
