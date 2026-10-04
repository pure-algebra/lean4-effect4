# Fold family selection receipt

The fold inference repair and its focused regression fixture pass.
The six explicit caller annotations also pass the bounded consumer check.

Repair commit: `77d040c0`.
The consumer follow-up starts from that commit.
The commit containing this receipt supplies its head.

## Placement

Concept: Free Algebra & Catamorphisms (`docs/core/semantics.md`).
Role: tooling for the existing agreement-of-folds proof graph.
Consumer: `Fits.eq_cata` in `src/Effect4/Laws/Program/Typed/Membership.lean`.
Requirement: R3, supporting M5 membership proofs.

`src/Effect4/Program/FoldOf.lean` selects a family supported by every mutual sibling.
It requires one choice or an explicit `(family := ...)` argument.
The explicit choice still requires support from every sibling.
Fixed-binder reopening retains that family's identity.
The repair adds no semantic premise or trust exception.

The metadata imports expose the old failure: `Fits` first names a value and then a type.
The old selector chooses `Store.Val` before considering the mutually defined `itemFitters`.
That sibling takes no value argument.
The repaired selector finds the common `Ty` family.

## Checks

```text
LEAN_NUM_THREADS=3 lake build Effect4.Program.FoldOf
Build completed successfully (2 jobs).
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Program/FoldFamilySelection.lean
```

The fixture imports both value and type-expression folds.
It checks successful mutual inference, refusal of an unsupported explicit choice, ambiguity refusal, and successful explicit selection.
The three generated connector queries report subsets of `[propext, Quot.sound]`.
The actual `Fits.eq_cata` consumer also compiles with its unchanged statement.

The coordinator imports `Test.Program.FoldFamilySelection` into `Test/All.lean`.

## Caller inventory

The source search finds 13 modules with `fold_of` commands.
The bounded build checks exactly those modules.
The first build reports ambiguity at six calls in two modules.
The follow-up supplies explicit family selections at those calls.
The repeated check passes all inventoried modules.

| Module | Calls with explicit selection | Selected family |
| --- | --- | --- |
| `Effect4.Laws.Program.Folds.Term` | `evalTerm`, `argTy` | `Effect4.Program.Term` |
| `Effect4.Laws.Program.Folds.Denote` | `denote`, `denoteB`, `denoteWith`, `denoteBWith` | `Effect4.Program.Eff` |

Their list-valued environments expose another generated family.
The follow-up changes only those command annotations.
The bounded check reports `Build completed successfully (407 jobs)`.
The command checks these source consumers:

```text
LEAN_NUM_THREADS=3 lake build \
  Effect4.Laws.Machine.Folds.Stores Effect4.Laws.Machine.Folds.Val \
  Effect4.Laws.Program.Folds.Checker Effect4.Laws.Program.Folds.Denote \
  Effect4.Laws.Program.Folds.Looped Effect4.Laws.Program.Folds.Projections \
  Effect4.Laws.Program.Folds.Provision Effect4.Laws.Program.Folds.Representation \
  Effect4.Laws.Program.Folds.Straight Effect4.Laws.Program.Folds.Term \
  Effect4.Laws.Program.Folds.Ty Effect4.Laws.Program.Typed.Membership \
  Effect4.Laws.Store.Folds.Val
```

The six annotated connectors report subsets of `[propext, Quot.sound]` under `#print axioms`.
`evalTerm.eq_cata` reports `[propext]`.
The remaining five report `[propext, Quot.sound]`.
Their statements retain the same judgments and premises.

The three new metaprogramming helpers reach `Classical.choice`.
`Test/Audit/AxiomGate.lean` already lists `Effect4.Program.FoldOf` in `choiceImplementationModules`.
The repair changes no gate entry and adds no trust exception.
No full battery or generator run forms part of this repair.
