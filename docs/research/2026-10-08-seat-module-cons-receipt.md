# Shared cons typing rule

The coordinator imports `Effect4.Laws.Modules.Cons` from the Step law module.
Its cons typing case consumes `Effect4.Modules.types_cons`.
This commit changes no Step file or root.

Base: `57bed1ec`, containing the checked shared construction core dependencies.
Head: the commit carrying this receipt.
Changed files: `src/Effect4/Laws/Modules/Cons.lean` and this receipt.

Placement: `store-typing`, helper of `step-language-typed`, requirement R4.
The matcher helper serves the native atom helper, which serves `types_cons`.
The reach is every scope and native atom signature at a common element type in normal form.
The rules establish neither membership, a run, allocation, nor target execution.
The module gaps plan places the obligation before implementation.

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Cons
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Construction
LEAN_NUM_THREADS=3 lake env lean /private/tmp/module-cons-check.lean
```

All commands pass.
The scratch reader prepends a natural number to an ascribed empty list.
Its finite controls check the normal element case and the refusal to retain a nonnormal union spelling.
The scratch axiom checks cover all three helpers.
Each uses only `propext` and `Quot.sound`.
No helper uses `sorryAx` or `Classical.choice`.
No full sweep or push runs here.
