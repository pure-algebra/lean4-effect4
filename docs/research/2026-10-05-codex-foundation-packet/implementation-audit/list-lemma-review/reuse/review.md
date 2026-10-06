# Shared list facts: bounded reuse review

Recommend a small cleanup. Reuse the existing proofs; do not replace them with weaker library facts or a new proof framework.

Evidence status: source inspection. The reviewed main is `0dbb17c3`, clean. The three requested modules are unchanged from `6214dcb8`.

No Lean command ran. No candidate proof below has been elaborated during this review.

## Exact reuse available

| Project helper | Installed Lean 4.33.1 support | Recommendation |
| --- | --- | --- |
| `Effect4.Program.Ty.flatMap_congr` | `List.flatMap_def` and `List.map_congr_left` | Keep the current tiny bridge and share it below the domain theory. |
| `Effect4.Program.Ty.lookup_of_mem_nodup` | `List.lookup_eq_some_iff` characterizes the first matching entry. | Keep the existing uniqueness proof. No exact direct replacement was found. |
| `lookup_weaken` and `getElem?_weaken` | `List.getElem?_append_left`, `List.getElem?_append_right`, `List.getElem?_cons_succ` | Share the FOLD proof, whose statement exactly matches the older private helper. |

The library sources are under `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/Init/Data/List/`.

`Lemmas.lean` owns the map and append facts. `Find.lean` owns the lookup characterization. `Basic.lean` owns first-match lookup.

## Flat-map agreement

The existing statement needs equality only for elements in the list:

```lean
{α : Type u} {β : Type v} {l : List α} {f g : α → List β}
(h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g
```

The current proof already uses the library directly:

```lean
rw [List.flatMap_def, List.flatMap_def, List.map_congr_left h]
```

There is no direct `List.flatMap_congr` declaration in the installed Init or Std sources. Requiring equality on every input would unnecessarily strengthen the hypothesis.

The three uses belong to `paramOccurrences_firsts`, in `src/Effect4/Laws/Program/Template.lean`.

Placement: helper of `template-match-anchored`, concept `subtyping-algebra`, R4. This cleanup adds no new semantic claim.

## Unique-key lookup

The exact shared statement can retain String keys first. A small optional generalization is:

```lean
{κ : Type u} {β : Type v} [BEq κ] [LawfulBEq κ]
{xs : List (κ × β)} (unique : (xs.map Prod.fst).Nodup)
{p : κ × β} (member : p ∈ xs) : xs.lookup p.1 = some p.2
```

The present inductive proof uses lawful key equality and requires no equality test for values. Preserve that property.

`Effect4.Constructive.List.lookup_mem`, in `src/Effect4/Data/Constructive.lean`, proves the reverse implication. It cannot replace this helper.

That existing helper also uses `DecidableEq`. Do not silently replace a caller's `BEq` lookup with a different equality instance.

`List.lookup_eq_some_iff` requires a prefix with no earlier matching key. It does not turn arbitrary membership into successful lookup.

For example, the second pair in `[("k", 1), ("k", 2)]` is a member, but lookup returns the first value. Unique keys remain essential.

Consumer: `infer_args` at the record case. Placement: helper of `template-match-anchored`, concept `subtyping-algebra`, R4.

## Shared weakening fact

The two current statements match exactly, including all indices and out-of-range answers. `source-checks.json` records the textual comparison.

The FOLD proof uses the three append/index lemmas and arithmetic. Prefer it over copying the older proof's unrestricted simplification.

The smallest cleanup makes the existing helper public in `src/Effect4/Program/Typing/Rules.lean`. Give it FOLD's explicit proof and retain its statement.

Delete the Laws copy. Change `evalTerm_weaken` to call the shared core helper. Both consumers already reach this module; no new import is needed.

`Var.weaken` lives earlier in `src/Effect4/Program/Eff.lean`. Moving the theorem into that syntax module adds scope without helping these two consumers.

`Effect4.Data.Constructive` suits the two ordinary Template facts. A theorem mentioning `Program.Var` must not move there, because that reverses the dependency direction.

A generic conditional-index bridge would avoid that dependency, but it adds another interface. These two callers do not require it.

Do not add an index-in-range premise. The current fact also preserves `none`, which its typing and evaluation consumers use.

Consumers: `argTy_weaken` in `src/Effect4/Program/Typing/Rules.lean`, and `evalTerm_weaken` in `src/Effect4/Laws/Program/Typed/ListFold.lean`.

Placement: helper of `fold-typed-atomic-update`, concept `store-typing`, R4. It supports both typing and full evaluation-result preservation.

## Namespace and trust boundaries

Use a project namespace such as `Effect4.Constructive.List`. Fully qualify standard-library lemmas while moving the proofs.

Keep the helper module free of Program and Laws imports. Never make core typing import `Laws.Program.Typed.ListFold`.

Generalized helpers should quantify `Type u` and `Type v`. The current helpers only quantify `Type`.

Do not register these equalities as global simplification or search rules merely because they moved. Their consumers already apply them explicitly.

A source proof containing no `classical` is not an axiom receipt. A standard-library replacement also needs its transitive axiom check.

The implementation owner should check the moved helpers and their existing consumers under `[propext, Quot.sound]`, using the usual narrow acceptance.

The current `Constructive` header does not substitute for that check. No broad dependency audit or new gate is required for this cleanup.

## Recommended scope

Share the two plain Template facts below the theory. Expose the existing core weakening helper. Update their concrete consumers.

Retain existing top statements and their registry placement. Keep any namespace alias only when another actual consumer needs it.

The neighboring zip lemmas may be useful later, but this review does not justify a broader list-library reorganization.
