# Template list-helper review

Status: source review, with the retained T4 proof receipt.
No repository edits, build, generator or new Lean check runs.
The requested base is `6214dcb8`; the observed main head is `0dbb17c3`.
The reviewed Template source is unchanged between those commits.

## Recommendation

Move five list-only helpers from `Effect4.Program.Ty` into `Effect4.Constructive.List`.
Use the existing `src/Effect4/Data/Constructive.lean` module.
Keep the current statements, bodies and universes in the first cleanup.
Update their eight non-recursive uses in `src/Effect4/Laws/Program/Template.lean`.
Do not move the other T4 declarations as a group.
They describe type normalization, template inference, anchors or their invariants.

No new representation, proof framework or list module is needed.
The existing module already contains constructive list lookup, membership and predicate facts.
`Ty` reaches it through `Data.Row`; the core never needs an import from Laws.
`Laws/Auto/ListSubset.lean` implements an inclusion checker and its tactic support.
It is not the home for general list facts.

The module is a low dependency, so changing it invalidates many dependent builds.
Schedule this cleanup after the active T5 proof batch, through the coordinator's existing build slot.
It has no semantic dependency on T5 and should not block its implementation.

## Exact statements and callers

All current type variables below are `Type`, meaning universe zero.
No helper assumes decidable equality for arbitrary list elements.
Keep these choices during relocation; broader universes are a separate optional generalization.

| Current helper in `Effect4.Program.Ty` | Exact premises and result | Current non-recursive consumer |
| --- | --- | --- |
| `flatMap_congr` | `{α β : Type} {l : List α} {f g : α → List β}`, `(∀ x ∈ l, f x = g x) → l.flatMap f = l.flatMap g` | `paramOccurrences_firsts`, three cases |
| `mem_zip_map_self` | `{α β : Type} {f : α → β} {l : List α} {p : α × β}`, `p ∈ l.zip (l.map f) → p.2 = f p.1` | `args_zip_of_map` |
| `mem_zip_middle` | `{α β γ : Type} {xs : List α} {ys : List β} {zs : List γ}`, `xs.length = zs.length → ys.length = zs.length → (a,b) ∈ xs.zip ys → ∃ c, (a,c) ∈ xs.zip zs ∧ (b,c) ∈ ys.zip zs` | `underInstance_args` |
| `eq_of_mem_zip_map` | `{α β γ : Type} {f : α → γ} {g : β → γ} {xs : List α} {ys : List β}`, `xs.map f = ys.map g → (a,b) ∈ xs.zip ys → f a = g b` | `underInstance_args`, `infer_args` |
| `lookup_of_mem_nodup` | `{β : Type} {L : List (String × β)} {p : String × β}`, `(L.map Prod.fst).Nodup → p ∈ L → L.lookup p.1 = some p.2` | `infer_args` |

Keep both alignment premises of `mem_zip_middle`.
Keep name uniqueness in `lookup_of_mem_nodup`; list membership alone does not determine the first matching entry.
Do not silently generalize String lookup to a different equality instance.
A later generic lookup law needs an explicit lawful equality contract.

The five helpers serve the existing `template-match-anchored` claim.
Its concept is `subtyping-algebra`, its role is decidability, and its requirement is R4.
The top declaration remains `Ty.matchTemplate_complete_anchored`.
Relocation changes neither that statement nor its exclusions.
The helpers need no independent semantic claim or new planned goal.

## Standard-library comparison

The inspected toolchain is the repository's `leanprover/lean4:v4.33.1` installation.
The conclusions below concern its actual source, not a newer API.

- `List.map_congr_left` and `List.flatMap_def` already constitute the current `flatMap_congr` proof.
  No exact `List.flatMap_congr` theorem appears in the installed source search.
- `List.map_prod_left_eq_zip` in `Init/Data/List/Zip.lean` rewrites `l.zip (l.map f)` as a mapped pair list.
  With `List.mem_map`, it can shorten `mem_zip_map_self`.
  That is a candidate proof replacement, not a checked axiom result from this review.
- `List.getElem?_zip_eq_some` offers an index-based route to alignment facts.
  It does not directly replace the current three-list membership statement.
  Reworking the existing short inductive proof adds no clear benefit to this cleanup.
- `List.lookup_eq_some_iff` in `Init/Data/List/Find.lean` describes a first matching entry through a prefix.
  It needs a lawful Boolean equality instance and is not the uniqueness-based statement above.
- `Effect4.Constructive.List.lookup_mem` proves the opposite direction: a successful lookup yields membership.
  It does not replace `lookup_of_mem_nodup`.

Do not add Mathlib or a new dependency for these facts.
Do not infer the project's axiom ceiling merely from a standard-library theorem's name.
The T4 receipt reports `flatMap_congr` and `lookup_of_mem_nodup` at `[propext, Quot.sound]`.
It reports the three zip helpers at `[propext]`.
These are retained historical results; any rewritten proof needs fresh axiom output when it lands.

## One optional reuse after relocation

`Typed.mem_zip_self` in `Laws/Program/Typed/Membership.lean` proves:
`{α : Type} {l : List α} {a b : α} → (a,b) ∈ l.zip l → a = b`.
It is the identity-function instance of `mem_zip_map_self`, with equality reversed.
Its four existing callers can retain their names and statements.
Only its body needs to call the shared fact, with `List.map_id`.
This is a concrete reduction of duplicate induction, not a new theorem requirement.

Leave `TyView.lean` untouched in this cleanup.
Its generic `map_fst_zipIdx` is already a direct standard-library alias.
Its source is generated by `tools/Effect4Gen/View.lean`; changing the generated file directly is invalid.
`fiber_lookup_of_mem_nodup` concerns `find?` over machine fibers, not the same associative-list lookup.
It is not an exact duplicate of the Template theorem.

## Landing scope and verification

The minimum changed paths are `Data/Constructive.lean` and `Laws/Program/Template.lean`.
A small fixture may check the relocated declarations' statements and axioms through the existing audit mechanisms.
The optional `Membership.lean` body reuse can wait.
Preserve the module's `module`, public imports and `@[expose] public section` structure.
Add only the standard list imports needed to elaborate the unchanged bodies.
Add no Aesop, ProofGraph, Program, Machine or Laws import to the shared data module.

After the coordinator grants a build slot, check the shared module and Template's affected direct consumers.
Print the five relocated declarations' axioms and the unchanged `matchTemplate_complete_anchored` axioms.
Recheck the existing anchored/bottomFree positive and negative controls.
Use the existing library-root and proof-style mechanisms; no new gate is needed.
The final receipt should record exact paths, source hashes, commands, axioms and unchanged top-level proposition.
This review does not supply those future build results.
