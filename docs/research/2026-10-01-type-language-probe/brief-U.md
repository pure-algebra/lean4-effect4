# Seat U: cash the initial algebra: every `Ty` traversal as an algebra of one fold

Read `README.md` here first (rules, authorities, the receipt). Your folder:
`docs/research/2026-10-01-type-language-probe/U/`. Worktree `/Users/pooks/Dev/lean4-effect4-probe-U`,
branch `probe/U`. Read in full: `docs/core/coherence-principle.md` and `docs/core/traversal-census.md`
(the rule: every traversal is a fold or generated from the signature; a hand `match` is an exemption
the census lists by name), `Test/Audit/TraversalCensus.lean` (`#traversal_census`; run it, cite the
log), `src/Effect4/Program/Fold.lean` (`TyAlgebra`, `cata_ty`, `foldMap_ty`, `foldMapAt_ty`,
`hom_eq_cata_ty`, the `fold_of` registrations), `tools/Effect4Gen/Fold.lean` (what the generator
emits, including the nested block), the synthesis's bill (`2026-10-01-data-probe/synthesis.md` §3.3
"Hand arms, compile-forced" and "Hand arms, review"), the R4/R5/R6 packet's template table and
generic reader (`docs/research/2026-09-17-*` notes on the reader line, `Codegen/Templates`), the
OCaml mirrors (`ocaml/engine/e4_program.ml:119-156`, `ocaml/eff/test/prop_wire.ml`, `src/OCaml5/Eff/`
`tyO`/`tyV`, `tools/Tools/ProfileJson.lean`, `tools/Conform/Effect4/LcnfMl.lean`, `LcnfSemantics`),
and `docs/core/lcnf-route.md`. Probe T's and R's notes for the wave's constructors.

**The one thing.** The owner (2026-10-01): "it feels like we're not getting enough out of the
initial algebra; so much is hand-written that could be obvious." Produce the table that says, for
every per-constructor traversal of `Ty` in the tree (Lean and the mirrors), which algebra of which
fold it is, whether the generator can emit it from the family description plus a per-constructor
table, and what the one agreement law it then inherits is; and state the steer for the wave's
commit 4 as a rule a reviewer can check: no hand `match` on `Ty` outside the generated folds and
`Membership.lean`.

## Questions

1. **The inventory.** Every definition and theorem that cases on `Ty` (the census's rows; the
   exhaustive gate's 65 matcher rows, 27 without a catch-all; the 38 catch-all rows; the 8 mirrors;
   the hand tables `cases-policy.json`, `Variances.lean`, `Metadata.lean:52-60`). One row each:
   site, today's form (hand match with or without catch-all; a fold; generated), what it computes.
2. **The classification.** Group the rows into generic fold families with their algebra shape:
   (a) the plain catamorphism with a full `TyAlgebra` (which ones carry genuine per-constructor
   content: `Fits`/`Val.hasTy`, `sub`'s congruence arms with the variance table, `inhabited`,
   `normalize`, `instantiate`, `closed`); (b) collection and predicate folds, `foldMap` into a
   monoid with per-leaf data (`varsOf`, `isNever`, `findInt`, `templateAdmissible`,
   `rawSupportedErrTy`, `members`?); (c) spelling folds driven by a per-constructor table
   (`renderRaw`, `Codegen.Types.ofNormalized`, `Bridge.schema`, `tyJson`, `tyOcaml`, `tyT`, `tyO`,
   `tyV`, `of_ty`, `rand_ty`'s generator, the wire tags, `key`), where the table is data the
   generator reads and the fold is one generic definition; (d) folds that are two folds composed
   (fusion: `schema ∘ normalize`, `key ∘ normalize`); (e) genuinely irreducible hand cases, with
   the reason. For each family: the generic definition's statement, the agreement law it gives
   (`hom_eq_cata_ty`: two folds agree when their algebras do; fusion), and the exhaustiveness it
   enforces (an algebra record has one field per constructor: a new constructor fails every
   algebra at compile time, which is the wanted failure, versus a catch-all that compiles silently).
3. **What the generator emits.** For families (b), (c) and (d): can `tools/Effect4Gen` emit the
   algebra from the family description plus the per-constructor table today (name the tool and the
   lines), with a small change (measure it on a copy under `U/`), or only with a new emitter
   (measure)? Show one worked instance per family on a copy: for example `renderRaw` as a spelling
   fold with its table, `varsOf` as `foldMap`, `of_ty` emitted into OCaml from the same table, each
   compiled or built in your folder with its agreement check (`#guard`s against today's function on
   the tree's own types, or the OCaml goldens).
4. **The mirrors as the same algebra.** State what "the OCaml mirror is the same algebra
   interpreted in OCaml" means as a conform rung: the family description plus the spelling table
   emitted twice (Lean and OCaml), with the agreement checked by the existing conform lane
   (`tools/Conform`, `make check-ocaml`), so a mirror is never hand-maintained; which of the eight
   mirrors fit that today and which are the LCNF cut's (already generated).
5. **The laws once.** Which laws are stated per constructor today and become one theorem over the
   fold family (monotonicity of a fold whose algebra is fieldwise monotone; `hasTy_normalize` as
   fusion; `key` injective from the table being prefix-free), with the lines each saves in the
   wave (the synthesis's census: 62 theorems recurse or case on `Ty`).

## Deliverable

`U/note.md`: the inventory and classification tables; the worked instances under `U/probes/` with
logs; the generator measurements as patches under `U/patches/`; the rule for commit 4 and the
list of hand matches that remain with their reasons; the lines for `docs/core/coherence-principle.md`,
`traversal-census.md`, decisions row 143 and a new row ("every `Ty` traversal an algebra; the
spelling folds table-driven and generated; the mirrors the same algebra"). Rules as the README:
`LEAN_NUM_THREADS=1`, no tracked-file edits, `#print axioms` on every theorem, evidence words.
