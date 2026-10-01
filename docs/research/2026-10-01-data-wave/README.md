# The data wave (2026-10-01): the type language landed once

The owner's instruction (2026-10-01): "start the data wave as the probes land". The wave runs in
parallel with wave 2 (D1, D3, then D2); its `Ty` append is sequenced after D1 merges because both
touch `Laws/Program/Typed/Membership.lean`. Briefs are cut from the probe notes as they land
(`docs/research/2026-10-01-type-language-probe/<X>/note.md`): T and R are in; P, Q and S follow.
Rules for every seat: `2026-10-01-landing/plan.md` §4 and `AGENTS.md` (one TypeScript compiler,
tsgo 7). Rulings the wave rests on: rows 119 (records; its value clause amended by row 165, ruled:
values carry their canonical names in the existing frames), 122, 127, 128, 137, 156, 162 (the single
append, ruled), 165 (ruled); recommended and proceeding with ratification owed: 157 (optional keys),
158 (`Ty.app`), 159 (tuples), 160 (`null`, `undefined`), 161 (`bytes`, the owner's choice), 120,
121 (a), 125, 131, 166 (term constructors), 167 (the name domain); 164 (the dependency bump).

## The commit series and the seats (probe T §2.4, amended by probe R)

| # | Commit | Seat | Inputs | Starts |
| --- | --- | --- | --- | --- |
| 0a | The lean4-typescript bump (row 164 as R amends it): `TypeRef.object` optional-field flag, `Expr.index` with an expression key, computed object keys, `Expr.new`, object spread; version 0.7.0 in the package's own repository | W0 | R's note Q2, Q3 | now |
| 0b | Paper: the rows above; the pin of 0a in `lakefile.toml` with `lake update typescript` at commit 8 | coordinator | — | done / at 8 |
| 1 | Exactness for today's `Ty` (row 128, TY-09): the decoder selects the encoder's canonical branch; `N_J`, `N_S` as functions; `ofSchema` compares whole checks, refuses `TypeParameter`; the two theorems | W1 | P's note (question 5), S's note (question 1) | when P and S land |
| 2 | Generator extensions for nested families of variable arity: the single-motive eliminator and the equality generated; `TyView` with list children (`record`, `app`, `tuple`); the variance table for a head of variable arity; the monadic-fold decision; **and the generated order laws extended to declared cross-head leaf edges** (`undefined ⊑ unit`, the number tower `nat ⊑ int ⊑ number`): one shared table of the exceptional rules read by the generator beside its six fixed cases, the different-head theorem restated (its conclusion is false only at heads with no declared edge), an accepted cross-head case and its rejected converse as controls (Codex, 19:30: Q's probe modelled no new non-congruence rule, so its green covers the structural family only) | W2 | Q's note **and** P's final cross-head rules | when P and Q land |
| 3 | The `Val` append (rows 121 (a), 109): the signed and binary64 frames, the store tag, the byte codecs, the `Val` group regenerated once | W4 (its first step) | Q's note; P's laws | after 2; after D1 merges |
| 4 | The `Ty` append: `record` (fields with optionality), `map`, `tuple`, `app`, `null`, `undefined`, `number` (and `bytes` if row 161 (a)); every hand arm; the named value clause (row 165) in `Fits`/`Val.hasTy`; canonical-order membership; `normalize`/`Normal`/`key`/`sub` and their laws; `hasTy_normalize`'s cases; `inhabited`'s arms; the generated groups regenerated once in the fixed order; `cases-policy.json`; wire tags; the OCaml mirrors; the conservativity check green; every new constructor refused by name in the codec, Schema and faces until its commit | W4 (one seat: laws, then generation and mirrors) | P's note, Q's note | after 2, 3; after D1 merges |
| 5 | Schema and JSON arms per form with the laws (objects, optional keys, `Record`, tagged unions with the whole-union check, `Number`/`Int`, `Null`/`Undefined`, tuples, declarations with type parameters); the readable profile's text | W5 | S's note | after 1, 4 |
| 6 | Term forms (rows 166, 167): `Term.record`, `Term.field`, the map atoms, tuple forms, the tag select `Decision.recordTag`, number-to-text (row 131); contract first (`R/contracts/record-terms.contract.md`), typing lemmas, behaviour laws | W6 | R's note Q1, Q3; P's laws | after 4 |
| 7 | Error payloads (row 120 as amended): the carrier, `Err`'s image, `FitsCause`, the six handle-freeness lemmas; the face as a `Data.TaggedError` class per payload type | W7 | P's laws; R's Q3 | after 4, 6 |
| 8 | The faces: printer arms for every new constructor, the object arm of `parseLegacy` (R's 46 lines), computed keys and bracket access by name class, the class declaration and `new`, the TypeScript reader's `TSTypeLiteral` arm; `read_print`/`read_exact` over the new forms; the pin of 0a | W8 | R's note Q2, Q3; 0a | after 0a, 4, 6, 7 |
| 9 | Row 68's vectors: record pairs (permutations agree, width `incomplete`), optional-key pairs, tuples, maps, classes | W9 | R's Q3 | after 8 |
| 10 | Acceptance: p2's handler end to end from `R/probes/P2RecordHarness.lean` (six parts filled, two pins flipped); then p1, p3, p5 as far as their non-data needs allow | W10 | R's Q5 | after 5–9 |

The v0 milestone is "p2's handler with host-side decoding" (commit 10, route A); in-program decoding (row 123) follows the wave. Reviews of the wave by Codex are kept under `reviews/`.

Each seat: its own worktree from the base the coordinator names, commits by explicit paths after
narrow builds, generators only where its commit says and in the fixed order, a receipt
(`receipt-W<n>.md` here), and nothing pushed. The coordinator verifies, merges, rebuilds and records
each landing; row 123 (decoding inside a program) follows commit 10; Queue follows for p4 and p5.

## Landing style (the owner, 2026-10-01: land it quickly, cut over, add gates back at stability)

The wave is a cut-over to the unified laws, not a migration beside the old ones (AGENTS: build in
parallel, slot in, delete at a good place; the owner's 2026-09-18 rule on gate removal).

- **Generated, never hand-migrated.** Every per-constructor artefact a generator can produce is
  regenerated in the fixed order in the append commit, and the hand copy deleted in the same
  commit: the fold group, `TyView`, the eliminator and equality, the wire tags, and (W2 to measure,
  Q's questions 4 and 5) `tools/Conform/Effect4/cases-policy.json` and the OCaml mirrors'
  constructor tables (`e4_program.ml`'s `of_ty` and its count, `prop_wire.ml`'s `rand_ty`,
  `OCaml5.Eff`'s `tyO`/`tyV`, `ProfileJson.tyJson`, `LcnfMl.tyOcaml`/`tyT`, `LcnfSemantics.tyValue`)
  generated from the family description where the generator reaches them. A hand table that
  stays is named in the receipt with the reason.
- **Laws stated once over the signature.** The order and membership laws (S6) land as theorems
  over the signature's description (the congruence rows, the declared leaf-order table, the union
  rules), and the per-constructor proofs they subsume are deleted in the same commit; the receipt
  lists them by name (plan §5 item 1). A new constructor after the wave costs its arms and no law.
- **The gates that run during the wave** are the ones with a reader: the trust gate (`lake build
  Effect4.Laws Test.All`, the axiom audit), `make check-gen` (byte-identity of the generated
  groups: the conservativity instrument), `dune build` and `make check-ocaml`, `make check-target`
  and `make check-truth` where a commit touches the faces, and the acceptance batteries (the
  counterexample register's controls, red and green). `make check-cases`, the exhaustive fixtures'
  pins ("alts 20") and the traversal census's pins are regenerated or re-pinned by the seat that
  changes the family, never hand-maintained against it; a pin that only restates a count is deleted
  rather than updated.
- **Added back after v0.** When commit 10 passes (p2's handler with host-side decoding), the
  coordinator runs `make check-full` once, reads what it says, and keeps the sweeps that found
  something or that a document names as a reader's instrument; the rest are retired with a dated
  line in `docs/GENERATED.md` or the Makefile, not left to rot.
- **No shortcut on rigor.** Unchanged: `[propext, Quot.sound]` everywhere, no `sorry`/`partial`/
  `unsafe`, every statement kept or refuted with its history, every traversal a fold or generated.
  Speed comes from deleting duplicates and hand tables, not from weakening a judgment.

## Testing during the wave (the owner, 2026-10-01: ratified; avoid testing that reads nothing)

- A seat builds narrowly: the touched modules and their direct importers after each change
  (`lake build <Module>`; `lake env lean` for a battery), the roots once at its final commit.
- The coordinator rebuilds main after a merge only where two code seats landed in parallel on
  overlapping cones (the interaction a seat's own build cannot see); a seat whose base is main's
  head merges on its own final build and `git merge-tree` alone. Docs merges never build.
- `make check-gen` runs only in a commit that ran a generator; `dune build` and `make check-ocaml`
  only in a commit that regenerated an OCaml group; `check-target`/`check-truth` only where the
  faces changed. `make check-full` once, after commit 10.
- A control is kept when it is a counterexample row's witness or an acceptance; a test that
  restates a count or a shape the generator owns is deleted with its generator run.
- The seats ask for a sweep only when a proof depends on it; nothing else is owed.

The series' commits 3 and 4 are one seat (W4): the `Val` append is its first step.
