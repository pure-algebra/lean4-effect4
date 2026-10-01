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
| 2 | Generator extensions for nested families of variable arity: the single-motive eliminator and the equality generated; `TyView` with list children (`record`, `app`, `tuple`); the variance table for a head of variable arity; the monadic-fold decision | W2 | Q's note | when Q lands |
| 3 | The `Val` append (rows 121 (a), 109): the signed and binary64 frames, the store tag, the byte codecs, the `Val` group regenerated once | W3 | Q's note; P's laws | after 2; after D1 merges |
| 4 | The `Ty` append: `record` (fields with optionality), `map`, `tuple`, `app`, `null`, `undefined`, `number` (and `bytes` if row 161 (a)); every hand arm; the named value clause (row 165) in `Fits`/`Val.hasTy`; canonical-order membership; `normalize`/`Normal`/`key`/`sub` and their laws; `hasTy_normalize`'s cases; `inhabited`'s arms; the generated groups regenerated once in the fixed order; `cases-policy.json`; wire tags; the OCaml mirrors; the conservativity check green; every new constructor refused by name in the codec, Schema and faces until its commit | W4 (laws), W4g (generation, mirrors) | P's note, Q's note | after 2, 3; after D1 merges |
| 5 | Schema and JSON arms per form with the laws (objects, optional keys, `Record`, tagged unions with the whole-union check, `Number`/`Int`, `Null`/`Undefined`, tuples, declarations with type parameters); the readable profile's text | W5 | S's note | after 1, 4 |
| 6 | Term forms (rows 166, 167): `Term.record`, `Term.field`, the map atoms, tuple forms, the tag select `Decision.recordTag`, number-to-text (row 131); contract first (`R/contracts/record-terms.contract.md`), typing lemmas, behaviour laws | W6 | R's note Q1, Q3; P's laws | after 4 |
| 7 | Error payloads (row 120 as amended): the carrier, `Err`'s image, `FitsCause`, the six handle-freeness lemmas; the face as a `Data.TaggedError` class per payload type | W7 | P's laws; R's Q3 | after 4, 6 |
| 8 | The faces: printer arms for every new constructor, the object arm of `parseLegacy` (R's 46 lines), computed keys and bracket access by name class, the class declaration and `new`, the TypeScript reader's `TSTypeLiteral` arm; `read_print`/`read_exact` over the new forms; the pin of 0a | W8 | R's note Q2, Q3; 0a | after 0a, 4, 6, 7 |
| 9 | Row 68's vectors: record pairs (permutations agree, width `incomplete`), optional-key pairs, tuples, maps, classes | W9 | R's Q3 | after 8 |
| 10 | Acceptance: p2's handler end to end from `R/probes/P2RecordHarness.lean` (six parts filled, two pins flipped); then p1, p3, p5 as far as their non-data needs allow | W10 | R's Q5 | after 5–9 |

Each seat: its own worktree from the base the coordinator names, commits by explicit paths after
narrow builds, generators only where its commit says and in the fixed order, a receipt
(`receipt-W<n>.md` here), and nothing pushed. The coordinator verifies, merges, rebuilds and records
each landing; row 123 (decoding inside a program) follows commit 10; Queue follows for p4 and p5.
