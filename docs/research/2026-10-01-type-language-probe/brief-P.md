# Seat P: records and the type algebra, on a production-shaped model

Read `README.md` here first (rules, authorities, the receipt). Your folder:
`docs/research/2026-10-01-type-language-probe/P/`. Worktree `/Users/pooks/Dev/lean4-effect4-probe-P`,
branch `probe/P`. Read in full: synthesis §3.1 (R3.1–R3.9), §3.3 "Proofs", §5's row 119, §8 Q1, Q2,
Q8; TY-10 (`2026-10-01-formal-pass/types/note.md:195-206`, `:711`); the tree seat's model
(`2026-10-01-data-probe/tree/RecordNested.lean`, `RecordSpine.lean`, `verify-RecordRed.lean`,
`verify-CoerciveWidth.lean`, `note.md`) and the synthesis model (synthesis Appendix A); Codex's
`ConstructiveOrdering.lean` and `NestedDeriving.lean` with their logs
(`/private/tmp/codex-record-review-2026-10-01/`); `src/Effect4/Program/Ty.lean` (the inductive,
`key`, `ltKey`, `insertMember`, `normalize`, `Normal`, `sub`, `isMember`, `closed`, `instantiate`,
`renderRaw`), `src/Effect4/Laws/Program/TypeAlgebra.lean` (`hasTy_normalize` and the subtyping
algebra through `TyView.sub_eq_args`: `sub_trans_core`, `sub_antisymm_normal`, `fits_sub`,
`sub_normalize_of_sub`, `infer_widens`), `src/Effect4/Laws/Program/Typed/Membership.lean` (`Fits`,
`fits_hasTy`, `fits_live`, `fits_map`, `fits_sub`, `HandleFits`, `Live`; at main after I2 these
carry seat A's checker-order `subN` and row 156's scope arm: read them at your base and say what
I2 changes, from `brief-I2.md`), `src/Effect4/Machine/Value.lean` (`Val.hasTy`).

**The one thing.** Row 119 is ruled (exact records, positional values, canonical order by name,
generated eliminator and equality). What is not known is the cost and the exact statements of the
production laws at records, and whether the same arms serve every variable-arity form the data
wave will add (optional keys inside a record, keyed maps, tagged unions of records as a
discriminated `union`). Answer with a production-shaped model: a copy of `Ty.lean`'s inductive and
the algebra functions with the record constructor (and the optional-key modifier and a map
constructor as variants of the model), the laws re-proved on the copy, and the list of production
theorems that change, by name, with the measured line counts.

## Questions (each answered proved, tested, or assumed, with the file:line of the evidence)

1. **The key order.** Reuse `Ty.key`/`ltKey` (UTF-8 byte order) for field names, as Codex's
   `ConstructiveOrdering.lean` does: state `canon : List (String × Ty) → List (String × Ty)` as
   an insertion sort by `ltKey` on the name's bytes, prove it idempotent, permutation-invariant,
   sorted, and duplicate-refusing at formation (a located refusal `repeatedField at`), all at
   `[propext, Quot.sound]`; show `String.lt`'s `decide` reaches `Classical.choice` (Codex's
   `Ordering.lean`) as the red control. Does `Effect4.Row`'s sorted-row library (synthesis §3.3
   "Model size") supply the lemmas? Name what it supplies.
2. **Membership in canonical order.** `Fits w (ctor 0 vs) (record fs) ↔ FieldsFit w vs (canon fs)`
   and `Val.hasTy`'s arm, with `fits_hasTy`, `fits_live`, `fits_map`, `fits_sub` gaining one arm
   each; `hasTy_normalize`'s record case (R3.2) with records as factors (no distribution over a
   union-typed field) and the named incompleteness `record_sub_not_complete` (TY-10). On the copy.
3. **Subtyping.** Raw `sub` at records compares canonical name lists (TY-10's acceptance item: a
   permuted record is raw-below its normal form, positive control); `sub_trans_core` and
   `sub_antisymm_normal` through a `TyView` whose record head has variable arity: what shape must
   `TyView.sub_eq_args` take (a per-field `sameHead` over a list, with the variance table's row for
   a head of variable arity)? Prove the two laws on the copy; measure the production proofs that
   change (the eight that follow `sub`'s own principle, synthesis §3.3 "Proofs"). Width refused
   inside a program, projected at the boundary (row 119): a red control that `sub (record [a,b])
   (record [a])` is false, and the boundary projection as a named function with its law (R3.3).
4. **The other variable-arity forms, on the same copy.** (a) Optional keys (stage 4): a field
   modifier `(name, τ, optional)` with the absent-versus-`undefined` policy of synthesis §3.2
   stage 4; does the canonical read and `sub` stay a fold with one more case, and what is the
   value encoding of an absent field (positional `ctor 0` cannot omit a slot: say what the slot
   holds)? (b) A keyed map `map (key value : Ty)` (row 125): membership as a sorted list of pairs
   with distinct keys (the key order of question 1 on the key *values* needs `Val` keys to be
   ordered: say which key types are admitted, `string` and `lit` unions and `nat`), `sub`
   covariant in value and exact in key. (c) Tagged unions of records (stage 2): no constructor;
   state the tag decision's record arm (`isTagged`, `payloadOf`, `selectTag`) on the copy and the
   one exception to non-distribution (a `_tag` field that is a union of literals is split or
   refused at formation). For each: the laws of questions 2–3 re-proved or the exact obstacle.
5. **Exactness today (row 128, stage 1's second commit).** State the two theorems' shapes
   against today's `Ty` and codec: `decodeRaw`'s union arm selecting the encoder's canonical branch
   (the `Success`/`Failure` confusion at `union (except nat nat) (exitOf nat nat)` as the red
   control, synthesis NS2), `N_J` the key-order normaliser as a function, `ofSchema` comparing
   whole checks and refusing `TypeParameter`, `N_S` as a function; prove what a copy allows and
   list the production obligations (`Laws/Schema/Codec.lean`'s `decode_of_encode`, `encode_sub`,
   `ofSchema_schema`).
6. **Inhabitance at the new forms** (row 127, landed by seat A, wired by I2): `inhabited`'s record,
   optional-field and map arms as a fold, with `record [(a, never)]` refused and `record []`
   inhabited; the law `inhabited τ = true ↔ ∃ w v, Fits w v τ` at the new arms on the copy.

## Deliverable

`P/note.md`: per question the evidence; the production obligations as a table (theorem, file:line
today, what changes, measured lines on the copy); the proposed statements (exact Lean text) for
`Fits`'s record arm, `sub`'s record arm, `canon`, `record_sub_not_complete`, the boundary
projection, and the row-128 theorems; the decisions rows to amend (119, 125, 128; a new row if
optional keys change the value encoding); the brief text for the data wave's commits 2 and 4
(synthesis §7). Probes under `P/probes/` with logs; `#print axioms` for every theorem.
