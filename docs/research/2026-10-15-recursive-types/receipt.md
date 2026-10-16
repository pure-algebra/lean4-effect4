# 2026-10-15 seat RECTYPES receipt: recursive types, the formal foundation

**The one thing to know before merging:** the new root import rebuilds every module that
imports the `Effect4` root once. The Lean code edits no existing definition. Membership under a
table is proved decided, conservative on the empty table and closed under `Ty.sub`. Three
properties stay planned goals.

## Base and head

- Branch `seat/rectypes`, worktree `.claude/worktrees/seat-rectypes`.
- Base `60f4d7f18`.
- Head: `db6eb59e3` (the Lean code), `a689cef36` (the note, `docs/core/semantics.md` and the tsgo
  fixture), then the commit that adds this receipt.

## Changed files

| File | Change |
| --- | --- |
| `src/Effect4/Program/TyDecls.lean` | new core module (not a Lean module: it imports `Program/Typed.lean`, row 202): `TyDecls`, `Val.obligations`, the checker `Val.hasTyIn`, `TyDecls.guarded`, `TyDecls.inhabited` |
| `src/Effect4/Laws/Program/TyDecls.lean` | new law module: `MemberIn` and its laws, `declAlg`, the three planned goals |
| `Test/Program/TyDecls.lean` | new battery: the probe's tables, finite evaluations, readers and red controls |
| `src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean` | one import line each |
| `tools/ProofGraph/Registry.lean` | seven claims under `store-typing`; R3's open part on recursive types restated |
| `docs/core/semantics.md` | §2.1: the required property of membership under a table |
| `docs/research/2026-10-15-recursive-types/formal.md` | the formal note |
| `docs/research/2026-10-15-recursive-types/probes/oracle/guarded.ts`, `.log` | tsgo's guardedness check |

`src/Effect4.lean` has no `Program.Typed` line, so its anchor is the block of type modules, after
`Effect4.Program.TyClasses`.

## Commands and results

Each Lean command ran from the worktree through `scratch/lean-slot.sh`.

| Command | Result |
| --- | --- |
| `lake build Effect4.Program.TyDecls Effect4.Laws.Program.TyDecls Test.Program.TyDecls Effect4 Effect4.Laws ProofGraph.Registry` | `Build completed successfully (1718 jobs).` |
| `lake env lean <scratch>/Audit.lean`, which runs `#axiom_audit Effect4.Program.TyDecls Effect4.Laws.Program.TyDecls` | `521 declarations within [propext, Quot.sound], 1 of them modulo planned goals; 3 planned goals` |
| `lake env lean <scratch>/Plan.lean`, which runs `#plan_status` on the seven claim pointers | four proved, one modulo `exists_memberIn_of_inhabited`, two goals |
| `python3 scripts/check-language.py --strict docs/research/2026-10-15-recursive-types/formal.md` | `PASS` |
| `python3 scripts/check-language.py --strict docs/research/2026-10-15-recursive-types/receipt.md` | `PASS` |
| `python3 scripts/check-language.py --show docs/core/semantics.md`, before and after | no new finding (86 lines of findings before and after) |
| `harness/truth/node_modules/.bin/tsgo --noEmit --strict --target es2022 --moduleResolution bundler --module esnext guarded.ts` | four TS2456 errors, at `A`, `B`, `C` and `D`; `L` and `S` accepted; `rc=1` |

The first audit refused 32 declarations. `beq_self_eq_true` at `String` reached
`Classical.choice` through `String.instTransOrd`. `beq_iff_eq.mpr rfl` replaced it in
`unseen_cons_lt`, and the audit then passed. No gate ran: `make check-*` and `lake build Test`
are the coordinator's.

## Axiom output

`#axiom_audit: 521 declarations within [propext, Quot.sound], 1 of them modulo planned goals;
3 planned goals`. The declaration modulo goals is `inhabited_iff_memberIn`.

## Evidence

- Proved: `hasTyIn_iff`, `memberIn_unfold_iff`, `tyDecls_conservative`, `memberIn_sub`,
  `memberIn_iff_cata`, `inhabited_of_memberIn`, `Val.sizeOf_obligation`, `hasTyIn_absorb`,
  `cata_declAlg_step`, `hasTy_eq_obligationsAll` and their helpers.
- Proved modulo a goal: `inhabited_iff_memberIn`, modulo `exists_memberIn_of_inhabited`.
- Declared, not proved: the goals `exists_memberIn_of_inhabited`, `memberIn_normalize` and
  `guarded_fixedPoint_unique`.
- Tested: the battery's finite evaluations over the probe's eight tables.
- Proved, as a control: the red case of `guarded_fixedPoint_unique` at `A = A`, in the battery.
- Tested, bounded and host-only: tsgo on `guarded.ts`, one hand-written file.
- Reading: the reuse pass below; the literature of the note's §9, by its audit rows or by name.

## Landed theorems and their placement

Every theorem below has the placement of `formal.md` §10. Concept `store-typing`. Property:
membership is a judgment with a decision procedure, closed under the order, invariant under
normalization, with inhabitance as its emptiness test. Requirement R3.

| Theorem | Claim and role | Reach | Does not establish | Unlocks |
| --- | --- | --- | --- | --- |
| `hasTyIn_iff` | `recursive-types-decided`, decidability | every table, guarded or not | anything of `Fits` | the wiring slice's checker |
| `memberIn_unfold_iff` | `recursive-types-unfold`, inversion | both spellings of a reference | formation of a table | `Fits`'s inversion under a table |
| `tyDecls_conservative` | `recursive-types-conservative`, compatibility | the empty table | anything of `Fits` | M7 as the empty-table instance |
| `memberIn_sub` | `recursive-types-sub`, preservation | `Ty.sub`, every table | `Ty.subN` | `fits_sub` under a table |
| `inhabited_iff_memberIn` | `recursive-types-inhabited`, decidability | every table | its completeness half, a goal | the table's column admission |
| goal `memberIn_normalize` | `recursive-types-normalize`, compatibility | every table | anything, until proved | `fits_normalize` under a table |
| goal `guarded_fixedPoint_unique` | `guarded-fixed-point-unique`, compatibility | guarded tables | anything, until proved | the table's admission |

## What was reused

- `Val.hasTy`: the leaf arms of `Val.obligations` call it. `hasTy_eq_obligationsAll` proves the
  recursive arms read it.
- `namedHasTy`, `itemsHasTy`, `entriesHasTy` and `causeAdmits`, by one agreement lemma each.
- The fold `Val.hasTy.alg`: `declAlg` is a structure update of it.
- `AdmitsSub`, `cata_admits_sub` and `Val.hasTy_admitsSub`: `memberIn_sub` with no new induction.
- `Ty.members`, `Ty.members_isMember`, `Ty.members_atom` and `hasTy_members`: the union reading.
- `inhabitedAlg`, by a structure update, and `inhabited_of_hasTy` at the leaves.
- `fieldCheckers_foldr`, `itemCheckers_foldr`, `admChecker` and `Field.canonBy_map`.
- The exactness of `causeImage` and of `Image.list`, for the size of each question.
- `ShapeDoc.acceptsAt` is the precedent: recursion on the value, names resolved per step. The
  set of unfolded names generalizes its one-step resolution to unions and chains of names.
- Not reused in this slice: `Document`, `Store.Image` and `Modeled`, which are the faces' owners.

## Deviations from the brief

1. The measure has two numbers, not three. A union is read by its members in one call, so the
   type's size is not needed. The budget is a set of unfolded names, not a count, which makes
   the cycle cut provable.
2. `MemberIn` is the declarative form of the shape check `Val.hasTy`, at an allocation table.
   "The existing membership" at the empty table is `Val.hasTy`'s answer
   (`tyDecls_conservative`). `Fits` takes the table in the wiring slice.
3. The checker decides `MemberIn` on every table, guarded or not. Guardedness is then a
   formation condition, and its semantic content is the goal `guarded_fixedPoint_unique`.

## Open obligations

1. The three planned goals, each with its route in its docstring.
2. The wiring slice. The world holds the table, and `Val.hasTy` reads as `Val.hasTyIn` at it.
   `Fits` gains the same unfold rule. `fits_mono`, `fits_subN` and `fits_normalize` are restated
   over the table.
3. The table's admission as a located refusal (proposal 2 below).
4. The faces: the Schema bridge with `Reference` and `Suspend`, the recursive deriver and its
   membership law, and the TypeScript printer with the probe's two repairs.
5. A new `Ty` constructor with children needs an arm in `Val.obligations`. The catch-all treats
   it as a leaf, and the proof of `cata_declAlg_step` then fails, so the build names the gap.
6. The traversal census lists new hand traversals: `Val.hasTyIn` and `TyDecls.reaches` (well
   founded) and the pair functions (structural). `make check-*` is not run here.
7. The system map's R3 row and `docs/STATE.md` still say that recursive types wait on a ruling.
   Both are the coordinator's.

## Proposed decisions rows (proposals only)

1. **Recursive types: the representation of the foundation.** The table is
   `TyDecls := List (String × Ty)`, monomorphic. A body refers to a declared name by `app n args`
   or by `handle n`, and the table reads both. A declared name shadows the handle arm. Membership
   under the table is `MemberIn`, the least fixed point, decided by `Val.hasTyIn` with no fuel.
   `Ty.sub` stays unchanged and nominal. Kind: representation. Evidence: this receipt.
2. **The table's admission.** It refuses a repeated name and a name at an internal handle
   spelling (`externalHandleTarget`). It refuses a body with a type variable, and a declared
   name at a non-empty argument list. It refuses an unguarded table at the name on its cycle
   (`TyDecls.unguardedAt?`). Kind: domain.
3. **An external allocation at a declared name's spelling** (an owner's decision). Option (a):
   refuse the allocation, so that one spelling has one meaning. Option (b): allow it, and the
   handle fits no declared type, as the battery's control shows today. Recommendation: (a),
   since the printed module would give the two meanings one name. Kind: domain.
4. **Parameters by regular recursion.** An entry gains its parameters, a reference unfolds to
   the body at its arguments, and each recursive occurrence keeps the parameters unchanged.
   Each variance is read off its parameter's polarity into the variance table. Kind:
   representation; the slice after the wiring.
