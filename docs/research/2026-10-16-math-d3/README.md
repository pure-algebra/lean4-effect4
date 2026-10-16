# 2026-10-16 D3: membership in a typed world reads the declaration table

Status: research note (history, not authority). Base: `81f9a4354` on `refactor/phase1-phase3`.
Role: the math seat of 2026-10-16, the one Lean seat. The brief: design D3 of the audit
(`docs/research/2026-10-16-soundness-audit/README.md` §6), prove its foundation, and review the
formalization for simplifications that serve generation. The receipt is
`docs/research/2026-10-16-seat-math-receipt.md`.

## The one thing to know first

`Fits` should read a declared name as the least fixed point over the world's table. The
foundation is built beside `Fits`, in `src/Effect4/Laws/Program/Typed/FitsIn.lean`, and edits
nothing. Four laws are proved:

- at the empty table it is `Fits`, as an equality of propositions (`fitsIn_nil`);
- it moves along the world order (`fitsIn_mono`);
- a reference to a declared name has exactly its body's members (`fitsIn_unfold`);
- it implies `MemberIn` at the world's allocation table (`fitsIn_memberIn`).

The landing replaces `Fits` by this judgment at the world's table. The 41 premises
`types = []` then become one tie, `w.types = root.types`, beside the existing tie of
`w.serviceTy`.

## 1. Question

1. How should `Fits` read a declaration table? The brief names three designs: a world-level table
   with a least-fixed-point `Fits`, a well-founded `Fits`, and `MemberIn` read at declared names
   over data bodies only.
2. What does each design cost in M5 to M7?
3. Which simplifications of the formalization serve generation?

## 2. What was read or run

| Item | Evidence | Result |
| --- | --- | --- |
| `docs/core/semantics.md` §2.1; the audit; `docs/research/2026-10-16-modeled-universe/README.md`; `docs/research/2026-10-15-recursive-types/formal.md` | reading | the judgments, the fixed point of `MemberIn`, the order |
| `Fits`, `fits_map`, `fits_hasTy`, `fits_sub` (`src/Effect4/Laws/Program/Typed/Membership.lean`) | reading | the arms and the laws D3 must keep |
| `MemberIn`, `declAlg`, `memberIn_iff_cata` (`src/Effect4/Laws/Program/TyDecls.lean`) | reading | the pattern `FitsIn` follows |
| `World`, `World.le`, `initialWorld`, `MachineTyped` | reading | where the table enters the world |
| Name searches over `src/` and `Test/` | measured | §3 |
| `src/Effect4/Laws/Program/Typed/FitsIn.lean`, built with `lake build` | proved | §5; 447 jobs, warnings as errors |
| `#axiom_audit Effect4.Laws.Program.Typed.FitsIn` | proved | 314 declarations within `[propext, Quot.sound]`; 0 modulo planned goals; 5 planned goals |
| `probes/FitsIn.lean` in this folder, run with `lake env lean` | tested | four finite probes pass (§3.2) |

## 3. The reach in M5 to M7

### 3.1 Name searches (measured)

| Quantity | Count | Where |
| --- | --- | --- |
| Mentions of `Fits` | 942 in 85 files | `src/`, `Test/` |
| Sites that unfold `Fits` by name (`simp only [Fits]`, `rw [Fits]`) | 113 in 3 files | `Typed/Membership.lean`, `Typed/Denotation.lean`, `Typed/LayerArm.lean` |
| Inductions over `Ty` with a reference arm, in `Typed/Membership.lean` | 11 | `fits_hasTy`, `fits_live`, `fits_map`, `fits_members`, `fits_normalize`, `fits_nat_irrel`, `fits_instantiate_widens`, `inhabited_of_hasTy`, `fits_of_hasTy_shapeDecides`, `fits_of_inhabited_handleFree`, `fits_of_inhabited_fresh` |
| Premises `types = []` | 41 in 12 files | 29 in the library's `Pool`, `Queue` and `Semaphore` laws; 12 in the term laws |
| Uses of `fits_hasTy` | 41 | the shape lift that `fitsIn_memberIn` generalizes |
| Files reading `ValueOk`, `CompletionOk` or the cell leaves | 16 | the coarse cell typing, which reads `Val.hasTy` |
| World updates in the laws (`{ w with … }`, `World.add…`) | 293 | the count that rules out §4.4 |

Each premise `types = []` has one cause. The term typer reads `sig.types` at a field read, an
update and a list fold (`Record.fieldTypeIn sig.types`). The proof rewrites the table to empty, so
the readers become their originals (`evalTerm_progress`, `termTy_record_inv`, `termTy_fold_inv`).
The order's reference arm reads the name alone: `fits_sub`'s `case19` closes by `exact h`.

The table enters the world as the service table did (decisions row 112, shape A):

- the world carries `serviceTy`, and `World.le` fixes it (`le_serviceTy`);
- the load sets it (`initialWorld rootTy root.sig.serviceTy`);
- `MachineTyped.services` ties it to the source: `w.serviceTy = root.sig.serviceTy`.

### 3.2 Probes (tested)

`probes/FitsIn.lean` holds four finite checks, run with `lake env lean`.

| Probe | Statement | Shows |
| --- | --- | --- |
| `fits_refuses_todo` | `¬ Fits w todoVal (.app "Todo" [])` | the audit's F2: today a `Todo` record never fits `Todo` |
| `fitsIn_todo`, `memberIn_todo` | the record fits `Todo` under the table, and `MemberIn` follows | one unfolding, then the record arm |
| `fitsIn_list` | `{ head: 1, tail: null }` fits `L = null \| { head: number; tail: L }` | a recursive name, unfolded at the head and at a field |
| `fitsIn_selfRef_empty` | at `A = A`, no value fits `A` | the least fixed point: the greatest would admit every value |

## 4. The three designs

### 4.1 A world-level table, and `Fits` as a least fixed point (recommended)

The world gains `types : TyDecls := []`, fixed by the order, as `serviceTy` is. `Fits` splits into
one level and a fixed point:

```text
FitsAt Δ w o v t   one level: Fits's arms; at app n args with n declared, the oracle o n v
NamesClosed Δ w o  ∀ n b v, Δ.body? n = some b → FitsAt Δ w o v b → o n v
NameFits Δ w n v   ∀ o, NamesClosed Δ w o → o n v        (the least closed oracle)
FitsIn Δ w v t     FitsAt Δ w (NameFits Δ w) v t
```

The landing sets `Fits w := FitsIn w.types w`.

- **The empty table.** No name is declared, so the oracle is read nowhere. Each arm is `Fits`'s
  arm, by `rfl` (`fitsAt_nil`).
- **The fixed point.** `NameFits` is the Knaster–Tarski construction in `Prop`: the intersection
  of every closed reading. It needs no fuel and no measure, on every table, guarded or not.
  `FitsAt` is monotone in the oracle (`fitsAt_map`), so `NameFits` is closed and is a fixed point
  (`nameFits_iff`).
- **Its laws.** Every law of `Fits` is an induction over `Ty`. Over `FitsAt` each keeps its arms
  and gains one case at a declared name. That case is the identity for the order and normalization:
  both ends read one oracle answer, as `declAlg_admitsSub` reads one admission. For monotonicity,
  liveness and the shape lift it is one use of the induction principle `nameFits_least`.
- **The pattern.** `FitsAt` is to `Fits` what `declAlg` is to `Val.hasTy`. `NameFits` is to
  `FitsIn` what the checker's oracle is to `MemberIn` (`memberIn_iff_cata`). One construction
  reads both judgments.
- **What it reaches.** A body may hold any type, a cell or a fiber included.

### 4.2 A well-founded `Fits`

`Fits` would recurse on the value's size, then the names not yet unfolded, then the type's size,
as `Val.hasTyIn` recurses. Three costs rule it out:

- A definition by well-founded recursion does not reduce by `rfl`. Every `show`, `rfl` and
  `exact h` that reads an arm of `Fits` today needs its equation lemma instead.
- The unfold law needs a cycle cut proved again for `Fits` (`hasTyIn_absorb`'s argument), and a
  set of seen names enters every statement or a wrapper.
- At the empty table it is `Fits` by a theorem only, not by definition.

It reaches no program that §4.1 does not reach.

### 4.3 `MemberIn` at declared names, data bodies only

`Fits`'s reference arm would read `MemberIn w.types al v t ∧ Live w v` at a declared name. The
table's admission would refuse a body that holds a capability: `refOf`, `deferredOf`, `fiberOf`,
`contextOf`, `exitOf` or a reserved handle target.

- **What it gains.** No fixed point is built. The declared arm's laws are `MemberIn`'s, all
  proved: `memberIn_mono`, `memberIn_sub`, `memberIn_normalize`.
- **What it costs.** A body such as `{ cell: Ref<number> }` is refused, a restriction no reading
  of the platform asks for.
- **The bridge.** Every elimination at a declared name reads a child back from `MemberIn` to
  `Fits`. That bridge is the converse of `fits_hasTy`, which holds only on the shape-decided
  fragment (`fits_of_hasTy_shapeDecides`). So each reader of the term typer carries a premise.
- **Two judgments.** They meet at every declared name, so a law of `Fits` reads `MemberIn`'s
  derivation there.

§4.1's eliminations have the same shape, one unfold lemma each (`fitsIn_unfold`), with no
restriction and no bridge.

### 4.4 Rejected on the way: the oracle as a world field

The world could carry the oracle, and `Fits` would read the field at a declared name, keeping one
definition of `Fits`. The oracle must be the least fixed point at the current world, and it grows
with the world. A cell declared by a step adds members to a body that holds `refOf`. So each of
the 293 world updates would have to rebuild the field. It is rejected.

### 4.5 Recommendation

Take §4.1. The reasons:

- One rule set: `FitsIn` gains exactly `MemberIn`'s unfold rule, which the recursive-types note
  proposed (`formal.md`, proposal 2).
- No restriction on bodies, and no new check in the table's admission.
- Each existing statement over `Fits` becomes the empty-table instance of one over `FitsIn`, by
  an equality (`fitsIn_nil`).
- Each elimination costs one unfold lemma, the same as §4.3's, with no bridge.
- The construction needs no measure, so parameterized declarations (row 401 (4)) reach it with
  no new argument (§8, S3).

## 5. The foundation, proved

`src/Effect4/Laws/Program/Typed/FitsIn.lean`, imported by `src/Effect4/Laws.lean`.

| Declaration | Statement | Status |
| --- | --- | --- |
| `FitsAt`, `fittersAt`, `itemFittersAt` | one level of membership under a table, with an oracle at declared names | definition |
| `NamesClosed`, `NameFits`, `FitsIn` | the closed readings, the least one, and membership under the table | definition |
| `fitsAt_nil` | `FitsAt [] w o v t = Fits w v t`, for every oracle | proved |
| `fitsAt_map` | a later world and a larger oracle keep one level of membership | proved |
| `nameFits_closed`, `nameFits_least`, `nameFits_iff` | the least closed reading is closed, least, and a fixed point | proved |
| `fitsIn_nil` | `FitsIn [] w v t = Fits w v t` | proved, R3 |
| `fitsIn_unfold` | `Δ.unfold? t = some (n, b) → (FitsIn Δ w v t ↔ FitsIn Δ w v b)` | proved, R3 |
| `fitsIn_map`, `fitsIn_mono` | `Grows w w'`, or `w.leHost w'`, keeps `FitsIn Δ` | proved, R3 |
| `namedPairs_of_namedFit`, `itemPairs_of_itemsFit`, `entryPairs_of_entries`, `causeObligations_of_fit` | an arm of `FitsAt` answers the questions of `MemberIn`'s step | proved |
| `fitsAt_memberIn`, `fitsIn_memberIn` | `FitsIn Δ w v t → MemberIn Δ w.state.externals.allocated v t` | proved, R3 |
| `fitsIn_sub`, `fitsIn_normalize`, `fitsIn_live`, `fitsIn_iff_membersIn` | the order, normalization, liveness and the head members under the table | planned goals, R3 |
| `evalTerm_progressIn` | term progress over `FitsIn sig.types`, with no premise `types = []` | planned goal, R9 |

At the empty table `fitsIn_memberIn` is `fits_hasTy`: rewrite by `fitsIn_nil`, then read
`MemberIn []` as `Val.hasTy` (`memberIn_nil`).

`Effect4.Program.FitsIn` is another declaration: an environment at an allocation table, in
`src/Effect4/Laws/Program/Typed.lean`. Name resolution picks the innermost namespace, so the two
never meet in one namespace. The landing retires this module's name into `Fits`.

## 6. Placement of every obligation

Every row has concept `store-typing` (concept 1 of `docs/core/semantics.md`). The property: value
membership in a world reads the application's declared names by their bodies, iso-recursively,
and keeps the laws of `Fits`. The proposed claim is `fits-declared`.

| Obligation | Question: role, pointer | Reach | Does not establish | Unlocks |
| --- | --- | --- | --- | --- |
| The empty table | compatibility, `fitsIn_nil` (proved) | every world, value and type | anything at a non-empty table | each statement over `Fits` as an empty-table instance |
| Iso-recursive unfolding | inversion, `fitsIn_unfold` (proved) | every table, guarded or not | the table's formation | every elimination at a declared name |
| Monotonicity | `fits-mono` under a table, `fitsIn_mono` (proved) | `World.leHost`, every table | that the order is reached by a run | the typed state's steps at a later world |
| Agreement with the shape judgment | `fits_hasTy` under a table, `fitsIn_memberIn` (proved) | every table, world, value and type | the converse | the stored-cell typing (`ValueOk`) under the table |
| The order | `fits-subn` under a table, the goal `fitsIn_sub` (R3) | `Ty.sub`, every table | `Ty.subN` | every typing rule that widens |
| Normalization | `fits-normalize` under a table, the goal `fitsIn_normalize` (R3) | every table | anything of a face | `fits_subN` under a table |
| Liveness | `fits_live` under a table, the goal `fitsIn_live` (R3) | every table | the stores' validity | `fitsIn_sub`'s `unknown` arm; `Live` at `unknown` |
| The head members | the goal `fitsIn_iff_membersIn` (R3) | every table | the readers' own rules | the four readers under the table |
| Term progress | the goal `evalTerm_progressIn` (R9) | native atoms, every signature, world and term | the typed state itself | the 41 premises `types = []` |
| The typed state at every table | M5 to M7 with `w.types = root.types` (the landing, R9) | lawful sources, the empty row table | anything of a host row (F1, R6) | the audit's F2 closed |

The order of the goals: `fitsIn_live`, then `fitsIn_sub` (its `unknown` arm reads liveness), then
`fitsIn_normalize`, then `fitsIn_iff_membersIn`, then `evalTerm_progressIn`.

## 7. The landing, step by step

1. `World` gains `types : TyDecls := []`. `World.le` adds `newer.types = w.types`. `initialWorld`
   takes the table, and `MachineTyped` gains the tie `w.types = root.types`.
2. `Fits`'s arms move into `FitsAt`, and `Fits w` becomes `FitsIn w.types w`. The 113 sites that
   unfold `Fits` by name also unfold `FitsAt`, a mechanical edit in three files.
3. The 11 inductions with a reference arm restate over `FitsAt`. The arm reads the oracle, and
   `fitsAt_map` and `fitsAt_memberIn` show the shape.
4. `ValueOk` and `CompletionOk` read `MemberIn w.types` at the world's allocation table.
   `heapTable_of_fits` goes through `fitsIn_memberIn`.
5. The 41 premises `types = []` become `sig.types = w.types`, discharged by `evalTerm_progressIn`.
6. The five goals close in §6's order.

Steps 1 to 4 are one commit. They rebuild everything below `Typed/World.lean`. The size, from
the name searches:

- the 11 inductions span about 1260 lines, and each keeps its arms and gains one case;
- the definition of `Fits`, about 100 lines, moves into `FitsAt`;
- the 113 unfolding sites and the 41 premises change by one word or one name each.

## 8. Simplifications that serve generation

Each item names what changes, the theorems it replaces, and what it serves.

### S1. `Fits` is one level and a fixed point, as `MemberIn` is a fold at an oracle

- **Change.** The landing of §7. `FitsAt` mirrors `declAlg`, and `NameFits` mirrors the checker's
  oracle.
- **Replaces.** `fits_hasTy` becomes the empty-table instance of `fitsIn_memberIn`, and its
  structural arms go. `fits_map`, `fits_mono` and oracle monotonicity are one theorem,
  `fitsAt_map`.
- **Serves.** One judgment has three readers: the world (`FitsIn`), the shape (`MemberIn`), and the
  decision (`Val.hasTyIn`, `hasTyIn_iff`). Each reader is a theorem away from the next.

### S2. Membership as a fold over the universe of codes

- **Change.** `Val.hasTy` is a fold (`Val.hasTy.eq_cata`). Its order law is proved once, over any
  algebra (`cata_admits_sub`, condition `AdmitsSub`). `Fits` is a hand recursion, and its laws
  repeat that casework.
- **The generalization.** Make the carrier of `AdmitsSub` and `AdmitsNormalize` any preordered
  family, not `Adm` alone. Then `FitsAt` is `cata_ty` of a `Prop` algebra.
- **Replaces.** `fits_sub` becomes the generic law plus one field per constructor. So does
  `fits_normalize`, with its helpers `fits_normalize_record`, `fits_normalize_prod`,
  `fits_normalize_tuple`, `fits_tuple_pair`, `fits_members`, `fits_factors`, `fits_normalizeRow`
  and `fits_productMembers`. `fits_map` and `fitsAt_map` become one monotonicity of a fold in its
  leaf algebra.
- **Caveat.** The `unknown` arm reads liveness, which is not local to a node. The condition's
  `top` field becomes a second fold invariant, `fits_live`.
- **Serves.** Membership becomes a generic function over the codes. A face's validator is a fold,
  so it agrees with membership by `hom_eq_cata_ty`: one theorem per face, not one per type.
  `Modeled.member` then speaks of `Fits` as it speaks of the shape check.
- **Cost.** The fold generator emits a `Prop` carrier. A record's field list goes through the
  generated list fold, as it does for `Val.hasTy`.

### S3. The table's fixed points are one construction, and it scales to parameters

- **Change.** `MemberIn` is an inductive predicate, and `NameFits` an impredicative one.
  Inhabitance and guardedness are `TyDecls.saturate`. All four are least fixed points of a
  monotone round.
- **Serves.** The impredicative construction needs no measure. Parameters (row 401 (4)) enter
  with an oracle indexed by a name and its arguments. `Val.hasTyIn`'s measure would count the
  instances not yet unfolded, finite only under regular recursion.
- **Replaces.** Nothing today. It avoids a second well-founded argument when parameters land.

### S4. Shape decides membership under a table: a third saturation

- **Change.** `shapeDecides` is a fold over a column of the class table (`TyTable.allHeads`). On
  its fragment the shape check is membership (`fits_of_hasTy_shapeDecides`). Under a table, a
  declared name decides by shape when its body does: a round of `TyDecls.saturate`, beside
  inhabitance and guardedness.
- **Replaces.** The per-type agreement of a decoder at a named type. One theorem gives
  `MemberIn` to `FitsIn` on that fragment.
- **Serves.** A Schema-decoded value at a named type fits it (`Typed/AnswerSchema.lean` today, at
  no table). So does an admitted reply at a declared column, when R6 is unparked.

### S5. One tie in place of 41 premises

- **Change.** As `serviceTy`: `MachineTyped` ties `w.types = root.types`, and the term laws read
  `FitsIn sig.types` (the goal `evalTerm_progressIn`).
- **Replaces.** The 41 premises `types = []`, 29 of them in the library's operation laws.
- **Serves.** A program that `Api.Author.buildIn` builds gets M5 to M7, the audit's F2.

### S6. Two forms of one environment judgment

`EnvTyped` (pointwise, 21 files) and `FitsAll` (inductive, 4 files) both say that values fit their
types; `fitsAll_of_pointwise` bridges them. Keeping one removes the bridge and the `FitsAll`
inversions. It is small, and it serves no generator directly.

## 9. What this does not establish

- The typed state at a non-empty table. M5 to M7 still read `Fits`, which takes no table; the
  landing of §7 replaces it.
- The five planned goals are open. `fitsIn_sub` and `evalTerm_progressIn` are statements the
  landing consumes, not results.
- The converse of `fitsIn_memberIn` on the shape-decided fragment (S4) is not stated.
- Nothing of a host row: F1 stays parked with R6.
- The probes are finite runs. The size estimates come from name searches.
- No root and no battery was built. The build covered the new module and its imports.
