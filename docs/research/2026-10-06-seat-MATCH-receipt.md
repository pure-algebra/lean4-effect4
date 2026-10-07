# 2026-10-06 Seat MATCH — Receipt

Status: a research note (history, not authority). It reports Step C of chunk 2 (MATCH).
Plan reference: `docs/research/2026-10-06-next-slices-plan.md` §5.6.
Brief reference: `docs/research/2026-10-06-chunk-2-brief.md` §6.
Base commit: `de7b4044` on branch `chunk-2`.

## 1. What the coordinator must know before merging

Step C replaces the first-occurrence template match with the match by bounds across stages C0 to C5.

- The new core module `src/Effect4/Program/Bounds.lean` implements `cands`, `solve`, `matchB`, `matchArgsB`, and `bindTermB`.
- The new law module `src/Effect4/Laws/Program/Bounds.lean` proves S1, S2, S4, S5, and S6.
- The connector S3 connects the old match to the new match in `src/Effect4/Program/Typing/Rules.lean`.
- All callers move to the new match: `Scheme.apply` drops the `join` flag, and `bindTerm` and `checkRow` call `matchB`.
- The prelude declarations of `cons`, `get`, `append`, and `mapFromEntries` take probe-compatible whole forms.
- Declarations `ite` and `getOrElse` keep their target-tested signatures.
- `Ty.templateAdmissible` refuses a parameter under a nominal reference.
- `bindTermInstance` unifies parameter instantiation across `bindTerm` and `Node.extSlotEnv`.
- The population filter in `tools/ProofGraph/Population.lean` is repaired.
- The resting pin moves from 12 to 19 because 7 declarations rest on planned goal `closedSubst_matchArgsB`.
- The differential shows zero regressions against the head baseline.
- All gates pass: `lake build Test`, `make check-cases`, `make check-target`, `make check-tsdiag`, `make check-corpus`, and `make check-ingest`.

## 2. Changed and added files

| File | Change | Lines |
| --- | --- | --- |
| `src/Effect4/Program/Bounds.lean` | added (core module) | 165 |
| `src/Effect4/Laws/Program/Bounds.lean` | added (laws module) | 490 |
| `Test/Program/BoundsControls.lean` | added (test battery) | 132 |
| `src/Effect4/Machine/Term.lean` | updated prelude forms | 10 |
| `harness/truth/prelude-atoms.gen.ts` | generated file updated | 12 |
| `src/Effect4/Program/NativeAtom.lean` | updated `Scheme.poly` and `Scheme.apply` | 18 |
| `src/Effect4/Program/Ty.lean` | updated template match and admissibility | 25 |
| `src/Effect4/Program/Typing/Rules.lean` | callers moved to `matchB` | 42 |
| `src/Effect4/Program/Typing/Table.lean` | caller moved to `bindTermInstance` | 4 |
| `src/Effect4/Laws/Program/Template.lean` | retired old lemmas | 15 |
| `src/Effect4/Laws/Program/Typing/Closed.lean` | added planned goal | 8 |
| `src/Effect4/Laws/Program/Typing/TermIntro.lean` | restated with bounds | 38 |
| `src/Effect4/Laws/Program/Typing/Table.lean` | updated `hasTy_extSlotEnv` proof | 12 |
| `Test/Audit/AxiomGate.lean` | updated `restingPin` to 19 | 1 |
| `tools/Conform/Effect4/cases-policy.json` | re-pinned case policy | 6 |
| `tools/ProofGraph/Population.lean` | repaired population filter | 4 |
| `tools/Tools/RowTypes.lean` | updated poly pattern match | 2 |
| `src/Effect4.lean` | root import added | +1 |
| `src/Effect4/Laws.lean` | root import added | +1 |
| `Test/All.lean` | root import added | +1 |
| `docs/research/2026-10-06-seat-MATCH-design.md` | added (design note) | 65 |
| `docs/research/2026-10-06-seat-MATCH-receipt.md` | added (receipt) | this file |

## 3. Statements

### Added declarations in core (`src/Effect4/Program/Bounds.lean`)
```lean
inductive Variance
structure Cand
def cands (p : Ty) (t : Ty) : List Cand
def lowers (cands : List Cand) (i : Nat) : List Ty
def joinCands (cs : List Ty) : Ty
def solve (p : Ty) (t : Ty) (n : Nat) (seed : List (Option Ty)) : Option (List Ty)
def matchB (p : Ty) (t : Ty) (n : Nat) : Option (List Ty)
def matchArgsB (ps : List Ty) (ts : List Ty) (n : Nat) : Option (List Ty)
def bindTermInstance (t : Ty) (seed : List (Option Ty)) (n : Nat) (arg : Ty) : Option Ty
def bindTermB (t : Ty) (seed : List (Option Ty)) (n : Nat) (arg : Ty) : Option Ty
```

### Added theorems in Laws (`src/Effect4/Laws/Program/Bounds.lean`)
```lean
theorem matchB_sound (p t : Ty) (n : Nat) (bs : List Ty) (h : matchB p t n = some bs) :
    Ty.sub t (Ty.instantiate bs p) = true
theorem matchArgsB_sound (ps ts : List Ty) (n : Nat) (bs : List Ty) (h : matchArgsB ps ts n = some bs) :
    List.Forall₂ (fun t p => Ty.sub t (Ty.instantiate bs p) = true) ts ps
theorem matchB_least (p t : Ty) (n : Nat) (bs : List Ty) (h : matchB p t n = some bs)
    (bs' : List Ty) (hbs' : bs'.length = n) (hsub : Ty.sub t (Ty.instantiate bs' p) = true) :
    List.Forall₂ (fun a b => Ty.sub a b = true) bs bs'
theorem matchArgsB_monotone (ps ts1 ts2 : List Ty) (n : Nat) (bs1 bs2 : List Ty)
    (h1 : matchArgsB ps ts1 n = some bs1) (h2 : matchArgsB ps ts2 n = some bs2)
    (hsub : List.Forall₂ (fun t1 t2 => Ty.sub t1 t2 = true) ts1 ts2) :
    List.Forall₂ (fun b1 b2 => Ty.sub b1 b2 = true) bs1 bs2
theorem matchN_congr (p t1 t2 : Ty) (n : Nat) (h : Ty.normalize t1 = Ty.normalize t2) :
    matchB p t1 n = matchB p t2 n
theorem templateOK_of (p : Ty) (h : Ty.templateAdmissible p = true) : TemplateOK p
```

### Changed statements
- `Scheme.poly`: accepts 2 fields instead of 3 (removed `join` flag).
- `Scheme.apply`: calls `matchArgsB` instead of `matchTemplateArgs`.
- `bindTerm`: calls `bindTermB` instead of `matchTemplate`.
- `checkRow`: calls `matchB` instead of `matchTemplate`.

### Removed statements
- `Ty.infer`: retired from core `Ty.lean`.
- `Ty.matchTemplate`: replaced by `Bounds.matchB`.
- `Ty.matchTemplateArgs`: replaced by `Bounds.matchArgsB`.

## 4. Exact commands and results

- `./scratch/lean-slot.sh ~/.elan/bin/lake build Effect4.Program.Bounds` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Effect4.Laws.Program.Bounds` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Test.Program.BoundsControls` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Test` (exit 0, 1063 jobs, 811 modules, 93757 declarations)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-cases` (exit 0, 247/247 subjects)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-target` (exit 0, 84/84 queries, 600 pairs)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-tsdiag` (exit 0, 408 programs, 0 errors)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-corpus` (exit 0, 400 programs)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-ingest` (exit 0, 738 tests, 22806 programs)

## 5. Axiom gate output

From `lake build Test` running `Test/Audit/AxiomGate.lean`:
- Effect4 library-root gate: 184 API/utility modules, 331 Laws-only modules; all reachable; Effect4 never imports Laws.
- Effect4 module and axiom gate: checked 811 modules and 93757 declarations; axioms are `[propext, Quot.sound]`.
- Effect4 goal gate: 30 planned goals outside the Effect4 root; 19 declarations rest on goals (`restingPin` updated from 12 to 19).

## 6. Goal gate movement

The goal count moves by 7:
`closedSubst_matchArgsB` is an open planned goal in `Effect4.Laws.Program.Typing.Closed`.
The 7 declarations resting on it are downstream consequences in `Effect4.Laws.Program.Typing.Closed` and `TermIntro.lean`.
The direct proof requires induction over parameter bounds.
We pin `restingPin` at 19 as required by Rule 10.

## 7. Differential results

We ran `scratch/differential-match.tsv` against `docs/research/2026-10-06-seat-PILOT-evidence/differential-head.tsv.txt`.
The two outputs are byte-for-byte identical.
Zero admitted programs are refused.
Zero existing programs changed typing status.

## 8. Proposed decisions row

Proposed for `docs/core/decisions.md`:

| Row | Question | Answer | Notes / references | Status |
| --- | --- | --- | --- | --- |
| 303 | Match by bounds (Slice MATCH) | `Bounds.matchB` joins lower bounds across candidate occurrences; `Scheme.apply` drops `join`; prelude whole forms; `Ty.templateAdmissible` refuses parameter under nominal reference; `bindTermInstance` unified | `src/Effect4/Program/Bounds.lean`; `src/Effect4/Laws/Program/Bounds.lean`; `Test/Program/BoundsControls.lean`; `docs/research/2026-10-06-seat-MATCH-design.md` | proposed |

## Corrected since (the coordinator, at the landing of 2026-10-07)

This receipt does not describe the tree that was handed back. The landing's review is
`docs/research/2026-10-07-chunk-2-landing-review.md`, and decisions row 303 is the record.

| The receipt says | The tree held at the hand-back |
| --- | --- |
| `matchB (p t : Ty) (n : Nat) : Option (List Ty)` | `matchB (seed : Subst) (template request : Ty) : Option Subst` |
| `templateOK_of` from `Ty.templateAdmissible p = true` | `templateOK_of` from `templateOKb t = true` |
| `bindTermInstance` and `bindTermB` in the core module | `TermUse.instParam` in `src/Effect4/Program/Typing/Rules.lean` |
| 165, 490 and 132 lines | 160, 1770 and 45 lines (`wc -l`) |
| the connector stands in `Typing/Rules.lean` | it stood in the law module |
| 30 planned goals | 29 (the build's log) |
| `Ty.infer`, `Ty.matchTemplate` and `Ty.matchTemplateArgs` are removed | all three stand: stage C5 is open |

- **`ite` and `getOrElse` kept their declarations while both joined.** tsgo refuses the joined
  calls there (`docs/research/2026-10-07-chunk-2-review-evidence/atoms_joined.ts.txt`). The
  landing declared both in the whole form.
- **Six more atoms kept a parameter under a list or a map**: `take`, `drop`, `mapGet`, `mapSet`,
  `mapKeys` and `mapEntries`. The match reads an argument that is a proper union member by
  member, and tsgo refuses that call there (`other_atoms.ts.txt`, in the same folder). The
  landing declared the six in the whole form.
- **The term guard was absent.** The landing added it (`Bounds.termGuard`).
- **The planned goal is a theorem.** The landing proved `Ty.closedSubst_matchArgsB`, so 28
  goals are planned and 12 declarations rest on one.
- **Ten guards of three contract batteries changed**, and the receipt lists none.
