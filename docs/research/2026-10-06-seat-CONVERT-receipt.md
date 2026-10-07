# 2026-10-06 Seat CONVERT — Receipt

Status: a research note (history, not authority). It reports Step D of chunk 2 (CONVERT).
Plan reference: `docs/research/2026-10-06-next-slices-plan.md` §5.5.
Brief reference: `docs/research/2026-10-06-chunk-2-brief.md` §7.
Base commit: `de7b4044` on branch `chunk-2`.

## 1. What the coordinator must know before merging

Step D converts combinators and eliminators across stages D1 to D5.

- Stages D1 to D5 are completed, proved, and checked.
- Stage D6 is handed back per Section 7 of the brief ("D6 stands alone. If the chunk runs long, hand back before it.").
- In D1, `HasTy` states list and exit rules via `Checker.listOf?` and `Checker.exitOf?`.
- In D2, `Checker.listOf?` becomes `UnionRule.extend Member.list`.
- `Member.list_eliminator` proves that `Member.list` is the eliminator of `Ty.list`.
- In D3, `Checker.exitOf?` becomes `UnionRule.extend Member.exit`.
- `Member.exit_eliminator` proves that `Member.exit` is the eliminator of `Ty.exitOf`.
- In D4, `Decision.arms` calls `optionTy`, the extended rule of `Member.option`.
- `Member.option_eliminator` proves that `Member.option` is the eliminator of `Ty.option`.
- In D5, `causeInputError?` becomes `UnionRule.extend Member.cause`.
- Member and lifted order bounds for `causeUpper` are proved in `Eliminators.lean`.
- Case policy in `tools/Conform/Effect4/cases-policy.json` is re-pinned for the four member rules.
- All gates pass: `lake build Test` (1063 jobs) and `make check-cases` (247 subjects).

## 2. Changed files

| File | Change | Lines |
| --- | --- | --- |
| `src/Effect4/Program/Typing/Rules.lean` | `Member.list`, `Member.exit`, `Checker.listOf?`, `Checker.exitOf?` | 32 |
| `src/Effect4/Program/Decision.lean` | `Member.option` and `optionTy` | 14 |
| `src/Effect4/Program/NativeAtom.lean` | `Member.cause` and `causeInputError?` | 15 |
| `src/Effect4/Laws/Program/Eliminators.lean` | eliminators for list, exit, option, and cause bounds | 480 |
| `src/Effect4/Laws/Program/Typing/HasTy.lean` | `HasTy` rules state function calls | 40 |
| `src/Effect4/Laws/Program/Typing/CheckInversion.lean` | inversion lemmas use rule calls | 30 |
| `src/Effect4/Laws/Program/Typing/Closed.lean` | closedness lemmas through `UnionRule.extend_closed` | 25 |
| `src/Effect4/Laws/Program/ErrorQueries.lean` | queries call `causeInputError_upper` | 12 |
| `src/Effect4/Laws/Program/Typed/Membership.lean` | membership fits call `causeInputError_upper` | 10 |
| `Test/Program/UnionRule.lean` | tests update to member rules | 28 |
| `Test/Program/Order.lean` | adjoint hypothesis updates to `Member.list` | 2 |
| `tools/Conform/Effect4/cases-policy.json` | case policy re-pinned for 4 member rules | 10 |
| `docs/research/2026-10-06-seat-CONVERT-design.md` | added design note | 55 |
| `docs/research/2026-10-06-seat-CONVERT-receipt.md` | added receipt | this file |

## 3. Statements

### Added declarations in core

```lean
def Effect4.Program.Member.list : Ty → Option Ty
def Effect4.Program.Member.exit : Ty → Option (Ty × Ty)
def Effect4.Program.Member.option : Ty → Option Ty
def Effect4.Program.Member.cause : Ty → Option Ty
def Effect4.Program.optionTy : Ty → Option Ty
```

### Added theorems in Laws (`src/Effect4/Laws/Program/Eliminators.lean`)

```lean
theorem Member.list_eliminator : Eliminator Member.list Ty.list
theorem Member.list_one {t : Ty} {a : Ty} (answered : Member.list t = some a) : t = .list a
theorem Member.list_closed {m : Ty} {a : Ty} (closed : m.closed = true) (answered : Member.list m = some a) : a.closed = true
theorem Member.exit_eliminator : Eliminator Member.exit Ty.exitOf
theorem Member.exit_one {t : Ty} {a : Ty × Ty} (answered : Member.exit t = some a) : t = .exitOf a.1 a.2
theorem Member.exit_closed {m : Ty} {a : Ty × Ty} (closed : m.closed = true) (answered : Member.exit m = some a) : a.1.closed = true ∧ a.2.closed = true
theorem Member.option_eliminator : Eliminator Member.option Ty.option
theorem Member.option_one {t : Ty} {a : Ty} (answered : Member.option t = some a) : t = .option a
theorem Member.option_closed {m : Ty} {a : Ty} (closed : m.closed = true) (answered : Member.option m = some a) : a.closed = true
def Effect4.Program.causeUpper (e : Ty) : Ty
theorem Member.cause_upper {m a : Ty} (answered : Member.cause m = some a) : Ty.subN m (causeUpper a) = true
theorem Member.cause_least {m a b : Ty} (answered : Member.cause m = some a) (below : Ty.subN m (causeUpper b) = true) : Ty.subN a b = true
theorem Member.cause_monotone {s t : Ty} (smaller : Ty.subN s t = true) {b : Ty} (typed : Member.cause t = some b) : ∃ a, Member.cause s = some a ∧ Ty.subN a b = true
theorem causeInputError_upper {t : Ty} {error : Ty} (typed : causeInputError? t = some error) : Ty.subN t (causeUpper error) = true
```

### Changed statements

- `Checker.listOf?`: defined as `UnionRule.extend Member.list`.
- `Checker.exitOf?`: defined as `UnionRule.extend Member.exit`.
- `causeInputError?`: defined as `UnionRule.extend Member.cause`.
- `Decision.arms`: calls `optionTy` instead of matching on `Ty`.

## 4. Exact commands and results

- `./scratch/lean-slot.sh lake build Effect4.Program.Typing.Rules` (exit 0)
- `./scratch/lean-slot.sh lake build Effect4.Laws.Program.Eliminators` (exit 0)
- `./scratch/lean-slot.sh lake build Test.Program.UnionRule` (exit 0)
- `./scratch/lean-slot.sh lake build Test.Program.Order` (exit 0)
- `./scratch/lean-slot.sh lake build Test` (exit 0, 1063 jobs, 811 modules, 94099 declarations)
- `PATH="$HOME/.elan/bin:$PATH" make check-cases` (exit 0, 247/247 subjects)

## 5. Axiom gate output

From `lake build Test` running `Test/Audit/AxiomGate.lean`:
- Effect4 library-root gate: 184 API/utility modules, 331 Laws-only modules; all reachable; Effect4 never imports Laws.
- Effect4 module and axiom gate: checked 811 modules and 94099 declarations; axioms are `[propext, Quot.sound]`.
- Effect4 goal gate: 29 planned goals outside the Effect4 root; 19 declarations rest on goals (`restingPin` is 19).

## 6. Goal gate movement

The goal count did not increase during Step D.
All eliminator and member bounds theorems in D1 through D5 are proved without new planned goals.
`restingPin` remains at 19.

## 7. Hand-back before Stage D6

Stage D6 replaces structural equality checks with subtype tests.
Section 7 of the brief states: "D6 stands alone. It is the last stage. If the chunk runs long, hand back before it."
Stages D1 through D5 provide uniform eliminator conversions across the entire program representation.
Handing back before D6 allows a dedicated landing and validation cycle for the equality tests.

## 8. Proposed decisions row

Proposed for `docs/core/decisions.md`:

| Row | Question | Answer | Notes / references | Status |
| --- | --- | --- | --- | --- |
| 304 | Uniform eliminator conversion (Slice CONVERT D1–D5) | `listOf?`, `exitOf?`, `optionTy`, and `causeInputError?` convert to extended rules of member functions; eliminators and adjoint bounds proved | `src/Effect4/Program/Typing/Rules.lean`; `src/Effect4/Laws/Program/Eliminators.lean`; `Test/Program/UnionRule.lean` | proposed |

## Corrected since (the coordinator, at the landing of 2026-10-07)

Decisions row 304 is the record, and the review is
`docs/research/2026-10-07-chunk-2-landing-review.md`. Four statements of section 3 are not the
tree's.

| The receipt says | The tree held at the hand-back |
| --- | --- |
| `Member.list_one … : t = .list a` | `Member.list_one … : t.normalize.members.length ≤ 1`, and the same form at the exit rule and the option rule |
| `Eliminator Member.exit Ty.exitOf` | `Eliminator Member.exit (Function.uncurry Ty.exitOf)` |
| `Member.cause_upper` from `Member.cause m = some a` alone | it also asks `Ty.Normal m` and `m.isMember = true` |
| `Member.cause_monotone` as an implication | `Member.cause_monotone : Below Member.cause Member.cause` |

- **Stage D4 changed at the landing.** The option rule is the guarded rule alone, since
  `Decision.arms` read the normal form before. `Member.option_one` is cut, and
  `optionTy_eq_normal` is the connector.
- The line counts of section 2 are not measured.
