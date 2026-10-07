# 2026-10-06 Seat TABLE — Receipt

Status: a research note (history, not authority). It reports Wave 1, Slice 2 (TABLE).
Plan reference: `docs/research/2026-10-06-next-slices-plan.md` §5.2.
Base commit: `6d097d64` on branch `refactor/phase1-phase3`.

## 1. What the coordinator must know before merging

Slice TABLE lands the program address table, the distinct refusal list, and the term slot
environment projector without modifying any existing statement.

- `Node.addresses` is defined over the generated `foldMapAt_*` functions in core module
  `src/Effect4/Program/Typing/Table.lean`. It connects to `Node.foldList` in Laws via `addresses_eq_foldList`.
- `refusals_head` and `refusals_nil_iff` are fully proved with zero open goals.
- `mem_addresses_of_at` is fully proved with zero open goals.
- `mem_addresses_iff` is stated as a placed planned goal under `initial-algebras-folds` (requirement R14).
- `table_replace_outside` is deferred to slice PASS as instructed by the coordinator.
- All 15 controls from `address-table-probe` pass in `Test/Program/TableControls.lean`.
- All gates are green: `lake build Test` (1055 jobs), `make check-cases`, `make check-docs`,
  and `make check-language`.

## 2. Changed and added files

| File | Change | Lines |
| --- | --- | --- |
| `src/Effect4/Program/Typing/Table.lean` | added (core module) | 111 |
| `src/Effect4/Laws/Program/Typing/Table.lean` | added (laws module) | 148 |
| `Test/Program/TableControls.lean` | added (test battery) | 84 |
| `src/Effect4/Program/Sketch.lean` | added `Sketch.table` and `Sketch.refusals` | +9 |
| `src/Effect4.lean` | root import added | +2 |
| `src/Effect4/Laws.lean` | root import added | +1 |
| `Test/All.lean` | root import added | +1 |
| `docs/research/2026-10-06-seat-TABLE-design.md` | added (design note) | 78 |

## 3. Statements

No existing statement was changed or removed.

### Added declarations in core (`src/Effect4/Program/Typing/Table.lean`)
```lean
def Node.addresses (n : Node Op) : List (List Nat)
structure Table.Entry
abbrev Entry := Table.Entry
def table (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : List Table.Entry
def refusals (s : Signature Op) (env0 : TyEnv) (p : Eff Op) : List TypeRefusal
inductive ExtSlot
def Node.extSlotEnv (s : Signature Op) (env : TyEnv) (n : Node Op) : ExtSlot → Option TyEnv
```

### Added declarations in core (`src/Effect4/Program/Sketch.lean`)
```lean
def table (s : Sketch) (app : SigApp := {}) : List Table.Entry
def refusals (s : Sketch) (app : SigApp := {}) : List TypeRefusal
```

### Added theorems in Laws (`src/Effect4/Laws/Program/Typing/Table.lean`)
```lean
def addressYield : PathYield Op (List Nat)
theorem addresses_eq_foldList (n : Node Op) : Node.addresses n = n.foldList addressYield []
theorem mem_addresses_of_at {n : Node Op} {a : List Nat} (h : (n.at_ a).isSome = true) : a ∈ Node.addresses n
theorem addresses_eff_head (p : Eff Op) : ∃ rest, Node.addresses (.eff p) = [] :: rest
theorem table_head (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    ∃ rest, table s env0 p = ⟨[], some (.env env0), some (Checker.check s env0 [] p)⟩ :: rest
theorem table_result_refusal_none_of_hasTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    (hp : HasTy s env0 p T) {e : Table.Entry} (he : e ∈ table s env0 p) : e.result.bind Checker.refusal = none
theorem refusals_of_hasTy {s : Signature Op} {env0 : TyEnv} {p : Eff Op} {T : EffTy}
    (hp : HasTy s env0 p T) : refusals s env0 p = []
theorem refusals_head (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    (refusals s env0 p).head? = explain s env0 p
theorem refusals_nil_iff (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    refusals s env0 p = [] ↔ (effTy s env0 p).isSome = true
proof_goal mem_addresses_iff (n : Node Op) (a : List Nat) :
    a ∈ Node.addresses n ↔ (n.at_ a).isSome = true
```

## 4. Exact commands and results

- `./scratch/lean-slot.sh ~/.elan/bin/lake build Effect4.Program.Typing.Table` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Effect4.Program.Sketch` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Effect4.Laws.Program.Typing.Table` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Test.Program.TableControls` (exit 0)
- `./scratch/lean-slot.sh ~/.elan/bin/lake build Test` (exit 0, 1055 jobs)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-cases` (exit 0)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-docs` (exit 0)
- `PATH="$HOME/.elan/bin:$PATH" ./scratch/lean-slot.sh make check-language` (exit 0)

## 5. Axiom audit output

From `lake build Test` running `Test/Audit/AxiomGate.lean`:
- Effect4 library-root gate: 183 API/utility modules, 330 Laws-only modules; every library source is reachable; Effect4 never reaches Laws.
- Effect4 module and axiom gate: checked 807 modules and 93114 declarations; semantic/test axioms are `[propext, Quot.sound]`.
- Effect4 goal gate: 29 planned goals outside the Effect4 root; 12 declarations rest on goals; no other declaration reaches `sorryAx`.

## 6. Proposed decisions row

Proposed for `docs/core/decisions.md`:

| Row | Question | Answer | Notes / references | Status |
| --- | --- | --- | --- | --- |
| 302 | The address table and list of refusals (Slice TABLE) | `Node.addresses` over `foldMapAt_*`; `table` with `Entry`; `refusals` via `filterMap` and `eraseDups`; `Sketch.table`/`Sketch.refusals`; `Node.extSlotEnv` for 5 extended term slots; `refusals_head` and `refusals_nil_iff` proved | `src/Effect4/Program/Typing/Table.lean`; `src/Effect4/Laws/Program/Typing/Table.lean`; `Test/Program/TableControls.lean`; `docs/research/2026-10-06-seat-TABLE-design.md` | proposed |

## 7. Open obligations

1. `mem_addresses_iff` converse (`a ∈ Node.addresses n → (n.at_ a).isSome = true`) remains a planned goal.
2. `table_replace_outside` (the frame of an edit) remains proposed for slice PASS.

## Corrected since (the coordinator, at the landing, 2026-10-06; decisions row 302)

- **`mem_addresses_iff` is a theorem.** Open obligation 1 is closed, by
  `Node.mem_foldList_iff` (`src/Effect4/Laws/Program/PathFold.lean`). `mem_addresses_of_at` is
  cut, since the two-way statement holds it. The goal gate reads 28 planned goals.
- **The slot table has its law**: `Node.extSlotTerm` and `hasTy_extSlotEnv`.
- **`abbrev Entry` is cut.** The type has one name, `Table.Entry`.
- **The counts at the landing**: 807 modules and 93227 declarations; 28 planned goals; 12
  declarations rest on goals, which the gate pins now (`restingPin`).
- The review is `docs/research/2026-10-06-slice-TABLE-review.md`.
