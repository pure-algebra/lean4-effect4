# 2026-10-06 Seat QUERY — Receipt

Status: a research note (history, not authority). It reports Step A of chunk 2 (QUERY).
Plan reference: `docs/research/2026-10-06-next-slices-plan.md` §5.3.
Brief reference: `docs/research/2026-10-06-chunk-2-brief.md` §4.
Base commit: `de7b4044` on branch `chunk-2`.

## 1. What the coordinator must know before merging

Step A lands the on-demand query library and driver without altering any existing theorem.

- The pure logic lives in `tools/Tools/Query.lean`.
- The CLI driver lives in `tools/Drivers/Query.lean`.
- The tool reads canonical program hex bytes via `Effect4.Store.bytesOfHex` and `Effect4.Program.Wire.decodeProgram`.
- Each answer names its supporting law:
  `holes_conservative`, `mem_addresses_iff`, `focusAt_typed`, `refusals_nil_iff`,
  `refusals_head`, `hasTy_extSlotEnv`, `Sketch.check_omit_focusAt`, or `Sketch.check_fill_focusAt`.
- The battery `Test/Program/QueryControls.lean` verifies operations against `FocusControls` and `TableControls`.
- `Test/fixtures/query/transcript.jsonl` records 10 concrete requests and answers.
- All gates pass: `lake build Test` (1056 jobs), library-root gate, axiom gate, and goal gate (pin 12).

## 2. Changed and added files

| File | Change | Lines |
| --- | --- | --- |
| `tools/Tools/Query.lean` | added | 224 |
| `tools/Drivers/Query.lean` | added | 30 |
| `Test/fixtures/query/transcript.jsonl` | added | 10 |
| `Test/Program/QueryControls.lean` | added | 73 |
| `Test/All.lean` | root import added | +1 |
| `docs/research/2026-10-06-seat-QUERY-design.md` | added (design note) | 67 |
| `docs/research/2026-10-06-seat-QUERY-receipt.md` | added (receipt) | this file |

## 3. Statements

Step A adds no new theorem or inductive type to the core tree.

### Added declarations in `tools/Tools/Query.lean`
```lean
def parseExtSlot (s : String) : Option ExtSlot
def extSlotToString : ExtSlot → String
structure Request
def Request.fromJson? (j : Json) : Except String Request
structure Answer
def Answer.toJson (a : Answer) : Json
def effTyJson (t : EffTy) : Json
def refusalJson (r : TypeRefusal) : Json
def checkResultJson : Except TypeRefusal EffTy → Json
def nodeEnvJson : Option NodeEnv → Json
def entryJson (e : Table.Entry) : Json
def litJson : Lit → Json
def termJson : Term → Json
def termsJson : Terms → Json
def answer (req : Request) : Answer
```

### Added declarations in `tools/Drivers/Query.lean`
```lean
def main : IO Unit
```

## 4. Exact commands and results

- `scratch/lean-slot.sh lake build Tools` (exit 0, 378 jobs)
- `scratch/lean-slot.sh lake build Test.Program.QueryControls` (exit 0, 305 jobs)
- `scratch/lean-slot.sh lake build Test.All` (exit 0, 1056 jobs)
- `python3 scripts/check-language.py --show docs/research/2026-10-06-seat-QUERY-design.md` (exit 0)

## 5. Axiom gate output

From `lake build Test.All`:
- Effect4 library-root gate: 183 API/utility modules, 330 Laws-only modules; every library source is reachable; Effect4 never reaches Laws.
- Effect4 module and axiom gate: checked 808 modules and 93227 declarations; semantic/test axioms are `[propext, Quot.sound]`; exact implementation boundary additionally allows `Classical.choice`.
- Effect4 goal gate: 28 planned goals outside the Effect4 root; 12 declarations rest on goals; no other declaration reaches `sorryAx`.

## 6. Proposed architecture rows

Proposed for `docs/ARCHITECTURE.md`:

| Module | Purpose | Imports |
| --- | --- | --- |
| `Tools.Query` | Evaluates program queries on demand from canonical bytes | `Effect4.Program.Sketch`, `Effect4.Program.Typing.Table`, `Effect4.Store.Domain.ProgramWire` |
| `Drivers.Query` | Thin standard-input driver for query tool | `Tools.Query` |

## 7. Open obligations

1. Canonical wire codec for `RowTable` and `Sketch`:
   `Sketch` currently lacks a canonical byte encoder.
   Future slices should define a dedicated canonical codec so requests can transmit hole tables directly.

## Corrected since (the coordinator, at the landing of 2026-10-07)

The landing kept the function's design and rewrote its reader, its writers and its battery.
Decisions row 305 is the record. The reviews are
`docs/research/2026-10-07-chunk-2-review-A-B.md` and
`docs/research/2026-10-07-chunk-2-landing-review.md`.

- The transcript of the hand-back was written by a scratch script, and the driver could not
  read it. The fixture is now the driver's own output on 16 requests, and the battery replays it.
- An answer names a law only where the function decided the law's premises.
- The line counts of this receipt are not measured.
