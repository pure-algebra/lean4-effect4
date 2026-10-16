# 2026-10-16 Math seat: receipt

Status: receipt (history, not authority). Seat: math and formalization, the one Lean seat.
Base: `81f9a4354` on `refactor/phase1-phase3`. Head: the commit that adds this receipt, on branch
`claude/math-d3`, not pushed. The design note is `docs/research/2026-10-16-math-d3/README.md`.

## What landed

| File | Change |
| --- | --- |
| `src/Effect4/Laws/Program/Typed/FitsIn.lean` | new: D3's foundation beside `Fits`; 4 placed laws, 5 planned goals |
| `src/Effect4/Laws.lean` | one import line: the new module, after `Effect4.Laws.Program.TyHead` |
| `docs/research/2026-10-16-math-d3/README.md` | new: the design, the reach, the placements, the simplifications |
| `docs/research/2026-10-16-math-d3/probes/FitsIn.lean` | new: four finite probes; no root reaches it |
| `docs/research/2026-10-16-seat-math-receipt.md` | this receipt |

No file of the coordinator's D2 surface was edited. `Fits`, `Typed/Membership.lean` and every
consumer of `Fits` are unchanged.

## Commands and results

| Command | Result |
| --- | --- |
| `cp -c -R <main checkout>/.lake/packages .lake/packages` | the packages copied |
| `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Program.TyDecls` | restored from the artifact cache: 446 jobs, 3 s |
| `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Program.Typed.FitsIn` | `Build completed successfully (447 jobs)`, warnings as errors |
| `#axiom_audit Effect4.Laws.Program.Typed.FitsIn`, in a scratch file importing `ProofGraph.AxiomAudit` | `314 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 5 planned goals` |
| `LEAN_NUM_THREADS=2 lake env lean docs/research/2026-10-16-math-d3/probes/FitsIn.lean` | no output; exit 0 |
| `python3 scripts/check-language.py --strict` on the note and on this receipt | `PASS` |

No root, no battery and no `make check-*` target ran. The build covered the new module and its
imports only, so the one import line in `src/Effect4/Laws.lean` is checked by no build of this
seat.

## The proved laws

- `fitsIn_nil`: `FitsIn [] w v t = Fits w v t`.
- `fitsIn_unfold`: a reference to a declared name has exactly its body's members.
- `fitsIn_map`, `fitsIn_mono`: `Grows`, or `World.leHost`, keeps membership under the table.
- `fitsIn_memberIn`: membership under the table implies `MemberIn` at the world's allocation
  table.

Each is placed at concept `store-typing`, R3. The proposed claim is `fits-declared`, not yet in the
registry.

## Open obligations

1. The planned goals `fitsIn_live`, `fitsIn_sub`, `fitsIn_normalize` and `fitsIn_iff_membersIn`
   (R3), and `evalTerm_progressIn` (R9). The note's §6 gives their order.
2. The landing of D3 (the note's §7): the world's table, `Fits := FitsIn w.types w`, the tie in
   `MachineTyped`, the cell typing under the table, and the 41 premises.
3. `generated/semantics.md` will drift: it lists the library's planned goals, and this module adds
   five and new R3 and R9 nodes. Its producer is `make gen-semantics`, which builds the roots.
4. The registry claim `fits-declared`, if the coordinator takes it.

## Bounded evidence

- The probes are four finite runs on hand-written tables.
- The reach numbers are name searches at the base.
- The name `FitsIn` is also `Effect4.Program.FitsIn`, an environment at an allocation table, in
  `src/Effect4/Laws/Program/Typed.lean`. Name resolution picks the innermost namespace, so neither
  shadows the other in its own namespace. The landing retires this module's name into `Fits`.
