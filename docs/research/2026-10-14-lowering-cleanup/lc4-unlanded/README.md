# The LCNF lowering cleanup: what the seat handed back unlanded

Status: the coordinator's hand-back note (history, not authority). Parts C and F landed on 2026-10-15 (the receipt, "LC-4 C and F"). The seat stopped on the
owner's order on 2026-10-15. LC-1 to LC-3 are merged (`6ce9ff704`). LC-4's parts A and B land
with this note. Its parts C, D and F are kept here, and nothing else of LC-4 to LC-9 started.

## 1. The one thing to know first

Parts C and F were never built or run. Build them before you trust them. Apply the patch to the
branch head that carries parts A and B.

## 2. What is here

| File | Part | What it does | Evidence |
| --- | --- | --- | --- |
| `Gen.lean` | C | The per-artifact pipeline, moved out of the driver into `src/OCaml5/Lcnf/Gen.lean`: `argvOf`, `recipeArgvs`, `run` with one line of phase times, `manifestPathFor` | never compiled; the seat doubts `Args.parse`'s structural recursion and `Json.getObjValAs? Nat` |
| `part-C-and-F.patch` | C | `src/OCaml5/Tools/LcnfGen.lean` becomes a thin driver whose `--recipe` makes every artifact in one process, importing each import set once. `src/OCaml5.lean` imports the new module. `scripts/generate.py` runs one `--recipe` process. `ocaml/gen/roots.json` names it | never run |
| `part-C-and-F.patch` | F | `scripts/lean-imports.py` gains a `--closure` mode. The `Makefile` takes `DERIVED_INPUTS` and `FIXTURE_INPUTS` from that closure, not from every Lean source. `docs/GENERATED.md` follows | `make -n -W` dry runs only |
| `patchD.py` | D | A draft: constructor origins enter the clock graph only once a field holds a fact, with one canonical call order. 93% of the 163,368 clock facts are constructor origins | not applied; it needs `ClockDiff` to compare calls and refusals as sets |

Apply it with `git apply docs/research/2026-10-14-lowering-cleanup/lc4-unlanded/part-C-and-F.patch`, and
copy `Gen.lean` to `src/OCaml5/Lcnf/Gen.lean`.

## 3. The measurements before parts A and B

Per artifact, `api_gen.ml` then `api_engine.ml`, by the seat's probe `LcnfPhases.lean`:
- the import takes 2.0 and 1.4 s;
- the walk with inference takes 6.85 and 6.67 s;
- within the walk, the clock refusals take about 5.6 and 3 s, and translation 0.82 and 0.78 s;
- the renaming pass takes 7.2 and 6.6 s;
- `checkModule`, hygiene, types, emission and rendering take under 0.6 s each.

## 4. What remains

- **LC-4:**
  - build and test C;
  - run the gates on A to F together;
  - apply D;
  - E, an idea: the checker's environment as tree sets and maps, with the guarded set built once.
  
  G, a compiled generator (`lean_exe`), is the coordinator's to rule on, since the lakefile is
  the coordinator's. Per-module native libraries failed on a build cycle between the shared
  libraries of `Conform` and `OCaml5`.
- **LC-5:** not started. The density control of the deleted `prop_store.ml` (ST9) has no line on
  `E4_table`.
- **LC-6 to LC-9:** not started. LC-7's blockers, by probe E:
  - the generator's run-wide heartbeat budget;
  - the F4 rows (`UInt64.ofNat`, `String.ofList`, `USize.repr`, `Array.getInternal`,
    `String.toByteArray`, `Char.ofNatAux`, `ByteArray.emptyWithCapacity`, `ByteArray.push`,
    `System.Platform.getNumBits`);
  - the clock refusal of `Effect4.Live.start`;
  - the F3 family parameter of `EffAlgebra`.

## 5. The seat's doubts

- A `check-ocaml` run after `touch ocaml/engine/tools/gen-check.sh` took 0.65 s and did not re-run
  the lane. The seat could not explain it.
- The message of `a06aa2ba6` says "row 494". The row is decisions row 362, at line 494.
