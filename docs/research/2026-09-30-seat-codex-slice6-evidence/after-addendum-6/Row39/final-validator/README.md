# Final row 39 static validator

Run after the final source and generator chain:

```sh
python3 /private/tmp/row39-series/final-validator/validate.py \
  --repo /Users/pooks/Dev/lean4-effect4-slice6 \
  --bundle /private/tmp/row39-series > /private/tmp/row39-final-validation.json
```

The script only reads files and Git objects. It prints structured JSON, returns 0 if every check passes, and returns 1 for a failed check or missing/unreadable required input. Shell redirection writes only the report. No Lean, build or generator runs. `--bundle` makes the validator usable from a retained evidence copy; `required-inputs.json` lists its nine bundle inputs and the two required Git revisions.

It checks:

- **Eight retained byte artifacts:** all three schema TypeScript fixtures; CAS `manifest.txt` and `cases.txt`; and `g1-genesisNode.hex`, `g1-censusSchema.hex`, `g1-censusEntry.hex`. Current bytes must equal the manifest SHA-256, size, and immutable d554 Git object. The five copied baselines must also equal that object.
- **Final source hashes:** the last expected hash for every path across all four prepared stages plus both register patches. This means 61 paths: 24 retained/created source files, 35 deletions, and two registers. A later intentional source correction requires an explicit reviewed manifest update; this validator does not refresh expectations from the live tree.
- **Register migration:** all 21 moved rows appear verbatim exactly once in the archive and nowhere in the live register. The mixed rows 017/059 remain once in the live register with the specified immutable evidence pins. Every moved source pin resolves to its recorded blob; no live row has a bare path to a retired file.
- **Duplicate counts:** all duplicate-ID multiplicities equal the pre-row39 `abc7b12401b22112ef29df886237a3d0024b33d6` baseline. This does not claim global ID uniqueness.
- **Deleted module imports:** no imports of the 23 deleted Lean files’ module names under live `src`, `Test`, `tools`, or `harness`. Nested comments and strings are masked before reading imports. `docs/research` is outside the scan, so historical copied trees do not count as live imports.
- **Pure Shape dependency closure:** the transitive local imports of `Effect4.Store.Domain.Shape` resolve all Effect4 modules and reach no `Effect4.Schema` module.

The four older duplicate IDs all refer to different attacks. The JSON includes both current row locations and attacked statements:

| ID | Live attack | Archived attack |
| --- | --- | --- |
| E4-TYPED-CE-003 | StrongCause/Die shape-defect exclusion | Compilation loses nonnumeric failure payloads |
| E4-SCHED-CE-004 | Race action needs a source-location premise | Bind-based representation loses interruption cleanup distinction |
| E4-PROV-CE-005 | Layer-build environment isolation | Middleware provider/consumer order |
| E4-PROV-CE-006 | Layer value/service carrier fit | String deployment law disagrees with binding rows |

They remain pre-existing register debt; the validator neither renumbers them nor drops history.

## Validation of the validator

`selftest.json` records a passing live read and five deliberate failures through in-memory file overrides: changed pinned hex, changed expected source, missing archived row, duplicate moved ID, and a stale deleted-module import into the Shape closure. Each intended check failed. A separate parser control confirms comments/strings do not invent imports and multiple imports on a line are read. These seven controls passed, with no repository mutation.

`intermediate-live.json` is an early passing source-tree snapshot while the root's serialized work was still in progress. It is not the final post-generation receipt; rerun the command above at the actual final state. Static byte/import checks supplement the root's compiler, trust, and runtime evidence and do not establish semantic equivalence by themselves.
