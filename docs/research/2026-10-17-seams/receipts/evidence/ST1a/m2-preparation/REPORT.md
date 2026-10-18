# ST1a M2 preparation

Apply `generator.patch` as a patch. Its full temporary files predate S0's current edits to `scripts/generate.py` and `Makefile`.

The M2 source patch compiles in a temporary module overlay. The production worktree remains unchanged by this preparation.
`base-check.json` records the checked head and source hashes. The M2 source inputs still match that worktree.

## Prepared changes

| Patch | Contents |
| --- | --- |
| `m2.patch` | Kind classifications, node M2 check, admission mapping, store and word invariants, Rocq proofs, refusal vocabulary, and finite controls. |
| `generator.patch` | The `store-rocq` family, its make target, and canonical output headers in `GallinaGen.lean`. |
| `generated-storecode.patch` | `rocq/StoreCode.v`, emitted from the changed Lean definitions. |
| `touched-paths.txt` | Exact proposed production paths. |

`NodeRead.lean` comes from the coordinator's temporary implementation. It is a dependency of this check and is absent from `m2.patch`.
The patch leaves `Store.get` unchanged for the coordinator's checked-reader migration.
The temporary `lib/lean` directory contains compiled files and dependency links. Do not copy it into the worktree.

## Proof placement

`PLACEMENT.md` retains the placement established before proof work.

| Declaration | Concept and property | Role | Checked reach | Consumer |
| --- | --- | --- | --- | --- |
| `putNode_accepted_new_to_old` (`src/Effect4/Store/Domain/Store.lean`) | exact-codecs, stored node admission, R13 | Helper for the existing compatibility claim | New successful admission implies every former `putNode_ok` conclusion. | `putNode_ok` and its existing consumers. |
| `putNode_ok_handleFree` (`src/Effect4/Store/Domain/Store.lean`) | exact-codecs, stored node admission, R13 | Preservation | Every successful insertion passes M2 before edge and resident checks. | `putNode_sound`, word replay, and local construction. |
| `admissibleAfter_handleFree` (`src/Effect4/Store/Domain/Word.lean`) | exact-codecs, stored node admission, R13 | Helper | Every accepted word binding passes M2. | `wfFrom_apply`. |
| `verifyNode_handleFree` (`src/Effect4/Store/Domain/Word.lean`) | exact-codecs, stored node admission, R13 | Helper | Every verified resident passes M2. | `verify_sound`. |

`putNode_ok` retains its exact tuple. Its named connector proves the implication from the new implementation.
`putNode_fresh`, `putNode_duplicate`, `put_duplicate`, and `admissibleAfter_of` now require an explicit M2 premise.
`Store.Sound.handles` states M2 for every resident. The empty store, insertion, word construction, closure extraction, and verification proofs carry it.

These statements establish neither progress nor host persistence. They assume no hash injectivity.
The Rocq proofs retain their `Prim` parameters, equality laws, and explicit codec premises.

## Checked evidence

All Lean commands run through `python3 /private/tmp/seams-lean-one.py`.
That wrapper serializes commands and invokes the required scratch launcher with `LEAN_NUM_THREADS=3`.

| Command | Evidence | Result and scope |
| --- | --- | --- |
| `python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-st1a-m2/build_overlay.py` | `build-overlay.log` | The changed core modules and Gallina printer compile with warnings as errors. |
| `python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-st1a-m2/validate.py` | `validate.log`, `build-overlay.log` | The M2 fixture and CasGoldens compile. The named module audit passes. Gallina emits the current store definitions. |
| The audit in `src/Test/Store/SeamsAdmissionAudit.lean` | `audit-final.log` | `1257 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`. |
| `python3 /private/tmp/seams-st1a-m2/run_rocq.py` | `rocq-m2.log` | Rocq compiles `Eff_types`, `StoreCode`, `StoreLaws`, `StoreGrammar`, and `StoreAssumptions`. |
| `python3 /private/tmp/seams-lean-one.py lake env python3 /private/tmp/seams-st1a-m2/family_controls.py` | `family-controls.log` | The actual producer emits current bytes. The family checks unchanged Skeleton and refuses its red mutation before installation. |
| `python3 /private/tmp/seams-st1a-m2/family_alias_controls.py` | `family-alias-controls.log` | Aliased output refuses before any command. The existing `--only rocq` invocation refuses with exit 2. |
| `make -f /private/tmp/seams-st1a-m2/Makefile -n gen-store-rocq` | Command output | The target invokes `python3 scripts/generate.py --only store-rocq`. |

The overlay uses the worktree's compiled dependency files through read-only links.
The family controls adapt dependency builds and producer paths to that overlay. They use the actual Lean producer and actual temporary-file installation logic.
These checks prepare the patch. They do not replace the production slice's build, audit, touched batteries, or OCaml gate.

## Controls and corrections

The retained baseline `StoreReadProbe.lean` accepts a schema node containing one handle and no checked edges.
Its payload is well formed, its version is zero, and its references are valid.
That counterexample shows why the former introduction premises cannot prove the new admission result.
The current fixture refuses it at insertion, word validation, word replay, and verification.
A forged resident cannot bypass M2 through the duplicate branch.
Version and malformed-reference refusals precede M2. M2 precedes missing-edge and resident checks.
The finite fixture also checks every current kind's classification.

`retained-controls/rocq-route.log` records the compiler mismatch in the full Rocq generation route.
The required `effect4` switch reports OCaml `5.1.1`. The Rocq switch carries OCaml `5.4.1`.
The unchanged type splitter fails under `effect4` because its `Longident.Ldot` pattern expects the newer compiler representation.
The new family regenerates only the changed store code and checks the independent tree skeleton.
It leaves the unchanged `Eff_types.v` producer outside this slice's regeneration.
Rocq compilation uses `opam exec --switch=rocq -- rocq compile`. No OCaml command uses that switch.

`validate-isEmpty-refusal.log` retains the printer's refusal of polymorphic `List.isEmpty`.
`Node.handleInContent` now tests the handle list's constructors directly after the same kind check.
This change avoids a new printer primitive and retains the same Boolean meaning.

`GallinaGen.lean` now writes canonical repository paths in generated headers.
Temporary destinations therefore produce byte-identical Skeleton output.
The new family checks Skeleton before installing StoreCode.
The family also refuses a check destination that aliases either canonical output.

## Integration work

1. Apply the source patch after the required earlier slices.
2. Integrate the coordinator's `NodeRead`, typed reader, and checked `Store.get` changes.
3. Apply the generator patch around S0's current script changes.
4. Connect the fixture at the slice's permitted `Test/All.lean` anchor.
5. Place the registry claim and proposed decisions rows in the ST1a receipt.
6. Run the new family through the strict outer launcher.
7. Run the production narrow build, named audit, touched batteries, and OCaml gate.

`Val.handles` in `src/Effect4/Store/Carrier/Val.lean` still says handles are admitted nowhere in the CAS.
That comment needs the run-relative exception. This preparation leaves that coordinator-owned file unchanged.
