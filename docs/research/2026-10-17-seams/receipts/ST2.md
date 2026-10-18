# ST2 — checked disk images and one writer

Published or sealed damage now returns a fault without discarding its evidence.
Only a writable, uncommitted tail permits truncation.
Recovery admits a checked image and retains exact generations; it invents no historical transaction journal.

Base: `0a8d7915a3e3bad7af939258ace0e71956d0e810`.
Implementation head: `e163b1ac64aa9c4c8ce91f2b7d54bd4d3aa3d061`.
The coordinator lands the implementation and receipt on `refactor/phase1-phase3`.

## Placement and evidence scope

`RESTORE-PLACEMENT.md` records each obligation before proof work.
The registry and semantics authority place three properties under translation-simulation and R13.
Their owner is `src/Effect4/Laws/Store/Recovery.lean`.

| Pointer | Role | Reach | Exclusions and consumer |
| --- | --- | --- | --- |
| `restore_roots` | compatibility | Accepted empty-store restoration retains the exact root table and its generations. | No ancestry or generation provenance. Serves ST4 and S6. |
| `restore_closed` | preservation | Every recovered node passes the shared admission rule in order; the resulting store is closed. | No filesystem correctness or hash injectivity. Serves checked image admission. |
| `restore_targets` | preservation | Every recovered root resolves to a durable resident of its fixed kind. | No host progress or historical root-chain claim. Serves ST4 and S6. |

All three pointers are proved; this slice adds no planned goal.
`RecoveryImage.read` checks raw bytes before constructing node data.
`Cas.restoreBytes` records the admitted empty-store recovery event.
Native `Disk.image` additionally compares each recorded address with its bytes' hash.
Its snapshots contain values, without mutable indexes or pack handles.

## Acceptance and red controls

| Plan row | Positive observation | Red control | Evidence |
| --- | --- | --- | --- |
| Owned writer | One locked writer commits fully validated transactions. | The premature-root-publication mutation fails the real interruption harness. | `test_disk`, `test_disk_kill`, retained writer mutation. |
| Frozen images | Earlier nodes, roots, and durable boundaries remain unchanged after later writes and index rebuilding. | The old mutable snapshot assertion fails in a child. | `test_disk`, retained control. |
| Model comparison | The oracle executes actual Cas operations and emits finite state transitions. | Unknown actions and missing table transitions refuse before writing. | `DiskOracle`, `test_disk_stm`, missing-row mutation. |
| Write interruptions | Reopened images equal the actual model's accepted fresh-node cuts. | A dependent later node is absent before its write. | Six actual SIGKILL points and `CasDiskCuts`. |
| Sync and publication | The post-sync prefix retains old roots; full publication retains all nodes and the new root table. | A lost acknowledgment never exposes a partial root table. | `test_disk_kill`. |
| Reopened generations | Version-1 generations and complete version-2 heads survive checked recovery. | The legacy generation-two image differs from an invented duplicate trace at generation one. | `test_control`, `SeamsRecovery`, STM reopen actions. |
| Sealed damage | Intact sealed segments reopen normally. | Interior corrupt heads, short sealed tails, and missing published bytes return faults without changing evidence. | `test_disk_damage`, retained old failures. |
| Capacity | A duplicate at the maximum generation remains unchanged. | A changed advance beyond wire capacity returns Capacity before any write hook. | `test_disk_boundary`. |
| Recorded address | Valid recorded hashes survive image admission. | Bytes stored under another address return `Fault (Corrupt address)`. | `test_disk_boundary`. |
| Shared raw reading | Ordinary byte writes and recovery use the generated refusal adapter. | Unknown tags and malformed-version cases keep their exact refusal phase. | `test_shared_facts`, `test_disk_boundary`, `SeamsRecovery`. |
| Checked roots | The restored legacy root retains its exact head and resolves at its fixed kind. | Nonempty restoration, duplicate names, missing targets, and wrong target kinds refuse. | `SeamsRecovery` and its law readers. |
| Rocq node laws | The current producer output compiles with the existing five-file store proof group. | Existing primitive, decoder, and accepted-new-to-old premises remain explicit. | Actual regeneration and recorded Rocq commands. |

The oracle generation records its state, action, and transition counts.
The STM log records its command-list bound and seed.
These are finite host observations; they establish no universal disk simulation or power-loss theorem.
Rocq proves node laws under its existing premises, without root, result, transaction, or crash claims.

## Deleted mappings and moved callers

The three independent raw-byte refusal mappings delegate to the Lean-generated adapter.
The generated admission family includes the concrete native Fault owner.
Native callers handle `open_rw` refusals as values.
The owned Disk wrapper exposes checked frozen images and atomic transaction submission.
The native tests, benchmarks, and check target use those explicit outcomes.
The standalone audit input remains receipt evidence; the acceptance fixture joins `Test/All.lean`.

## Corrections and controls

A legacy image can retain generation two where a new duplicate trace retains generation one.
The recovery event therefore validates an image instead of fabricating a transaction history.
It checks nodes, unique root names, and target kinds, but reconstructs no past ancestry.

Raw native strings pass byte reading before semantic node checks.
The retained K14 assertion demonstrates the previous disagreement between two entrances for identical bytes.
Lean's already-decoded Val law keeps its oversize-before-version order.

The earlier recovery path clamps a published boundary when bytes disappear and can truncate sealed damage.
The retained X1/X4 and damage controls expose those behaviors.
Recovery now reports faults and preserves the pack bytes, control bytes, and sealed permissions.
The no-root `(0,0)` boundary sentinel alone normalizes to the pack header.
That normalization changes no root generation.
The earlier vacuous R4 control is removed; the real checksum control remains.

The CasGoldens refusal printer needs cases for the two new recovery refusals.
Its retained exhaustiveness failure and successful producer rerun record the correction.
No existing golden observation changes through those additional cases.

The STM dependency is installed in the native CI toolchain with the same tested package versions.
The package inventories show no compiler or existing-package replacement.

Four prepared files had no header: `Test/Store/SeamsRecovery.lean`, `src/OCaml5/Tools/CasDiskCuts.lean`, `src/OCaml5/Tools/CasDiskOracle.lean` and `ocaml/engine/cas/test/test_disk.ml`.
The coordinator added each, matching its peers; `ocaml/STANDARDS.md` asks for a property list at the head of every component.

## Proposed decisions rows

Admit reopened images through canonical empty-store recovery with exact roots and shared node admission.
Keep Capacity and Fault outside modeled admission refusals.
Retain frozen snapshot values and one owned writer.
Treat sealed damage and missing published bytes as faults; truncate only writable, uncommitted tails.
Use generated actual-model tables for finite native comparison and retain real process-interruption controls.
Keep host tests distinct from proved recovery and Rocq node properties.

## Current production evidence

`landed-source-paths.txt` lists every implementation path.
`landed-source-hashes.json` pins its bytes at the implementation commit.
The frozen preparation records keep their bounded scope; the production commands below establish this landing.

```text
#axiom_audit: 1041 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |
| [versions](evidence/ST2/versions.json) | 0 | 1.178 | `python3 /private/tmp/seams-lean-one.py python3 /private/tmp/seams-runtime-versions.py` |
| [narrow](evidence/ST2/narrow.json) | 0 | 18.002 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Laws.Program.Simulation.Evaluate Effect4.Laws.Store.Recovery Effect4.Store.Domain.Cas Effect4.Store.Domain.Genesis Effect4.Store.Domain.Store Effect4.Store.Domain.Traits Effect4.Store.Domain.Transaction Effect4.Store.Domain.Word OCaml5.Store.DiskOracle OCaml5.Store.Facts OCaml5.Tools.CasDiskCuts OCaml5.Tools.CasDiskOracle OCaml5.Tools.CasFacts OCaml5.Tools.CasGoldens Test.Store.NodeContract Test.Store.ProgramContent Test.Store.SeamsRead Test.Store.SeamsRecovery Test.Store.SeamsTransactions Test.Store.WordContract` |
| [audit](evidence/ST2/audit.json) | 0 | 1.645 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-st2-audit.lean` |
| [generate-cas](evidence/ST2/generate-cas.json) | 0 | 8.064 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only cas` |
| [generate-store-rocq](evidence/ST2/generate-store-rocq.json) | 0 | 6.21 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only store-rocq` |
| [rocq](evidence/ST2/rocq.json) | 0 | 3.457 | `python3 /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/9702bd4d-c422-4d7e-85c6-6052708a5ba3/scratchpad/seams-st2-rocq-production.py` |
| [native-store](evidence/ST2/native-store.json) | 0 | 7.067 | `opam exec --switch=effect4 -- dune runtest --force --root ocaml engine/cas/test` |
| [batteries](evidence/ST2/batteries.json) | 0 | 135.406 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=0a8d7915a3e3bad7af939258ace0e71956d0e810` |
| [check-ocaml](evidence/ST2/check-ocaml.json) | 0 | 291.02 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
| [generate-semantics](evidence/ST2/generate-semantics.json) | 0 | 312.629 | `python3 /private/tmp/seams-lean-one.py make gen-semantics` |
