# ST1a — checked node reading and admission

M2 strengthens node admission, including resident duplicates.
Fresh and duplicate introduction laws therefore require the new handle premise.
The retained old-premise control accepts a content handle and shows why that premise is necessary.

Base: `489e127a8b94f4796ff40ef4200080b5e83a94f2`.
Implementation head: `637fd14686343632378427190c9a4ed9142a0fc7`.
All required production checks pass. The command records below retain their measured results.

## Placement before proof

| Claim or helper | Concept and role | Reach and hypotheses | Exclusions | Consumer |
| --- | --- | --- | --- | --- |
| `Node.read_exact` | exact-codecs; compatibility | Success returns exactly encoded bytes, a well-formed payload, and version zero. | Admission, hashing, capacity, persistence. | Raw byte entrance; R13. |
| `Node.read_ok_iff` | exact-codecs; helper | Successful diagnostic reading has exactly the existing decoder's success image. | Failure diagnostics and admission. | `Node.read_exact`; R13. |
| `Node.readContent_exact` | exact-codecs; helper | Version, kind, per-value spec, and exact canonical reading determine the returned node. | Hash injectivity, graph closure, native refinement. | `Cas.get_exact`; R13. |
| `Node.expectedSpec_toVal`, `Node.readContent_nodeOf` | exact-codecs; helpers | Canonical nodes pass the per-value spec and exact reader, including the genesis. | Node admission and hash injectivity. | `get_nodeOf`, `Node.readContent_exact`; R13. |
| `Cas.get_exact` | exact-codecs; compatibility | A successful typed read names the carrier's exact resident node. | Atomicity or admission for an arbitrary replay parameter. | Session-chain loading; R13. |
| `get_nodeOf`, `get_put`, `get_preserves` | exact-codecs; helpers | Exact resident images read back; successful non-conflicting puts retain their typed carriers. | Collision resistance and host persistence. | Program and trait readers; R13. |
| `putNode_ok_handleFree` | exact-codecs; preservation | Every successful insertion passes M2 before edge and resident checks. | Progress and host persistence. | `Store.Sound.handles`, word replay; R13. |
| `putNode_accepted_new_to_old` | exact-codecs; helper | New successful admission implies the former admission and outcome conclusions. | The converse without M2. | Existing node laws; R13. |
| `admissibleAfter_handleFree`, `verifyNode_handleFree` | exact-codecs; helpers | Accepted words and verified residents pass M2. | Native crash behavior. | Word construction and verification; R13. |

The packet's `PLACEMENT.md` records these obligations before implementation.
The registry adds the byte-reading, typed-reading, and handle-admission claims in this slice.
The later transaction slice fixes the replay parameter to the actual event interpreter.

## Acceptance and controls

| Plan row | Positive observation | Red control | Evidence |
| --- | --- | --- | --- |
| Node check with M2 | Run-relative kinds retain allowed handles. | Content handles refuse through insertion, word validation, word replay, and verification. | `Test/Store/SeamsAdmission.lean`; production narrow build. |
| Double faults | Refusals follow version, malformed reference, M2, edge, then residency checks. | A forged resident cannot waive M2; earlier faults win. | `Test/Store/SeamsAdmission.lean`. |
| Node bytes | Accepted bytes match the existing exact decoder. | Unknown nested tags, truncation, trailing bytes, and bad headers refuse. Bytes payloads remain leaves. | `Test/Store/SeamsRead.lean`. |
| Typed reads | Real entry and program carriers read their exact resident nodes. | Wrong version, kind, spec, and payload refuse in order. | `Test/Store/SeamsRead.lean`, `Test/Store/ProgramContent.lean`. |
| Genesis | The meta-schema reads through its per-value zero spec. | A universal `specOf` comparison would reject it. | `Test/Store/SeamsRead.lean`. |
| Re-hash | The native record reader checks the requested address against retained bytes. | A repaired CRC cannot disguise a forged digest. | Current native pack controls in `make check-ocaml`. |
| Shared facts | The Lean producer emits every kind classification and admission constructor. | Unknown-byte mapping, large naturals, and the mutated mapping control distinguish the required fields. | `CasFacts`, `test_shared_facts`, retained native controls. |
| Rocq connector | Current generated node code compiles with the retained node proofs. | M2's old introduction premises fail; unchanged-Skeleton and alias controls refuse invalid generation. | Production store-rocq generation and five-file Rocq compilation. |

The generic theorem restatement was removed from the fixture during integration review.
The concrete entry reader and byte controls retain the required observations.

## Replaced owners

`Store.get`, `get_put`, and `get_preserves` are deleted.
`Cas.get` owns typed version, kind, spec, and payload checks.
Trait and program callers use the new reader and its exact-image laws.
The root imports Cas, and the test root imports both slice fixtures.

`Node.read` adds diagnostic refusals around the existing decoder's exact success image.
It does not introduce a second successful byte decoder.
The diagnostic walk follows frame structure and treats a bytes payload as one leaf.

`Kind` owns the classifications.
`Admission` owns the modeled refusal constructors.
The native kind and refusal files are generated from those owners.
Naturals map to exact `Z.t`; capacity remains outside modeled admission.

## Corrections and controls

The genesis needs a per-value spec, rather than one universal carrier spec.
Its positive and rejecting comparison controls retain that distinction.

The generic `CasOf replay` package retains the probe's explicit replay parameter.
Its reader proves an exact resident image without claiming that every interpreter performs admission.
The next slice fixes the actual transaction interpreter.

The private constructor conflicts with exposed checked construction in Lean's module compiler.
`CasOf.ofReplay` remains checked and uses `no_expose`; the failing compiler control is retained.

The full Rocq generation route requires a newer OCaml compiler than the mandated effect4 switch.
The store-only family regenerates current StoreCode and compares the unchanged Skeleton before installation.
The retained compiler mismatch explains that narrower producer. The required store proof check still runs.

`Node.handleInContent` matches the handle list's constructors because Gallina refuses the polymorphic emptiness call.
The matched list computes the same Boolean result; the printer refusal is retained.

The native byte library is unwrapped.
Its fixture uses the actual module names; an invalid wrapper import is removed before the production build.

The shared-facts check formerly compared each destination only with its matching published file.
A cross-artifact symlink could overwrite another published output.
`cross-alias-red.log` demonstrates that failure using disposable files.
Both new producer families now compare every destination against every published path before invoking the producer.
The Rocq family retains its matching red and green controls in `rocq-cross-alias-red.log` and `rocq-cross-alias-green.log`.
`cross-alias-green.log` records zero producer calls and unchanged retained bytes.

The native G2 fixture still expected Lean and OCaml to disagree on M2.
The regenerated golden makes both implementations refuse the handle.
`native-g2-red.log` retains the obsolete assertion's single failure.
The repaired fixture requires every row to agree; `native-g2-green.log` passes with the existing corruption and mutation controls.
The first complete OCaml gate finds the same obsolete exception in the byte-layer fixture.
`check-ocaml.log` retains its two failing assertions.
The repaired byte-layer fixture requires all 14 admission rows to agree; `native-bytes-green.log` passes.

K14 assigns the shared mapping producer to ST1a and its caller migration to ST2.
The generated `E4_admission.of_decode` lands here. ST2 retains the three legacy caller migrations.
K15's sealed-damage value also remains ST2's obligation.

## Evidence limits

The Lean laws establish their stated byte, payload, and resident observations.
Rocq's existing node laws retain their explicit primitive and codec assumptions.
They establish no root, transaction, result, crash, or liveness theorem.
Native runs and damaged-record controls are finite host evidence.
The host boundary remains unchanged.

## Proposed decisions rows

Adopt typed reads that check version, kind, per-value spec, and exact payload.
Retain the genesis exception and the accepted-new-to-old connector when admission gains M2.
Generate native kind classifications and modeled refusal fields from the Lean owners.
Keep exact naturals and outside-model capacity distinct.

## Commands and changed paths

`evidence/ST1a/landed-source-paths.txt` lists every changed source path.
`landed-source-hashes.json` records their exact bytes at the implementation commit.
The preparation subdirectories retain earlier failures and controls, with their original bounded evidence scopes.
Current production records supersede preparation counts.

The production axiom audit reports:

```text
#axiom_audit: 1876 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The narrow build completes 118 jobs.
The selected battery command reaches 95 batteries; its full output records the completed jobs.
The Rocq command compiles the five copied current files and prints each file's source hash.
The OCaml gate runs the current native, compiler, and estate comparisons.
Both producers run again after the final alias corrections.
`regeneration-hashes.json` confirms that every checked published output stays byte-identical.
No ST1a proof obligation remains open.

| Check | Exit | Seconds | Exact command |
| --- | --- | --- | --- |

| [narrow](evidence/ST1a/narrow.json) | 0 | 79.502 | `python3 /private/tmp/seams-lean-one.py lake build Effect4.Store.Domain.Cas Effect4.Store.Domain.Traits Effect4.Store.Domain.Genesis Effect4.Store.Domain.Pin Effect4.Store.Domain.ProgramWire OCaml5.Tools.CasGoldens OCaml5.Tools.CasFacts OCaml5.Lcnf.Gallina Test.Store.SeamsAdmission Test.Store.SeamsRead Test.Store.ProgramContent Test.Store.WordContract` |
| [audit](evidence/ST1a/audit.json) | 0 | 1.801 | `python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true /private/tmp/seams-st1a-audit.lean` |
| [generate-cas-final](evidence/ST1a/generate-cas-final.json) | 0 | 134.353 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only cas` |
| [generate-store-rocq-final](evidence/ST1a/generate-store-rocq-final.json) | 0 | 8.551 | `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only store-rocq` |
| [rocq-final](evidence/ST1a/rocq-final.json) | 0 | 5.378 | `python3 /private/tmp/seams-st1a-rocq-production.py` |
| [batteries](evidence/ST1a/batteries.json) | 0 | 989.908 | `python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=489e127a8b94f4796ff40ef4200080b5e83a94f2` |
| [check-ocaml-final](evidence/ST1a/check-ocaml-final.json) | 0 | 20.261 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
| [generate-semantics](evidence/ST1a/generate-semantics.json) | 0 | 610.91 | `python3 /private/tmp/seams-lean-one.py make gen-semantics` |
| [cross-alias-green](evidence/ST1a/cross-alias-green.json) | 0 | 0.076 | `python3 /private/tmp/seams-st1a-alias-control.py` |
| [native-g2-green](evidence/ST1a/native-g2-green.json) | 0 | 1.725 | `opam exec --switch=effect4 -- dune exec --root ocaml engine/cas/test/test_cas.exe` |
| [native-bytes-green](evidence/ST1a/native-bytes-green.json) | 0 | 0.916 | `opam exec --switch=effect4 -- dune exec --root ocaml engine/cas/test/test_bytes.exe` |
| [facts-staging-final](evidence/ST1a/facts-staging-final.json) | 0 | 0.053 | `python3 /private/tmp/seams-st1a-facts-staging.py` |
| [rocq-cross-alias-green](evidence/ST1a/rocq-cross-alias-green.json) | 0 | 0.077 | `python3 /private/tmp/seams-st1a-rocq-alias.py` |
| [native-versions](evidence/ST1a/native-versions.json) | 0 | 0.259 | `opam exec --switch=effect4 -- sh -c 'ocamlc -version && dune --version'` |
| [lean-version](evidence/ST1a/lean-version.json) | 0 | 115.843 | `python3 /private/tmp/seams-lean-one.py lake env lean --version` |
| [cross-alias-red](evidence/ST1a/cross-alias-red.json) | 1 | 0.08 | `python3 /private/tmp/seams-st1a-alias-control.py` |
| [rocq-cross-alias-red](evidence/ST1a/rocq-cross-alias-red.json) | 1 | 0.062 | `python3 /private/tmp/seams-st1a-rocq-alias.py` |
| [native-g2-red](evidence/ST1a/native-g2-red.json) | 1 | 2.534 | `opam exec --switch=effect4 -- dune exec --root ocaml engine/cas/test/test_cas.exe` |
| [check-ocaml](evidence/ST1a/check-ocaml.json) | 2 | 275.81 | `python3 /private/tmp/seams-lean-one.py make check-ocaml` |
