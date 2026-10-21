# Program data landing receipt

Saved sessions use a changed record layout. The current reader refuses previous layouts; this landing supplies no migration reader.

The program object contains only its language signature and program.
Its operations compose admission, store decoding, source checking and service-role reading.
No host implementation, run state, target naming rule or cache enters the stored object.

## Commits and scope

Base: `40770f079d8d7594021691e0f0b1d39025b211e0`.
Implementation head: `9dc684fcb`.
Branch: `codex/program-domain`.
The final receipt commit contains only documentation and retained evidence.

The [plan](README.md) records decisions row 439 and the proof placement made before implementation.
The design note records its historical evidence. Its probes require the pre-landing record shapes.
The permanent library laws and batteries replace those probes as current checks.

| Files | Change |
| --- | --- |
| `src/Effect4/Program/Object.lean`, `src/Effect4/Api/Object.lean` | The two data carriers and their pure operations |
| `src/Effect4/Program/Services.lean`, `src/Effect4/Codegen/Print.lean` | One service formation check, with an explicit executable name profile |
| `src/Effect4/Program/SigApp.lean`, `src/Effect4/Api/Built.lean`, `src/Effect4/Api/Author.lean` | Derived row names and the reduced internal constructor |
| `src/Effect4/Run/LiveRecord.lean` | Saved sessions contain the shared object |
| `tools/Effect4Gen/manifest.json`, generated Object, Check, Refusals and Tool codecs | One owner per generated carrier; no printer dependency in the object codec |
| `tools/Compiler/Check.lean`, `tools/Compiler/Inspect.lean`, `tools/Compiler/Main.lean` | Generated certificate printing, direct inspection, saving and source-independent opening |
| `src/Effect4/Laws/Api/Object.lean`, `Test/Api/ObjectContract.lean` | Object laws and positive and negative controls |
| `scripts/check-program-object.py`, `Makefile` | Repeatable file-command controls; derived outputs read from the manifest |
| `ocaml/` and `scripts/check-lcnf-sealing.py` | Regenerated native consumers and current-shape rejection controls |

The changed path list is [changed-files.txt](changed-files.txt).
It comes from `git diff --name-only 40770f079 9dc684fcb`.
The service, record and compiler receipts retain their slice-specific changes and checks.

## Verification

Commands run in the implementation worktree unless the row names the baseline.
Every Lake build uses `LEAN_NUM_THREADS=3`, directly or through Make.

| Command | Result and retained evidence |
| --- | --- |
| `sh docs/research/2026-10-21-program-domain-design/audit.sh` at the base | Pass: eight probes; 381 declarations within the trust ceiling; [baseline-audit.log](baseline-audit.log) |
| `sh docs/research/2026-10-21-program-domain-design/codec/gen.sh` at the base | Pass: fresh generated carrier and refusal codecs; [baseline-codec.log](baseline-codec.log) |
| `python3 scripts/generate.py --only derived` | Pass: generation in dependency order; [derived-final.log](derived-final.log) |
| `lake env lean -DwarningAsError=true docs/research/2026-10-21-program-domain-landing/audit.lean` | Pass: [audit.log](audit.log) |
| `make check-program-object LAKE='env lake'` | Pass: eight command-control groups; [cli-final.log](cli-final.log) |
| `make check-ts check-ocaml` | TypeScript, native conformance and compiler conformance pass; two old OCaml callers fail; [behavior-initial.log](behavior-initial.log) |
| `make check-ocaml` after the caller repairs | Pass: [ocaml-final.log](ocaml-final.log) |
| `make batteries-touched BASE=40770f079` | Pass: 233 selected batteries; [batteries.log](batteries.log) |
| `make check-sweep` | Pass: full batteries, root and axiom gates, documents, policies and generated drift; [sweep.log](sweep.log) |

The TypeScript gate uses tsgo `7.0.0-dev.20260629.1` and Effect `4.0.0-rc.112`.
Its target comparison resolves all 104 selected cases, with no mismatch or refusal.
These are finite outside-implementation checks, not a proof of host execution.

The full sweep checks 1,634 modules and 142,437 declarations.
It reports 22 existing planned goals outside the ordinary library root.
The object slice introduces no planned goal, and its audited declarations rest on none.
The generated outputs match fresh generation.

The integrated narrow build passes before the audit:

```sh
LEAN_NUM_THREADS=3 lake build ProofGraph.AxiomAudit Effect4.Laws.Api.Object Effect4.Laws.Api.AuthorBuild Effect4.Laws.Program.Author Effect4.Laws.Api.LiveRecord Effect4.Laws.Codegen.Services Test.Api.ObjectContract Test.Codegen.ProgramServices Test.Program.RunAdmissionControls
```

The declaration audit reports:

```text
#axiom_audit: 4777 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The [compiler receipt](cli-receipt.md) retains a separate tool-audit limitation.
Compiler rendering, parsing and file-path operations reach `Classical.choice` outside the library gate.
This landing adds no trust exemption and does not report that combined compiler audit as passing.

The file controls compare prior and current certificate and inspection bytes.
They cover repeated saving, opening outside the project, usage errors, file errors and program admission refusals.
They also cover node framing, specification mismatch, malformed payloads and an unchanged existing file after refusal.

The integrated contract includes nonempty service declarations and named types.
It distinguishes source-layer checking from raw program syntax checking.
A malformed signature can pass typing and still fail program admission.
The contract checks that loading retains that distinction.

Native testing finds two stale constructors after regeneration.
The repaired controls cover malformed-program refusal and empty-session restoration.
The to-do fixture now checks its saved row names against the row projection.
Two hostile-client controls use the current record shape, so deleted fields cannot cause false rejection success.

## Proof placement

All object declarations below live in `src/Effect4/Laws/Api/Object.lean`.

| Declarations | Claim, role and requirement | Scope and consumer |
| --- | --- | --- |
| `open_ofBuilt`, `ofBuilt_of_open` | `object-exact`; compatibility; `exact-codecs`; R13 | Every admitted program; opening and record restoration |
| `open_ok_iff`, `open_error_iff` | Instantiations of `built-admission-exact` | Exact admission success and refusal at the stored signature |
| `read_exact`, `read_bytes` | `object-bytes-exact`; compatibility; `exact-codecs`; R13 | Accepted bytes are exact; retraction requires `Val.WF`; file reading |
| `load_bytes`, `load_exact` | `object-load-exact`; compatibility; `exact-codecs`; R13 | Exact admitted program recovery; byte retraction requires `Val.WF`; file loading |
| `ref_eq_or_collision` | Instantiation of `program-digest-exact` | Well-formed node bytes; object references; no hash injectivity premise |
| `table_eq`, `table_head`, `table_root_toOption`, `table_root_of_open`, `refusals_nil_iff` | Instantiations of `source-annotation-agrees`; `initial-algebras-folds`; R14 | Source checking through layer references; compiler inspection |

The [service receipt](services-receipt.md) places service formation and entry-reading proofs.
The [record receipt](../2026-10-21-program-record-receipt.md) places authoring, rebuilding and restoration proofs.
Their useful public conclusions remain unchanged.
The internal constructor no longer accepts arbitrary row names.

## Boundaries and remaining work

The pure object operations perform no file operations. The compiler driver owns file reading and writing.
`Built.bytes` remains the existing bare program encoding; `Object.bytes` encodes the complete store node.
A printed certificate is display data, not stored program admission evidence.
Opening always runs program admission again.

Byte retraction retains the store's frame-length hypothesis, `Val.WF`.
Equal references imply equal objects or an exhibited SHA-256 collision.
The specification checks compare digests; distinct future layouts are not proved to have distinct digests.

This landing establishes no external resource restoration, runtime progress or cross-layout migration.
Target printing, the host interface and the session program remain the next separate slices.
No assigned implementation or proof obligation remains open.
Persistent caching remains deferred. The existing build and gate caches continue to serve their current owners.
The semantics report remains an on-demand generated report and is not regenerated here.

The implementation worktree is the retained review checkout.
The three completed helper worktrees are archived with recoverable snapshots.
The owner checkout remains at the base, with its pre-existing untracked video script untouched.
