# Standards review: A3–A8

The strongest findings concern acknowledged persistence and shutdown acceptance. These failures have retained counterexamples against the pinned implementation.

The reviewed commit is `3471cbe35`, in `/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4`.
No production file changes, commits, pushes, or merges belong to this review.
The parent completes A1 before this review starts.

Evidence status: finite host probes and source inspection. No hardware power-loss experiment or Lean proof appears here.
Scope: A3–A8. The parent owns A1, A2, A9, A10, and consolidation into the report.
Completion requires retained inputs, commands, outputs, positive controls, source declarations, and limits for each reported defect.

## Ranked findings

| ID | Severity | Finding | Evidence |
| --- | --- | --- | --- |
| A3.1 | high | CAS verification accepts a structurally corrupted committed record | Production-library corruption probe |
| A3.2 | high | WAL write failure loses pending rows and permits a false later acknowledgement | Exact-source I/O injection |
| A4.1 | high | Shutdown can finish before a successful concurrent send enters its mailbox | Scheduled qcheck-stm counterexample |
| A3.3 | high | Directory sync failures are silently acknowledged | Exact-source I/O injection |
| A5.1 | medium | Failed WAL opening leaks the writer claim | Production-library failure and repaired retry |
| A3.4 | medium | WAL recovery contradicts its all-or-none batch property | Constructed torn-batch image |
| A5.2 | medium | A negative CLI budget reaches an uncaught generated-array exception | Executable CLI input |
| A7.1 | low | Kit_serve exposes its inferred implementation interface | Compiler-inferred interface |
| A7.2 | low | Documentation retains 37 warnings | Fresh Dune documentation run |

### A3.1 — CAS verification ignores a failed scan

Severity: high. Kind: defect.

Where: `ocaml/engine/cas/e4_cas.ml`, `walk_records`, `rebuild_index`, `verify`, and `open_rw_exn`.

Evidence: run `storage_probe.ml` using the command below. The probe commits one valid schema node, closes it, and preserves its control boundary `(0,121)`.
It changes the first record tag to `X`, at `E4_pack.head_length`. It leaves the control file unchanged.
The positive control reports `verify=Ok count=1`. The changed bytes report `verify=Ok count=0`; opening with `verify_on_open=true` also succeeds.
The retained bytes live under `storage-run-2/cas/`. The output is `storage.log`.

Why: `verify` discards the scan's stop result. It verifies the collected prefix, which can be empty before the published boundary.
The corruption therefore disappears from the verifier's candidate set. The same completion assumption affects the rebuilt index.
This breaks the declared independent verification property and STANDARDS rule 6.

Boundary control: `E4_disk.open_` refuses this same image. This finding does not claim that the checked Disk boundary accepts corruption.

Fix: retain and classify the scan stop in `E4_cas`. Require the scan to reach the published boundary before returning success.
Return a structural verification error and avoid marking a partial index finished.

Deletes: zero declarations are proposed for deletion. This is a behavior repair, with no asserted net line saving.
Test: keep the positive schema image and the one-byte corruption. Verification and verified opening must refuse the changed image.
Plan: new. Size: S.

### A3.2 — A failed WAL flush destroys its retry state

Severity: high. Kind: defect.

Where: `ocaml/engine/cas/e4_wal.ml`, `flush_buf`, `commit`, and the writer state.

Evidence: `python3 fault_injection.py` embeds the exact pinned source and replaces only the Unix I/O boundary.
It stages rows zero and one, injects `EIO` before writing, then permits I/O and stages row two.
The retained output in `injected.log` is:

```text
WAL commit failure: Unix.Unix_error(Unix.EIO, "write", "injected")
WAL after failed write: staged=0 next=2 durable=0
WAL later successful commit: durable=3 replayed=0 stop=gap: index 0 is missing; the next stored row is 2
```

Why: `flush_buf` clears its buffer before the write and sync succeed. It leaves the writer usable after failure.
A later commit advances the durable count beyond the missing rows. This violates the WAL acknowledgement property and STANDARDS rule 6.

Fix: retain pending state until success. Treat uncertain partial writes and sync failures as a poisoned writer requiring recovery.
Do not blindly retry a buffer after an unknown partial write. Return a typed I/O refusal from the public commit boundary.

Deletes: replace the ten-line `flush_buf` body; `function-spans.json` records that measured span. Net deletion is not claimed.
Test: retain this pre-write `EIO` test and add partial-write and sync-error controls. No later commit may acknowledge an unreadable prefix.
Plan: new. Size: M.

### A4.1 — A successful send can arrive after shutdown finishes

Severity: high. Kind: defect.

Where: `ocaml/engine/e4_sched.ml`, `lookup`, `send`, `enqueue`, `wake`, and `shutdown`.

Evidence: `python3 shutdown_model.py` builds a scheduled qcheck-stm test around the exact scheduler source.
The wrapper pauses immediately before the original `E4_mailbox.push_with`. It changes scheduling only.
The source digest is retained in `scheduler-source-sha256.txt`.

```mermaid
sequenceDiagram
    participant S as Sender
    participant R as Router
    participant D as Shutdown
    S->>R: lookup succeeds under router lock
    R-->>S: machine returned; router lock released
    Note over S: pause before mailbox push
    D->>R: seal router
    D->>D: pending is zero; stop and join workers
    S->>S: enqueue; pending becomes one
    S->>R: wake reaches closed inbox
    R-->>S: wake refused, result ignored
    S-->>S: send returns Ok
```

The sequential control applies one accepted send and leaves pending zero. Sending after shutdown returns `Stopped`.
The concurrent history reports `Send: ok`, `Shutdown: applied=0`, and pending one.
Neither sequential ordering permits this history. qcheck-stm reports `Results incompatible with linearized model`; the expected test exit is one.
See `shutdown-model.log` and `shutdown_model_tail.ml`.

Why: lookup acceptance and mailbox insertion do not share ownership through shutdown's seal.
Quiescence cannot count a send that passed lookup but has not entered its mailbox.
The ignored inbox refusal leaves accepted work without a worker. This breaks the scheduler's accepted-work drain behavior.

Fix: retain send ownership through enqueue, or register in-flight admissions before releasing the router lock.
Shutdown must wait for those admissions before checking quiescence. Handle the closed-inbox result consistently.

Deletes: zero declarations are proposed for deletion. Net line saving is not claimed.
Test: extend the scheduler model with `Shutdown`; retain both serial controls and the forced overlapping history.
Plan: new; extend the existing scheduler model. Size: M.

Limit: an additional unmodified-library stress test finds no mismatch in 2,000 unscheduled races.
That result is retained in `shutdown-stress.log`. It does not invalidate the scheduled counterexample or measure its production frequency.

### A3.3 — Failed directory syncs are treated as success

Severity: high. Kind: defect.

Where: `ocaml/engine/cas/e4_control.ml`, `commit`; `e4_pack.ml`, `e4_wal.ml`, and `e4_index.ml`, `fsync_dir`.

Evidence: `python3 fault_injection.py` keeps real file writes and file syncs, but injects `EIO` for directory sync.
The exact pinned `E4_control.commit` returns success after rename:

```text
control commit: returned success after 1 injected directory EIO; readable=true
```

Why: the commit path catches the error and acknowledges the update. Readability in the live process does not establish persistence after power loss.
The pack and WAL directory helpers use the same error-swallowing pattern.
POSIX permits partial or reordered persistence without the required synchronization. A failed sync supplies no successful durability evidence.
See the POSIX references below.

Fix: provide one durable-file helper with an explicit supported-filesystem contract. Propagate directory open and sync failures.
Synchronize the parent after creating a directory whose existence forms part of the acknowledged state.
If weaker durability remains intentional, the owner must change the public guarantee explicitly.

Deletes: replace three eight-line `fsync_dir` copies, measured as 24 lines in `function-spans.json`.
The new helper's size is not measured, so no net saving is claimed.
Test: the injected directory error must produce a refusal. A normal commit remains readable and verifiable.
Plan: new; shared helper is also a B2 consolidation candidate. Size: M.

Scope: `E4_index.save` also ignores its file-sync error. That index is reconstructable, so its loss alone loses a cache.
The control and segment-directory cases protect durable publication. No physical power-loss outcome is asserted from this injection.

### A5.1 — A failed WAL open leaves its writer claim held

Severity: medium. Kind: defect.

Where: `ocaml/engine/cas/e4_wal.ml`, `open_`; `ocaml/engine/cas/e4_lock.ml`, `acquire` and `release`.

Evidence: `storage_probe.ml` creates and closes a valid log. It temporarily replaces its segment pathname with a directory.
Opening acquires the writer claim, then raises `Sys_error("Is a directory")`.
The probe restores the original segment and retries. The retry raises `E4_wal.Locked`, although no writer was returned.
The retained log contains both failures and the restored segment bytes.

Why: cleanup covers selected scan verdicts, but not exceptions from filesystem operations after acquisition.
The failed call makes a repaired store unavailable for the rest of that process.
Malformed stored headers also escape as `Failure`, contrary to the newer STANDARDS rule 6 boundary.
The older WAL interface documents that exception; documentation does not repair the leaked resource.

Fix: bracket lock and descriptor ownership throughout opening. Transfer ownership to the writer only after every opening step succeeds.
Return a typed open refusal for bad stored input and I/O failure.

Deletes: rewrite the 57-line `open_` span measured in `function-spans.json`. No net line reduction is claimed.
Test: the restored segment must open successfully after the first failure. Add failures at segment creation, truncation, sync, and final opening.
Plan: new. Size: S.

### A3.4 — The WAL batch property promises more than recovery implements

Severity: medium. Kind: defect.

Where: `ocaml/engine/cas/e4_wal.mli`, property LG3; `e4_wal.ml`, `flush_buf`, `walk_segment`, and `open_`.

Evidence: `storage_probe.ml` constructs a pre-sync crash image containing one complete row and three bytes of the second row.
Both rows belong to one buffered commit. Recovery retains the first row and removes the partial tail:

```text
WAL torn batch: recovered=1 next=1 durable=1 stop=eof: every stored row was delivered
```

Why: LG3 says rows in one commit are all durable or all absent. Independent row frames contain no complete-batch marker.
A partial write can leave a valid proper prefix. Recovery cannot reconstruct the stronger batch property from these bytes.
This is a constructed interrupted-write image, not evidence that a successfully synced commit lost data.

Fix: if LG3 remains the contract, add a batch envelope or commit marker.
Recover only groups with a validated end marker.
Alternatively, obtain an owner ruling for row-prefix recovery and revise LG3. Do not silently weaken the stated property.

Deletes: zero declarations are proposed for deletion. A format change needs versioning; no size saving is claimed.
Test: enumerate truncations of a two-row batch. The chosen contract must distinguish batches with an end marker from partial groups.
Plan: new owner decision. Size: M.

### A5.2 — Negative CLI budgets escape as implementation exceptions

Severity: medium. Kind: defect.

Where: `ocaml/engine/kit/bin/eff.ml`, CLI integer parsing and top-level exception handling.

Evidence: `program.json` is a generated JSON spelling of a program returning natural one.
The normal `check` exits zero with structured success. `explore program.json --budget -1` exits two with empty stdout:

```text
Fatal error: exception Invalid_argument("Lcnf_array.get_exn: -1 outside [0,128)")
```

`run program.json --limit -1` instead exits zero with a finished result. Full arguments and channel bytes are retained in `cli.json`.

Why: signed CLI integers enter generated natural-number consumers without a nonnegative input check.
An ordinary user option reaches a documented internal precondition failure. STANDARDS rule 6 requires an ordinary refusal at this boundary.

Fix: validate nonnegative option domains before invoking generated code. Use the planned Cmdliner interface for typed option errors.
Keep structured command errors. Do not hide arbitrary programmer exceptions with a blanket catch.

Deletes: zero declarations are proposed for deletion by this focused fix. H4 can replace the manual parser separately.
Test: retain negative, malformed, overflowed, zero, and positive values for every numeric option.
Plan: H4. Size: S.

### A7.1 — Kit_serve has no explicit installed interface

Severity: low. Kind: smell.

Where: `ocaml/engine/kit/kit_serve.ml`, module interface.

Evidence: `ocamlc -i` succeeds and exposes twelve value declarations, plus types and module aliases.
The exact command is `interface-commands.json`; its output is `kit_serve.inferred.mli`.
The source has no companion `.mli`, although it is an installed library module changed by wave 2.

Why: STANDARDS rule 5 requires a small explicit interface. Readers cannot distinguish supported calls from serialization helpers without reading the implementation.

Fix: add `kit_serve.mli` exposing the supported request, answer, and serving boundary. Document ordinary refusals and exceptional preconditions.
Hide private helpers and retain the one generated owner of schema meaning.

Deletes: zero implementation lines need deletion. Restrict the public declarations after checking callers; do not assume all twelve are private.
Test: build current consumers through the explicit interface. A separate negative fixture must fail when it calls a deliberately hidden helper.
Plan: H8. Size: S.

### A7.2 — Documentation warnings still obscure interface contracts

Severity: low. Kind: cleanup.

Where: OCaml interface documentation named by `doc.log`, including interval syntax, exception references, and scheduler type links.

Evidence: `dune build @doc` exits zero with 37 `Warning:` lines and zero `Error:` lines.
The old lead of 39 warnings or errors is stale. The command and retained log appear below.

Why: malformed markup and unresolved references make the generated API harder to read correctly.
Examples include interval brackets parsed as markup, unresolvable exception identifiers, and unresolved `Delay` links.

Fix: repair the cited markup and qualify references. Keep the actual contracts and exception names.

Deletes: zero code declarations. No line saving is claimed.
Test: rerun the same documentation target and require these warnings to disappear without suppressing them.
Plan: H6. Size: S.

## A3: persistence and lock audit

`rg -n 'Unix\.fsync|Unix\.rename|Sys\.rename' ocaml --glob '*.ml'` confirms fifteen sync call sites.
It also finds one `Unix.rename` and one `Sys.rename`; the latter publishes the index snapshot.
The normal CAS publication order writes and syncs pack bytes before publishing the control boundary.
`E4_control.commit` writes a temporary file, syncs it, renames it, then attempts directory sync.
The order is appropriate; the missing error propagation produces A3.3.
Segment creation syncs the new file and attempts its containing directory sync.
Recursive directory creation does not establish persistence of every newly created ancestor.
WAL recovery truncates a torn active tail. A sealed damaged segment receives a refusal in the relevant scan path.
These are source observations. The finite probes above establish only their stated cases.

| Ignored-error site | Effect | Assessment |
| --- | --- | --- |
| `E4_cas.cid_map`, durable decoded nodes | Omits a node from the derived by-CID map and advances coverage | Hides a corrupt member in the cache; deletes no pack bytes |
| `E4_cas.cid_map`, staged nodes | Skips a decode failure | Normal admitted staging should exclude this case; no reachable counterexample claimed |
| `E4_cas.result_map` | Omits undecodable results and advances derived coverage | Hides a corrupt member; deletes no source bytes |
| `E4_cas.open_rw_exn`, failed `E4_index.load` | Rebuilds the index from pack bytes | Intended cache recovery, subject to A3.1's scan-completion requirement |
| `E4_index.Deps.rebuild` | Skips invalid node decoding | Incomplete dependency cache; scan completion alone does not prove node validity |

The current tree has additional `Error` branches beyond the old five-site description.
The verifier's by-query table also skips invalid envelopes, but its subsequent per-node check normally rejects them.
A3.1 identifies the earlier structural stop that defeats that complete-record assumption.
No listed skip directly deletes stored bytes. WAL recovery's intentional truncation is a separate operation.

`rg -n '"LOCK"|lockf' ocaml --glob '*.ml'` finds no second production opener of the lock pathname outside `E4_lock`.
The host probe demonstrates the relevant process semantics:

```text
another process while claimed: can_lock=false
after extra LOCK fd closes: can_lock=true
after parent release, child raw=true inherited_registry=refused
```

The extra descriptor is a test control, not an identified production caller.
Closing any descriptor for the same file can release that process's record locks.
After fork, the child has a copied in-memory held-writer table but does not inherit the record lock.
Using an inherited writer therefore has no supported exclusion guarantee; reacquisition also needs a PID-aware held-writer table or an explicit prohibition.
The implementation currently relies on a local, cooperative, process-owned writer discipline.

NFS is not tested here. NFSv4 locks have lease and server-state semantics, including state loss after partitions.
A supported NFS profile must address those failures explicitly; POSIX-looking `lockf` calls alone do not establish it.
The owner should state the supported filesystem and fork profile before widening the durability claim.

## A4: concurrency coverage and rejected leads

| Structure | Ownership and existing evidence | Review result |
| --- | --- | --- |
| Mailbox | Locked bounded queue; exercised by scheduler model suites | A4.1 concerns router-to-mailbox acceptance, not an isolated queue-order failure |
| Ring | Append, read, and written count share its mutex; append checks writer ownership | No new counterexample; absence of a standalone model proves no defect |
| Log | Persistent `Lcnf_array` state | Sharing immutable values differs from sharing a mutable append cursor |
| Cache | Mutable cache without its own lock | STANDARDS rule 8 requires one owner; no supported multiwriter use is established |
| Kit session | Abstract mutable session; P1 gives independent owners | P2 deliberately shares one session as a negative control |
| Scheduler | Existing scheduler model lacks a shutdown command | The new scheduled history exposes A4.1 |

`stm_tool` supplies `~retries:2` to its deliberately failing P2 control, with `~neg:true`.
That argument does not suppress a failure in the positive session model. The lead is refuted in its stated form.
`Stm_support` has its own general retry policy; A9 owns load and reliability review.
`E4_quiescence` documents the 0.2 ms polling timeout and the missing timed condition wait in this stdlib profile.
No measured latency defect follows from the constant alone.

## A5: exception inventory and CLI channels

`python3 inventory.py` retains the lexical inventory and classification in `inventory.json` and `inventory-summary.json`.
It finds 221 hand source/interface files. These are matching-line counts, not counts of reachable runtime exceptions.
The lexical `library` bucket includes a few generator-interface fixtures. It is not an authoritative production-library census.
Comments can also match. The source checks below qualify the raw counts.

| Pattern | Library bucket | Test/bench | Interface | Tool/template | Total |
| --- | ---: | ---: | ---: | ---: | ---: |
| `failwith` | 1 | 82 | 1 | 2 | 86 |
| `invalid_arg` | 80 | 9 | 0 | 0 | 89 |
| `Option.get` | 2 | 5 | 0 | 0 | 7 |
| `List.hd` | 0 | 22 | 0 | 0 | 22 |
| Whole-token `List.nth` | 0 | 88 | 0 | 0 | 88 |

The old `List.nth` count also includes substring matches such as `List.nth_opt`.
Most library `invalid_arg` calls guard programmer capacities, bounds, ownership, closed writers, or one-use resources.
`exception-contracts.txt` preserves the corresponding interface excerpts. This is not a claim that every guard documents every possible exception.
The two library `Option.get` sites follow local synchronization or retained-slot invariants in `E4_reply` and `E4_ring`.
The concrete external-input failures are A5.1 and A5.2.

| CLI input | Exit | stdout | stderr |
| --- | ---: | --- | --- |
| Valid program, `check` | 0 | Structured success | Empty |
| Missing program | 2 | Structured error | Empty |
| Negative explore budget | 2 | Empty | Fatal exception |
| `--help` | 2 | Empty | Usage |
| Malformed request, `serve` | 0 | Structured error | Empty |
| Malformed request, `mcp` | 0 | JSON-RPC parse error | Empty |

Serving processes remain available after per-request refusal; exit zero is appropriate for that loop.
H4 should give explicit help success and consistent command-error behavior. A5.2 is the demonstrated defect, not a general stdout prohibition.

## A6: constants and configuration

Format owners already name magic and version bytes: control version 2, pack version 1, index version 1, and WAL version 1.
`Eff_frame` owns framing tags. `E4_shape` repeats six of those tags; the parent receives this B2 consolidation candidate.
SHA-256 constants belong to the standard and do not require arbitrary renaming.

Scheduler defaults have one named owner in `E4_sched`: domains, mailbox bound, ring capacity, batch, spin, checkpoint spacing, and minor heap.
Finalizer fuel belongs to `E4_abandon`. Their interface describes their purpose, but not every numerical choice has measured justification.
No performance finding is claimed without a benchmark.

The public `config_of_env` contract explicitly documents fallback on malformed integers. The finite result is retained in `config.log`:

```text
E4_BATCH="8" => batch=8
E4_BATCH="eight" => batch=8
E4_BATCH="-1" => batch=-1
E4_BATCH="9999999999999999999999999" => batch=8
```

That behavior can conceal an operator typo, but it is not an undocumented regression.
A future explicit configuration loader should distinguish absent, malformed, and out-of-domain values.
It should return the effective configuration and its provenance. This remains an optional boundary improvement rather than a ranked defect here.

The recipe caps of 4,000 and 2,000 are traversal limits, not silent output truncation.
`Gen.emit` reports headroom and refuses an unresolved frontier. Current manifests contain 3,253 API rows and 822 engine rows.
Thus the measured headroom is 747 and 1,178. `inventory.py` measures those manifest rows.
The round limits lack a numerical rationale, but the explicit refusal prevents silently omitting required declarations.
Test counts and mutation value belong to A9; this seat does not invent a reason for them.

## A7: interfaces, comparisons, ignored results, and warnings

No exposed mutable record field appears in the hand `.mli` files inspected here.
Twelve lexical interface matches for `mutable` are prose. Actual mutable implementations remain behind abstract types.
This does not establish safe use of an abstract value across domains; its ownership contract still matters.

The typed comparison checker passes across 75 built library `.cmt` files, with exit zero.
The complete argv is retained in `interface-commands.json`; `typed-lint.log` retains the result.
No finding duplicates the enforced comparison rule. A lexical `compare` count cannot identify unsafe abstract-value comparison.

Of 220 `ignore (` matches, thirteen fall in the library bucket and 207 in tests or benches.
Scheduler inbox results participate in A4.1. Other inspected cases discard unit or an intentionally unused value.
The count alone establishes no additional lost-error defect.

The named missing-interface leads have different owners:

| Module | Verdict |
| --- | --- |
| `Kit_serve` | A7.1: installed library boundary needs its `.mli` |
| `Api_engine_inst` | Explicit functor-only exception in STANDARDS rule 5 |
| `api_engine_prelude.ml` | Generator input fragment, not an installed module boundary |
| `join_escape.ml` | Intentional negative compiler control |

The kit warning string now enables the ordinary warning set. Its lack of `@55` is not a demonstrated missed local-join check.
Generated local joins belong to the API, closure, and lanes stanzas, which enable fatal warning 55.
The test-local `-w -33` suppresses unused-open warnings in `api_gen_inst.ml`; it does not disable the library's type checks.
Seven flag spellings remain a consolidation question for B2, not seven independent defects.

## A8: source comparisons and pedigree

Repository rules control this review. The references supply concrete techniques and boundary examples, not a style vote.

| Question | Primary source and compared declaration | Effect4 conclusion |
| --- | --- | --- |
| Results and exceptions | Jane Street, *Base* v0.16.5, `base/or_error.mli`, `try_with` and `of_exn`; *Core* v0.16.2, `core/result.mli` | Typed refusal values fit ordinary domain errors. This does not require replacing programmer-precondition exceptions. |
| Cleanup | Jane Street, *Base* v0.16.5, `base/exn.mli`, `protect` and `protectx`; *Stdio* v0.16.0, `stdio/in_channel.mli`, `with_file` | Bracket resource ownership in A5.1. Merely replacing `Printf` adds no safety. |
| Compiler idiom | Xavier Leroy, INRIA, *OCaml compiler Misc interface*, copyright 1996, distributed with OCaml 5.1.1; `compiler-libs/misc.mli`, `try_finally` | The compiler's cleanup API runs cleanup on success and failure and preserves exception information. |
| Compiler error boundary | Fabrice Le Fessant, INRIA, *Cmt_format*, copyright 2012, OCaml 5.1.1; `compiler-libs/cmt_format.mli`, `Error`, `read_cmt` | Compiler-libs also uses exceptions. It does not justify claiming that all OCaml pedigree uses results everywhere. |
| File replacement | Irmin contributors, *Irmin filesystem backend*, pinned commit `7a09a06fff67bc4981faca36a332c51fc16e819e`, `irmin_fs_unix.ml`, `with_write_file` | `Lwt.finalize` brackets descriptor ownership before rename. This illustrates cleanup, not a power-loss guarantee. |
| Derived host data | Jane Street, *ppx_sexp_conv* v0.16.0 and *ppx_expect* v0.16.0 | Use only for hand host types or suitable golden tests, with a measured maintenance benefit. Lean-owned carriers still need generated faces. |

The installed reference roots are `/Users/pooks/.opam/effect4/lib/base`, `/Users/pooks/.opam/effect4/lib/core`, and `/Users/pooks/.opam/effect4/lib/stdio`.
Compiler reference files are under `/Users/pooks/.opam/effect4/lib/ocaml/compiler-libs`.
The Irmin source is `/Users/pooks/Dev/refs/irmin/src/irmin-fs/unix/irmin_fs_unix.ml`.
Its pin comes from `/Users/pooks/Dev/refs/ocaml-tooling/MANIFEST.txt`.
The installed package versions come from `opam list --switch=effect4 --installed --columns=name,version base core stdio ppx_expect ppx_sexp_conv`.
The compiler version is OCaml 5.1.1.

`Printf.sprintf` primarily constructs diagnostic strings. The scheduler writes worker failures and optionally writes its effective configuration to stderr.
Those explicit effects do not justify a blanket prohibition on Printf within libraries.
Binary framing already uses Buffer in the relevant paths. A10 owns measured concatenation costs.
No measured hand derivation warrants a new deriver finding from this seat.

The `probe/sexp-face` comparison uses Git objects only: commits `6c1485863` and `d7b02d1a9`, dated 2026-10-18.
Its seven-file diff adds 707 lines and removes six. It adds a Lean Sexp carrier, laws, and generated LCNF faces.
It does not authorize handwritten OCaml derivations for Lean-owned carriers.
H5 can migrate appropriate golden tests to ppx_expect when touched. No extra test framework is justified solely by appearance.

The smell checklist remains a heuristic. Duplication matters where sync handling or constants have two owners.
Resource-lifetime message chains matter in A5.1 because an error leaks ownership.
No independent finding survives for feature envy, refused bequest, or speculative generality after applying actual ownership and behavior requirements.
Tooling-enforced layout and comparison preferences are excluded.

### Published primary references

- IEEE and The Open Group, *The Open Group Base Specifications, Issue 8*, POSIX.1-2024, General Concepts §4. Persistence can be partial or reordered without synchronization. [Filesystem crash semantics](https://pubs.opengroup.org/onlinepubs/9799919799/basedefs/V1_chap04.html).
- IEEE and The Open Group, *fsync*, Base Specifications Issue 6, IEEE Std 1003.1-2004. A failed call does not guarantee completion of queued I/O. [fsync contract](https://pubs.opengroup.org/onlinepubs/009695399/functions/fsync.html).
- OCaml team, *OCaml 5.1 Reference Manual*, 2023, Unix library. [Unix interface](https://ocaml.org/manual/5.1/api/Unix.html).
- OpenBSD Project, *fcntl(2)*, operating-system manual, accessed 2026-10-19. Record locks are process-associated and are not inherited by fork. [Record-lock contract](https://man.openbsd.net/fcntl.2).
- T. Haynes and D. Noveck, editors, *Network File System (NFS) Version 4 Protocol*, IETF RFC 7530, 2015, §§9.5–9.6.3. Lease expiry can invalidate lock state. [NFS failure recovery](https://www.rfc-editor.org/rfc/rfc7530.html#section-9.6.3).
- Yaron Minsky and Anil Madhavapeddy, *Real World OCaml*, second edition, Cambridge University Press, 2022, Error Handling. The chapter explains protected cleanup and file brackets. [Error handling](https://dev.realworldocaml.org/error-handling.html).

## Reproduction and retained evidence

All scratch outputs must stay below this report folder. The shared build already contains the pinned libraries.

```sh
R=/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-19-quality-review/codex-review/probes
W=/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4
python3 "$R/standards/inventory.py"
python3 "$R/standards/measure_spans.py"
python3 "$R/standards/fault_injection.py"
python3 "$R/standards/shutdown_model.py"
python3 "$R/run_ml.py" "$R/standards/shutdown_stress.ml"
```

Use a new scratch directory for the storage and lock probes. The following runner chooses one without overwriting retained evidence.

```python
from pathlib import Path
import subprocess, time
r = Path('/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-19-quality-review/codex-review/probes')
for name in ['storage', 'lock']:
    scratch = r / 'standards' / (name + '-run-' + str(time.time_ns()))
    subprocess.run(['python3', str(r / 'run_ml.py'),
                    str(r / 'standards' / (name + '_probe.ml')), str(scratch)], check=True)
```

The storage probe's `List.hd` operates on its own freshly created positive fixture. It does not assess production reader totality.
The source wrappers retain the unmodified source hashes. They do not edit a production file or replace the shared libraries.

The documentation command runs from the pinned worktree's `ocaml` directory:

```sh
opam exec --switch=effect4 -- dune build --build-dir /Users/pooks/Dev/lean4-effect4/docs/research/2026-10-19-quality-review/codex-review/probes/_build @doc
```

`doc.log` retains stdout and stderr. Count diagnostics with:

```sh
rg -c 'Warning:' "$R/standards/doc.log"
rg -c 'Error:' "$R/standards/doc.log"
```

No Error match makes the second command exit one. That result means zero matched errors, not a failed documentation build.
`interface-commands.json` retains the exact infer and typed-lint argv, including its build-directory working path.
`cli.json` retains each CLI argv, stdin, exit code, stdout, and stderr.
`cli_fixture.ml` regenerates `program.json` and the configuration control.

To repeat CLI observations, invoke `$R/_build/default/engine/kit/bin/eff.exe` with each retained `cli.json` argument list and stdin.
To repeat the interface checks, execute the `infer` and `lint` arrays in `interface-commands.json`.
Run `lint` with that file's `lint_cwd`. Both commands return zero in this review.

Limits: this review does not prove physical persistence, NFS exclusion, race frequency, or all possible exception reachability.
The scheduled race, corrupted-record acceptance, lost WAL staging, leaked claim, and CLI failure each have a concrete retained witness.
