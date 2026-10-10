# Queue service-client and build-repair review

The Queue service client returns the recorded Lean answer and rejects changed values, unexpected failure, and a lost queue capture.
The build repair closes the original import-reader finding.
Two build paths still miss changed pins, and the standalone truth runner can skip a required client while reporting PASS.

## Reviewed state

Previous checkpoint: `f1f7ee6f3ef44e9f7402044ad4c3ef992d64985e` on `codex/host-followup-review`.
Its implementation review ends at `294c89cdee0fd5874c01df45fb2654c5a480b2cd`.
This review tests `f6bf77246cd73e4d3b5206b239132fc4f0d037cd`.
The service-client implementation lands in `d0fdd93faf8b1935281cbfc67de4249beae2617a`.
The later observed head is `e7931623287bedd4a7a6afbeb8817b106906e8c2`.
That later commit changes only `tools/target/checker.ts`.
It leaves every tested source unchanged.

The active Claude session remains `9ebf38b2-8b2f-44e5-8fd9-2dc0cb5a1f50`.
A bounded recent tail confirms its directory as `/Users/pooks/Dev/lean4-effect4`.
The session reports a build of the stricter service reader, TypeScript printer controls, and Semaphore service.
These changes remain uncommitted at this checkpoint.
Their reported progress does not close the earlier service findings.
No message goes to Claude, and no review edit touches the primary checkout.

The completion criteria are executable controls for the build repair and Queue client, retained evidence, and a checkpoint separating committed work from active edits.

## BUILD-IMPORTS resolves

**Role:** finite control of the build helper.
**Evidence:** the committed Make helper with a harmless Lake substitute.
**Scope:** `build_imports` in `Makefile` and `main` in `scripts/lean-imports.py`.

The command now uses `imports_of` from `scripts/lib/lean_imports.py`.
The current consumer, a leading block comment, and a comment between imports all produce the same three workspace targets.
An empty workspace-import list starts no build.
An unreadable input exits unsuccessfully before any build call.
The shared reader's eight existing controls pass against the committed sources.
`checks/import-controls.json` and `checks/shared-import-tests.log` retain the results.

## BUILD-PINS remains open on two paths

**Role:** finite control of check freshness.
**Evidence:** dry runs against the exact committed `Makefile`, with source paths and controlled timestamps.
**Scope:** `check-cases`, `corpus`, and `check-proof-style`.

The original `check-cases` control now reruns after each changed build pin.
The shared `BUILD_PINS` declaration names `lean-toolchain`, `lakefile.toml`, and `lake-manifest.json`.
An unchanged tree still uses its marker.

Two paths do not consume that declaration:

- `CORPUS_TRACE` depends on `LEAN_SOURCES`, without `BUILD_PINS`.
- The `proof-style` marker filters `LEAN_SOURCES`, without `BUILD_PINS`.

Each path reruns after a core-source change.
Neither reruns after changing only one of the three build pins.
A caller can therefore request either path and reuse output or acceptance from the previous compiler or package configuration.
The corpus finding concerns the direct `corpus` target.
The proof-style finding concerns its named check, with an unchanged source inventory.

`checks/make-controls.json` retains fifteen controls and ten local repair controls.
The probe holds the unchanged inventory marker old with Make's `-o` option.
It never starts Lake or touches the primary markers.
Adding `BUILD_PINS` to both prerequisites makes every changed-pin control schedule the intended work.
The unchanged controls still use their markers.

**Next action:** use `LEAN_INPUTS` for `CORPUS_TRACE`, and add `BUILD_PINS` to the proof-style marker.
Keep their narrow builds.
This finding does not establish that every other dependency has been inventoried.

## CO6B-CLIENT: a required client can disappear from a passing runner result

**Role:** finite control of required execution evidence.
**Evidence:** the committed runner, one committed Queue entry, and a missing-module mutation.
**Scope:** standalone execution through `main` in `harness/truth/run-truth.ts`.

The entry retains its `client` field, but the mutation sets both `decl` and `expr` to `null`.
`moduleFor` returns `null`.
The runner records `hostExit = "not run"` and skips the client before computing `clientAgree`.
The disagreement filter rejects false values, but these comparison fields remain absent or null.
The process exits zero and prints that one program agrees.

`checks/client-controls.json` retains this result beside the accepted and rejected controls.
The full `check-truth` gate also compares the manifest, result, and generated-module inventory against retained artifacts.
Those comparisons would reject this mutation against the current artifacts.
This probe therefore establishes a standalone runner gap, not a bypass of that full gate.

**Next action:** reject a client-bearing entry when no module can run.
`runner-repair.patch` gives the smallest local repair for this control.
The repaired copy sets `clientAgree = false` in that refusal branch.
It rejects the missing module and unexpected failure, while the original client still passes.
Pinned tsgo 7 checks the repaired runner with the installed Bun types.
The patch remains review evidence and does not alter the implementation.

## The Queue comparison exercises a real service

**Role:** finite comparison of exit observations.
**Evidence:** fresh rc.112 executions compared with the committed Lean result.
**Scope:** `pQueueService` and `queueServiceClient` in `harness/truth/Truth.lean`.

The Lean program allocates one queue, offers `1`, then takes from that queue.
The TypeScript client obtains `NumberQueue` from its layer and calls the exported methods.
The layer captures one allocated queue for those methods.
The independent expected answer is `success [true,1]`.
Both the generated main and a separately observed service client return that answer.
The probe reads the committed Lean observation and does not rerun Lean.

| Control | Runner result | Service-client result |
| --- | --- | --- |
| original | exit 0 | agrees, `success [true,1]` |
| client returns a wrong value | exit 1 | disagrees, `success [false,1]` |
| client fails unexpectedly | exit 1 | disagrees, failure `42` |
| take allocates a fresh queue | exit 1 | disagrees, no exit before the deadline |
| required module disappears | exit 0 | client never runs |
| original restored | exit 0 | agrees, `success [true,1]` |

All five printable controls type-check under tsgo `7.0.0-dev.20260629.1`.
The runtime is Effect `4.0.0-rc.112`, under Bun `1.4.2`.
The client deadline is 100 milliseconds.
A missing shared queue changes execution even though the mutated program still type-checks.
The comparison therefore detects behavior beyond target typing.

The client observation covers its exit only.
The recorded schedule and synchronous comparison concern the generated main.
This fixture does not establish general failure behavior, fairness, cancellation, or service lifetime laws.
`checks/client-controls.json` records the commands and outcomes.
The original and restored controls also retain the independently observed client result.

## Shared structure and the next slice

`Queue.serviceDefs` in `src/Effect4/Library/Queue/Defs.lean` declares the service's initial program and first-order methods.
The printer builds the layer and shares its state among methods.
This arrangement concentrates capture and lifetime wiring behind the service declaration without adding another program representation.

Keep the independent client source as the behavior witness.
Add an explicit required observation for every service-client fixture.
The same fixture identifier should connect its machine observation, target check, and host execution receipt.
An ordinary corpus entry may omit a client, but a declared service-client fixture must not silently omit its execution.

The current Semaphore work follows the first-order method interface.
The Pool plan records a different requirement: `use` accepts a program body while holding its protection mask.
Splitting it into separate lease and return methods would change that behavior.
The program-valued method work remains explicitly deferred.
This review does not treat that deferral as a regression.

Two GPT-6.1 Sol agents independently inspect build freshness and the client comparison.
A follow-up source review checks the later binding-owner change at `e7931623`.
It finds no false acceptance in the current helper inventory.
Compiler module resolution remains a useful future consolidation target for the hand-written export-path lookup.
No executable result for that later checker change is claimed here.

## Verification and limits

```sh
python3 docs/research/2026-10-10-service-client-overwatch/check.py
python3 docs/research/2026-10-10-service-client-overwatch/check-repair.py
```

`pins.json` records the reviewed commit, source hashes, runtime, and TypeScript compiler.
The probes capture committed source, with runtime dependencies from the existing pinned installation.
The review adds no theorem or planned goal.
It runs no Lean compilation, axiom gate, full sweep, merge, or push.
Axiom output is inapplicable to these TypeScript executions and Make dry runs.
The earlier proof graph and its open obligations do not change.
The whitespace check reports one final blank line in the retained `snapshot/harness/truth/control.ts`.
Those bytes match the reviewed source and remain unchanged.
Every other staged path passes the whitespace check.

## Checkpoint

The tested build repair and Queue client now cover the committed state through `f6bf7724`.
The later observed head is `e7931623`, whose tested files remain identical.
`BUILD-IMPORTS` closes.
`BUILD-PINS` closes for its original conformance control and remains open for corpus generation and proof-style checking.
`CO6B-CLIENT` is the new confirmed standalone runner finding.
`CO6B-READ`, `CO6B-NAMES`, and `CO6B-KEYS` await the active repair's landing and independent checks.
The earlier `CLOSURE-POP` and `CLOSURE-ERASURE` findings remain unchanged.
Next triggers are those service repairs, the Semaphore client landing, or changes to either new control's owner.
