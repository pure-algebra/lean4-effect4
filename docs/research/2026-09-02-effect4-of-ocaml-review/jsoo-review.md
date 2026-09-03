# Review: the OCaml / js_of_ocaml / host-comparison side of `effect4_of_ocaml`

Reviewer: Claude, 2026-09-02. Subject: `/Users/pooks/Dev/effect4_of_ocaml` (read-only).
Scope: the pipeline, the agreement claims against `effect@4.0.0-rc.112`, and what the
work offers the Lean trace lane (`misty-frolicking-naur.md` packets P-T3, P-T9a/b, P-T11).
Codex was editing `docs/` while I read; doc citations are to the 21:28 state, script and
evidence citations to the 20:36–21:18 state.

## 1. What the pipeline is, what is pinned, and whether it reproduces

Two independent chains, sharing one Rocq extraction.

| Stage | Artifact | Pin |
| --- | --- | --- |
| Rocq source | `rocq/Effect4Probe.v` (11-constructor term language, `eval`), `rocq/MachineProbe.v` (frame machine), `rocq/CallbackProtocol.v`, `rocq/CellExecutionCertificate.v` | Rocq 9.1.1 |
| Extraction | one `machine_extracted.ml` copied to `effect4_extracted.ml` so both evaluators share data types (`scripts/build-effects5.sh:18-24`) | — |
| Native | `ocamlc` bytecode; `ocaml/effects5_runtime.ml` is a hand-written OCaml 5 deep-handler interpreter over the *same* extracted terms | OCaml 5.1.1 |
| JavaScript | `js_of_ocaml compile --enable effects --target-env=nodejs` (`build-effects5.sh:34,36,39`) | js_of_ocaml 5.7.1, built from source in `_build/` |
| Oracle | `effect@4.0.0-rc.112` from `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect` | Node 22.23.2 |

The js_of_ocaml pin is real work: the installed 5.7.1 was built with OCaml 4.14.2 and
rejects OCaml-5 bytecode, so `scripts/build-effects5-toolchain.mjs` copies seven cached
opam release sources into an isolated dune workspace and builds `js_of_ocaml.exe` there
(`:13-14, :56-63`), asserting the executable digest on every later run
(`verify-effects5.mjs:45`). The refusal is kept as a negative control (`:64-67`), as is a
build without `--enable effects` (`:68-71`).

**Reproducibility on this machine: yes for the artifacts, no for the toolchain.** Every
digest recorded in `evidence/effects5.json` still holds: the five `deterministicRegeneration`
outputs, the fourteen own-source files, the executed rc.112 package files. But the built
compiler *and its 6472-file source tree* live under `_build/`, which `.gitignore` excludes,
and the workspace has **zero git commits** (`git log` → "does not have any commits yet";
every path is untracked). A rebuild needs `~/.opam/4.14.2/.opam-switch/sources` and a
network fetch of four Unicode 15.0.0 tables (`build-effects5-toolchain.mjs:64-71`). Nothing
off this machine can reproduce it.

**Commands I ran** (all read-only; every `scripts/*.mjs` check writes into `evidence/`, so I
did not run those):

1. `node test/parity.mjs` with `OCAML_BIN=/Users/pooks/.opam/4.14.2/bin` — passed, printed
   the 75 cases. This is the only README-listed check that writes nothing.
2. A scratchpad driver against the prebuilt `_build/effects5/effects5.{js,byte}` and
   Codex's own `test/effects5-{cases,oracle}.mjs`: **875 tuples, 875/875 agreement on each
   of native-vs-Rocq-interpreter, machine-vs-interpreter, and native-vs-Effect; native and
   JS output byte-identical.** Reproduced exactly.
3. The same against `_build/callback-protocol/callback.js`: **539 cases, 1859 interaction
   prefixes, 0 mismatches on both the extracted reference and the OCaml handlers, 68
   unfinished** — matching `evidence/callback-protocol.json` exactly.
4. Digest re-verification of `effects5.json` and `callback-protocol.json` against disk.

The recorded Lean snapshot in `effects5.json` names head `c951711`; `lean4-effect4` is now
at `5173288`. I re-hashed its ten trace-lane inputs: all still byte-identical, only
`lake-manifest.json` drifted. The receipt is honest, just stale.

## 2. Are the agreement claims sound evidence?

**How the comparison is made.** For the 875-case battery, `scripts/verify-effects5.mjs:99`
compares the OCaml handler run against `observe(term, initial)` from
`test/effects5-oracle.mjs` — a **hand-written shallow embedding** of the same 11-constructor
toy language into Effect combinators (`succeed / fail / die / failCause(Cause.interrupt) /
Ref.get / Ref.set / sync / flatMap / catch / ensuring / provideService`, `:21-39`). The
observation is a tuple `{exit, state, trace}` where `exit` keeps ordered cause reasons
*including* interrupt identity (`:40-50`) and `trace` is the program's own `emit` list.

That is a genuine and useful differential test — it caught two compiled cleanup mutations
(`verify-effects5.mjs:142-179`) — but note the ceiling:

- The whole battery runs under `Effect.runSync` (`effects5-oracle.mjs:53`). **No fiber, no
  scheduler, no async, no real interruption.** `interrupt` is a synthesized `Cause.interrupt`
  *value*, not an interrupted fiber. `effects5.json.limits` says so; the README summary
  ("875 cases agree with … Effect TypeScript") does not.
- Both sides are authored by the same agent from the same intended semantics. What is
  checked is that Codex's Rocq/OCaml/machine implementations match Effect's real
  `flatMap`/`catch`/`ensuring`/`Ref`/`exit` behaviour on a small fragment. **No lowering is
  exercised** — there is no compiler from a source language to TypeScript in this path.
- 875 = 175 programs × 5 initial states, of which 160 programs come from one seeded LCG at
  depth 4 (`effects5-cases.mjs:38-56`). It is a grid, not 875 independent facts.

**Wire form and alphabet.** The one place Codex touches your alphabet is
`ocaml/effects5_runtime.ml:100-105`: for terms that are `cell_only` (Return/Get/Put/Bind,
`:95-98`) **and succeed**, it emits `op\tget\t[]`, `answer\tget\tN`, `op\tput\tN`,
`answer\tput\t[]`, `done\t{"success":N}`. I ran it: the rows for `incr` at 41 are
byte-identical to the event rows of `generated/traces/incr.empty.tsv`.

**Overclaim to flag.** `docs/BOOTSTRAP-RESULTS.md` ("What now works", row 4) says `incr` and
`twice` "agree under all three registered masks". Because the adapter emits only
`op`/`answer`/`done`, `m1` and `m2` project to *the same* row set —
`effects5.json.traceComparisons` records `m1 rows 7, m2 rows 7` for both programs. Only two
distinct projections were exercised, and the m1-vs-m2 discrimination that
`docs/TRACE-DAG.md` separation 2 calls a required self-test is untested here. Six
comparisons, two programs, one tape.

**Failures, cleanup, interruption.** Cleanup ordering *is* well covered in the 875 battery
(`ensuring` with combined exits, `combine_exits`, cleanup-defect-after-success,
cleanup-order, duplicate/distinct interruptors). It is **not** covered in the trace lane:
the Cell adapter refuses failure outright (`Failure _ -> None`).

**Host instrumentation.** Two different things, and only the second is strong:
- The 875 battery instruments *Codex's own* OCaml handler (`captures`/`consumed` counters,
  `effects5_runtime.ml:70-71`). Runtime accounting, not a linearity proof; the docs say so.
- The **callback packet does instrument the real rc.112 fiber**: `Effect.runFork(p, {scheduler})`
  with a dispatcher that throws on `scheduleTask` (`test/callback-oracle.mjs:30-34`),
  `fiber.pollUnsafe()` and `fiber.interruptUnsafe(id)` (`:82-90`), and an `AbortController`
  whose allocation depends on `register.length >= 2` (`:75-79`). Zero patching. This is the
  most valuable host work in the workspace.

**The 100 generated-TypeScript runs are the real thing.** `test/script-bridge-host.mjs:10-11`
imports *your* `harness/trace/fixture.ts` and `harness/trace/tracer.ts`, provides a `Ref`-backed
Cell, and runs `tracer.runTraced` at `maxOpsBeforeYield` 1000000 and 3, asserting `yields > 0`
at 3 (`:34`); `check-script-bridge.mjs:210-217` then compares the resulting TSV rows against
Lean's own expected rows. 100 = 50 points (2 programs × 5 arguments × 5 states) × 2 budgets.
That is an independent re-run of your host gate, and it passed.

**What the counts do not establish.** No compiler theorem (extraction, ocamlc, js_of_ocaml,
JSON codec all remain trusted); no statement about `Flow`; nothing about scheduling in the
875 or 130 batteries; nothing about failure or async in the 130 Cell execution certificates
(success-only, total view). All of this is stated in the evidence files' `limits`/`openBoundaries`
arrays. The gap is between those arrays and the README's numbered list.

**Gate gap.** `scripts/check-report.mjs:7-9` still lists seven documents and does not include
`docs/CALLBACK-PROTOCOL-CONTRACT.md`, and asserts nothing from `evidence/callback-protocol.json`.
The README was updated at 21:28 to advertise the callback packet; the self-check was not.

## 3. What this offers the Lean lane

### (a) Host tracer and goldens (`harness/trace/`, `generated/lowering-coverage.tsv`)

Complementary, not better. Your tracer is richer in every dimension Codex does not reach
(decisions, regions, finalizers, phase sentinels, budget/frontier, typed answers). Codex adds
one thing you do not have: a **native/JS byte-equality check on the same emitter**
(`verify-effects5.mjs:93`), which is a cheap cross-host determinism self-test worth copying in
spirit.

On receipts: do **not** import Codex's JSON into `generated/lowering-coverage.tsv`. The ledger's
`host` column is already `1` for all eight rules, `check-lowering-coverage.sh` rejects a host
receipt whose pin differs from the current one, and R8 forbids evidence crossing columns.
Codex's `evidence/effects5-lean-host-{incr,twice}.json` were produced by *your* driver
(`effect4-tools/packages/harness/trace.mjs`) at the correct pin, so they are the right shape —
but they live in an untracked workspace and would trip your drift gate. The column Codex could
plausibly feed is `property` (currently `0` for all eight rules), and only once the corpus is
Flow-shaped rather than shaped by his 11-constructor toy language.

Three things *are* worth importing:

1. `lean/WireBoundaryProbe.lean:14-31` proves, against your current `Trace.lean` (byte-identical
   to his snapshot), that `rows` is not injective: `Val.nat 7` and `Val.int 7` render identically
   while `Trace.agree m2` is false. That is a ready-made `E4-TARGET-CE-*` counterexample.
2. A stronger finding he did not name: your `escape` (`Effect4/Target/TypeScript/Trace.lean:24-29`)
   handles only `"` `\` `\n` `\r` `\t`, while the host encoder uses `JSON.stringify`
   (`harness/trace/tracer.ts:41`). For a `Val.str` containing any other C0 control the two faces
   **disagree**: the host emits a `\uXXXX` escape, the golden emits the raw byte. Today this
   is masked because Cell values are `nat`/`unit`; it becomes a live face divergence the
   moment a string-valued operation lands, and it surfaces as a mask *failure*, not a
   silent pass.
3. `Val.nat 9007199254740993` renders exactly in Lean and parses as `…992` on the host — the
   exact-number policy the plan already wants frozen before P-T8.

### (b) P-T9b structured lowering

The concrete asset is a **complete, offline, pinned js_of_ocaml 5.7.1 compiler source tree** at
`_build/toolchains/ocaml5-jsoo-5.7.1/vendor/js_of_ocaml-compiler.5.7.1/compiler/`, including
`lib/structure.ml` (256 lines), `lib/generate.ml` (2025), `lib/effects.ml` (933) and
`tests-compiler/effects.ml`, plus a working build of the compiler.

The parts of the plan's normative algorithm that *are* present and stable in 5.7.1:
`build_graph`/`reverse_post_order`, `is_backward g pc pc' = order pc >= order pc'`
(`structure.ml:37`), `dominator_tree` by Cooper–Harvey–Kennedy with the reducibility
fixed-point check (`:108-141`), `is_merge_node`/`is_loop_header` (`:142-147`),
`measure … 20`/`is_small` (`:191-211`), `shrink_loops` (`:213`).

**But the pin is not the version the plan re-derives.** I verified: 5.7.1's scope-stack type is
`type edge_kind = Loop | Exit_loop of bool ref | Exit_switch of bool ref | Forward`
(`lib/generate.ml:313-317`) — there is **no `Dispatch`** anywhere in `lib/`, and no
`merge_node_max`. Master has `Dispatch of Code.Var.t * int` and
`if List.length new_scopes > Config.Param.merge_node_max ()`. The plan's step 5 (scope stack
`Loop | Exit_loop | Forward | Dispatch`, "more than 10 siblings → selector switch") is master's.
Treat Codex's tree as a second, older data point, not the normative reference.

Likewise 5.7.1's effects backend is the FSCD 2017 Hillerström/Lindley/Atkey/Sivaramakrishnan
CPS transform (`lib/effects.ml:20-33`) behind a boolean `--enable effects`
(`lib/config.ml:71`). **There is no double translation and no `--effects=` flag in this pin.**
If P-T9b wants double-translation facts it needs a newer checkout.

Finally: Codex never *exercised* `Structure`/`generate`. The only flags used anywhere are
`--enable effects --target-env=nodejs`; no `--pretty`, no sourcemaps, no assertion on generated
control flow. He compiled *through* js_of_ocaml; he did not study its output.

### (c) P-T11 patched rc.112

The most directly reusable packet. `docs/CALLBACK-PROTOCOL-CONTRACT.md:10-18` names exactly the
internals P-T11 plans to patch — `callbackOptions`, `asyncFinalizer`, `FiberImpl.evaluate`,
`interruptUnsafe`, `getCont`, `exitFailCause`, the mask-restoration frame — and establishes their
behaviour **with no patch at all**. Findings I re-ran and confirmed
(`check-callback-protocol.mjs:104-116`):

- synchronous resumption never installs the cancellation frame (signal stays `open`, no
  `cleanup-start`); delayed resumption does;
- a typed failure or defect does not run cancellation; an interrupt-bearing cause does;
- the callback is closed before abort listeners run, so a reentrant offer from an abort
  listener runs no body;
- pending cleanup survives repeated interrupts and completes with the *first* captured cause
  (`["failure",[["interrupt",17]]]` with request history `[17,18]`);
- a cleanup defect **replaces** the prior failure (`["failure",[["die",91]]]`) — which is *not*
  `Ensuring`'s combining rule.

These are the behaviours a patched host must not change, i.e. free regression fixtures for
P-T11. Caveat: scheduling is disabled throughout, so nothing here speaks to P-T11's actual
target (pop order via `frames.jsonl`).

### (d) OCaml 5 handlers as a second reference semantics for the frame machine

Useful, narrowly. `rocq/MachineProbe.v` is a first-order configuration (control, finite
bindings, a stack of bind/catch/cleanup/restore frames, state, history) with six axiom-free
theorems. The one worth copying is `resume_frontier`: resuming an unfinished configuration
with extra fuel equals supplying the combined budget initially. `Effect4/Runtime/Runtime.lean`
has `FrameEvent`/`FrameStep` but no analogous resumption law, and TRACE-DAG separation 5
("frontiers compare as frontiers") is exactly the statement that law would justify.

The genuinely new host evidence is `ocaml/effects5_capabilities.ml:69-87`: a parked deep
continuation is a **frontier whose `Fun.protect` finalizer has not run**
(`cleanupBeforeCancel: 0`), and only an explicit `discontinue` runs it (`cleanupAfterCancel: 1`);
a second resume raises `Continuation_already_resumed` (`:32`). That is the discipline behind
`FRAME-FB-ASYNC-FINALIZER` demonstrated on a runtime that enforces one-shot continuations
natively.

The limit: OCaml deep handlers are one-shot, synchronous and single-fiber; Effect's fibers are
scheduled. Codex's machine has four frames against your seventeen `Prim` constructors and the
`Arm`/`contA`/`contE`/`contAll` machinery — no masking, no scope, no interrupt frames. It is a
sanity model for cleanup and resumption, not a competing semantics.

## 4. Next steps for Codex, things to stop, risks

Next (each one sentence, with its file):

1. Add `docs/CALLBACK-PROTOCOL-CONTRACT.md` to the document list and the twelve theorems plus
   the 539/1859/68 counts to the assertions in `scripts/check-report.mjs`.
2. Commit the workspace (it has zero commits) and record the seven opam source URLs and four
   Unicode 15.0.0 URLs+digests in `toolchains/effects5/` so the toolchain build stops depending
   on this machine's opam sources cache.
3. Emit at least one row category beyond `op`/`answer`/`done` from
   `ocaml/effects5_runtime.ml:100-105` so `m1` and `m2` become distinguishable projections.
4. Add a fixture pair to `test/effects5-cases.mjs` that agrees under `m1` and differs under
   `m2`, the self-test `docs/TRACE-DAG.md` separation 2 requires.
5. Upgrade the string witness in `scripts/check-wire-boundary.mjs` from "invalid JSON" to the
   sharper face divergence: Lean's `escape` versus the host's `JSON.stringify` on C0 controls.
6. State the oracle's execution mode in `README.md` — the 875-case battery is `Effect.runSync`
   with synthesized interrupt causes, so it exercises no fiber, scheduler or real interruption.
7. Record in `docs/BOOTSTRAP-RESULTS.md` that the local 5.7.1 pin lacks `Dispatch` and
   `merge_node_max`, and point any structured-lowering reading at a master checkout instead.
8. Give `test/callback-profile-cases.mjs` stable case ids so the five source-grounded rc.112
   behaviours can be consumed as data by the Lean lane without rerunning OCaml.

Stop doing:

- Stop leading with cross-product totals (875, 130, 539, 1859, 100); report programs × states ×
  budgets, and say how many *distinct* observations there are.
- Stop calling an in-repo shallow embedding "Effect TypeScript" without naming `runSync`.
- Stop writing `evidence/` from every check script — it makes reviewing this workspace a
  mutation, and it is why I could run only three of the twelve documented checks.
- Stop committing multi-megabyte stdout logs as receipts (`callback-protocol-commands.json`
  2.5 MB, `callback-protocol-observations.json` 4.2 MB) in a directory that is not in git.
- Stop opening new packets until the report gate covers the ones already advertised.

Risks:

- **Untracked, uncommitted, unreproducible.** Zero commits; `_build/` (297 MB) is the only copy
  of the pinned compiler and its source tree and is gitignored.
- **Machine-specific defaults** baked into every script: `EFFECT_PACKAGE_ROOT` →
  `foldlab/library/effects/node_modules/effect`, `ROCQ_BIN` → a foldlab annex opam root,
  `OCAML5_BIN` → `~/.opam/default/bin` (a movable alias, guarded only by a version assert).
- **Moving inputs.** `effects5.json`'s Lean snapshot is three commits stale; the packets
  re-hash before and after, which is the right discipline, but any consumer of these receipts
  must re-verify rather than cite.
- **Self-authored adversarial controls.** The mutation battery is designed by the same agent
  that wrote the implementation; it is a good regression suite, not an independent breaker.
- **Provenance of the oracle.** The rc.112 package used is a `node_modules` copy under
  `foldlab`, not `lean4-effect4/vendor/`; `source-inventory.json` records `sameSourceBytes:true`
  for two files, which is a spot check, not a full tree comparison.
