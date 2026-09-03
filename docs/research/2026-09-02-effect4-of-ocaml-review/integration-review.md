# Integrating `effect4_of_ocaml` with the Lean trace lane

Reviewer: Claude, 2026-09-02. Subject: `/Users/pooks/Dev/effect4_of_ocaml` (read-only),
against lean4-effect4 `5173288`, lean4-effects `e86f141` (v0.4.0), and the approved plan
`~/.claude/plans/misty-frolicking-naur.md`.

Codex's workspace is not a competing semantics. Every Lean file it carries either imports
our declarations or is explicitly labelled a research view. The integration problem is
therefore narrow and mechanical: **its Lean bridge is pinned one Effect4 commit and one
Effects tag behind**, its trace rows are our wire form minus a header, and three of its
findings belong in our registers and are not there.

## 1. Object-by-object alignment

| Codex object | Lean-lane object | Verdict |
| --- | --- | --- |
| Service-level rows in `evidence/script-lean-observations.json` (`op\tget\t[]`, `answer\tget\t0`, `done\t{"success":1}`) | `Effect4/Target/TypeScript/Trace.lean:47-60` `row`/`rows`; goldens `generated/traces/*.tsv` | **Same wire form**, byte for byte. Missing only the golden header block (`format`/`generator`/`input`/`pin`/`face`/`program`/`tape`/`rules`) that `effect4-trace` requires. |
| `CellExecution.Event`/`eventLog` (`lean/CellExecution.lean:12-27`) | `Effects.Trace.Event` (`Effects/Trace.lean:70-80`) | **Compatible**. Codex keeps a private `read`/`write` alphabet and projects it into ours via `eventLog`. Covers `op`/`answer`/`done` only: no `failed`, `decide`, `enter`/`leave`/`finalizer`, `frontier`. |
| `CellTarget.Term` + `denote` (`lean/CellTarget.lean:18-43`) | `Effects.Program Cell.Sig` via `harness/trace/Generate.lean:16-27` | **Compatible research view**, not a rival carrier; its own header (`:3-7`) says so. It is a second program spelling for the `ret/get/put/bind` fragment only. |
| Execution certificates `Certificate`/`check`/`check_sound`/`checked_program`/`checked_source` (`lean/CellExecution.lean:84-152`) | none — our nearest is the golden + `harness/trace/receipts/*.json` pair | **Complementary and strictly stronger inside its fragment.** `checked_program` (`:135`) makes the trace log of a run a *theorem* about `Cell.traced cellLive`; our receipts are executable evidence with no soundness statement. Axioms `propext`, `Quot.sound` — inside our ceiling. |
| Simulation certificates `SimulationProbe.check` / `accepted_is_bisimilar` (`lean/SimulationKernel.lean:55-64`) | `docs/TRACE-DAG.md:39` `semantics` edge, `required-open` | **Compatible, and the only concrete shape anyone has offered for that edge.** But its subject is literal labelled graphs; its own header (`:3-5`) disclaims "the unproved projection from `Effects.RawFlow`". It does not close our edge as it stands. |
| Cell script bridge `ScriptRowsExport.lean:9-46` | `Effect4.Target.EffectV4.{Script, ServiceRow, OpRow, Step, PureTerm}`; inventory `harness/trace/Generate.lean:119-123` | **Same objects, exported verbatim.** All four entries appear in `evidence/script-rows-export.json`; `incr`/`twice` translate, `recover`/`fallible` are explicitly refused. Duplicates part of `Generate.lean`'s `types` subcommand. |
| Callback protocol (`docs/CALLBACK-PROTOCOL-CONTRACT.md`; `evidence/callback-*.json`) | `Effect4.Prim` excludes `Async`/`AsyncFinalizer` (`Effect4/Runtime/Runtime.lean:90`); `FRAME-FB-ASYNC-FINALIZER` (`docs/FRAMES-DAG.md:353`) is an authored refusal | **Compatible; it is the missing evidence for a row we authored blind.** Its contract (`:16-18`) names our gap correctly, including the fused pop loop. This is the *only* Codex packet pinned at our current HEAD. |
| Wire-boundary probe (`lean/WireBoundaryProbe.lean:11-31`) | `Effect4.Target.TypeScript.Trace.rows`, `Effect4.Trace.agree Mask.m2` — both ours, unmodified | **Compatible, and it finds real defects.** Two proofs axiom-free; two reach `propext`/`Classical.choice`/`Quot.sound` through the renderer, which `docs/TRACE-DAG.md:40` already admits as an exact module. No new exemption. |
| Trust/axiom reporting (`evidence/cell-execution.json` `leanUniversalReceipts`, `rocqAxioms: []`) | `scripts/test-trust-gate.sh`, `EffectsTest/Flow/FlowV2AxiomReport.lean` | **Compatible discipline, separate gate.** Codex inspects `#print axioms` per declaration; nothing of ours runs over its tree and nothing of its runs over ours. |

### Pin drift in Codex's Lean bridge

`evidence/cell-execution.json` and `evidence/script-bridge.json` record `leanSourceSnapshot.head = c951711` with `lakefile.toml` sha `eb2e64e2…` and `lake-manifest.json` sha `e24a92fe…`. Both files have since changed (`6dfb3fbd…`, `834ddac3…` at `5173288`). Every *source* file Codex hashed — `harness/trace/Generate.lean`, `tracer.ts`, `atoms.ts`, `Effect4/Meta/Derive.lean`, `Target/TypeScript/{EffectV4,Trace}.lean`, `Semantics/Observation.lean` — is still byte-identical today. So the bridge's inputs are current; only the **dependency pin** moved, from Effects `9595a88` (v0.3.1) to `e86f141` (v0.4.0). `evidence/lean-baseline.json` is older still: it records lean4-effects at `570c7f3` (v0.3.0) and a *failing* Effect4 build caused by that skew; `README.md:50` correctly labels it historical.

What changed under the bridge:

1. **Flow v2 replaced one-payload-per-block** (`test/contracts/flow-v2.contract.md:27-41`; `docs/CLAIM-BOUNDARY.md:118-138` in lean4-effects). `RawBlock` gains `params`, terminators name operands by `Var` and carry argument lists, and `CyclesWF`/`unchosenCycle` is a new global clause. `test/FlowExport.lean:36-52` is written against the v1 shapes (`⟨⟨id⟩, 0, term⟩`, `.perform ⟨0⟩ ⟨1⟩`, nullary `.ret`) and **will not elaborate** at `e86f141`.
2. **Four of the seven admitted graphs are now inadmissible.** `single-cycle` (`:41`), `double-cycle` (`:42`), `choice` and `swapped-choice` (`:48-50`, both carrying `block 2 (.jump ⟨2⟩)`) contain `jump` cycles with no `choose`. `EF-FLOW-CE-002` reverses exactly this. `evidence/lean-flow-export.json` records all four as `admitted: true`, and `evidence/simulation.json`'s `lean-cycles-one-to-two`, `lean-swapped-branch-polarity` and `infinite-same-labelled-cycle` cases rest on them.
3. **The trace alphabet is service-level and now has a failure arm.** `Effects/Trace.lean:74` `failed`, and `Family.Service.tracedExcept` (`:256-270`) with `interpret_tracedExcept_fst` — the carrier is `ExceptT ε (StateT log M)` so the log survives a failure (`E4-TARGET-CE-010`). Codex's `eventLog` has no `failed` arm, which is why `recover`/`fallible` are refused.
4. **`Ref.set` returns the MutableRef** under a declared `Effect<void>`; answers are encoded from the declared spelling, not the runtime value (`harness/trace/tracer.ts:74-77`, `docs/TRACE-DAG.md` separation 7, `E4-SEM-CE-009`).
5. **The yield floor is 3, not 1** (`docs/TRACE-DAG.md` separation 8; `scripts/check-trace-host.sh:23-27`). `BOOTSTRAP-RESULTS.md:200` says "both tested yield budgets" without naming them.
6. `Effect4.Target.TypeScript.Trace.golden` now takes a `face` argument (default `"lean"`), which is the natural slot for a third emitter.

## 2. Findings that should enter our registers now

None of these three appear in `test/counterexamples/REGISTER.md` or `docs/TRACE-DAG.md`. All are proved or executed against our unmodified definitions.

**`E4-TARGET-CE-011`** — evidence `evidence/wire-boundary.json` `witnesses.erasedNumberConstructor`; proof `lean/WireBoundaryProbe.lean:14-31`.

> | `E4-TARGET-CE-011` | SEEDED | Equality of rendered trace rows implies semantic agreement under `m2`, so a host comparison over TSV bytes is a comparison of the alphabet | `Effect4/Target/TypeScript/Trace.lean` `val` sends `.nat 7` and `.int 7` to the same cell: `rows [.done (.success (.nat 7))] = rows [.done (.success (.int 7))]` by `rfl` while `Effect4.Trace.agree Mask.m2` of the two is `false` (`unrestricted_wire_implication_false`, `evidence/wire-boundary.json`) | state the host comparison as agreement *under a declared answer-type profile*, or make the renderer injective on `Val`; record in `docs/TRACE-DAG.md` that rendered rows, not events, are what the host gate compares |

**`E4-TARGET-CE-012`** — evidence `evidence/wire-boundary.json` `witnesses.invalidJsonControlCharacter`.

> | `E4-TARGET-CE-012` | SEEDED | Escaping quote, backslash, newline, carriage return and tab makes a value cell valid JSON | `Effect4/Target/TypeScript/Trace.lean:24-29` emits U+0001 raw inside the quotes; the resulting cell `""` is rejected by `JSON.parse`, so a golden containing it can never be read back by `effect4-trace` | escape every C0 control (`< 0x20`) as `\uXXXX` in `Trace.escape`, mirror it in `harness/trace/tracer.ts` `wire`, and plant the character as a mutant in `scripts/test-trace-goldens-gate.sh` |

**`E4-TARGET-CE-013`** — evidence `evidence/wire-boundary.json` `witnesses.unsafeNatural`.

> | `E4-TARGET-CE-013` | SEEDED | A `Val.nat` renders as a JSON integer the host reads back unchanged | `Trace.val (.nat 9007199254740993)` renders `9007199254740993`; JavaScript parses it as `9007199254740992`. `harness/trace/tracer.ts:36-39` guards non-integers only, so the host encoder cannot detect the loss either | declare the exact-number domain of the wire (`|n| ≤ 2^53 − 1`) as an admission clause on goldens and a `TracerDefect` in `wire`, or encode naturals as strings; the current Cell/Nat corpus stays inside the domain, which is why no golden has failed |

Two more, weaker but worth seeding:

- **`docs/TRACE-DAG.md`, new separation 9.** "Rendering is compared, not the alphabet. `check-trace-host.sh` compares TSV bytes against `generated/traces/*.tsv`; `E4-TARGET-CE-011` shows `rows l = rows r` does not imply `agree m2 l r`. The comparison is sound only inside a declared answer-type profile."
- **`E4-RUN-CE-022`, RESERVED**, pointing at `evidence/callback-source.json` and `docs/CALLBACK-PROTOCOL-CONTRACT.md:57-71`, so `FRAME-FB-ASYNC-FINALIZER` has a witness before its packet opens. The two facts that bite hardest: a *synchronous* resumption never installs the cancellation frame while a delayed one retains it until the resumed computation exits; and a cleanup defect **replaces** the prior failure, which is not what `Ensuring` does. A registration that throws publishes `die 23` with the signal still `open` and only a `register` event (`evidence/callback-boundaries.json`, first entry).

I would *not* import `evidence/blaze.json`'s "scheduler return leaves the client unfinished" as a register row yet: it is an adapted OCaml example, not an rc.112 observation, and Codex says the upstream Iris proofs were inspected, never replayed (`BOOTSTRAP-RESULTS.md:434-439`).

## 3. Prioritized tasks

### Codex should

1. **Re-pin `lean/` to Effect4 `5173288` / Effects `e86f141`** and rewrite `test/FlowExport.lean:36-52` for Flow v2 (`params`, `Var`, argument lists). Rerun `check-lean-baseline.mjs`; `evidence/lean-baseline.json` currently records a build that failed for a skew we have since fixed.
2. **Regenerate `evidence/lean-flow-export.json` and the simulation corpus.** `single-cycle`, `double-cycle`, `choice` and `swapped-choice` are rejected with `unchosenCycle` at v0.4.0; replace each `jump` cycle with a `choose`-guarded one so the bisimulation cases survive.
3. **Emit the golden header on the rows it already produces.** `evidence/script-lean-observations.json` `observations[*].rows` is our wire form exactly; prefix `format`/`generator`/`input`/`pin` plus `face ocaml` / `program` / `tape` / `rules` and `effect4-trace` can check it with no new format.
4. **Replay our four goldens through the OCaml 5 machine as a third emitter.** This needs the admitted profile extended past `ret/get/put/bind`: an `Except` answer (`recover`) and an aborting operation (`fallible`), i.e. a `failed` arm in `CellExecution.eventLog` (`lean/CellExecution.lean:23-27`).
5. **Freeze the typed wire contract its own probe demands** — exact-number domain and string profile — as a Codex-side document, and hand us the three witnesses as the register rows in §2 rather than as prose in `BOOTSTRAP-RESULTS.md:398-402`.
6. **State the disposition of `CellTarget.Term`.** Once the Script bridge reaches Flow v2 it is a second program carrier for the same fragment; either retire it or say in `CELL-EXECUTION-CONTRACT.md` that it stays a permanent research view.

### Claude should

7. **Finish regenerating the pinned projections.** Commit `5173288` bumped `lake-manifest.json` to `e86f141` without re-running the generators, which read the rev from the manifest (`scripts/generate-trace-goldens.sh:13`), so every file under `generated/` still said `pin effects 9595a88` at HEAD. The four `generated/traces/*.tsv` and `masks.tsv` have since been regenerated in the working tree by the concurrent P-T2 lane; **`generated/lowering-coverage.tsv` has not** and still carries `9595a88`, so `scripts/check-lowering-coverage.sh` remains red. Re-run `scripts/generate-lowering-coverage.sh` and commit both together. Highest-priority item in the list.
8. **Seed `E4-TARGET-CE-011/012/013` and TRACE-DAG separation 9** with the row text in §2, citing `evidence/wire-boundary.json` and `lean/WireBoundaryProbe.lean` as external pinned witnesses.
9. **Fix `Trace.escape`** (`Effect4/Target/TypeScript/Trace.lean:24-29`) to escape all C0 controls, mirror it in `harness/trace/tracer.ts:34-55`, and add the planted control character to `scripts/test-trace-goldens-gate.sh`.
10. **Accept a third `face` in the host gate.** `Trace.golden` already takes `face`; teach `effect4-trace` and `scripts/check-trace-host.sh:18-28` to compare an `ocaml`-face TSV against the same golden under the same `masks.tsv`, so task 3 lands with no format negotiation.
11. **Give the `semantics` edge a shape using Codex's certificate idea.** `Effect4/Semantics/Runs.lean` now has `run_checked_not_stuck` and `run_fuel_mono` but no agreement theorem. State Flow-runner-versus-traced-service agreement as a checked relation over the two logs, in a new `Effect4Test/Semantics/RunsAgreement.lean`, rather than leaving `docs/TRACE-DAG.md:39` open with no proposed statement.
12. **Retire the exporter duplication.** Add a `rows` subcommand to `harness/trace/Generate.lean:129-146` that prints what `ScriptRowsExport.lean:44-46` prints, so Codex consumes one Lean exporter instead of maintaining a byte copy of our harness source.

## 4. Risks and hygiene

**The workspace has no commits.** `git log` reports *"your current branch 'main' does not have any commits yet"*; all ten top-level entries are untracked. Every `.lean`, `.v`, `.ml` and evidence JSON is unversioned. The sha256 fields inside the receipts are the only provenance, and they hash files that can be edited without trace. Nothing in §3 should depend on a Codex file until it has a commit. Codex's own discipline is otherwise good — it hashes inputs before and after each run — but the hashes have no immutable anchor.

**Absolute machine paths everywhere.** `README.md:5,7,44,54-62` and every cross-reference in `docs/` are `/Users/pooks/Dev/…` links; the evidence `commands[*].cwd` fields point at `/Users/pooks/.opam/4.14.2/bin/ocamlrun` and `_build/` temp directories. Mutation evidence names directories under `_build/` (e.g. `callback-mutant-Txecuw`) that `.gitignore` excludes, so the negative controls are not reproducible from the workspace.

**The Effect runtime under test is Foldlab's.** Every packet hashes `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/...`. `AGENTS.md:79` says this repository must not depend on Foldlab. That rule binds Effect4, not Codex, but it means Codex's host receipts and ours are not directly comparable: ours pin `effectUpstreamCommit 2600f62f…` and `effectTreeSha256 aea8ac8a…` (`harness/trace/host-pin.json`), Codex pins per-file `package.json`/`dist/*.js` digests. Before task 4 lands, one of the two receipt shapes has to absorb the other.

**Toolchain.** Lean 4.33.1 matches our `lean-toolchain` exactly. Rocq 9.1.1, OCaml 4.14.2 and 5.1.1, Node 22.23.2 are all pinned in the receipts. The js_of_ocaml 5.7.1 used for the OCaml 5 route was **built from cached sources inside `_build/`** with a version-specific `--enable effects` flag (`BOOTSTRAP-RESULTS.md:110-117`) — that build is gitignored and not reproducible from the repository, which is the single largest reproducibility risk in the workspace.

**Claim hygiene is sound.** Both `README.md:3` and `BOOTSTRAP-RESULTS.md:6-7` say full agreement is the objective, not a result; `MACHINE-PROOF-CONTRACT.md:38-42`, `SCRIPT-BRIDGE-CONTRACT.md:64-68` and `CELL-EXECUTION-CONTRACT.md:9-21` each carry an explicit edit fence and refuse to promote. `README.md:63` states no Lean library source was edited, and the file hashes above confirm it. Nothing here needs a wording repair on our side.
