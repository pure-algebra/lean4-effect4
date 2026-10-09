# Shared TypeScript branch receipt

Integrate the template, helper export and reader changes together.
The new canonical TypeScript image requires the shared `ifCase` helper.
Authors keep ordinary `ifElse` and remove the former branch annotations.

## Commits and ownership

Base: `4a596d5bbcda7d38964735a250471a014484e1a1`.
Implementation and evidence: `e3eda3b2e193b81e17f6f0453c245f46589f1da7`.
Branch: `codex/authoring-branches`.
Worktree: `/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4`.
The primary checkout and Claude's visual work remain unchanged by this slice.
Three GPT-6.1 Sol agents inspect independent concerns; the parent owns every Lake command and commit.
No merge or push runs.

## Result and boundaries

The shared template prints `ifCase(() => condition, () => left, () => right)`.
The helper infers each branch's answer, error and requirement columns independently.
Each resulting column is their union.
Execution evaluates the condition and constructs only its selected branch.
Each later execution reevaluates the condition.
The helper introduces no new cast, machine operation or stored representation.

The reserved-head table prevents helper-name capture.
The canonical readers reject the old conditional image and malformed helper calls.
The foreign readers retain their previously accepted suspended conditional through the new canonical template.
They acquire no new foreign helper spelling.
The generated head and template tables remain projections of Lean.

Channel's producer now needs neither branch annotation.
Its retained earlier failure packet remains byte-identical.
Current Queue and Semaphore printed expectations change only at boolean branches.
The four Queue programs retain their canonical program fingerprints.
The measured current printed fixture comes from its existing Lean producer expression.

Handle declaration headers remain outside the module reader's domain.
The Channel packet therefore retains its expected definition-header refusal.
The eleven new inline authoring examples all read back to their admitted programs.
These statements concern different named fragments.

## Proof placement

The design records placement before implementation in `docs/research/2026-10-09-authoring-branches-plan.md`.
The existing `read_print`, `read_exact`, typed-print and module reconstruction statements retain their premises and proof bodies.
Their concept is `exact-codecs`; they serve R8 and its existing printing and reading path.
The new battery applies `read_print` at a concrete boolean program.
No new semantic claim or planned goal enters the proof graph.
No syntactic reconstruction theorem establishes host simulation.

The scoped compiled audit checks 5204 declarations in fourteen named modules.
Every reached axiom lies within `propext` and `Quot.sound`.
The audit checks forbidden declaration shapes and the new battery's parsed proof style.
The imported core roots exclude the Laws graph.
The exact audit source and output are retained.

## Reproduced checks

Every Lean command uses `LEAN_NUM_THREADS=3` and the pinned Lean `4.33.1`.
The compiler is tsgo `7.0.0-dev.20260629.1`; the runtime is Bun `1.4.2`.
The evidence directory is `docs/research/2026-10-09-authoring-branches-evidence/`.

| Check | Reproduced result |
| --- | --- |
| `lake build Effect4.Codegen.Templates Effect4.Laws.Codegen.ReadPrint Effect4.Laws.Codegen.PrintTyped` | Existing reconstruction and typed-print proofs compile unchanged |
| Focused battery build, exact command below | New authoring controls and touched printer consumers pass |
| `lake env lean -DwarningAsError=true docs/research/2026-10-09-authoring-branches-audit.lean` | Compiled declarations, axioms, import direction and proof style pass |
| `python3 scripts/generate.py --only ts` | Generates the new head and template projections |
| `python3 scripts/generate.py --only ts --output-dir /private/tmp/effect4-authoring-branches-ts-check` | Byte-identical regeneration passes |
| `python3 scripts/generate.py --only readme` | Refreshes the generated ingest document |
| `bun test ts/eff/test/read.test.ts ts/eff/test/payload-classes.test.ts ts/eff/ingest/test/printer.test.ts` | 162 tests and 385 expectations pass |
| `bun test ts/eff/test/term-rows.test.ts` | 16 tests and 64 expectations pass |
| `node node_modules/@typescript/native-preview/bin/tsgo --noEmit -p tsconfig.json`, from `ts/eff` | Passes with the pinned compiler |
| Authoring packet command below | Eleven generated programs pass module reconstruction, target compilation and independent numeric observations on Effect `4.0.1` |
| Helper packet command below | Exact union controls pass; three wrong helpers compile and fail their intended runtime observations |
| Channel packet command below | Eight positive callers and two wrong transformations pass on Effect `4.0.1` |
| Retained `pinned-helper/result.json` | Actual public prelude, exact column checks and four runtime tests pass on Effect `4.0.0-rc.112` |
| `python3 scripts/check-conform.py cases` | 241 case sites pass after four missing existing policy entries are recorded |
| `python3 scripts/check-docs.py` | All references in 84 authority documents resolve |
| Scoped `scripts/check-language.py --strict` | The plan, packet README and inventory pass |
| Retained packet hashes | Current sources, compiled inputs and emitted declarations match all three successful packet receipts |

```sh
LEAN_NUM_THREADS=3 lake build Test.Program.BranchAuthoring Test.Program.Channel   Test.Codegen.PrintContract Test.Codegen.DefinitionsPrint Test.Codegen.PayloadClasses   Test.Codegen.ReadContract Test.Codegen.TemplatesContract Test.Codegen.PrintTyped   Test.Codegen.TermRows Test.Program.QueueFaces Test.Program.SemaphoreFaces
LEAN_NUM_THREADS=3 python3 harness/authoring-branches/run.py --skip-build   --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules   --out docs/research/2026-10-09-authoring-branches-evidence/programs
python3 harness/authoring-branches/check-helper.py   --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules   --out docs/research/2026-10-09-authoring-branches-evidence/helper
LEAN_NUM_THREADS=3 python3 harness/channel-transforms/run.py --skip-build   --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules   --out docs/research/2026-10-09-authoring-branches-evidence/channel
```

Replay packet commands with fresh output paths; occupied evidence directories refuse overwriting.
The packets retain exact compiler inputs, observed values, commands and hashes.
They establish finite observations, not universal target simulation or asynchronous progress.

## Repairs during verification

The initial new battery puts a docstring before a macro that accepts no docstring.
The ordinary comment repairs that parser error.
The first helper setup imports unrelated prelude exports unavailable on latest (Effect 4.0.1).
The focused controls now import the actual shared helper directly.
A separate rc.112 check retains the real public prelude path.
Both initial failures remain recorded.

The first `make check-cases` invokes the Makefile's default build prerequisite.
That attempt stops at the old rendered Queue and Semaphore expectations.
After their measured repair, the case checker runs directly with its named build targets.
This avoids repeating the default build; no successful full sweep is claimed.

The direct checker finds four policy omissions already present at the base.
They name `PartitionedSemaphore.countsFields`, `PubSub.cellFields`, `PubSub.subscriberFields` and `Stream.Source.fromDefinitions`.
Their source, prior policy and tool configuration are byte-identical to the base.
The first three default to empty fields for non-record types.
The source adapter refuses non-list Chunk payloads.
Four exact default covers record these existing behaviors; `unlisted: refuse` remains unchanged.
The before and after census reports are retained.

Eight retained helper inputs contain the original final blank line.
Whitespace checking excludes only that existing EOF condition after checking its exact paths.
No evidence bytes are normalized.

## Remaining authoring work

Rows 218 and 266 can record the shared branch repair through this receipt.
The owner decisions and STATE remain with the coordinator.
The supplied-definition adapter still needs a connection to its actual installed module.
The type reader still needs a separately scoped handle-header reconstruction extension.
The user next requests consolidation of the TypeScript authoring implementation and CK/OXC shared abstractions.
