# Probe: the open items of the 2026-10-11 notes (2026-10-12)

Status: research note (history, not authority). A read-only scout at `7d1e9c2f7` on
`refactor/phase1-phase3` (`e9e199c9d` and one research commit). No `lake` ran, nothing was built,
and nothing was committed. Every fact below comes from a command in the last section.

Scope: `docs/research/2026-10-11-machine-models/` (`README.md`, `AUDIT.md`, `CODEX-PROMPT.md`,
`codex/`), and the other design notes of 2026-10-11: `type-interface`, `handles`, `view-model`,
`docs-design-language`, `docgen`, `machine-from-the-base`, `tokens-in-places`, `topology-graphs`,
`first-exit-plan.md` and the two Codex plans. Out of scope: the top-level Codex and timeout
receipts of 2026-10-11, the restore slot, the typed context, the release merge, the proof-style
ratchet and the `Scope.close` and failure-walk slices. Items in
`2026-10-12-probe-backlog-queue.md` and `2026-10-12-probe-alignment-plans.md` are not repeated,
except to correct them. `E4-PRINT-CE-003` and `E4-OCAML-CE-001` are the coordinator's.

## Know this first

- **The generated semantics page breaks two owner rulings.** Row 354 (2) rules status by shape
  with no hue, and (3) rules the dark look as the base. `Tools.Document.Html.style` colours
  `proved` green, `modulo`/`wanted` amber and `open`/`refuted` red. Its base is light, with dark
  only under `prefers-color-scheme: dark`. The fix is one tools module (item 1).
- **Two rows of the backlog queue are stale.**
  - B5 is done: `Test/Dogfood/Proofs/HostTimeoutLocalSteps.lean` has no
    `simp only [evaluatePrim` arm. `AUDIT.md` (18:30) records the repair at `1591530e9`.
  - B6 is partly done: `256b60ac5` cut the Boolean `Dispatcher.armed` (the machine now keeps an
    `armed : List FiberId` queue) and `Pending.waitingOn`.
  - B6's list also holds `Race.settled`, which is not dead data. The race exit path in
    `Machine/Fibers.lean` matches on it to settle once.
  - Re-census B6's list before a slice: `Resume.continueWith`, the `RaceAllState` fields, the
    `finalizing` exit, the budget copy and `WakeMode.scheduled`.
- **The register contradicts the tree on `mul`.** Row 309 (1) still says "No multiplication …
  enters". The atom `mul` stays, marked by `Profile.scale` (`src/Effect4/Machine/Term.lean`,
  `src/Effect4/Machine/Integers.lean`). `E4-RUN-CE-047` is REPAIRED. Codex's receipts propose a
  register amendment, and no row records it (item 3).
- **One runtime question has no probe.** At budget 2, the cut run of
  `Test/Program/MaskContract.lean` spends its command fuel inside the provider's masked entry.
  Before row 349 it was interrupted before the form. The battery pins the frontier as "Open".
  `CODEX-PROMPT.md` asks whether a masked entry can spin under a pending interrupt. No note
  answers (item 2).
- **`CODEX-PROMPT.md` is the live brief of the goals lane** (`docs/STATE.md`, next item 00), but
  its newest section is 2026-10-12 00:45. Items 5, 10 and 12 have landed, and item 1 has partly
  landed. A status header saves the next agent a census (item 8).
- **Three more Codex worktrees hold 4.6 GB** beyond the four in backlog A5. Their branches'
  commits are in HEAD. Each holds uncommitted tracked edits, about half of which differ from HEAD,
  so none can go blind (item 9).

## Ranked

Ranked by the owner's two tests (an outcome of a real run; the proof graph), then by the current
focus (the core language and the docgen release), then by cost. "No build" means no Lean build of
any library. "Tools" means only `tools/` modules rebuild, never `Effect4` or `Effect4.Laws`.

| # | Item: the ask (path) | Open at HEAD: evidence | Impact | Cost | Ruling |
| --- | --- | --- | --- | --- | --- |
| 1 | D2, statuses by shape on the page: "A status prints its shape mark beside its word, in the text" (`2026-10-11-docs-design-language/README.md` §7) | `Tools.Document.Html.style` sets `--proved`, `--modulo`, `--open` hues and `.status[data-status=…]` colours; light base; `Tools.View.Look`'s `Organic.noise` defaults to 350, against row 354 (9) | release readiness: the docgen page | 2a: `tools/Tools/Document/Html.lean` only. 2b: tokens from `Tools.View.Tokens` (`--e4-*`), a new import of the view. Tools build; `make check-semantics` | none for the five ruled marks; the owner names marks for `absent` and `assumed` |
| 2 | Probe the masked provider entry: "Check whether a masked entry can spin under a pending interrupt" (`CODEX-PROMPT.md`, newest section) | `Test/Program/MaskContract.lean`: `#guard … (cut false 2) … = some .frontier`, comment "Open (row 349)"; no 10-12 note probes it | runtime outcome: a live frontier where the earlier machine interrupted; raw runs only, since the checker refuses the budget's provision | probe: a scratch file, `lake env lean`, no library rebuild. A fix in `Machine/Fibers.lean` rebuilds the whole tree | none for the probe |
| 3 | Record `mul`: "Propose the R-T8 boundary repair and R-T2 retained-atom choice in the coordinator's register" (`codex/type-profile/IngressReceipt.md`) | row 309 (1) unchanged; no decisions row names `Profile.scale`; `codex/type-profile/MachineCoreReceipt.md` "Proposed register amendment" | core language: the authority states the opposite of the tree | `docs/core/decisions.md` (the coordinator's); no build | owner: row 309 is the owner's ratification. Keep `mul` marked, or remove it with `Test/Dogfood/P1HttpCache.lean`'s one use |
| 4 | D1, the authority: "Write the design language for documents into `docs/core/`, in controlled English" (docs design language §7) | `docs/core/` has no such file; `AGENTS.md`'s map has no row; `docs/design/design-language.md` is in place | release readiness: D2 to D6 cite it | a new `docs/core/` file, one `AGENTS.md` row, a move to `docs/research/history/`; no build | none (row 354 (1)) |
| 5 | Gate the OCaml run against Lean's: "Gate the Lean-to-OCaml run comparison on the corpus." (`2026-10-11-type-interface/README.md` R-T8) | `ocaml/engine/test/test_diff.ml` prints "reported, not gated"; no current count on disk (the last one found is from 2026-09-11) | runtime outcome: the OCaml route's agreement with the model is unchecked | `test_diff.ml` and a signed exception list; dune only, no Lean build; measure first with `make check-ocaml` | coordinator: an existing gate grows stricter |
| 6 | The release text: "The emitted module needs `exactOptionalPropertyTypes`." (type interface §3.3, item 15) | `README.md` names no compiler flag; only the lane tsconfigs set it (`ts/eff/tsconfig.json`, `harness/truth/tsconfig.json`, two more). "Building" names `effects`, `typescript` and `hash`; `lakefile.toml` also requires `whatwg` and `aesop` | release readiness, usability | `README.md`; no build | `README.md` is the product's face: the owner or coordinator confirms the words |
| 7 | Trace the assignability table: "The battery reads the TSV at build time, and Lake does not trace that file." (type interface R-T3) | `Test/Codegen/TargetOrder.lean` reads `generated/assignability.tsv` in a `run_cmd`; `make gen-assignability` promotes it and runs no Lean | evidence: a promoted table can leave a stale passing battery | `Makefile`, two recipe lines; no library rebuild when the import is built | none |
| 8 | A status header on the lane's brief, and the backlog corrections above | `CODEX-PROMPT.md` newest section is 2026-10-12 00:45; item states below | usability: the agent who carries the lane | `CODEX-PROMPT.md`; no build | none |
| 9 | Worktrees beyond backlog A5 | `codex/timeout-answerflow-consolidation` (2.0 GB): its tree equals `f821dd533`, in HEAD; `codex/machine-structure` (1.2 GB): its two unique commits are in HEAD in equivalent form (the research files and `NativeStacks.lean` identical; `Interference.lean` changed since); `codex/symbolic-native-fold` (1.4 GB): merged. Uncommitted tracked edits: 91, 31 and 15 files; of them 44, 15 and 11 differ from HEAD | disk at 97% stops a landing | none tracked | owner or coordinator: Codex's worktrees |
| 10 | F9, split `Effect4.Api`, and drop `Means`' import: "split `Effect4.Api` (F9) and drop `Means`' import" (`2026-10-11-topology-graphs/README.md` §11) | `src/Effect4/Laws/Program/Means.lean` imports `Effect4.Api`; `Api.lean` imports the printer, reader and codecs; no row records F9 | rebuild cost: a printer edit rebuilds 283 modules, 146 after the split (the note's simulation) | the import drop: `Means` and its three importers. The split: `Api.lean`, 14 law importers, core rebuild | coordinator: no meaning changes |
| 11 | Register the base laws' structure claims (AGENTS.md, Trust 2) | `tools/ProofGraph/Registry.lean` has no `evaluation-moves`, `command-moves`, `ledger-run`, `place-ledger`, `names-parametric`, `names-equivariant`, `stack-local`, `stack-ancestor-chain`, `ctx-chain`. Their laws landed: `iteration_moves`, `iteration_interferes`, `driveStep_framesFollow`, `iteration_under`, `LedgerRun.funded_reachable`, `PlaceLedger`, `validIn_iff_diag` | proof graph: landed structure the plan does not show | `Registry.lean`, `docs/core/semantics.md`; ProofGraph build and `make gen-semantics` | coordinator; the owner rules orphans fine for planning, so low |
| 12 | R-T9's remainder: "the stale text of §3.4" (type interface) | DB-11 lists certificate fields "no `int` in the table, the program or its type"; `AdmittedProgram` (`src/Effect4/Program/Admission.lean`) has `signature`, `formed`, `columnsType` over `TypedProgram`. `ocaml/eff/README.md` says "the 48 goldens"; its own table says 89, and 89 `.bin` files exist. Rows 3 and 6, DB-15 and `semantics.md` §2.5 are already amended | hygiene | `docs/DESIGN-BASIS.md`, `ocaml/eff/README.md`; no build | none |
| 13 | Row 355's last clause: "The reached behaviour gates are owed at the sweep" | the release merge receipt ran `check-compiler`, `check-native`, `check-ocaml`, `check-truth` and `check-host-protocol`: pass | hygiene: the register lags | `docs/core/decisions.md` (the coordinator's) | none |
| 14 | R4 to R6: one `Life` sum, the interrupt state as a sum, dense arenas. They "wait until L1 to L3 have moved the invariants" (machine models §4) | L1 (`Ledger`), L2 (`Moves.balance`, `getCont_spec`) and L3 (`Machine/Fold.lean`) landed; row 355 rules R1, R2, R3 and R7 only | proof graph: about nine of `GuardState`'s fifteen fields exist to forbid states | `Machine/Fibers.lean` and every law over it; whole tree; OCaml route | owner: representation |
| 15 | Item 1's two consolidations: `HostTimeoutFlow` and most of `HostTimeoutFrames` onto `AnswerFlow`; `HostTimeoutRaceSteps.after_exit_*` citing the `RaceFirst` laws | `HostTimeoutFlow.lean` (226 lines) and `HostTimeoutFrames.lean` (608) name no `AnswerFlow`; `HostTimeoutRaceSteps.lean` names no `RaceFirst`. The chain is 37 files, 10,057 lines | proof graph: the base of the two open Timeout goals | `Test/Dogfood/Proofs/HostTimeout*.lean`; Test build of the chain only | none |
| 16 | The ledgers left on their own command passes: "release custody, finalizer credits and Atomic `WriterPhase` still carry their own command passes" (`AUDIT.md`, 07:45) | `ReleaseCustody/` keeps `CommandDebit`, `CommandRaceDebit`, `NativeActionDebit` and more; only `LedgerRun`, `LedgerFinalizer`, `FinalizerCommands` and `SourceOpportunityCommands` call `PlaceFunding.command_funded` | proof graph: the shape of the four application log goals | `src/Effect4/Laws/Program/ReleaseCustody/`; Laws rebuild above it | none |
| 17 | The base laws not yet stated: B3's run half, B4, B5, B6 (`2026-10-11-machine-from-the-base/README.md` §6) | `compiled_region_bracket` keeps its shape premise (`MaskBracket.lean`); R11's open part "the carrying fact of a region" stands in `generated/semantics.md`; no `CtxChain` | proof graph: the bracket without its premise; B6 is unblocked by row 349 | `src/Effect4/Laws/Machine/`, `Laws/Program/`; Laws rebuild | none |
| 18 | Handles, steps 3 to 9 (`2026-10-11-handles/README.md` §7) | steps 1 and 2 landed, and `StoresLaws` reads `validIn_iff_diag`; `tools/Effect4Gen/Fold.lean` emits no support fold or `Rel`; no `names-equivariant` | proof graph: DET-3, one world, the 48 hand support functions | generator, regeneration, Laws | none |
| 19 | D3 to D6 (docs design language §7): the figure, the motion value, automata, Mermaid, the architecture map | the semantics page prints Mermaid as code (docgen note, "Open"); `Tools/Architecture.lean` loads IBM Plex from Google Fonts; the proof-graph view loads d3 from a CDN and gives each concept a hue | release readiness; L | tools | none (ruled) |
| 20 | The view model R-V1 to R-V5 (`2026-10-11-view-model/README.md` §3) | two `abbrev Key := String` (`Tools/View/Picture.lean`, `Tools/View/Place.lean`); two `structure Frame` (`Tools/View/Build.lean`, `Tools/View/Flow.lean`); no shared scene `Delta` or session structure | hygiene, tools | tools; R-V4 touches `src/Effect4/Api/` | none |
| 21 | Later: L4 to L6 (`AppendOnly`, `FreshSupply`, `Census`, `Linear`); tokens' F2 (edit commutation); P4 and P5 | none of these names exists in `src/` | proof graph, later | Laws | none |

Seen, out of scope:
- `E4-CTX-CE-001` reads SEEDED, while row 349 says the typed context repairs it. The typed context
  is excluded.
- `lean4-whatwg`'s `origin/html-h7` is still not in `origin/main` (37 commits behind). Backlog
  names it as the owner's push.
- The PC seat's SVG rulings (`svg-owner-rulings.md`) live in another repository.

## Do now, no Lean build

Each item gives the files, the change and the check. None edits `docs/core/decisions.md` or
`lakefile.toml`.

### N1. D2a: statuses by shape on the semantics page (tools build only)

This item rebuilds tools modules. It is here because no `Effect4` or `Effect4.Laws` module
rebuilds.

- File: `tools/Tools/Document/Html.lean`.
- In `Tools.Document.Html.style`:
  - make the dark values the `:root` base;
  - move the light values under `@media (prefers-color-scheme: light)` and `@media print`;
  - delete `--proved`, `--modulo` and `--open`, and the three `.status[data-status=…]` colour
    rules. A status keeps the ink colour.
- In the `.status` arm of `Tools.Document.Html.inline`, put the shape mark before the word, as
  text:
  - `proved` ● (U+25CF);
  - `modulo` ◐ (U+25D0);
  - `wanted` and `goal` ○ (U+25CB);
  - `open` ◌ (U+25CC, the dotted circle; row 354's dashed outline);
  - `refuted` ✕ (U+2715).
- `absent` and `assumed` have no ruled mark: print the word alone and ask the owner.
- Leave the Markdown fold (`Tools/Document.lean`) unchanged. `scripts/status.py` parses
  `generated/semantics.md` (backlog A1), so a Markdown mark lands with that parser's repair.
- Check: `make check-semantics`; open `.lake/gen/semantics-report/semantics.html` at 375 px in both
  schemes; `git diff --stat generated/` is empty.
- D2b, later: read the colours from `Tools.View.Tokens`' `--e4-*` properties, and set
  `Organic.noise`'s default to 0 (row 354 (9)). Both import or edit the view: run
  `make gen-architecture` for the new edge, and the view's scene test.

### N2. The masked provider entry at budget 2 (a probe, no library rebuild)

- Write a scratch file in the session scratchpad, never in the tree. Copy `mk`, `fuel`, `rawOf`,
  `budgeted`, `formAfterMark` and `cut` with the five imports of
  `Test/Program/MaskContract.lean`.
- `#eval`, for `k` from 1 to 8 and both callers:
  `(rawOf (cut c k)).map fun p => (Api.run p fuel).outcome`.
- At `k = 2`, print the last thirty trace events of `Api.run p 300`. Look for a repeated cycle:
  yield, park and resume with no new operation.
- Run with `lake env lean <file>`. It needs current `Effect4` oleans and rebuilds nothing.
- Report three things:
  - whether the frontier holds only for `k` below the entry's five operations;
  - whether a masked caller (`cut true k`) spins too;
  - the cycle's events.
- A spin at any `k` is a counterexample candidate for the register. A frontier only at `k < 5`
  is still an outcome to compare with the census row `rule.budget-per-runloop-entry`.

### N3. The release text of `README.md`

- In "Building", name the five pinned dependencies: `effects`, `typescript`, `hash`, `whatwg`
  (the `Tools` library only) and `aesop` (the law graph only).
- In "The application face", add one sentence: an emitted module type-checks only under
  `exactOptionalPropertyTypes`, because a field's `?` means rc.112's `optionalKey`. Cite
  `ts/eff/tsconfig.json` as the reference configuration.
- Check: `python3 -I scripts/check-docs.py`.

### N4. Re-read the assignability table at promotion

- File: `Makefile`, target `gen-assignability`. After the `--promote` line, add:
  - `$(call build_imports,Test/Codegen/TargetOrder.lean)`;
  - `$(LAKE) env lean Test/Codegen/TargetOrder.lean`.
- The battery's `run_cmd` then reads the promoted table against the model at once.
- Check: `make -n gen-assignability` prints both lines. The run happens where Lean builds run.

### N5. A status header for `CODEX-PROMPT.md`

Add a dated section above "The one thing to know first", "Status at `7d1e9c2f7`". One line per
item, each with its evidence:

| Item | State at HEAD |
| --- | --- |
| 1, Timeout over the shared laws | `NativeStacks` landed on `StackRegion.other_edits_stack`. `HostTimeoutFlow`/`Frames` are not on `AnswerFlow`, and `after_exit_*` cites no `RaceFirst` law. `retries_declared` and `cleanup_keeps` stay planned goals |
| 2, labelled moves | `Moves.balance` (`TracedMoves.lean`) and `getCont_spec` (`PopTrace.lean`) landed |
| 3, ledgers as instances | `FiberSum` landed; `SourceOpportunities.command_debit` is a `PlaceFunding` instance; release custody, finalizer credits and `WriterPhase` keep their passes |
| 4, code weights | `Machine/Fold.lean` (generated) and `PrimWeights` landed |
| 5, R2 | landed at `6c4bb709d`; `E4-RUN-CE-046` REPAIRED; join, countdown, link and interrupt cuts are guards in `Test/Machine/EditMessages.lean`; the gates ran at the release merge |
| 6, R1, R3, R7 | `Dispatcher.armed` and `Pending.waitingOn` cut (`256b60ac5`); `Race.settled` is read; the rest open |
| 7, the context region | row 349 landed; excluded here |
| 8, worktrees | the named worktrees are gone; three Codex worktrees remain (item 9 above) |
| 9, L4 to L6 | not started |
| 10, machine edits | landed (`AUDIT.md`, 18:30) |
| 11, handles | steps 1 and 2 landed; `validIn_iff_diag` in use; steps 3 to 9 open |
| 12, `mul` and the ingress | landed; warning 8 restored; `Sys.int_size` asserted; the register row is missing (item 3 above) |

- Also strike "Codex" as the lane's owner where `docs/STATE.md` already says Claude carries it.
- Check: none; `docs/research` is not checked.

### N6. R-T9's remainder

- `docs/DESIGN-BASIS.md`, DB-11, after "Admission exists": add a "Superseded in part" line.
  - Name the fields of `AdmittedProgram` (`src/Effect4/Program/Admission.lean`): `TypedProgram`,
    `signature`, `formed`, `columnsType`.
  - Say that row 309's integers inhabit `int`, so the `int` scan is gone.
  - Before writing where the host-row handle rule lives now, read `admitSig`.
- `ocaml/eff/README.md`: replace "the 48 goldens" with the count that
  `ls ocaml/eff/goldens/*.bin | wc -l` gives (89 today).
  - The same sentence also counts the printed corpus (408) and the random values (1 250).
  - Re-measure each count, or drop it (`ocaml/STANDARDS.md`: every number behind a command).
- Check: `python3 -I scripts/check-docs.py`; `python3 scripts/check-language.py` shows no new
  finding in `docs/DESIGN-BASIS.md`.

### N7. For the coordinator's register (text only)

Propose these in the next receipt. Each needs no build.

- Row 309 (1) against `mul`: the owner's choice (item 3). Row 321 is the pattern of a marked atom.
- Row 355's clause "behaviour gates owed at the sweep": met by the release merge receipt.
- F9: a row for the `Effect4.Api` split, or a ruling not to split (item 10).
- R4 to R6: a ruling question for the owner (item 14).

### N8. D1, the authority (no build, larger)

- Write `docs/core/design-language.md` in controlled English from:
  - row 354 (1) to (10);
  - the docs design language note §§3 to 5;
  - the standing parts of `docs/design/design-language.md` (that note §2, F3);
  - rows 308, 336 and 337 as amended.
- Add its row to `AGENTS.md`'s authority map.
- `git mv docs/design/design-language.md docs/research/history/2026-09-08-design-language.md`, then
  fix `docs/design/README.md` and the two other references (`grep -rn design-language.md docs`).
- Moving the file also removes its 26 line-cite findings from the language report (backlog A4).
- Check: `python3 -I scripts/check-docs.py`, and
  `python3 scripts/check-language.py --strict docs/core/design-language.md AGENTS.md`.

## How this was measured

Every command ran read-only at `7d1e9c2f7`.

| Command | Result |
| --- | --- |
| `grep -n "E4-…" Test/Counterexamples/REGISTER.md` | CE-046, CE-047, PRINT-CE-002 REPAIRED; PRINT-CE-001, CTX-CE-001 SEEDED |
| `grep -n "^| 3\|6\|309\|321\|346\|353–357" docs/core/decisions.md` | rows as quoted above |
| `grep` of `--proved`, `data-status`, `prefers-color-scheme` in `tools/Tools/Document/Html.lean`; `noise` in `tools/Tools/View/Look.lean` | hues by status; light base; noise 350 |
| `grep -c "simp only \[evaluatePrim" Test/Dogfood/Proofs/HostTimeoutLocalSteps.lean` | 0 |
| `git show 256b60ac5 -- src/Effect4/Machine/`; `grep` of `armed`, `waitingOn`, `continueWith`, `settled` in `Machine/Fibers.lean` | `armed` Bool and `waitingOn` removed; `continueWith` 2 uses; `settled` read on the race exit path |
| `grep -n "Profile.scale\|\.mul" src/Effect4/Machine/Term.lean` | `.mul` evaluates through `Profile.scale` |
| `grep -n "reported, not gated" ocaml/engine/test/test_diff.ml` | present |
| `grep -n "warning" src/OCaml5/Tools/LcnfGen.lean`; `grep Sys.int_size ocaml/engine/e4_engine.ml` | 8 not disabled; 63-bit asserted |
| `grep -rn readNamed src/Effect4/Codegen/Classes.lean` | `["number"] => some .nat`; no `Int` or `Num` (owner's, in `docs/STATE.md`) |
| `grep IO.FS.readFile Test/Codegen/TargetOrder.lean`; `sed` of `gen-assignability` in `Makefile` | the table is read in a `run_cmd`; promotion runs no Lean |
| `grep -c` of nine claim ids in `tools/ProofGraph/Registry.lean` | 0 each; `profile-mul-exact` 1 |
| `git worktree list`; `git merge-base --is-ancestor`; `git cherry`; `git diff --stat f821dd533 125865d20` | three Codex branches unmerged; the timeout branch's tree adds nothing to `f821dd533` |
| `git -C <worktree> status --short`, then `cmp` of each changed file against `HEAD` | 91/31/15 changed; 44/15/11 differ |
| `du -sh ~/.codex/worktrees/*/lean4-effect4` | 2.0, 2.3, 1.9, 1.2, 1.4, 1.0 GB |
| `git -C ~/Dev/lean4-whatwg merge-base --is-ancestor origin/html-h7 origin/main` | not merged; 37 commits on `main` |
| `wc -l Test/Dogfood/Proofs/HostTimeout*.lean`; `grep -c AnswerFlow`, `RaceFirst` | 37 files, 10,057 lines; 0 and 0 in the three files named |
| `grep -n import src/Effect4/Laws/Program/Means.lean` | imports `Effect4.Api` |

What this note does not establish: no item was built or run. The spin in N2 is unexplained, not
confirmed. Item 9's file comparisons show only that the edits differ from HEAD, not whether they
matter. Every count is from `grep`, `wc`, `du` or `git`, at the commit above.
