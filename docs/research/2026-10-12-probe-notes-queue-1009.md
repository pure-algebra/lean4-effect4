# Backlog queue: the notes of 2026-10-09, checked at HEAD (2026-10-12)

Status: research note (history, not authority). A read-only scout at `e9e199c9d` on
`refactor/phase1-phase3`. No `lake` ran, nothing was built, and nothing was committed. One `bun`
probe ran from the session scratchpad and wrote nothing in the tree.

Scope: every note dated 2026-10-09 under `docs/research/`, files and folders: the packet receipts,
the host, coalgebra, view and MCP notes, and the review packets. Each open ask was checked against
HEAD by `grep`, `git log` or a probe.

Out of scope: the items of `2026-10-12-probe-backlog-queue.md` and
`2026-10-12-probe-alignment-plans.md`. Also out: the restore slot, the typed context, the release
merge, the proof-style ratchet, and the `Scope.close` and failure-walk slice.

## Know this first

- **Most asks of 2026-10-09 landed.** The closed list is at the foot of this note. Of what is
  left, most is design-scale work that `docs/STATE.md` already orders.
- **One reader gap changes an outcome.** The CK reader (`ts/eff/ingest/ck.ts`) refuses the
  canonical `optionCase` and `caseTag` heads. OXC and the canonical reader accept both. The probe
  at HEAD reproduces it. The fix is TypeScript only (N1).
- **N1 is already in the working tree, uncommitted.** At this scout's end, the main checkout's
  `ck.ts` adds `optionSelect` and `tagSelect` and their foreign overrides, with tests in
  `printer.test.ts`. Review and land that edit; do not write it again.
- **Two sentences of `docs/STATE.md` claim more than their theorems.** A guarded reactor
  supplies the reply conditions of H9, not its funding, rest and exit premises. The typed layer's
  driver still calls `guardRows`; only its denotation drops the guard (N2).
- **Decisions rows 218 and 266 (3) lag.** They say the TypeScript branch print is not landed. The shared
  `ifCase` landed at `e3eda3b2e` and is in HEAD. `docs/core/decisions.md` is the coordinator's (N3).
- **Three owner questions have no register line.** The host-call note's section 8 asks for one
  form of a host call, the live call view and the slice order. No decisions row records them,
  and slice HC-1 is in no plan (O1).
- **A docstring edit in a low law module cascades.** `src/Effect4/Laws/Program/Address.lean` has
  496 transitive importers. Ride such edits with a slice that touches the module (L2).

## The queue, ranked

Ranked by the owner's two tests (an outcome of a real run, then the proof graph), then by cost.
"Importers" counts transitive importers in `src`, `tools`, `Test` and `harness`, read by the
shared import reader.

| # | Item | Evidence it is open at HEAD | Impact | Cost | Ruling |
| --- | --- | --- | --- | --- | --- |
| N1 | CK refuses `optionCase` and `caseTag` | the probe: CK refuses with `literal`; OXC accepts; `ck.ts` has selectors for `ifCase` and `caseTagR` only | runtime outcome of a reader: two required readers disagree on canonical bytes | `ts/eff/ingest/ck.ts` and one test; no Lean | none |
| N2 | `docs/STATE.md` overclaims the guarded and typed-layer drivers (HCO-09, HCO-11) | "always does" and "needs no guard" stand; `runWith_layer_denotes` still drives `.guardRows` | proof graph: the entry document states a stronger theorem than the tree holds | two sentences; no build | coordinator edits STATE by custom |
| N3 | Rows 218 and 266 (3) say the branch printer is not landed | row 218 reads "not landed"; `git merge-base --is-ancestor e3eda3b2e HEAD` holds | release readiness: the register misstates a landed repair | two cells; no build | coordinator's file |
| N4 | The shared import reader drops a quoted import and reads past a doc comment (HCF-01, HCF-02) | `_tokens` skips `/-!` and `/--`; `header_imports` keeps `«…»` spelling; `build_profile.imports_of` compares it with file names | tooling: the build profile's graph and the generator's imports; latent, no production file triggers it | `scripts/lib/lean_imports.py`, `scripts/lib/build_profile.py`, `scripts/test-lean-imports.py`; no Lean | none |
| N5 | Four tool docstrings name a wrong law or claim too much (D1R-1, D3R-1, D3R-2) | `FlowOrder.lean`: "Above means before"; `AlgGraph.lean` cites `lay_keeps_order`, which does not exist; `place_descends` claims accepted waits; LV-3's heading says linear while `parBottom` adds n² edges | proof graph: tool laws are registry claims (row 345 (2)(a)) | four docstrings in `tools/Tools/View/`; at most 6 importers; no build owed | none |
| L1 | Prove the unguarded driver for a typed layer (HCO-11) | the driver in `runWith_layer_denotes` is `(Reactor.ofHost …).guardRows` | proof graph: claim `rows-denotation-driver`; usability: a typed layer runs with no per-reply check | `src/Effect4/Laws/Api/HostDrive.lean`; 21 importers, 16 of them batteries | none |
| L2 | Correct five law docstrings | see L2 below: handle rows, membership, reply tape, `check_rebase`, a prospective consumer | proof graph wording | text only; `HostDrive` and `RowProtocol` ride L1; `Calls` 66 importers; `Address` 496 | none |
| L3 | Give `hostAnswered_guardRows` its consumer (HCO-08) | no file outside `RowProtocol.lean` uses it; its module doc names no claim | proof graph: a helper with no consumer | one battery reader, reached from `Test/All.lean` | none |
| L4 | The closure audit's population and erasure (CLOSURE-POP, CLOSURE-ERASURE) | `elabClosureAudit` still skips by `isAuxiliary`, which drops private names and `instSizeOf…`; `letsBeforeClosure` records proof `let`s | hygiene of a gate: a private table-per-use passes; an erased proof binding is refused | `tools/ProofGraph/ClosureAudit.lean`; 3 importers; the audit may then name new offenders | none |
| L5 | Place CO-6b's unstated obligations | no registry text names role inertness, the formation decision or service-image exactness | proof graph: declared open work with no open part | `tools/ProofGraph/Registry.lean`, then `make gen-semantics` | coordinator sorts open parts |
| L6 | Split `PrintTyped.lean` by printer phase (cleanup C9) | 8,180 lines; 184 s alone on the critical path of 2026-10-09's profile | build time of every change below it | `src/Effect4/Laws/Codegen/PrintTyped.lean`; 9 importers | none; measure first |
| L7 | Put the guard and lookup behind the public entries (HCO-10) | `Effect4.Run` and `Effect4.Laws.Author` reach no `guardRows`, `answerAdmits`, `rowPosition` or `Reactor.ofHost` | usability of the run interface | core move plus one import; `Effect4.Laws.Author` has 110 importers | coordinator: rows 39 and 332 |
| O1 | Record or retire the host-call note's questions 1, 3, 4 | no decisions row; STATE names only HC-6 and HC-7 | design: HC-1 (the live call view) has no owner | one register line | owner |
| O2 | Accept the `Row.trailing` encoding, and fix the policy's gate name | the policy comment says the owner must accept it; it names `make check-compat`, which no Makefile defines | release readiness of the compatibility record | `Test/fixtures/baseline/66ee4657-supplement-v1.policy.json`, a review event | owner |
| O3 | Freeze the checked module print obligations | `typed-module-erasure` is in no registry; the public packet's strict compile failure stays | release readiness: printed modules with definitions | large Lean work after the freeze | coordinator |
| O4 | Keep or delete the seat PILOT patches | `docs/research/2026-10-09-cleanup/` holds two untracked patches, 824 KB, against a base of 2026-10-06 | hygiene | none | owner |

## Do now, no Lean build

### N1: the CK reader reads `optionCase` and `caseTag`

An uncommitted edit in the main checkout follows the steps below. Check it against them, then
run the verification.

The generated template table (`ts/eff/templates.gen.ts`, constructor `select`) prints:

- `optionCase(s, () => a0, (x) => a1)`, decision `{ _tag: "option" }`; `a0` at depth 0, `a1`
  under one binder;
- `caseTag(s, "t", (x) => a0, (x) => a1)`, decision `{ _tag: "tag", tag: "t" }`; both arms under
  one binder.

Change, in `ts/eff/ingest/ck.ts`:

1. Add `optionSelect` and `tagSelect` to `CompilerReader`, beside `boolSelect` and `recordSelect`.
2. Copy the guards of those two: an identifier callee, no `optional`, no `typeArguments`.
3. Refuse a shadowed head, as `boolSelect` refuses a bound `ifCase`.
4. Check the arity: three arguments for `optionCase`, four for `caseTag`.
5. Read each arm with `this.arrow(arg, env, n)`: `n` is 0 for the `none` arm, else 1.
6. Read the tag as `recordSelect` reads it: a string literal, else `bad(...)`.
7. Chain both into `eff`'s `selected` expression after `recordSelect`.
8. Override both in `ForeignCompilerReader` to return `undefined`, as it does for the other two.

Step 8 keeps the foreign language unchanged. The authoring-branches receipt requires that.

Add controls to `ts/eff/ingest/test/printer.test.ts`, inside its loop over CK and OXC:

- the two sources of `docs/research/2026-10-09-ingest-form-selection-evidence/canonical-gaps.ts`
  (`option`, `tag`) read to the same tree in both readers;
- a shadowed `optionCase` binder refuses;
- a `caseTag` with a non-literal tag refuses;
- `recognizeSource` of CK still refuses both heads.

Verify, from `ts/eff`: `bun test`, then `bun run typecheck`. Then run `make check-ts-reader`
and `make check-corpus`, the gates the change reaches. If either starts a Lean build of the
corpus, stop and leave the gate to the coordinator.

### N2: two sentences of `docs/STATE.md`

In "Where the tree stands", bullet "The host meaning on a run", replace:

> A reactor behind its rows' types (`Reactor.guardRows`) always does.

with:

> A reactor behind its rows' types (`Reactor.guardRows`) always stays inside the envelope.
> Funding, rest and the root's exit stay premises.

In the bullet "The coalgebra layer", replace:

> A typed layer over a host that meets its lower protocol needs no guard (`runWith_layer_denotes`).

with:

> For a typed layer over a host that meets its lower protocol, the meaning needs no host guard
> (`runWith_layer_denotes`). The driver still checks each reply until L1 lands.

Verify: `python3 -I scripts/check-docs.py` passes; `python3 scripts/check-language.py --show
docs/STATE.md` shows no finding on the two edited sentences.

### N3: decisions rows 218 and 266 (coordinator)

- Row 218, status: landed 2026-10-09 at `e3eda3b2e`, with
  `docs/research/2026-10-09-authoring-branches-receipt.md`.
- Row 266, point (3): the branch printer of row 218 landed. Close it only after the routing twin
  type-checks under tsgo 7.0.0-dev.20260629.1. This scout ran no tsgo.

Verify: `python3 -I scripts/check-docs.py`. Run the probe of the routing twin first.

### N4: the shared Lean import reader

In `scripts/lib/lean_imports.py`:

1. **HCF-02.** In `_tokens`, stop the header at a doc comment. When the text at `i` starts with
   `/--` or `/-!`, yield that marker word, not a skip. A plain `/-` comment stays skipped, nested.
   `header_imports` then stops at the marker, as Lean's header parser does.
2. **HCF-01.** Add `canonical(name)`. It splits a name at dots outside `«…»` and strips the
   guillemets of each part. `«Effect4».Program.Ty` becomes `Effect4.Program.Ty`.
3. Keep `header_imports` returning the source spelling: `scripts/lean-imports.py` passes it to
   `lake build`.
4. In `scripts/lib/build_profile.py`, compare `canonical(name)` with the file-derived names in
   `imports_of`.

In `scripts/test-lean-imports.py`, add controls:

- `import A`, then `/-! doc -/`, then `import B`: the reader returns `['A']`;
- the same with `/-- doc -/`;
- `canonical('«Effect4».Program.Ty') == 'Effect4.Program.Ty'`;
- `canonical('«my mod».X') == 'my mod.X'`.

`test_header_ends` sets an option after the doc comment, so it cannot see HCF-02. Keep it.

Verify:

- `python3 scripts/test-lean-imports.py` passes.
- The imports of every tracked `.lean` file are unchanged. Collect `imports_of` per file before
  and after the edit, in a scratchpad script, and diff the two lists.
- `python3 scripts/build-profile.py .lake/gen/build.log` gives the same critical path as before.

### N5: four tool docstrings

- `tools/Tools/View/FlowOrder.lean`, module doc: replace the sentence that calls "Above means
  before" a theorem. Write `Structural precedence implies vertical separation.` Its own scope
  paragraph already says the converse is false.
- `tools/Tools/View/AlgGraph.lean`, module doc: replace `Tools.View.Flow.lay_keeps_order` with
  `Tools.View.Flow.lay_realizes` and `Tools.View.Flow.place_keeps_order`.
- `tools/Tools/View/FlowLaws.lean`, docstring of `place_descends`: drop "the waits accepted as
  edges are met too". Its premise is an edge of `layWith` alone; `acceptWaits` adds waits later.
- `tools/Tools/View/LiveChecks.lean`, the heading "LV-3: the layout in linear time": say linear in
  the layout's edges. `parBottom`'s `aligned` list adds n² edges to a part of n branches.

`generated/semantics.md` quotes none of these texts, so no regeneration follows. No build is
owed for a docstring. The next tools build recompiles at most six modules:
`LEAN_NUM_THREADS=3 lake build Tools.View.LiveChecks`.

## Lean items

### L1: the unguarded driver for a typed layer (HCO-11)

Placement, before work:

1. Concept `translation-simulation`; the driver's simulation.
2. Question: claim `rows-denotation-driver` (pointer `Effect4.Run.runWith_denotes`). Consumer: an
   unguarded form of `runWith_layer_denotes`.
3. Reach: actual external rows, distinct row keys, typed handlers, the lower host's protocol.
4. Not established: funding, rest and the root's exit stay premises; checked call instances and
   allocation stay outside.
5. Serves R6.

Steps, from `docs/research/2026-10-09-host-typed-indexed-review/README.md`:

1. `Reactor.ofHost` returns only exits.
2. It meets the envelope on actual external rows (`rowPosition_external`, `admit_of_answerAdmits`).
3. The unguarded adapter's round trip holds under those premises.
4. Apply `runWith_denotes` to it.

Do not state global equality of the two reactors: the review's control refutes it. Build
`Effect4.Laws.Api.HostDrive`, then `#axiom_audit` it. The gates reached: `check-host-protocol`.

### L2: five law docstrings

| Module | Text at HEAD | Correction | Source |
| --- | --- | --- | --- |
| `src/Effect4/Laws/Api/HostDrive.lean`, `runWith_guarded_denotes` | a handle row "answers nothing through the guard" | it answers no success: `answerAdmits` admits a failure at any row | HCO-09 |
| `src/Effect4/Laws/Program/RowProtocol.lean`, module doc | "a success value is a member of the answer type" | template admission at the empty allocation table; membership holds for data replies | HCO-07 |
| the same module doc | "claim: none of its own yet" | a step of `rows-denotation-host`, once L3 gives it a reader | HCO-08 |
| `src/Effect4/Laws/Program/Agreement/Calls.lean` and `localRunC_compile` in `Agreement/LoopCalls.lean` | "run under a reply tape", "every reply tape" | the statements quantify over a host (`Effects.Comodel`) and its state | the host generalization review |
| `src/Effect4/Laws/Program/Address.lean`, module doc and `at_replaceAt_below` | `check_rebase` "not stated"; a pasted subtree as its consumer | `Checker.check_rebase` is proved in `Typing/Rebase.lean`; mark the consumer prospective | org cleanup; address overwatch |

`HostDrive` and `RowProtocol` ride L1. `Address` waits for a slice that edits it.

### L3: a reader of `hostAnswered_guardRows` (HCO-08)

Port the two-call control of `docs/research/2026-10-09-row-protocol-review/` to a battery. The
host's state must change its second reply. Reach the file from `Test/All.lean` at the anchor the
brief names. Then name `rows-denotation-host` in `RowProtocol`'s placement (L2).

### L4: the closure audit's population (CLOSURE-POP, CLOSURE-ERASURE)

In `tools/ProofGraph/ClosureAudit.lean`:

- Read every computational definition, private ones included.
- Skip a generated companion by its declaration metadata, not by the name prefix `instSizeOf`.
- In `letsBeforeClosure`, drop a `let` whose type is a proposition or a type former, as LCNF does.

Controls: `docs/research/2026-10-09-report-overwatch/ClosureControls.lean`. It holds the private
and renamed red cases and the accepted proof binding. Then `lake env lean
Test/Audit/ClosureAudit.lean`. The audit may name new private offenders: list them and fix
them by passing the table as data.

### L5: CO-6b's open parts (coordinator)

Add three `.proposed` open parts to the requirement rows of `tools/ProofGraph/Registry.lean`,
from `docs/research/2026-10-09-co6b-service-plan.md` section 5:

- roles are inert: program admission, the denotation and the machine read no role (R2);
- `serviceFault` decides a service's formation, as a located refusal (R5);
- an accepted service image is its canonical image under a stated normalization (R8).

Then `make gen-semantics`.

### L6: split `PrintTyped` (C9)

Run `make build-profile` after the next full build first: the measured profile is from
2026-10-09. Split by printer phase, so that the parts build in parallel. Nine modules import it.
Read its slowest proofs with `make profile-module FILE=src/Effect4/Laws/Codegen/PrintTyped.lean`.

### L7: the guard behind the public entries (HCO-10)

Move `answerAdmits`, `rowPosition` and the plain guard into the core, behind `Effect4.Run`, with
their names. Keep the proofs and the generic adapters in Laws. Expose `Reactor.ofHost` through
`Effect4.Laws.Author`. `#exposure_gate` decides what an application may import.

## Low, latent, or ordered elsewhere

- **C3b** (HCF-03): `localRun` beside `localRunC`. Restrict a projection to the empty reply tape,
  and port the loop case. No plan names it now.
- **GT-01**: `Graph.pointKey` (`tools/Tools/View/Graph.lean`) spells a routing point `k@r`. A node
  key of that spelling collides with it. No program's naming triggers it.
- **TB-01**: `Effect4Gen.Fold.emitBlock` always writes structural termination. A family with no
  recursive child fails strict compilation. No registered family lacks one.
- **C6**: the fragment table (`tools/Effect4Gen/Fragments.lean`) carries no reason per constructor.
- **The binary64 retraction**: `src/Effect4/Data/JsonNumber.lean` calls it owed. No goal or
  consumer places it. It has 894 importers, so ride a slice that edits it.
- **`view-forest-components`** (row 345 (1)): a claim with no Lean statement.
- **Ordered in `docs/STATE.md`**: CO-7's handle rows and call sites; HC-6 and HC-7; HO-4 and
  HO-5; CX3 and CX4. Also the view slices B to G, J1 to J9, and MCP's M0 to M12 after six rulings.
  Also the stream and module breadth: Channel, SynchronizedRef, PartitionedSemaphore, PubSub.
- **Placed in the registry**: `waiting-request-obligation-preserved`, `semaphore-protected-permit`,
  `pool-lease-return`, as proposed open parts.

## Closed since 2026-10-09 (verified at HEAD)

| Ask | Evidence |
| --- | --- |
| H8 and H9, and both on loops | `denoteRows_eq_session`, `denoteRows_eq_session_host`, `h8_loopedRows`; `git log` from `37d566d80` to `a6f4e8bba` |
| H8R-01, H8R-02 | `ReachesC`'s docstring names L4's closure; H8 has no depth premise |
| HC-2: preloaded answers deleted | row 343, merge `45873fc76` |
| HC-R8, an axiom's type | `df9d1c408` |
| The shared `ifCase` branch printer | `e3eda3b2e` in HEAD |
| CP-01, CP-02, CP-03 | `Readonly` and `Record` in `SourceBindings.builtins`; `Tools.Code.Module` checks equality; `Doc.lean` scopes the whitespace claim |
| PGS-2, PGS-3, PGS-6 | `d8ca89980` |
| JSON-01, EDIT-OW-01, EDIT-OW-02, the S1 findings | the overwatch resolutions receipt; `8811a61b`, `90940a54`, `205f4fea` |
| CO6B-NAMES, CO6B-KEYS, CO6B-READ | the CO-6b plan's review section; `Test/Codegen/ServicesPrint.lean` |
| TB-02: text mode without the graphical build | `tools/view/v` builds `draw` or `play` only in its own branches |
| The packet's `control.ts` dependency | `TRUTH_SOURCES` in the `Makefile` |
| PubSub's root integration | `src/Effect4/Laws.lean` imports `Effect4.Laws.Library.PubSub.Steps` |
| `TyView`'s hand edit | `sizeOf_field_lt_record` stands in the generated file again |

## How this was measured

| Command | Result |
| --- | --- |
| `ls docs/research \| grep 2026-10-09` and `git ls-files` | 105 entries; every file entry tracked; the folder `2026-10-09-cleanup` is ignored |
| `bun` (1.4.2) on a scratchpad copy of `canonical-gaps.ts`'s sources, from `ts/eff` | CK: `option` and `tag` refused (`literal`); OXC: both accepted; `ifCase`: both accept |
| `git merge-base --is-ancestor` on `e3eda3b2e`, `d8ca89980`, `171399304` | all three in HEAD |
| `grep` for `guardRows`, `answerAdmits`, `rowPosition`, `Reactor.ofHost` in `Effect4.Run` and `Effect4.Laws.Author` | none |
| `grep -rln hostAnswered_guardRows src Test` | `RowProtocol.lean` only |
| a scratchpad reverse-import walk over the shared reader | the importer counts of the table |
| `wc -l src/Effect4/Laws/Codegen/PrintTyped.lean` | 8,180 |
| `.lake/gen/build-profile.md`, dated 2026-10-09 | `PrintTyped` 184 s on a 269 s critical path |
| `grep -rn check-compat Makefile scripts AGENTS.md docs` | no target |

No item here is evidence of a theorem. The CK probe is a finite reading of three closed sources
with an empty row table. The importer counts are a reverse walk of import headers, not a
measured rebuild.
