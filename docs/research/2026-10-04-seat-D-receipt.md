# 2026-10-04 seat D receipt: the probe programs as tracked acceptance tests (row 206)

**The one thing to know before merging:** the batteries pin today's refusals on purpose. A slice
of row 204 that lifts one fails `Test/All.lean` until it updates the program's battery and README
row. Generic cells, error payloads and form rows each lift one. Measured today, p2's bounded
handler and p4 reach rc.112's answers and read back. That is the Lean half of the data wave's v0
acceptance (seat W10, never landed). Programs p1 and p3 run to other answers, and p5 has no
admitted program.

## Base and head

| Tree | Branch | Base | Head | State |
| --- | --- | --- | --- | --- |
| `/Users/pooks/Dev/lean4-effect4-dogfood` | `seat/dogfood` | `37289464` (`refactor/phase1-phase3`) | `077ab876` | four commits, never pushed; the worktree is clean |
| the main checkout | `refactor/phase1-phase3` | — | — | only this receipt written, not committed |

The commits, in order:

1. `5d5e332b`: the reference texts, `Test/Dogfood/rc112/`.
2. `7ce0c680`: the shared module, the five batteries and the five imports of `Test/All.lean`.
3. `b74633a7`: the plan rows, `Test/Dogfood/README.md`.
4. `077ab876`: wording only. Program p4's docstrings keep "admit" to its dictionary meaning, and
   `Stage.lean` names the actor of the `admitted` field.

The branch merges into `refactor/phase1-phase3` at `36deb569` with no conflict (`git merge-tree`,
tested). The seven commits there since the base change the proof graph, the tools and
`Test/Audit` only; no library code these batteries run changed. The gate's one new rule reads
planned goals of `Effect4.Laws`, and these batteries declare none (reading). This seat did not
build the merged head.

## Changed files

- `Test/Dogfood/rc112/` (20 files, new):
  - the five programs, `p1-http-cache.ts` to `p5-ledger-service.ts`;
  - the six run scripts, `run-p1.ts` to `run-p5.ts` and `run-p2-noenv.ts`;
  - the controls `capture-control.ts`, `capture-cache-control.ts` and `red-control.ts`;
  - the records `hostruns.log`, `typecheck.log` and `sha256.txt`;
  - `tsconfig.json`, `tsconfig.red.json` and `tsconfig.bun.json`.
- `Test/Dogfood/Stage.lean` (new): `verdict`, `typingReason?`, `Answer`, `answerOf`, `Reach`,
  `printedOf`, `formAdmits`, with a green and a red control for each.
- `Test/Dogfood/P1HttpCache.lean`, `P2HandlerLayers.lean`, `P3WorkerQueue.lean`,
  `P4RateLimiter.lean`, `P5LedgerService.lean` (new): one battery per program.
- `Test/Dogfood/README.md` (new): the plan rows.
- `Test/All.lean`: five imports appended at the end of the import list.

## Commands and results

Every Lean or Lake process ran through `scratch/lean-slot.sh`, from the seat's worktree.

| Command | Result |
| --- | --- |
| `lake build Effect4 Effect4.Laws` | 639 jobs, restored from the artifact cache |
| `git show ce2ece4f:<path>` for the 51 files of the probe's `programs/` folder | recovered into the session scratchpad |
| `shasum -a 256 -c sha256.txt`, in `Test/Dogfood/rc112` | 14 lines `OK` |
| `git hash-object` of each file of `rc112/` against `git rev-parse ce2ece4f:<path>` | 20 identical, 0 different |
| `lake env lean -DwarningAsError=true` on the four 2026-09-30 encodings, unchanged | `ProbeRefusals` and `ProbeFormLaws` exit 0; `ProbeProgram1` and `ProbePrograms345` exit 1, both only at the driver's tuple pattern over `outstanding` |
| the same two, with the pattern read as an `Await` record | both exit 0: every guard holds |
| the verifier's `VerifyPrograms.lean`, unchanged | exit 0 |
| `lake env lean -DwarningAsError=true Test/Dogfood/<File>.lean`, each battery | exit 0, each |
| a red copy of each battery with two flipped guards (the verifier's flips where it had one) | exit 1, each, at exactly the two flipped guards |
| an axiom walk over every declaration of the six dogfood modules (`Lean.collectAxioms`) | 301 declarations; none beyond `[propext, Quot.sound]` |
| `lake build` of the 215 imports of `Test/All.lean` | 888 jobs, restored, 1 s |
| `lake env lean -DwarningAsError=true Test/All.lean`, before the second commit | exit 0, 40 s |
| the same, after rebuilding the dogfood modules, before the last commit | exit 0, 22 s; the gate lines below |
| `python3 scripts/check-language.py --show Test/Dogfood/README.md` | no finding |
| `python3 scripts/check-docs.py` | PASS: 72 documents resolve |

The red copies flipped these guards:

| Battery | First flipped guard | Second flipped guard |
| --- | --- | --- |
| p1 | the retired count, `1` to `0` | the stage's `readBack` |
| p2 | the wider record's missing exit | the stage's `answer` |
| p3 | the retired count, `2` to `0` | the stage's `answer` |
| p4 | rc.112's answer, to the pair `[3, 2]` | the stage's `answer` |
| p5 | the truncated `0`, to `1` | the stage's `int` verdict |

## Axiom output

```text
Effect4 library-root gate: 156 API/utility modules, 273 Laws-only modules; every library source is reachable; Effect4 never reaches Laws
Effect4 module and axiom gate: checked 654 modules and 80188 declarations; phases (ms): sources and closure 13, library roots 178, declarations 2218, resolution 657, axioms 14417, exemptions 256; semantic/test axioms are [propext,
 Quot.sound]; exact implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice
Effect4 goal gate: 12 planned goal(s), each a theorem whose body is `sorry` outside the Effect4 root; 8 declaration(s) rest on goals; no other declaration reaches sorryAx
```

`#print axioms` on the three ported theorems gives the probe's log. `timeoutForm_scoped` and
`retryForm_scoped` print `[propext, Quot.sound]`, and `leaky_not_scoped` prints `[propext]`.

## Evidence

- **Tested**: each program's stage, a finite probe of one scripted host and one decision tape per
  run. A red copy fails at each pin.
- **Tested**: the checksums and blob identity of the reference texts, the fresh gate, the docs
  check and the language check of the README.
- **Proved**: the three ported theorems, rerun.
- **Reading**:
  - no route A row adapter exists (a search of `src/` for an adapter or a width projection);
  - `Run.driveFrom` stops when its reactor declines;
  - no atom turns a number into text (the atom list of `src/Effect4/Machine/Term.lean`).
- **Host-only and bounded**: the rc.112 answers are the recorded bun runs of 2026-09-30, one
  schedule each. This seat did not rerun them, and no gate runs them. Each battery compares the
  model's run with one recorded rc.112 run and claims no simulation.

## The stages, measured

| Program | Admitted | Answer | Printed | Read back | Refused parts (verdict) |
| --- | --- | --- | --- | --- | --- |
| p1 | yes | differs: the body text, where rc.112 answers `42` | yes | no: the retry loop's annotation (DI-91) | `HttpError{status, url}` (`errorNotAdmitted`); a `Quote` in the key-value cache (`requestNotSubtype`) |
| p2, the bounded handler | yes, at `Response` | rc.112's three answers, also as JSON modulo key order | yes | yes, as an expression and as a module | string and record service carriers (`serviceCarrier: signature none`); `NotFound{id}`, `Unauthorized{reason}` (`errorNotAdmitted`); a number in a template (`typing: term`) |
| p3 | yes | differs: `[3, 5]`, where rc.112 answers its log | yes | yes | a list cell (`requestNotSubtype`); `JobFailed{id, reason}` (`errorNotAdmitted`) |
| p4 | yes | rc.112's `[3, 2, 3]` | yes | yes | the `Window` record cell (`requestNotSubtype`) |
| p5 | no | not run | no | no | the `Account` record cell (`requestNotSubtype`); `InsufficientFunds{needed, available}` (`errorNotAdmitted`); `int` (table admission: `uninhabited`) |

## What no longer holds, and what changed, in the old encodings

1. **One construct changed.** `outstanding` answers `Await` records (row 16, `ffc8bb93`). The
   probe's two host drivers matched tuples and failed to compile. With the record pattern, every
   guard of the four 2026-09-30 encodings and of the verifier's probe holds at `37289464`.
2. **Everything else the encodings pinned still holds.** Cells hold numbers only, a typed failure
   carries no number, and the service table types no string. The runs give the same answers, call
   counts and retirements.
3. **The verifier's reason for p3's pool is wrong.** It wrote that the printer drops a scoped
   fork's daemon flag. The printer refuses a child fork into a scope
   (`internalAction "forkScoped:child"`), by the owner's ruling of 2026-09-17 (`09be67a8`, an
   ancestor of the probe's base `7cae243a`). The battery measures the pool with rc.112's
   `Effect.forkScoped` options instead. Both spellings run to the same observations.
4. **Records moved p2.** The handler with records reaches every Lean-side stage. Of seat R's
   six `DataWave` parts, five exist. Route A's row adapter does not, so the reply check refuses a
   wider record (`envelope`), and the battery pins that.
5. **Two authority texts are stale (reading; outside this seat's files).** `Api.readable`'s note
   in `src/Effect4/Api.lean` still says the printer loses the daemon flag of a scoped fork. The
   dictionary's §3.9 rows for the Schema bridge and the JSON codec
   (`docs/core/controlled-english.md`) say record support is open in both. Both have a record arm
   today, and p2's battery encodes and decodes records through them.
6. **Two encoding changes of this seat.** Program p4 answers rc.112's triple, where the probe
   answered a pair. The triple's first two items are the dogfood's `[3, 2]` and `[5, 0]`. Program p1
   adds `run-p1.ts`'s own 404 run, with `fetchQuote` alone, which fails after one call as rc.112's
   did.

## Landed theorems and their placement

The three theorems are the probe's `ProbeFormLaws.lean`, ported unchanged into
`Test/Dogfood/P1HttpCache.lean`. Each records that p1's hand forms meet the one form obligation
that comes for free.

`timeoutForm_scoped` and `retryForm_scoped`:

- Concept: `initial-algebras-folds`, since the authoring surface is the algebra of the program's
  binding signature on the scope-reader carrier (`src/Effect4/Program/Authoring.lean`). Property:
  lexical well-scoping of a form, which `docs/core/semantics.md` does not list (proposed below).
- Question: no semantics registry claim. R10's shape in the system map names lexical well-scoping
  among a form's obligations. Consumer: none in the tree; p1's battery uses the two forms.
- Reach: `Src.Scoped` of the form for scoped arguments, at every scope, with no typing and no
  run. The rows that bound it are DI-89 and R10's C8.
- Does not establish:
  - a typing lemma;
  - a behaviour law against rc.112's `raceFirst` or `retryOrElse`;
  - reader admission of a program;
  - a readable expansion (the retry form fails it, tested);
  - a stable identity.
- Unlocks: R10's per-form obligations, when DI-89 or W6 lands a `timeout` or `retry` form;
  nothing on the M5 to M7 spine.

`leaky_not_scoped` is the red control of the two, with the same placement. Its consumer is the two
theorems' meaning.

## The semantics report and the plan rows (proposal; the registry is not edited)

The registry (`tools/Tools/SemanticsRegistry.lean`) could read the plan rows as it reads the
requirements:

```lean
/-- A tracked acceptance program (decisions row 206). The registry names it and what it waits
on; its battery measures how far it gets. -/
structure Acceptance where
  id : String          -- `p1` … `p5`
  title : String
  source : String      -- `Test/Dogfood/rc112/p1-http-cache.ts`
  battery : Name       -- `Test.Dogfood.P1HttpCache`; its `stage` holds the measured `Reach`
  waitsOn : List String  -- requirement ids and rows: `R4`, `row 42`
  slice : String       -- the slice of row 204 expected to move it

-- in `Registry`: `acceptance : List Acceptance := []`, and the five battery modules in `roots`
```

The report then:

1. Reads each battery's `stage` declaration: a literal `Reach` the report prints from the
   definition's value. It runs no program. The battery's `#guard measured = stage` ties the literal
   to the measurement, so a stale literal fails `Test/All.lean`, not the report.
2. Lists, beside each requirement row, the programs that wait on it, from `waitsOn`. These are the
   witness programs the model probe asked each requirement to name (its finding P6).
3. Lists, beside each row 204 slice, the programs it is expected to move.

With it, the README's table is a projection the report writes. Until then the README is its one
hand input.

## Open obligations

- Row 206 makes an admitted program's semantic claims planned goals. This seat declares none,
  because each needs its placement first. Candidates:
  - p4: no run lets more than three requests through between two clock decisions;
  - p2: the bounded handler answers 401 exactly when the token differs;
  - p3: the pool releases each connection once.
- The host half of W10's acceptance did not run (`docs/research/2026-10-01-data-wave/brief-W10.md`).
  It is tsgo 7 on the printed module, bun on it, and the external reader on the rendered text.
- The two stale authority texts of finding 5.
- The architecture map's role register (`tools/Tools/ArchitectureRoles.lean`) has no
  `Test/Dogfood` area, so the new files roll up into `Test`. The map is a generated artifact,
  regenerated at a sweep.

## Proposed decisions rows (proposals only)

1. The semantics registry gains the `acceptance` list above, and the README's table becomes its
   projection. Recommendation: yes, with the slice that next moves a program.
2. Who declares row 206's planned goals: the slice that admits a program, with the placement in
   its brief. Recommendation: that slice, starting with p4's claim above.
3. W10's v0 acceptance: record its Lean half as measured by `Test/Dogfood/P2HandlerLayers.lean`, and
   rule whether its host half is still owed. Recommendation: owed, run once at the next sweep.
4. A `Test/Dogfood` area in the architecture role register. Recommendation: yes, one line.

## Process notes

- Scratch files stayed in the session scratchpad, except one backup copy written to `/tmp` by
  mistake and removed at once.
- No file outside `Test/Dogfood/**` and the import list of `Test/All.lean` changed in the worktree.
