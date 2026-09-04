# Deep packets: the gates they must pass, and the frozen-surface tax

Research note, 2026-09-03. HEAD `6d835330133b056f95c308d55cbbe67eb680213f`, branch `main`,
clean tree. Every claim below is labelled **verified by reading** or **verified by running**
(a Lean scratch elaboration against the built library, or a shell probe) or **inferred**.

## Summary

1. A new `Effect4/Runtime/Fiber.lean` needs **one** production-side edit outside its own
   directory — an import line in `Effect4.lean` — because the per-area Lake targets are globs
   (`lakefile.toml:36-78`) and the module-closure gate keys on `Effect4Test.lean`'s import
   closure, which reaches `Effect4` through `Effect4Test/Audit/AxiomGate.lean:3`.
2. Five gates then run over it: the source tokenizer (7 refused words), the declaration pass
   (`unsafe`/`partial`/bodyless `opaque`), the axiom gate (ceiling `propext`/`Quot.sound`), the
   module-closure gate (both directions against `known-red.txt`), and the trust-gate self-test
   with its nine planted defects.
3. A `Classical.choice`-reaching *helper* costs one exact-root line in
   `choiceImplementationDeclarations` (`Effect4Test/Audit/AxiomGate.lean:140-224`) plus a
   staleness obligation; a `Classical.choice`-reaching *theorem intended as a coverage witness or
   an assurance receipt* cannot be admitted at all and must be refactored.
4. A model packet under `Effect4/Runtime/` does **not** move the Fiber frozen surface. Verified
   by running: `Effect4Test/Concurrency/FiberAssurance.lean:1-4` imports only Scheduler and
   Supervision, and the owned census is import-context sensitive — Supervision owns **705**
   declarations in that narrow environment and **699** under `import Effect4`, the six being
   `Effect4.ScopeState.entries.eq_{1..5}` and `Effect4.Scope.finalizers.eq_1`, which
   `Effect4.Runtime.ScopeMachine` mints first in the wide one.
5. The L15 inversion is half-right. The three `*Owned` lists (504 entries) and `supervisionOwned`
   (705) are derivable; `authoredApiDeclarations` (185) and `supervisionApi` (294) are **not** —
   verified by running, a declaration-range filter yields 327 and 466, not 185 and 294.
6. The right shape is: derive the owned census, and have the checker *read the committed TSV at
   elaboration*, exactly as `AxiomGate.lean:540-548` already reads `known-red.txt`. The
   exact-surface property then still fails inside `lake build`, not only in a shell gate.
7. `Effect4Test/Schema/StructuralAssurance.lean:38-212` is the inverted design already running in
   this tree — derived census, authored route rule, authored forbidden-duplicate list, no counts —
   and its gate is the one assurance gate CI runs (`.github/workflows/lean_action_ci.yml:24`).
8. `scripts/check-fiber-assurance.sh` and `scripts/test-fiber-assurance-gate.sh` are invoked by
   **no** automated runner: not `scripts/sweep.sh:64-79`, not CI. The 2 400-entry frozen surface's
   only automatic enforcement today is the in-Lean count assertions.
9. So the inversion packet must add `fiber-assurance` to the sweep table *before* it deletes the
   inline lists, or it trades a real gate for a manual one.
10. The runtime-coverage join costs, per new witness: a `w` line, a `#check (@… : …)` ascription,
    a `snapshotWitnesses` entry in the same order, and possibly a coverage state and the two
    totals. 137 rows, denominator 117, green 49, partial 25, absent 43, owned-with-green 3
    (counted from source, not the sanctioned report).
11. Replacing the twelve `fork.*` rows' witnesses means replacing 181 witness references drawn
    from 131 distinct `Effect4.Supervision.*` theorems; nothing in the gate stops a row going
    `partial` → `absent`, so the packet must assert the twelve rows' coverage states explicitly
    and carry a register row per retired witness family.
12. The 4 004-line coverage module is 452 `#check` ascriptions plus a 1 288-line row table; the
    rows and the totals can move to a generated TSV without losing a guarantee, but the
    ascriptions cannot — they are the only thing that freezes a statement, and they must stay
    authored Lean.
13. L27, L10, L53, L18, L19, L20, L21, L22, L24, L52 all still hold at HEAD (each re-checked).
    Of these only L53 (`FrameSimulation` → `Effect4/Runtime/`) is naturally carried by a deep
    runtime packet; L27 and L10 are `Effect4.lean` edits any packet can make in four lines.
14. The sweep will not run under WSL sharing this checkout (no lean/lake/node there, and Linux
    Lean cannot read the Windows oleans in `.lake`), and will not run under Git Bash either
    (`lake env printenv LEAN_PATH` returns `;`-separated Windows paths, while
    `scripts/test-trust-gate.sh:235` joins with `:`; and `ln -s` copies). The one setup is a
    second clone inside WSL with its own elan and `.lake`.
15. `COORDINATION.md` splits cleanly at line 160: lines 1-159 are the live file (identity, claims,
    collision costs, operational facts, working rules), lines 160-2730 are 74 append-only landing
    records that belong in `docs/COORDINATION-LOG.md`, with the owed items lifted into a table.

---

## 1. The gates a new model module must pass, exactly

### 1.1 What each gate is, and what it rejects

**Verified by reading** unless marked otherwise.

| Gate | Where | Rejects |
| --- | --- | --- |
| module closure | `Effect4Test/Audit/AxiomGate.lean:571-576` | a `.lean` file under `Effect4/` or `Effect4Test/` that the audit root does not import and `known-red.txt` does not declare |
| stale red entry | `Effect4Test/Audit/AxiomGate.lean:577-586` | a `known-red.txt` entry whose source is missing, **or** whose module the audit root does import ("its red phase is over") |
| source tokenizer | `Effect4Test/Audit/AxiomGate.lean:283-299, 433-506` | the raw tokens `unsafe`, `partial`, `sorry`, `axiom`, `native_decide`, `extern`, `implemented_by` anywhere in an audited source, including inside an `example`; `admit` only if a future toolchain makes it a keyword |
| declaration safety | `Effect4Test/Audit/AxiomGate.lean:594-604` | `isUnsafe`, `isPartial`, and an `opaque` whose value's head is `Inhabited.default` or `Classical.ofNonempty` |
| axiom ceiling | `Effect4Test/Audit/AxiomGate.lean:615-630` | any axiom outside `[propext, Quot.sound]` (`:65-66`), and outright `sorryAx`, `Lean.ofReduceBool`, `Lean.ofReduceNat`, `Lean.trustCompiler` (`:246-247`) |
| admission staleness | `Effect4Test/Audit/AxiomGate.lean:635-651` | a module in `choiceImplementationModules` or a name in `choiceImplementationDeclarations` that no longer reaches `Classical.choice`, or no longer exists |

Cross-module admission is inherited only through `sameModuleAncestors` and names for which
`Lean.isReservedName` holds (`Effect4Test/Audit/AxiomGate.lean:336-389`); a hand-spelled
`f.proof_1` in a foreign module is refused, and
`test/fixtures/trust-gate/forged-auxiliary.lean.txt` is the fixture that says so.

`scripts/test-trust-gate.sh` is the self-test. It plants **nine** defects and expects two
acceptances:

- accept: `lake build Effect4TestGreen` (`:102-109`), and the benign fixture (`:292-295`);
- reject, source tokens (`:297-304`): `partial`, `unsafe`, `sorry` in a named theorem, `sorry`
  inside an `example`, `native_decide`, `axiom`;
- reject, compiled declarations (`:333-357`): bodyless `opaque`, unadmitted `Classical.choice`,
  hand-spelled auxiliary of an admitted declaration;
- then three narrow harnesses (`:363-373`): the tokenizer fixtures, the exact-admission probe
  `scripts/test-trust-boundaries.sh`, and the `Expr`-equality probes.

The declared-red set is checked in both directions: `Effect4Test/Audit/AxiomGate.lean:577-586`
catches a declared module the root imports, and `scripts/test-trust-gate.sh:157-175` runs
`lake build $declared_red` and refuses a declared module that is green. Today the file holds two
entries: `test/fixtures/trust-gate/known-red.txt:26` (`Effect4Test.Protocol.ByteParserContract`)
and `:31` (`Effect4Test.Concurrency.RaceRepresentativeContract`).

### 1.2 The checklist for `Effect4/Runtime/Fiber.lean` with N public theorems

1. **`Effect4.lean`** — add `import Effect4.Runtime.Fiber`. This is what satisfies the
   module-closure gate, because the audit root reaches `Effect4` transitively through
   `Effect4Test/Audit/AxiomGate.lean:3`. *(Alternative: have a battery import the module
   directly; the gate only asks for reachability.)*
2. **`lakefile.toml`** — no edit. `Effect4` is `globs = ["Effect4.*"]` (`lakefile.toml:12`) and
   `Effect4TestRuntime` is `globs = ["Effect4Test.Runtime.+"]` (`:52-54`); both pick the new
   modules up. `defaultTargets` (`:8`) is unchanged.
3. **Contract** — a breaker packet under `test/contracts/`, frozen before the builder starts
   (`test/contracts/README.md:1-7`). A run-loop over a program-carrying fiber is an interpreter
   and a transition system, so it is on the **graph** route, not the leaf route
   (`docs/AGENT-ROUTING.md`, "Assurance threshold", the six graph triggers).
4. **Red battery + `known-red.txt`** — while the battery is frozen and the implementation is not
   there, add its module name to `test/fixtures/trust-gate/known-red.txt`; **remove it the same
   day it goes green**, or `scripts/test-trust-gate.sh:157-175` fails for everyone. A red module
   nobody declared blocks the whole gate, and the planted-`unsafe` detector runs last
   (`COORDINATION.md:155-158`).
5. **Test umbrella** — add every new `Effect4Test/Runtime/*.lean` (contract, axiom report,
   counterexample witnesses) to `Effect4Test.lean`. Not appearing there means the module-closure
   gate names the file.
6. **Axiom report** — `Effect4Test/Runtime/FiberModelAxiomReport.lean`, one
   `#print axioms <name>` per public theorem, in the shape of
   `Effect4Test/Concurrency/FiberAxiomReport.lean:11-30`. Where an assurance join exists, the
   report's names must equal the join's theorem list *in order*
   (`scripts/generate-fiber-assurance.sh:365-373`).
7. **Counterexample rows** — a stable `E4-…-CE-nnn` row in `test/counterexamples/REGISTER.md`,
   a `## <id> — ` heading in the area `ATTACKS.md`, and an executable witness under
   `Effect4Test/Counterexamples/Runtime/` citing the id. The Fiber generator enforces exactly
   this triple (`scripts/generate-fiber-assurance.sh:245-271`); a Runtime-lane generator would
   have to do the same or the rows are prose.
8. **Runtime coverage** — only if a theorem is *intended* as a witness. Then §3 applies; a
   theorem alone moves no number (`docs/RUNTIME-COVERAGE.md:84-97`).
9. **Fiber frozen surface** — **not touched**, provided the new module is not imported by
   `Effect4/Concurrency/Supervision.lean` or `Scheduler.lean`. See §2.2: verified by running.
10. **Gate runs before handoff** — `lake build Effect4TestGreen`; `lake env lean` on the narrow
    battery (with `-DmaxErrors=10000` if it is red, `COORDINATION.md:118-120`);
    `./scripts/test-trust-gate.sh`; `./scripts/sweep.sh --hermetic`.

### 1.3 What a `Classical.choice`-reaching helper costs

- **A metaprogramming or rendering helper**: one line in
  `choiceImplementationDeclarations` (`Effect4Test/Audit/AxiomGate.lean:140-224`), or a
  `(owner, originalName)` pair in `choiceImplementationPrivateDeclarations` (`:230-244`) if it is
  private. `#effect4_print_choice_reachers` (`:676-703`) prints the exact list in the shape both
  want. The entry then carries a permanent staleness obligation (`:645-651`): when the helper
  stops reaching `Classical.choice`, the gate fails until the line is deleted. Cost: one line,
  one re-pin command, and `scripts/test-trust-boundaries.sh` re-elaborates the admissions.
- **A semantic theorem**: not admissible. `Effect4Test/Audit/RuntimeCoverage.lean:3877-3889`
  rejects any witness axiom outside `propext`/`Quot.sound` before a receipt can even be spelled,
  and `scripts/check-effect-runtime-census.sh:192-204` re-checks it on the emitted rows;
  `Effect4Test/Concurrency/FiberAssurance.lean:1045-1058` does the same for assurance receipts.
  Refactor is the only route. The four known traps and their axiom-free alternatives are
  tabulated at `COORDINATION.md:121-128`: `simp` on a positive `String` disequality (use
  `decide`), `decreasing_by` (use `termination_by structural`), `omega` on `Nat` chains (use
  explicit `Nat.lt_of_lt_of_le`), and Std's `IsLinearOrder.of_lt` / `LE.ofLT` factories.

---

## 2. The frozen-surface machinery, and the L15 inversion designed

### 2.1 What is there now

`Effect4Test/Concurrency/FiberAssurance.lean` is 2 512 lines. The machine parts are small: an
owner lookup (`:23-29`), a one-pass fold `declarationsOwnedBy` (`:31-37`), and
`checkExactModuleSurface` (`:70-79`), which compares an authored list against the fold in both
directions. Everything else is data. Two independent joins live in the file — the representative
join (`#effect4_check_fiber_assurance` / `#effect4_emit_fiber_assurance` at `:1176-1177`) and the
supervision join (`#effect4_emit_supervision_assurance` at `:2510`).

`scripts/generate-fiber-assurance.sh` runs the module under `lake env lean` (`:273-284`), reads
the `E4FIBER`/`E4SUP` lines it prints, asserts hardcoded counts (`:310-338`: 504 total owned,
62/79/363 per module, 185 API, 92/92 theorem/axiom, 16 type, 14 leaf, 12 absent, 10 edges),
cross-checks the axiom report name list (`:365-373`), and emits the TSV
(`:407-459`). `scripts/check-fiber-assurance.sh:54-60` regenerates and `cmp`s byte for byte
against `generated/fiber-assurance.tsv` (237 235 bytes; 1 209 `owned-declaration` rows,
479 `api`, 228 `theorem`, 228 `axiom`, 43 `type`, 17 `leaf-receipt`, 19 `shape`, 20 `graph-edge`).
`scripts/test-fiber-assurance-gate.sh` plants ten defects: four Lean mutants
(`:70-77` — extra, missing, duplicate, owner drift), a stale TSV (`:80-90`), two manual
`required-closed` overrides in the authored DAGs (`:91-108`, `:146-159`), a supervision extra
field (`:115-140`), and two evidence-schema substitutions (`:161-190`).

**The sibling lanes have already diverged in design.** `Effect4Test/Schema/StructuralAssurance.lean`
holds *no* name census at all: `sourceModules` (`:38-47`) names eight modules, `routeFor`
(`:60-110`) is a **rule** from `(owner, name)` to a route, `forbiddenDuplicateDeclarations`
(`:112-122`) is authored, and `checkStructuralAssurance` (`:171-198`) walks the derived census
demanding that no declaration route to `UNALLOCATED`. Its exact-surface property is carried
entirely by the byte drift gate (`scripts/check-schema-structural-assurance.sh:37-42`), which
prints "exact 1426-declaration census" (`:45`). `Effect4Test/Data/RowAssurance.lean:64-127` and
`Effect4Test/Environment/ContextKeyAssurance.lean:73-201` are still on the FiberAssurance side —
authored `expectedOwnedDeclarations` plus authored API.

### 2.2 Two verified facts the design has to respect

**(a) The derived census is import-context sensitive.** *Verified by running* (`lake env lean` on
a scratch module, ~8 s each). Bucketing `environment.constants` by owning module:

| owning module | with `import Effect4.Concurrency.{Scheduler,Supervision}` | with `import Effect4` |
| --- | ---: | ---: |
| `Effect4.Concurrency.Interrupt` | 62 | 62 |
| `Effect4.Concurrency.Fiber` | 79 | 79 |
| `Effect4.Concurrency.Scheduler` | 363 | 363 |
| `Effect4.Concurrency.Supervision` | **705** | **699** |

The six that move are equation lemmas of `Effect4/Runtime/Scope.lean` declarations, minted in
whichever module first unfolds them. Under the full umbrella `Effect4.Runtime.ScopeMachine` wins:
`Effect4.Scope.finalizers.eq_1` and `Effect4.ScopeState.entries.eq_{1..5}` (verified by running an
owner probe); `Effect4.Scope.finalizerKeys.eq_1` and `Effect4.Scope.tableRemove.eq_1` stay with
Supervision. The 705 in `FiberAssurance.lean:2438` is therefore a fact **about that module's
import header** (`:1-4`), not about the library. Consequence: the derivation must stay in a module
with exactly those imports, and any new module that `Effect4/Concurrency/Supervision.lean` comes
to import can steal an equation lemma and fail the census as `missing` — the same shape as the
drift recorded at `COORDINATION.md:104-107`.

**(b) The authored API is not derivable.** *Verified by running.* The obvious rule — "has a
declaration range in the source, and is not a name Lean reserves" — gives 38/51/238 = **327** for
Interrupt/Fiber/Scheduler against an authored API of **185** (`FiberAssurance.lean:1076`), and
**466** for Supervision against **294** (`:2438-2439`). Structure projections, constructors and
`instDecidableEq*` companions all carry ranges. The survey's proposal to derive
`authoredApiDeclarations` (`docs/research/2026-09-03-survey-lean-core.md:588-591`) does not
survive contact; the API subset is a genuine authored judgement.

### 2.3 The design: before and after

The move that makes it work is already in the tree: `Effect4Test/Audit/AxiomGate.lean:540-548`
reads `test/fixtures/trust-gate/known-red.txt` **from disk at elaboration time**, having located
the project root by walking up for `Effect4.lean` (`:508-516`). Do the same with
`generated/fiber-assurance.tsv`: the checker parses the committed projection's
`owned-declaration` and `api` rows and compares them with the environment. The exact-surface
property then still fails inside `lake build Effect4TestGreen`, which is what the inline lists buy
today and what a shell-only drift gate would lose.

| list (line range, entries) | now | after | why |
| --- | --- | --- | --- |
| `expectedInterruptOwned` (`:81-145`, 62) | inline Lean names | **derived**, compared to TSV | `declarationsOwnedBy` already computes it (`:31-37`) |
| `expectedFiberOwned` (`:146-227`, 79) | inline | **derived**, compared to TSV | same |
| `expectedSchedulerOwned` (`:228-593`, 363) | inline | **derived**, compared to TSV | same |
| `supervisionOwned` (`:1188-1895`, 705) | inline | **derived**, compared to TSV | same |
| `authoredApiDeclarations` (`:594-781`, 185) | inline `(name, owner, route)` | **read from the TSV's `api` rows**; route re-derived by rule and cross-checked | not derivable (§2.2b); the route column already has a rule for supervision (`:2422-2429`) |
| `supervisionApi` (`:1896-2192`, 294) | inline `(name, route)` | **read from the TSV's `api` rows** | same |
| `theoremReceipts` (`:782-876`, 92) | inline `(name, route)` | **derived**: the API names whose `ConstantInfo` is `.thmInfo` | `theoremNamesOwnedBy` in `StructuralAssurance.lean:161-165` is the pattern |
| `axiomReceipts` (`:877-971`, 92) | inline `(name, receipt)` | **derived** by `canonicalAxiomText` (`:1045-1058`), emitted, compared to TSV | receipts are computed today and only *compared* to the literal (`:1069-1071`) |
| `supervisionTheorems` (`:2193-2331`, 136) | inline `(name, receipt, census-row)` | **derived** for name and receipt; the **census-row id stays authored** | the id is a human judgement about which behaviour the theorem witnesses |
| `typeRows` (`:972-990`, 16) | inline | **stays authored** | dispositions are rulings |
| `supervisionTypes` (`:2354-2382`, 27) | inline | **stays authored** | mirrored into `PORT-MANIFEST.md` by `generate-fiber-assurance.sh:157-176` |
| `leafReceipts` (`:991-1007`, 14) | inline | **stays authored** | leaf routes are rulings |
| `supervisionLeaves` (`:2384-2388`, 3) | inline | **stays authored** | same |
| `forbiddenDuplicateDeclarations` (`:1008-1022`, 12) | inline | **stays authored** | absence facts have no environment source |
| `graphEdges` (`:1023-1034`, 10) | inline | **stays authored** | breaker-owned |
| `supervisionEdges` (`:2390-2401`, 10) | inline | **stays authored** | breaker-owned |
| `supervisionShapes` (`:2332-2352`, 19) | inline | **stays authored** | a frozen expectation about constructor and field order; deriving it would make it vacuous |

Deleted: about 1 900 lines of names. Kept: about 110 lines of rulings, plus the two route rules.

**The regeneration command does not change**:
`./scripts/generate-fiber-assurance.sh > generated/fiber-assurance.tsv`
(`generated/fiber-assurance.tsv:3`). It becomes the *only* place a surface change is recorded,
which is the point.

**Where the counts go.** `generate-fiber-assurance.sh:310-338` asserts 504/62/79/363, 185, 92/92,
16/14, 12, 10; `FiberAssurance.lean:1076` and `:2438-2441` assert the same numbers a second time.
Keep the shell-side assertions (they are the "the driver actually emitted rows" check) and delete
the Lean-side ones: with the TSV as the comparison target, a count assertion is a third statement
of a fact two other places already carry, and it is the one that produced the
"expected a compiler-generated companion that had been deliberately eliminated" failure recorded
at `COORDINATION.md:104-107`.

**Performance.** *Verified by running*: one bucketed pass over the 208 929 constants of the
narrow environment costs **~3.2 s**; `collectAxioms` over Supervision's 297 theorems adds ~20 ms.
The current file calls `declarationsOwnedBy` four times (`:1112-1114`, `:2433`) — four separate
folds, ~13 s. The inversion should build all four buckets in one pass and get *faster*.

**The day a packet retires 300 Supervision declarations.** Three things happen and one does not:

- the derived census shrinks, the fresh TSV differs, `check-fiber-assurance.sh:56-60` prints a
  diff of the removed `owned-declaration` rows — the removal is visible, line by line, in the
  committed artefact's git history, which is the record;
- `generate-fiber-assurance.sh:310-338`'s hardcoded 705/294/136 fail first, so the packet must
  restate the counts deliberately;
- `SUPERVISION-FROZEN-BATTERY` and the five frozen hashes at `:149-155` fail, so the breaker
  packet must be re-frozen or explicitly superseded — this is the expensive part and it is
  correct: retiring a frozen contract is a ruling, not a refactor.

What does **not** happen: nothing marks the retired declarations as retired. There is no
`retired` disposition anywhere in the vocabulary. **Recommendation:** add one authored list,
`retiredDeclarations : List (Name × String)` (name, superseding owner), checked exactly like
`forbiddenDuplicateDeclarations` (`:1083-1089`) — the name must be **absent** from the
environment — and emitted as `E4SUP retired <name> <supersededBy>` rows. That gives the TSV a
positive record of the retirement instead of a silent absence, and it makes an accidental
resurrection fail. `supervisionTypes` rows for retired types move to a `retired` route in the
same packet.

### 2.4 The gate that is not wired up

**Verified by reading.** `scripts/sweep.sh:64-79` lists twelve gates; `check-fiber-assurance.sh`
is not among them. `.github/workflows/lean_action_ci.yml:14-39` runs the vendor check, the trust
gate, `test-schema-structural-assurance-gate.sh`, `check-effect-runtime-census.sh`, and
`sweep.sh --hermetic`. Grepping `.github/`, `scripts/sweep.sh` and `harness/` for
`check-fiber-assurance`, `test-fiber-assurance-gate`, `check-data-row-assurance`,
`check-environment-context-key-evidence`, `check-fiber-representative-red` and
`check-race-representative-red` finds hits **only in `docs/`**. Five assurance gates and both
representative-red gates run nowhere automatically. That is why the inline Lean lists are load-
bearing today, and it is the prerequisite the inversion has to satisfy before it deletes them.

---

## 3. The runtime coverage join mechanics

### 3.1 Structure and failure conditions

**Verified by reading.** `Effect4Test/Audit/RuntimeCoverage.lean` is 4 004 lines in three parts:

- `section StatementSnapshot` (`:43-2540`) — **452** `#check (@name : proposition)` ascriptions;
- `censusRows` (`:2573-3860`) — 137 `Row` values (`:2545-2555`: `id`, `kind`, `disposition`,
  `coverage`, `witnesses : List (Name × String)`), carrying **581** witness references;
- `snapshotWitnesses` (`:3406-3859`) — the same 452 names in the same order, plus
  `expectedRowTotal := 137` and `expectedDenominator := 117` (`:3861-3862`).

The module rejects on: a duplicate row id or a row-count drift (`:3891-3895`); an unknown kind,
a disposition outside the manifest vocabulary, or an unknown coverage state (`:3896-3902`); a
witness listed twice in a row (`:3903-3904`); `absent` with witnesses or a non-`absent` row with
none (`:3905-3909`); an `owned` row with no witness (`:3910-3911`); a witness on an
`excludedInternal`/`targetOnly`/`evidenceOnly` row (`:3912-3913`); a missing witness, a
non-theorem witness — with a distinct message for a Prop-typed `def` (`:3915-3926`); an axiom
receipt drift or any axiom outside `propext`/`Quot.sound` (`:3877-3889`, `:3927-3930`); a
snapshot entry that witnesses nothing, or a witness with no snapshot entry (`:3932-3941`); and a
denominator drift (`:3946-3949`).

`scripts/check-effect-runtime-census.sh` adds eight checks on top: byte drift of the census
(`:136-142`); ids equal in both directions (`:159-166`); kinds equal (`:168-175`); the `#check`
names extracted from the *source text* equal the emitted `snapshot` list **in order**
(`:177-190`) — this is what stops an ascription being deleted; the axiom ceiling again
(`:192-204`); declared witness counts equal emitted witness rows per id (`:206-215`); and the
coverage summary's arithmetic (`:217-237`).

Counted from the module source (**not** the sanctioned report of
`scripts/report-effect-runtime-coverage.sh:58-63`): 137 rows, denominator 117, green 49,
partial 25, absent 43, owned-with-green 3.

### 3.2 What changes per witness and per row

Per new **witness** (`docs/RUNTIME-COVERAGE.md:84-92`): a `w \`Name "receipt"` entry in the row;
a `#check (@Name : …)` ascription transcribed from `#check @Name`; the name appended to
`snapshotWitnesses` **in the same position**; the coverage state changed only if every clause of
the census summary is now a named theorem; `expectedRowTotal`/`expectedDenominator` kept true;
`./scripts/check-effect-runtime-census.sh`.

Per new **row** (`:99-105`): the row is added to the generator only —
`kind|id|file|anchor|offset-start|offset-end|expected-span-sha256|summary` with an anchor that
occurs exactly once in its file — plus a matching Lean row at `absent` with no witness, the
per-kind counts and totals in both places, a regeneration, and the gate.

### 3.3 Replacing the twelve `fork.*` witness sets

**Verified by reading** (`RuntimeCoverage.lean:2768-2980`, plus a parse of the row table): the
twelve `fork.*` rows carry **181** witness references, of which 179 name `Effect4.Supervision.*`
theorems — **131 distinct** ones — and two name `Effect4.join_agreement` and
`Effect4.double_join_agreement` (`:2921-2922`). Eleven rows are `separateCalculus`; `fork.join`
is the one `owned` row (`:2919`). All twelve are `partial`.

What the existing gates would and would not catch if a packet swapped those witnesses:

- **Caught**: a retired theorem still listed (`:3920` missing witness); a new witness with no
  ascription, or an ascription in the wrong order (`check-effect-runtime-census.sh:177-190`);
  a witness reaching `Classical.choice`; a row left with zero witnesses while still `partial`
  (`:3908-3909`); `fork.join` losing every witness (`:3910-3911`, `owned`).
- **Not caught**: a row **relabelled** `partial` → `absent` with its witness list emptied. That
  passes `checkRowShape`, passes the denominator check (the denominator counts rows, not states),
  and moves `green + partial + absent` around inside the same total. The only trace is the
  emitted `coverage` row and the `partial:` line of the report.

So the packet must carry the guard itself. **Recommendation, in the packet, not as a later
cleanup:**

1. a `frozenCoverageStates : List (String × String)` list — for at least the twelve `fork.*` ids —
   asserting the state each row had **before** the packet, checked at elaboration, so a downgrade
   is a build failure and an upgrade is a one-line authored diff;
2. one register row per retired witness family in `test/counterexamples/REGISTER.md`, naming the
   `Effect4.Supervision.*` statement retired and the fiber-model theorem that supersedes it,
   with the retired witness kept in the tree until the register row closes;
3. the retired names entered in the §2.3 `retiredDeclarations` list, so their absence is a
   positive TSV fact rather than a diff;
4. the *before* and *after* report blocks from `scripts/report-effect-runtime-coverage.sh` pasted
   into the handoff, per `docs/RUNTIME-COVERAGE.md:57-80`.

### 3.4 Is there a cheaper structure? Partly

**Rows to a TSV: yes, and it loses nothing.** The 1 288-line `censusRows` table is
`(id, kind, disposition, coverage, [(witness, receipt)])`. `id` and `kind` are already required to
equal `generated/effect-runtime-census.tsv` in both directions
(`check-effect-runtime-census.sh:159-175`), so they are duplicated today. `disposition` mirrors
`PORT-MANIFEST.md`. `coverage` and the witness lists are the authored numerator. Move the whole
table to a committed `generated/runtime-coverage-rows.tsv`, read it in the elaborator the way
`AxiomGate.lean:540-548` reads `known-red.txt`, and the checks at `:3891-3949` run unchanged over
the parsed rows. `expectedRowTotal` and `expectedDenominator` become derived from the file and the
byte drift gate carries the freeze. Saving: ~1 290 lines, and one place instead of two for the
id/kind columns.

**Ascriptions to a generated file: no.** The 452 `#check (@name : proposition)` lines are the only
thing that freezes a *statement*. Generating them from the environment would make them tautologies
— they would agree with whatever the theorem currently says, which is exactly the drift they
exist to catch. `check-effect-runtime-census.sh:180-184` reads them out of the **source text** with
an `awk` match for this reason. They stay authored Lean.

**`snapshotWitnesses`: derive it.** It is the 452 ascription names re-typed. The elaborator cannot
see `#check` syntax after the fact, but the packet can invert the dependency: make the snapshot
list the authored one and check that the *source text* between the section markers contains
exactly those `#check (@name` lines in that order — which is what
`check-effect-runtime-census.sh:177-190` already does from the shell. Moving that comparison into
Lean makes it a `lake build` failure instead of a gate-only failure, and then the list appears
once.

Net: 4 004 lines → roughly 2 600 (2 500 ascriptions + ~100 lines of checks), with every current
failure condition preserved and two of them (row shape, snapshot order) promoted from shell to
`lake build`.

---

## 4. Structure items a deep packet should carry

All re-verified at HEAD `6d83533`.

| Finding | Still true? | Files it touches | Carried by a `Runtime`/`Concurrency` packet? |
| --- | --- | --- | --- |
| **L27** `import Lean` in the production umbrella | **Yes**. `Effect4/Meta/Derive.lean:1` is `import Lean`; `Effect4.lean:115` imports `Effect4.Meta.Derive` | `Effect4.lean` (4 lines), `lakefile.toml` if a second lib is wanted | **No** — independent, but it is a four-line edit any packet can make |
| **L10** 55 stub modules in the umbrella | **Yes**, recount at HEAD: **55** of 117 `Effect4/` modules declare nothing | `Effect4.lean` (55 import lines), 6 essay stubs → `docs/` | **No** — independent |
| **L53** `FrameSimulation` layering | **Yes**. `Effect4/Semantics/FrameSimulation.lean:72-80` still says "if the merge prefers strict directory layering the module moves to `Effect4/Runtime/FrameSimulation.lean` unchanged"; `Effect4.lean:56-58` carries the fence comment | `Effect4/Semantics/FrameSimulation.lean` → `Effect4/Runtime/`, `Effect4.lean`, `Effect4Test/Semantics/FrameSimulation*`, `docs/FRAMES-DAG.md`, `test/contracts/frame-simulation.contract.md` | **Yes** — a deep runtime packet is already in `Effect4/Runtime/` and already touches the frame machine |
| **L18** `autoImplicit` on | **Yes**, recount: **8** of 117 modules set `autoImplicit false` | 109 modules | **Partly** — a packet should set it false in the files it creates, and in `Effect4/Runtime/*` if it rewrites them; the tree-wide sweep is separate |
| **L19** `Equiv`/`Logic` at `Ty : Type` | **Yes**. `Effect4/Semantics/Equivalence.lean:29` and `Effect4/Semantics/Logic.lean:288` both read `variable {Ty : Type} {alphabet : FlowAlphabet Ty}` (the survey cited `Logic.lean:285`; it is now `:288`) | those two files, `Effect4/Semantics/Denotation.lean` to check | **No** — Flow lane, not runtime |
| **L20** fuel theorems `StateT σ Id`-only | **Yes** — `Effect4/Semantics/Fuel.lean`, `Runs.lean` headers still silent | those two | **No** |
| **L21** ASCII one-liner statements in `Supervision.lean` | **Yes** | `Effect4/Concurrency/Supervision.lean`, `FiberAssurance.lean` `supervisionTheorems`, the TSV | **Yes if the packet retires Supervision** — reformatting and retiring collide; do not do both |
| **L22** kernel `decide` on fuel-20 runs | **Yes** | `Effect4Test/Counterexamples/Target/RegionSimulationBoundary.lean`, `Effect4Test/Counterexamples/Runtime/ScopeRestorationBoundary.lean` | **No** |
| **L24** 21-way conjunctions in `Schema/Check.lean` | **Yes** | `Effect4/Schema/Check.lean` | **No** |
| **L52** `?` means `Bool` in `Supervision.lean` | **Yes** | `Effect4/Concurrency/Supervision.lean`, `FiberSupervisionContract.lean`, `supervisionApi`/`supervisionTheorems`, the TSV | **Yes if the packet retires Supervision** — a retirement makes the rename moot |

### 4.1 L27 in detail: every importer, and whether the move is safe

**Verified by reading.** Importers of `Effect4.Meta.Derive`:

- inside `Effect4/`: `Effect4/Concurrency/FiberFamily.lean:1`, `Effect4/Layer/LayerFamily.lean:1`,
  `Effect4/Stateful/RefFamily.lean:1`, and the umbrella `Effect4.lean:115`;
- inside `harness/`: `harness/effect-v4-family/Generate.lean:1`, `harness/trace/Generate.lean:1`,
  `harness/trace/Property.lean:1`;
- plus 16 batteries under `Effect4Test/`.

Importers of the three family modules: `Effect4.lean:47,64,66`; `harness/trace/Generate.lean:14-16`;
and eight batteries.

Findings:

- **`Effect4Test.lean` is safe.** It imports batteries, and the batteries import
  `Effect4.Meta.Derive` and the families *directly*, never through the `Effect4` umbrella. Dropping
  `Effect4.lean:47,64,66,115` changes nothing for the test tree, and the module-closure gate stays
  satisfied because the batteries keep those modules in the audit root's closure.
- **`harness/trace/Generate.lean` is safe** for the same reason: it names `Effect4.Meta.Derive` and
  the three families itself (`:1`, `:14-16`), so it does not depend on the umbrella re-exporting
  them. It is run by `lake env lean --run` (`scripts/lib/portable.sh:62-82`), which resolves
  modules through `lake env`'s `LEAN_PATH`, so the oleans need only to exist.
- **The minimal change is four deleted lines in `Effect4.lean`.** A second `lean_lib` is optional.
  If one is added, note two constraints. First, `lakefile.toml:12` globs `Effect4.*`, which would
  also claim `Effect4.Meta.*`; the tree already tolerates overlapping libs (`Effect4Test` at `:19`
  overlaps `Effect4TestGreen` at `:22-25`), but if the intent is that the `Effect4` *target* stops
  building Meta, `Effect4` must become closure-shaped (`roots`/`globs = ["Effect4"]`) like
  `Effect4TestGreen`, and the new lib must be added to `defaultTargets` (`:8`) or
  `harness/trace/Generate.lean` will find no olean after a plain `lake build`. Second, **do not
  move the files to a new top-level directory**: `Effect4Test/Audit/AxiomGate.lean:550-557` walks
  only `Effect4/`, `Effect4Test/` and the two root files, so a new `Effect4Meta/` tree would be
  outside the source tokenizer entirely — a real hole in the `sorry`/`native_decide` gate. Keep the
  files under `Effect4/Meta/` and change only the lakefile.

---

## 5. The sweep on this machine

### 5.1 What each hermetic gate needs

**Verified by reading.** `scripts/sweep.sh:64-79` has twelve gates; `--hermetic` selects five:
`check-trace-goldens.sh`, `check-lowering-coverage.sh`, `check-internal-citations.sh`,
`check-effect-runtime-census.sh`, `test-lowering-coverage-gate.sh`.

| Need | Which gates | Note |
| --- | --- | --- |
| `bash` (arrays, `< <(…)`, `<<<`) | all | `#!/usr/bin/env bash` throughout |
| `lean`, `lake` | trace-goldens, lowering-coverage, runtime-census | each does `lake build` then `lake env lean` |
| `sha256sum` **or** `shasum -a 256` | all, via `scripts/lib/portable.sh:17-28` | either back end; both agree on the bytes |
| GNU **or** BSD `sed -i` | generators, via `portable.sh:33-40` | `sed_inplace` picks by `sed --version` |
| `python3` | `generate-trace-goldens.sh:21`, `generate-lowering-coverage.sh:42,74`, `test-lowering-coverage-gate.sh` | reads `lake-manifest.json`, joins TSVs |
| `mktemp -d`, `find`, `awk`, `cmp`, `diff`, `comm`, `paste`, `tr`, `sort -u`, `xargs -0` | all | `stamp_key` (`scripts/lib/stamp.sh:53-70`) uses `find` + `sort -u`; `check-internal-citations.sh` uses `xargs -0` |
| `date -r <file>` | `stamp_report` (`scripts/lib/stamp.sh:94-97`) | GNU form |
| **no** node, **no** tsc, **no** tsgo | the five hermetic gates | `generate-effect-runtime-census.sh:25-31` says so explicitly and reads only `vendor/effect-4.0.0-rc.112/src` |

The host lane (`sweep.sh:70-74`, plus `trace-goldens-gate` and `lowering-mutations` at `:76-77`)
needs `node`, the external runner `$EFFECT4_TOOLS/packages/harness/check.mjs` (default
`../effect4-tools`, `scripts/check-trace-host.sh:36`), and `EFFECT4_EFFECT_NODE_MODULES`.

### 5.2 What breaks where

**Windows + Git Bash** (what the Bash tool here already is). *Verified by running.*

- Everything the hermetic gates need is present: `sha256sum` at `/usr/bin/sha256sum`, `shasum`,
  `mktemp`, GNU `awk`/`sed`/`comm`/`cmp`/`diff`/`paste`, `find`, `date -r` (works), plus
  native `lean`/`lake` (elan 4.2.3, Lean 4.33.1 `x86_64-w64-windows-gnu`), `node v22.23.2`,
  `python3`. The checkout is LF-clean: `core.autocrlf=false`, `core.eol=lf`, no `.gitattributes`,
  and `file scripts/sweep.sh` reports "ASCII text executable" with no CRLF.
- **`scripts/test-trust-gate.sh` cannot run.** `lake env printenv LEAN_PATH` returns
  `C:\…;C:\…;C:\…` — Windows paths, `;`-separated — while `:235` builds
  `LEAN_PATH="$planted_lib:$real_lean_path"` with a `:` and an MSYS `/tmp/…` path. Both the
  separator and the path syntax are wrong for `lean.exe`.
- **`ln -s` copies.** Verified: `ln -s a b` produced a regular file, not a link. `:196-203`
  mirrors the whole real build directory that way, so the probe would copy every olean instead of
  linking — slow, and the comment's guarantee ("nothing in the real build directory is written")
  is preserved but the cost is not.

**WSL Ubuntu sharing the Windows checkout.** *Verified by running*
`wsl -e bash -c 'command -v …'`: WSL has `sha256sum`, `mktemp`, `python3`, `git`, GNU sed 4.9,
bash 5.3 — and **no `lean`, no `lake`, no `node`, no `tsc`**. `npm` resolves only to the Windows
`/mnt/c/Program Files/nodejs/npm` through interop, which is not a usable node. Beyond the missing
tools, sharing `/mnt/c/Users/kokok/Dev/lean4-effect4` is wrong for three reasons:

- `.lake/build/lib/lean` holds `x86_64-w64-windows-gnu` oleans; a Linux `lean` cannot read them,
  so the first `lake build` rebuilds the whole tree into the same directory and destroys the
  Windows build (**inferred** from the toolchain triple, not tested);
- `.lake/stamps` is shared, and `stamp_key` (`scripts/lib/stamp.sh:53-70`) hashes **paths as well
  as contents**, so a Windows-side stamp is never a hit on the Linux side and vice versa — the
  two would silently churn each other's `stamp_write` (`:86-90` deletes older stamps for the gate);
- `/mnt/c` I/O is roughly an order of magnitude slower than the WSL filesystem, and `stamp_key`
  walks every `.trace` under two trees on every gate (**inferred**).

There is no `platform` field in `harness/trace/host-pin.json` (it has `effectVersion`,
`effectUpstreamCommit`, `effectFileCount`, `effectTreeSha256`, `typescriptVersion`,
`diagnosticVersion`) — the platform is only *printed* by the fiber-supervision host gate
(`harness/README.md:128-131`), so it is not a cross-platform pin hazard.

### 5.3 The one setup

**A second clone inside WSL, on the Linux filesystem, with its own toolchain.**

```
wsl                                  # Ubuntu
curl … elan-init.sh                  # elan; lean-toolchain pins 4.33.1
git clone <this repo> ~/lean4-effect4
cd ~/lean4-effect4 && lake build     # its own .lake, Linux oleans
./scripts/sweep.sh --hermetic
./scripts/test-trust-gate.sh
```

Rationale: this is the same OS CI runs (`.github/workflows/lean_action_ci.yml:10`,
`ubuntu-latest`), the four portability shims in `scripts/lib/portable.sh` were written for exactly
the macOS/Ubuntu pair, `ln -s` and `:`-separated `LEAN_PATH` both work, and nothing contends with
the Windows `.lake` the interactive work uses. Node is needed only if the host lane is wanted;
`apt install nodejs` plus the two directories below.

**What the host gates need and where it is expected to live** (none of it is present here —
verified: all three paths are absent):

| Variable | Default | What it must contain |
| --- | --- | --- |
| `EFFECT4_EFFECT_NODE_MODULES` | `$repo_root/../foldlab/library/effects/node_modules` (`scripts/check-effect-runtime-census.sh:102`, `generate-effect-runtime-census.sh:76`, `check-fiber-supervision-host.sh:7`) or `$HOME/Dev/foldlab/library/effects/node_modules` (`scripts/lib/stamp.sh:156`, `check-lowering-types.sh:28`) | an installation of `effect@4.0.0-rc.112`, `typescript@7.0.2`, `@effect/tsgo@0.38.0`, matching `harness/trace/host-pin.json` |
| `EFFECT4_TOOLS` | `$repo_root/../effect4-tools` (`scripts/check-trace-host.sh:36`, `check-trace-patched.sh:26`, `check-lowering-property.sh:30`, `test-lowering-mutations.sh:19`, `test-trace-goldens-gate.sh:21`, `harness/effect-v4-family/check.sh:23`) | `packages/harness/check.mjs` and friends |

Note the two defaults disagree — `$HOME/Dev/foldlab/...` versus `$repo_root/../foldlab/...` — so
`EFFECT4_EFFECT_NODE_MODULES` should be set explicitly rather than relied on. The hermetic lane
does not need either: `generate-effect-runtime-census.sh:74-91` treats an unreachable install as
"no cross-check" and keeps going, which is what makes the census gate green in CI.

---

## 6. Records

### 6.1 The split

`COORDINATION.md` is 2 730 lines / 179 KB, 79 `##` sections, and every agent is told to read it
first. The break is clean at line 160: `## Completed trust-gate repair, 2026-09-01` starts the
append-only history and nothing before it is history.

**Stays live in `COORDINATION.md`** (~160 lines):

| Section | Lines | Change |
| --- | --- | --- |
| header + continuation notes | 1-22 | drop `Last updated: 2026-08-31` (`:9`), which already contradicts the 2026-09-03 sections; git is the record |
| `## Who is active` | 23-28 | rewrite from `git worktree list`; both rows are stale (L11) |
| `## Current claims` | 30-84 | clear the 47 dead rows; the first one still names worktree `agent-a7d1f74bf61e7c52b` as uncommitted for files committed at `2328fa8`/`96b1ae2` |
| `## What collisions have already cost` | 85-110 | keep verbatim — four recorded failures, all caught by gates |
| `## Operational facts worth not rediscovering` | 112-143 | keep verbatim — the `known-red.txt` both-directions rule, the `-DmaxErrors=10000` fact, the four axiom traps, `inferInstanceAs`, the citation gate, the Context/Key census coupling |
| `## Working rules that follow` | 144-158 | keep verbatim |
| **new** `## Owed` | — | a table replacing the prose paragraphs, columns: id, owed item, owing packet, file, landed-in |
| **new** `## Where the history went` | — | one line pointing at `docs/COORDINATION-LOG.md` |

**Moves to `docs/COORDINATION-LOG.md`**: lines 160-2730, 74 landing records, append-only, cited but
not mandatory reading. Two of them are exceptions worth keeping *pointers* to in the live file
because they are still open: `## Open items either agent may take` (`:229-245`) and
`## Coordination: wave 1 landed on 63e6e45; waves 2–5 on hold` (`:2713-2730`).

Also update the root router's authority row for `COORDINATION.md` to name the log file, and add a
`docs/COORDINATION-LOG.md` row.

Two mechanical cautions:

- `scripts/check-internal-citations.sh:59` protects `PLAN.md`, `AGENTS.md`, `ARCHITECTURE.md`,
  `PORT-MANIFEST.md`, `AGENT-ROUTING.md` and `SCHEMA-CUTOVER.md` from line-numbered citations;
  `COORDINATION.md` is **not** protected, so `COORDINATION.md:112` citations exist and will
  silently retarget after the split. Grep for them and re-point at headings in the same commit,
  and consider adding `COORDINATION.md` to the protected list once it is short and stable.
- the split changes `check-internal-citations.sh`'s stamp key (it hashes every scanned file,
  `:132-138`), so the gate re-runs once — expected, not a failure.

### 6.2 Owed items recorded in "Wave 1 of the refactor plan landed, 2026-09-03", verbatim

From `COORDINATION.md:2726-2729`:

> Owed and recorded: H16 remainder (`OpSpec` defaults, five sites), `String.mk` in
> `Trace.lean` with a golden regeneration, `flow-runner.contract.md` lines 13/35 (two refusal
> constructors, four endings), `Interrupt.lean` docstring "four of five", the `_With`-from-
> `_bind` derivation (scope predicate abstraction).

Two further obligations are recorded in the same section as parenthetical owings rather than in
that sentence, and belong in the same table (`COORDINATION.md:2722-2724`):

> `errorTy` is an `Option` (`some`, behaviour kept; the `"never"` → `none` reading is owed to
> the lowering packet), `RegionSafety` ported mechanically through `regionWF_iff_check` (field
> rewrite owed)

And the scheduling fact that gates the whole plan (`COORDINATION.md:2730`):

> Waves 2–5 are on hold until the user says so.

---

## What I could not verify

- **`Effect4Test/Audit/{Declarations,TypeClosure,Cutover}.lean` do not exist.** The real files are
  `Effect4/Audit/Declarations.lean`, `Effect4/Audit/TypeClosure.lean` and
  `Effect4/Audit/Cutover.lean` — all three are 9-line placeholders that declare nothing, and are
  among the 55 stubs of L10. There is no declaration-closure gate and no cutover gate; the
  declaration-closure work is done by the four assurance modules (§2) and the module-closure work
  by `Effect4Test/Audit/AxiomGate.lean:571-586`.
- **`harness/trace/host-pin.json` has no `platform` field**, so I could not assess a
  platform-pin hazard; see §5.2.
- I did **not** run any gate, the sweep, or `scripts/report-effect-runtime-coverage.sh`. The
  coverage counts in §3.1 are parsed from the module source and are not the sanctioned report; the
  handoff that uses them must run the script and paste its block.
- The claim that a Linux `lean` cannot read the Windows oleans in a shared `.lake` is **inferred**
  from the toolchain triple `x86_64-w64-windows-gnu`, not tested — testing it would have destroyed
  the working build.
- Whether Lake accepts a closure-shaped `Effect4` lib (`roots`/`globs = ["Effect4"]`) alongside a
  new `Effect4Meta` lib without a glob conflict is **inferred** from the existing
  `Effect4Test`/`Effect4TestGreen` overlap (`lakefile.toml:17-25`); I did not edit the lakefile.
- I did not measure the elaboration cost of the *whole* `FiberAssurance.lean` before and after the
  inversion, only the cost of one bucketed environment pass (~3.2 s) and of `collectAxioms` over
  Supervision's 297 theorems (~20 ms).

---

## Recommended packet shape

### (a) The L15 inversion packet

**Fence.** `Effect4Test/Concurrency/FiberAssurance.lean`, `scripts/generate-fiber-assurance.sh`,
`scripts/check-fiber-assurance.sh`, `scripts/sweep.sh`, `generated/fiber-assurance.tsv`.
Read-only: `Effect4/Concurrency/*`, the two frozen DAGs, both contracts.

**Size.** Deletes ~1 900 lines of Lean names, adds ~150 lines of TSV parsing and derivation, plus
one row in the sweep table. The TSV is regenerated, not hand-edited.

**Prerequisites.**

1. **First commit, on its own**: add `hermetic|fiber-assurance|scripts/check-fiber-assurance.sh`
   to `scripts/sweep.sh:64-79` and stamp it (inputs: the two scripts, `scripts/lib/*.sh`,
   `Effect4Test/Concurrency/FiberAssurance.lean`, its Lake trace via `stamp_lean_traces`, the
   three frozen DAG/contract/battery files, `PORT-MANIFEST.md`,
   `scripts/check-supervision-evidence.py`, and `generated/fiber-assurance.tsv`). Without this the
   packet trades a `lake build` failure for a gate nobody runs (§2.4).
2. No packet may be open on `Effect4/Concurrency/*` — the derived census is import-sensitive
   (§2.2a) and a concurrent declaration change makes the diff unreadable.
3. Waves 2-5 are on hold (`COORDINATION.md:2730`); this is packet 5 of the plan
   (`docs/research/2026-09-03-refactor-plan.md:110-115`), so it needs the user's word.

**Green before and after.** `lake build Effect4TestGreen`; `./scripts/check-fiber-assurance.sh`;
`./scripts/test-fiber-assurance-gate.sh` (all ten planted defects still rejected — this is the
acceptance criterion, and two of the four Lean mutants at `test-fiber-assurance-gate.sh:70-77`
have to keep failing with the *same* signal strings after the lists are derived);
`./scripts/test-trust-gate.sh`; `./scripts/sweep.sh --hermetic`. `generated/fiber-assurance.tsv`
must be **byte-identical before and after** — that is the proof the inversion changed no fact.

### (b) The coverage-join restructure — recommended, but as its own packet

**Fence.** `Effect4Test/Audit/RuntimeCoverage.lean`,
`scripts/check-effect-runtime-census.sh`, `scripts/report-effect-runtime-coverage.sh`, new
`generated/runtime-coverage-rows.tsv` + its generator, `docs/RUNTIME-COVERAGE.md`.

**Size.** Moves ~1 290 lines of row table to a generated TSV; keeps the 452 ascriptions; derives
`snapshotWitnesses` and promotes the source-order check from shell to Lean (§3.4). Net ~1 400
lines out of the module.

**Prerequisites.** Do it **before** any packet that replaces the `fork.*` witnesses, not after —
otherwise the same 181 witness references are edited twice, once in Lean and once in the TSV.
`docs/RUNTIME-COVERAGE.md:84-111` is the authority for the add-a-witness procedure and moves with
the packet.

**Green before and after.** `lake build Effect4TestGreen`;
`./scripts/check-effect-runtime-census.sh`; `./scripts/sweep.sh --hermetic`; and
`./scripts/report-effect-runtime-coverage.sh` must print **the same block** before and after,
which is the packet's acceptance criterion.

### (c) The structure packet (L27, L10, L53, plus L18 where it is free)

**Fence.** `Effect4.lean`; `Effect4/Semantics/FrameSimulation.lean` →
`Effect4/Runtime/FrameSimulation.lean`; `Effect4Test/Semantics/FrameSimulation*` imports;
`docs/FRAMES-DAG.md`; `test/contracts/frame-simulation.contract.md`; the six essay stubs and their
`docs/` destinations; optionally `lakefile.toml`.

**Size.** L27 is four deleted import lines (`Effect4.lean:47,64,66,115`). L10 is 55 deleted import
lines plus six prose moves. L53 is one `git mv`, one import line, and two doc edits. L18 in the
files the packet already touches only.

**Prerequisites.** Nothing in flight on `Effect4.lean` — it is the most-contended file in the
tree. Keep `Effect4/Meta/` where it is (§4.1): moving it out of `Effect4/` puts it outside
`auditedSources` (`Effect4Test/Audit/AxiomGate.lean:550-557`) and silently disables the source
trust tokenizer for the DSL.

**Green before and after.** `lake build Effect4` and `lake build Effect4TestGreen` (the second is
what proves the module-closure gate still accepts every file after 59 imports leave the umbrella);
`./scripts/test-trust-gate.sh`; `lake env lean --run harness/trace/Generate.lean` (proves the
harness driver still resolves `Effect4.Meta.Derive` and the three families without the umbrella);
`./scripts/sweep.sh --hermetic`.

### (d) The records split

**Fence.** `COORDINATION.md`, new `docs/COORDINATION-LOG.md`, the root router's authority table,
and whatever files a grep for `COORDINATION.md:` line citations turns up.

**Size.** ~2 570 lines move; ~30 lines of new table and pointer; the 47 claim rows are cleared.

**Prerequisites.** Do it when no other agent is mid-packet — the file is the claim channel, and
`COORDINATION.md:146-147` ("Re-read a file immediately before writing it") is exactly the rule a
2 570-line move breaks for anyone holding a stale copy. It is the cheapest item in the plan
(`docs/research/2026-09-03-survey-lean-core.md:452-455` calls it the highest DX return per minute)
and it is independent of every other packet here.

**Green before and after.** `./scripts/check-internal-citations.sh` — it scans `docs/` and will
re-run once because its stamp key changes; a citation left pointing at a moved line is what it is
there to catch. Then `./scripts/sweep.sh --hermetic`.
