# Skeleton-first implementation receipt

In progress on `refactor/phase1-phase3`, base `15cb510e2ea747364e1c814e3a92f1e1ac0075eb`.
The earlier M1 types commit `97e75781` stands. Work continues in the owner's checkout;
nothing is pushed and README.md is outside the edit set.

## Phase boundaries and finishing criteria

The owner's redirect supersedes the earlier M1 receipt's sequencing. Phase A finishes the
data changes and compile maintenance, regenerates LCNF, CAS and the Effect mirror once each,
re-pins position/typing/frame controls, then commits. Placement follows as its own commit;
the imports and module paths must settle before new proof work begins. A successful full
check and the architecture report are required evidence at that boundary.

Phase B extends column generation, then records the world, arena, connector, handshake and
changed M1 statements as named obligations with wanted markers and exact namespace ceilings.
Statements are committed before proof filling. Phase C grows the Stores and TypedState
banks with failing controls, fills in dependency order, and records each module's search
counts and falling ceiling. ParkHandshake stays open for M4. The final full check and the
runtime coverage report must pass; coverage remains 133/135.

The Phase B ceiling is the number of declared obligations. The ledger may already close
some by search and publish their checked proofs without an authored proof body. Every
statement first appears in the wanted snapshot; live wanted markers are removed exactly
when the instrument reports them solved. Counts distinguish open and instrument-proved
goals. Search is not replaced by a deliberately failing tactic to inflate the open count.

Runtime modules retain their local proofs. As the owner approved, their search evidence and
obligations live in the Laws graph; the runtime root never imports the proof tools.

## Phase A decisions and evidence

- The deferred carrier has a defaulted opaque payload parameter. All ten existing operation
  bodies were compared with the base and are unchanged.
- The abandoned historical store copy was 334 lines; it is removed. Refinement now retains
  only Projects and Refines. There is no fallback completion or second observation type.
- This tree's runtime fork alphabet is WithFiberAction; the reference evaluator's is
  FiberOp. Both carry source paths. Source paths enter from the compiler's action Point.
  Race entrants retain the effs-cons path with a cursor advanced alongside the entrant
  list. Internal forks without a source Point have an empty path.
- Origin records provenance; parentOf continues to report the current tracking relation.
  API status and fork inspection read state. Trace extraction belongs to proof diagnostics.
- Memo completion retains its identity update of the memo entry. Removing that update
  changed the behavior of duplicate map IDs; deleting the unused effect field does not
  authorize that additional behavior change.

Completed regeneration counts so far: LCNF 3, CAS 3, Effect mirror 3. The second
completed cut repairs a missing retained Origin type; the third updates the prelude
annotations for the generic deferred store. Both were found by OCaml compilation. Before
the first successful cut, two partial LCNF attempts wrote the smaller cuts and then failed
before completing the API cut; a separate first attempt stopped before any producer ran.
The requested single regeneration was therefore not achieved; these are actual producer
counts, including corrections, rather than a relabeled single logical cut.
No Phase A commit or full check yet. Earlier M1 census evidence remains in
`2026-09-20-m1-evidence`; fresh per-module results will be appended at the phase boundary.

## Clock addition, authorized during Phase A

The owner chose an exact bigint clock while keeping clockNow's number result with explicit
overflow refusal. Large advances use canonical decimal text on the wire. Lean's logical
clock was already an unbounded natural; the change removes fixed-width narrowing in the
clock's generated representation. Ordinary program numbers retain their existing profile.
The stock rc.112 TestClock has number-valued timestamps, so its adapter must refuse an
out-of-profile advance before adjusting time and an out-of-profile sleep before registering
its timer. A continuation awakened by an admitted advance can still encounter a later
refusal; that stops receipt publication, rather than claiming rollback of the stock runtime.
That boundary is separate from the exact clock used by the model and OCaml engine.

Zarith 1.14 was installed in the existing `effect4` OCaml switch for the exact target
carrier. The subsequent auxiliary producer runs are recorded below; the requested runtime cut
has not run yet.

The standalone OCaml clock arithmetic/parser controls and six rc.112 adapter controls pass.
The adapter checks nanoseconds before conversion and checks pending profile refusal even if
a concurrent root has already completed. LCNF controls cover direct construction beyond the
native integer limit, local arithmetic refusal, helper parameters and return values, factory
and callback results, and a value-container route. These finite controls do not establish
unrestricted translation agreement.

The timer, store and handle laws compile with ClockMillis. The handle proof maintenance
generalizes nine shared fork helpers over origin/site, with statements recorded in
OriginHandlesWanted before proof attempts. The final handle build is
`/tmp/m1-phase-a-handles-5.log`; it passed. No new Phase A commit or full check yet.

The exact-clock source is now stable: Data.ClockMillis, Store.Clock and the Laws-side Clock
companion each passed a narrow build. Its ledger closed 28/28 obligations at ceiling 0.
The decoder itself is axiom-free; round-trip proofs and the Canonical instance use only
propext and Quot.sound. The temporary Std string-to-natural proof route was rejected for
Classical.choice and replaced with the checked byte-fold route. The final evidence is in
`2026-09-20-m1-evidence/clock/`.

Clock transport also changes the generated Runner codec and host-protocol schema. Those
producers must refresh before their consumers can build; generated files will only be
written through the existing producers. These auxiliary groups are recorded separately
from the requested single LCNF/CAS/Effect cut.

Timer frontiers expose exact ClockMillis deadlines too. The owner's number-valued exception
applies to clockNow; silently narrowing frontier deadlines would undermine the exact clock.
Api.Frontier passed its narrow build. Its Api codec is the second auxiliary derived group,
alongside Runner. The host-protocol schema is a third auxiliary producer.

Auxiliary generation completed once each: Api and Runner through Effect4Gen's existing
Driver command descriptions and Main producer, followed by narrow builds and projection
checks; HostProtocol through its existing producer. All passed. Logs are in
`/tmp/m1-derived-bootstrap/` and `/tmp/m1-host-protocol-generate.log`.
`bun test harness/truth/session/keyed-protocol.test.ts harness/truth/session/clock.test.ts`
then passed 20 tests with 58 assertions, including canonical advances beyond host integer
ranges. LCNF, CAS and Effect regeneration counts remain zero.

The pre-maintenance census attempt for Guard.Single and Guard.OuterDriver could not load
the mixed old/new compiled tree: after restoring Api.Derived, it reports a duplicate
registerRace equation from old Guard.Interruption and rebuilt Clauses. This is failed
elaboration, not census evidence. The six clock statement changes have wanted snapshots;
their old proof bodies are untouched at this point. Fresh counts will be labeled as such.

The Simulation chain now compiles through Actions. A fresh Fibers census before the next
origin repair closed 4/95 statements; those four proofs were replaced by the searched proof.
The generalized pendingOk_make first failed with the Stores bank alone. Registering the
PendingOk definition and the constructor's empty-pending equation closed it on retry. Its
statement and wanted marker were saved first in PendingOriginWanted.lean. The final Fibers
and Actions build logs are retained in the evidence directory. This is Phase A compile
maintenance; the final-path skeleton and its full ledgers remain Phase B work.

Simulation.Evaluate and Simulation.Drive now pass their narrow builds. Pending required
four site-generalized helper statements; their wanted snapshot preceded proof attempts.
The first unrestricted searches exposed expensive unfolding. Registering the existing
start_pending equation lets each fork helper search after exposing its answer premise.
The new Pending before-census could not import a missing compiled module; that failure is
retained as non-evidence, and its later census will be labeled as a maintained-tree count.

## Keyed clock wire identity correction

The coordinator authorized protocol version 3 on 2026-09-20 after the clock boundary review.
Version 2 had numeric `advanceClock.millis`; the exact-clock change made that field canonical
decimal text. Keeping the same version would give two incompatible record shapes the same
identity. The current Lean protocol and keyed readers, recorder and tests now use version 3,
format `effect4-host-session-v3` and profile `keyed-v3`. The numeric version remains owned by
`HostProtocol.hostProtocol`; the TypeScript recorder reads its generated projection.
Version 2 input is refused explicitly. Legacy recordings and their readers are unchanged;
this correction adds neither implicit migration nor a number-or-string admission branch.
DB-14 records the version ruling.

New controls reject version 2 headers and version 2 clock records, including a decimal
payload placed under an old record version. The current Lean session battery also pins
version 3 and rejects a version 2 header. The coordinator's narrow HostProtocol build and
second auxiliary HostProtocol generation passed; the generated table and schema both name
version 3 and describe milliseconds as canonical decimal strings. The coordinator also
added the missing `clockMillis` branch to the Lean record preflight, before consumption.
Direct Lean `Keyed.lean` elaboration remains a separate coordinator check.

After that refresh, `bun test harness/truth/session/keyed-protocol.test.ts
harness/truth/session/clock.test.ts` passed 23 tests with 63 assertions. The run includes
explicit version 2 header and record refusals, exact transport above both host integer
ranges, and rc.112 refusal before an overflowing adjustment or deadline mutates the timer.
Logs are `/tmp/m1-host-protocol-v3-generate.log` and `/tmp/m1-host-protocol-v3-tests.log`,
with retained copies in `2026-09-20-m1-evidence/`. Completed auxiliary counts are now Api 1,
Runner 1, HostProtocol 2; the second protocol run is the explicit wire-version correction.
Requested LCNF, CAS and Effect cuts remain at zero at this point.

Phase A state controls are pinned from fresh output: 85 positions from four roots and 94
source rows; 16 generated predicates and 11 carrier predicates, with two explicit refusals.
RunFiber frames report 16 checked rules, 87 reused clauses and nine premises; the other
records report 44 rules, 77 reused clauses and 31 premises. The generated origin update
requires no new value-typing premise, while changing id retains its three dependent clauses.
Typed.State, Typed.Frames and Test.Audit.PositionCensus passed with those pins.

Pending's four site-generalized helper proofs compile. Its attempted early ledger exposed
expensive normalization of the higher-order answer premise, and a norm-apply experiment
was invalid because it produced multiple goals. Those failed probes are not proof evidence.
The three outstanding search markers remain; the namespace ceiling will be pinned with
the final-path Phase B skeleton, rather than pulling more bank work into Phase A.
The final successful source build is simulation-pending-site-build.log.

Version 3 also passes the Lean HostSessionContract and KeyedHostContract batteries and
direct elaboration of harness/truth/session/Keyed.lean. The latter includes the new
clockMillis scalar validator branch before record consumption. HostSession's searched
proofs needed their Laws-side tactic import; the runtime graph remains independent.

Guard.Single and Guard.OuterDriver now pass their narrow builds with one compiler thread
and warnings treated as errors. The maintenance restored seven previously truncated
clock obligation captures to the complete theorem conclusions, aligned Single's timer
helper parameters with completion data, and mapped those values through completionPrim
before embedding them. Their existing proof strategies did not need further changes.
The wanted snapshot preceded the builds and is retained as
`2026-09-20-m1-evidence/GuardClockMaintenanceWanted.lean`; it is a statement capture,
not a separately elaborated proof file.

The first successfully loaded census for these modules closes 0/34 statements in Single
and 0/36 in OuterDriver with plain aesop. These are maintained-tree counts, not a recovered
pre-edit baseline. The earlier failed import attempts remain non-evidence. The successful
commands were `LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.Guard.Single`, then
the corresponding OuterDriver build, then `lake env lean -DwarningAsError=true` on
`GuardClockMaintainedCensus.lean`. The build and census logs are retained in the same
evidence directory. No new bank-filling work or final-path ledger was started here.

The remaining store, scheduler, run, typed-state and frame-rule controls passed narrow
builds. The bank-negative CompletionData fixture was re-pinned to the explicit default
payload in Lean's diagnostic; the bank still closes its positive counterpart while plain
aesop fails. Agreement.Machine needed one additional completion payload binder repair,
recorded first as M1Quiet.complete_quiet with its wanted marker; its existing proof compiles.
The runtime coverage census gate passed, followed by the fresh sanctioned report:

```text
Effect rc.112 runtime coverage: denominator 135; owned-with-green 8/135;
green 133, partial 2, absent 0; census 137 rows, 2 excluded
partial: op.Failure layer.launch-holds-scope
produced at 15cb510e (working tree has uncommitted changes) by scripts/report-effect-runtime-coverage.sh
```

The search-budget review found that ProofGraph.search updates maxHeartbeats in the
options but does not update Lean 4.33.1's cached Core.Context limit. Existing successful
proofs remain kernel checked, but historical search counts cannot be labeled as running
at the requested smaller cap. The focused correction and finite controls are prepared
for Phase B's instrument slice; no budget is being raised.

The first `make gen-lcnf` attempt stopped in its full-build prerequisite, before any
producer ran. It exposed LayerSharing's two obsolete memo-field writes and HandlesContract's
race/completion fixture shapes. Those repairs each passed their own narrow build. The
CasGoldens producer was scouted ahead, repaired for the four-field memo entry, and passed
a narrow build before its generation turn. RuntimeRShapesContract and TestClockContract
also passed. The producer wrapper now requests one module per Lake call and the outer
make runs with LEAN_NUM_THREADS=1. A process inspection during the full build confirmed
one active compiler (the editor's separate idle language server was left alone).

The resumed full build passed: the root/axiom gate checked 458 modules and 65,456
declarations; runtime root reachability remains separate from Laws. The complete derived
producer then ran once, including a second Api and Runner projection (byte-identical to
their bootstrap output). Auxiliary totals are Api 2, Runner 2, HostProtocol 2.

The first runtime cut then wrote fibers_gen and machine_gen, but the API cut refused
unknown higher-order Nat provenance at clock ingress; api_gen and api_engine were not
written. This is a failed partial generation, not a completed regeneration. The clock
analysis had conflated internal callbacks with untrusted producers; a separate callable
provenance analysis is being prepared, retaining the unknown-callback and narrowed-value
negative controls. LCNF completed cuts: 0; partial attempts: 1. CAS and EFF remain 0.

The refreshed statement inventory counts 151 changed and 34 new explicit theorem
headers against the redirect base. It identifies 32 manual live-ledger gaps for Phase B,
plus two producer-generated clock lifts. Four live-covered statements have no matching
retained pending snapshot; the old Links.beginRace snapshot also omitted its supplied site
while the live checked statement includes it. These are recorded evidence gaps, not
retrospectively repaired provenance. Phase B must freeze the exact current statements and
add the missing live entries before further proof work. The inventory lives beside the
census evidence, with file/name-level details.

The API LCNF cut exposed 22 clock-analysis refusals caused by unresolved internal callbacks.
A source-only closure probe reproduced them. Callable origins now follow helper arguments,
constructor fields, partial applications and scoped returns; genuinely unknown callbacks
still refuse, and an unfinished origin fixed point refuses explicitly. A checked negative
control caught a missing return-risk link in the first candidate: a known callback returning
a narrowed natural was accepted. That link was repaired before the final checks. All 18
finite lowering controls pass, including that negative case and the original unknown-function
controls. The actual Api.run/Api.replay closure now checks 664 declarations with zero missing
declarations, frontier or todos. Exact source hashes, the rejected-candidate log, final logs
and probe input are retained in `2026-09-20-m1-evidence/clock-callables/`. This correction ran
no producer and made no generated-file edits; generated OCaml validation remains the next
boundary. The coordinator resumed the canonical LCNF producer afterward.

The next canonical `make gen-lcnf` attempt passed its build and rewrote the fibers and
machine cuts, but the full API producer reached its existing 200000-heartbeat limit during
`whnf`, before writing the API artifacts. The successful 664-declaration translation probe
covered only translation, not the producer's subsequent type generation and collision
passes. This is the second partial LCNF attempt; completed LCNF/CAS/EFF counts remain zero.
The source of the extra work is being measured before another attempt; no limit or gate
has been weakened. The failed command is retained in `/tmp/m1-phase-a-gen-lcnf-3.log`.

The TypeScript boundary review reproduced two recorder defects: an advance was recorded
after the calls it enabled, and an advance could resolve successfully after an awakened
continuation hit an overflowing sleep. Recording now occurs inside the serialized clock
adjustment, after preflight and before waking work. A post-adjust refusal is checked and
latched by the recorder, which then refuses receipt publication. Preflight failures record
no attempted decision; failures after execution begins retain attempted-decision ordering
without claiming stock-runtime rollback. Four integration controls were red before repair.

The provided clock service also exposed the stock TestClock's unchecked mutation methods
through object spreading. It now forwards only rc.112's six Clock readers and checked
sleep. Two controls first failed, then verified that TestClock.adjust/setTime are unsupported
through that service and leave time unchanged. The host-protocol check now runs clock.test.ts
alongside its existing tests. Final Bun result: 42 tests, 179 assertions, zero failures;
session TypeScript checking and whitespace checks pass. Exact commands/results are in
clock-host-boundary; this is host-only finite evidence, with no Lean or generation run.

The full-driver timeout is now diagnosed and repaired without changing or resetting its
200000-heartbeat budget. Pure callable analysis had consumed 566805 heartbeats before the
next type operation checked the limit; the earlier closure-only probe never reached that
check. A finite fact worklist replaces repeated whole-graph scans, and carrier inference
validates its final settled closure once through the same public checked boundary. The
engine also exposed cross-export contamination: a generic comparator's uncertain result
entered the concrete interpreter through a shared helper. Clock-reaching roots and their
complete available flow union now retain all opaque inputs together; unrelated exports
without a clock boundary do not seed another export's shared parameters. No export was
removed. All 22 finite controls pass, including the two final-inference and two mixed-root
checks. Exact no-write full-driver diagnostics pass both flat API (124584 heartbeats) and
engine with its actual externs/prelude (158907), including type collision passes, manifests,
module checks, extern ledger and rendering. Evidence and source hashes are in
`2026-09-20-m1-evidence/clock-budget/`. This seat ran no producer and wrote no generated
artifact; completed runtime-cut counts are unchanged by these diagnostics. The compiler
lease was returned for the coordinator's canonical cut.

The canonical `LEAN_NUM_THREADS=1 make gen-lcnf` run now passes in full. Its four artifacts
and closure manifests were written by their producer, including both API variants. The
producer wrapper now enforces warnings-as-errors on its direct Lean invocations; the
budget stays unchanged. This is completed LCNF cut 1 (two earlier partial cuts and one
pre-producer build failure remain recorded above). CAS/EFF generation follows through
the canonical Make dependency order. Log: phase-a-gen-lcnf-final.log.

`make gen-cas` passed, running the Effect mirror, wire manifest and CAS producer in
dependency order. The separately requested `make gen-eff` then passed without invoking
the producer again. Completed data-cut totals are LCNF 1, CAS 1 and EFF 1, with the earlier
failed/partial LCNF attempts counted separately. Host and OCaml execution gates follow.
The generated api_engine file retains its producer's existing indentation on blank lines;
`git diff --check` flags those newly added generated lines. Generated bytes are not trimmed
by hand. Handwritten source whitespace is checked separately.

The first fresh OCaml build found that the generated engine omitted Origin's constructors:
its only construction callers were replaced by external implementations, so type pruning
left a placeholder. Origin is now an explicit retained type in the existing generation
manifest, and the manifest is a Make dependency of LCNF. No generated file was edited by
hand. The corrective `LEAN_NUM_THREADS=1 make gen-lcnf` and `make gen-cas` both passed;
the latter also ran the Effect mirror and wire producer. Actual completed totals are now
LCNF 2, CAS 2, EFF 2 and wire 2, in addition to the failed partial attempts above.

The fresh host-protocol gate passed 57 replay runs over 52 programs, with 30 negative
controls, and its 42 host tests passed 179 assertions. The cases gate also passed.
Commands were `LEAN_NUM_THREADS=1 python3 scripts/check-host-protocol.py` and
`LEAN_NUM_THREADS=1 make check-cases`. These are finite host/protocol evidence and the
policy-case gate, respectively; neither substitutes for the pending full `make check`.

The next OCaml build exposed three stale handwritten prelude annotations: DeferredStore
is now parameterized, so the helpers take `_ deferred_store`. Before another producer run,
a temporary full generated candidate with exactly those three template changes compiled
against the abstract target interfaces. Its embedded prelude matched the current source
template; no tracked generated file was edited. The isolated seam gate now explicitly
loads both E4_clock.mli and the already-used E4_nat.mli, without implementations or carrier
instances. Candidate compilation is diagnostic evidence only; canonical output is still
required for the execution tests. The template correction is undergoing canonical generation.

The canonical template correction passed (`make gen-lcnf`, log gen-lcnf-6; then
`make gen-cas`, log gen-cas-3). Completed totals are LCNF 3, EFF 3, wire 3, CAS 3.
The full generated engine candidate and the canonical output both carry the same corrected
prelude. Fresh OCaml execution is now in progress.

Phase A's fresh OCaml validation passed: the full Dune build, exact clock controls,
generated-reference smoke tests, engine (80 checks), query (21), checkpoints (107),
differential test driver (32), and generation seam checks C1–C4. The finite differential
run covered 472 programs, 2960 tapes and 65712 positions: 131424 projection comparisons,
zero divergences, zero profile-refused or raised tapes. Profile refusals and exceptions are
now counted separately from successful comparisons; nine finite classification controls
exercise this distinction. Exact commands, exits and hashes are in
`2026-09-20-m1-evidence/phase-a-final/m1-ocaml-checks.json`.

Phase A is ready to commit. The full Lean build and axiom/root audit passed before runtime
generation; subsequent changes to the generation manifest and OCaml prelude were verified
by their canonical producers and the fresh OCaml checks. The requested full `make check`
remains the placement boundary's gate. Handwritten whitespace is clean; the generated
engine's existing blank-line indentation remains a recorded producer formatting caveat.
No README edit or push occurred. The 334-line legacy file was an abandoned untracked
candidate: its removal is an actual file deletion, not a claimed 334-line Git deletion.
The open Phase B skeleton and its evidence gaps remain as listed above.

Seven verbose generation/build logs are retained as deterministic gzip archives beside
their small text indexes; large-log-archives.json records raw sizes and SHA-256 hashes.
This preserves exact diagnostics without repeating about seven megabytes of build replay
in the textual commit. Census and obligation sources remain plain text.

## Phase A landing and placement

Phase A committed as `8b64039f` on `refactor/phase1-phase3`; nothing was pushed.
The placement plan was refreshed against that commit and applied afterward. It moves
47 files (40 handwritten and seven generated), splits the six checker/fold connector laws
from the runtime projection theorem, and extracts two shared test fixtures. Declaration
names and existing proof bodies are compared by the placement script; runtime code is
unchanged. The 11 affected derived groups are regenerated through their canonical producer.

The aggregate projection check exhausted its unchanged 200000-heartbeat cap after the
11 selected outputs had individually been generated and built. The same Canonical checker passed separately on its seven applicable outputs, retaining
the cap and all comparisons. It refused TyView because that output is not a Canonical
ShapeDoc; that invocation was a tool-applicability mistake, not projection evidence.
TyView, ValFold, Forms and FormsLaws use their own producers, exact declaration/proof
fingerprints, narrow builds and embedded guards, all of which passed. Old generated
paths are removed after these applicable checks pass. This changes the orchestration granularity,
not the checked projection or its budget. The failed aggregate log is retained.

The placement narrow checks now pass at all 68 planned entries. A repair moved the new
Laws imports into the leading import block; no proof body changed. The complete build
required by architecture generation subsequently ran Test.All's actual root/axiom audit:
138 runtime modules, 192 Laws-only modules, 459 audited modules and 65386 declarations.
Semantic/test dependencies remain [propext, Quot.sound]; the unchanged exact implementation
boundary contains 14 modules and 29 declarations allowed Classical.choice. The architecture
producer reports 553 Lean modules and zero imports against the declared direction, down
from the retained report's 26. Placement comparison and per-module evidence live in
`2026-09-20-m1-evidence/placement/`; the full check is still pending at this point.

Canonical placement validation found two additional mechanical issues. Direct execution of
the authoring generator now treats warnings as errors and exposed two unused parameters;
commit `f7d22703` renames those parameters separately from placement. The wire driver kept
a dynamic import of the old module path; its import now names Domain.ProgramWire. The
completed repair ran derived, EFF, wire, CAS, TypeScript and generated ingest documentation,
then the corpus producer. The changed target files differ only in provenance paths. The
corpus command now explicitly treats warnings as errors; a fresh temporary run produced
the identical index (408 kept, 385 readable, zero refused). No runtime LCNF producer ran
during placement. Cumulative completed runtime counts are LCNF 3, EFF 4, wire 4 and CAS 4;
one failed full-derived attempt and one failed wire attempt are retained separately.
Exact compressed logs and counts are in `2026-09-20-m1-evidence/placement/full-check/`.

`LEAN_NUM_THREADS=1 make check` passed at the placement boundary: the full build, fresh
Test.All root/axiom audit, and generated-file drift gate are green. The check invoked no
additional group producer. The same 459-module / 65386-declaration trust counts were
measured by the fresh audit, not inferred from replay output. A read-only audit of all
47 moved module names found no remaining executable stale module reference. Declaration
names and proof bodies are retained. Root README.md is unchanged; nothing was pushed.
Phase B's corrected-cap census and statement ledgers have not run yet.

## Phase B installation

Placement committed as `05417cc6`; its preceding warning-only correction is `f7d22703`.
The new heartbeat control failed against the old search wrapper specifically because
the cached Core heartbeat limit stayed unchanged. With Search updating that cache, the
control and existing ProofGraph/Obligations controls pass. The control verifies requested
and cached caps, zero/unlimited mode, state rollback after success and forced timeout,
and a fresh subsequent search. Its published theorem has no axioms. The old-cap census
counts remain historical; the new baseline will use the corrected 20000 cap, and ledgers
their corrected 40000 cap. No budget was raised.

The manual 32-entry ledger package, indexed-column/Expect instrument and 97-entry main
statement package are installed. The main package has 96 active entries and one held M4
entry; Expect adds a separate active entry. These are declaration counts, not proof results.
World and its two leaf predicates reuse Columns.Stores_refs and Columns.DeferredStore_cells
from the generator. The retained snapshots precede Phase C fills; they do not repair the
historical Phase A before-proof evidence gaps documented above.

The corrected column producer now compiles, including explicit List Nat columns that
the value census does not visit; a constructor-field check also handles a parameterized
nested record. Four positive shapes and five refusal controls pass. Its two new projection
seats make twelve indexed-control obligations. Actual generated counts are 17 predicates,
12 carrier predicates, two refusals; position coverage remains 85 positions with 95 source
rows. Frame generation gives unchanged RunFiber 16/87/9 and remaining records 46 checked
theorems / 90 reused clauses / 27 explicit premises, including DeferredStoreOk.

All statement-only semantic modules, including World, ForkSource, trace/origin seats and
the held handshake, have compiled. The complete Laws root passes with the corrected
search budget and the existing zero ceilings unchanged. The fresh static ledger inventory
contains 311 task statements: 169 prior + 32 manual + 97 main (including one held) + one
Expect + 12 indexed. It separates six intentional audit fixtures. Its 54 complete scopes
need 36 additional gate sites beside 19 existing sites (one prefix has two checkpoints).
No proof fill or new gate is installed yet; the fresh census and measured open counts follow.


The first corrected-cap census ran across 218 modules and reported 648 closures out
of 4062 statements; 647 passed its axiom scan. These figures are retained as provisional,
not portable-proof evidence. The following status pass found that a searched proof referred
to a temporary spawn splitter removed by rollback. A minimal independent control reproduced
that defect. The status pass stopped before any valid complete scope or marker removal.

Search now expands temporary definitions and theorems into the returned proof, checks the
exact requested proposition synchronously against the original checked kernel environment,
and rejects unavailable dependencies. Temporary axioms and unsafe definitions are refused.
The closure and kernel check share the search attempt's original heartbeat cap and origin;
dependency expansion uses the existing recursion-depth limit. Axiom checking covers both
statement and proof before publication. The finite controls pass, including polymorphic
helpers, rollback, wrong-type assignment, missing constants and a forbidden dependency only
in the statement. One control syntax-hygiene error was corrected before the successful run.
Exact source/log snapshots and commands are retained in phase-b/search-portability. The
full rebuilt audit and a fresh portable-proof census remain pending at this point.


The repaired-tool full build passed (`LEAN_NUM_THREADS=1 lake build Test.All`):
469 modules and 66144 declarations, 138 API/utility and 198 Laws-only modules.
All sources remain reachable, and the runtime root never imports Laws. The semantic/test
axioms remain [propext, Quot.sound]; the exact implementation exception remains 14 modules
and 29 declarations. The refreshed search-portability archive retains this fresh log,
command and exit code alongside the previous unit-stage evidence. The new 218-module
census is running separately; none of the provisional closures are counted into it.


The fresh portable-proof census completed: 218 modules, 139 serial calls, 648 closures
out of 4062 statements; 647 are within [propext, Quot.sound]. The original 38-module radius
is 247/1584. Every candidate passed the exact-proposition kernel check. The one rejected
candidate remains path_beq_self (Classical.choice). The closed name set matches the
provisional run; seven recorded dependency lists gained permitted axioms after temporary
helpers were included. The corrected table, every raw report and frozen input are retained
losslessly in phase-b/portable-census. The earlier run remains provisional history.

The complete status pass measured the 221 statements requiring new gates at cap 40000:
48 closed, 173 open, zero rejected. Together with the 90 distinct statements covered by
existing zero gates, the skeleton accounts for all 311 task statements. One open statement
is the held M4 handshake, leaving 172 active open statements for Phase C. Exactly 47 wanted
markers were removed from checked closures; the remaining closed statement already had no
marker. No proof body changed. The 36 new gates keep ceiling=N (their statement counts),
and all 19 existing zero gate sites remain byte-for-byte unchanged. Their serial owner
builds are running. Nonterminal search diagnostics can be the generic open-goal message;
Phase C proof probes must inspect the actual residual goals before adding support facts.

A copied unusedSectionVars suppression in Refinement had no justification and was removed.
The narrow Refinement build passes with that warning check enabled. This option-only cleanup
followed the completed census; it changed no statement or proof body.


All 30 gate-owner builds passed. Each owner has a fresh Built line and its own emitted
report; none is a replay-only confirmation build. The 36 scopes exactly match the status
pass: 48 proved, 173 open, 221 statements, ceiling=N. M4 remains one open statement at
ceiling 1. The status and gate packages are separate, with failures and the applied
marker-only patch retained. Phase B's `make check` is now running. Both sanctioned
coverage scripts now pass `-DwarningAsError=true` to their direct Lean calls; their shell
syntax check passed, and the fresh coverage commands will run after the full check.


Phase B's `LEAN_NUM_THREADS=1 make check` passed: the fresh Test.All audit checked 469
modules and 66145 declarations, with the same root and axiom boundaries, and the generated
file drift gate passed. No group producer ran in this phase's check; the cumulative runtime
producer totals remain LCNF 3, EFF 4, wire 4, CAS 4. Both sanctioned coverage commands passed
with warnings treated as errors. Their exact report is retained with the full-check evidence:

Effect rc.112 runtime coverage: denominator 135; owned-with-green 8/135;
green 133, partial 2, absent 0; census 137 rows, 2 excluded
partial: op.Failure layer.launch-holds-scope
produced at 05417cc6 (working tree has uncommitted changes) by scripts/report-effect-runtime-coverage.sh


All 311 statement seats and their gates are now installed. Phase C has not begun: no manual
proof body was changed by the marker/gate patch. The corrected before-fill census and
source snapshots are retained for the per-module searched rewrites and bank comparison.
README.md is unchanged; nothing has been pushed.


The staged whitespace check is clean for source and prose. Two retained evidence formats
are excluded from that formatting-only check: build-results.tsv preserves an empty final
column, and reviewed-live-diff.patch preserves blank diff-context lines. Their original
bytes and checksum manifests remain unchanged; no repository build or trust gate is relaxed.
