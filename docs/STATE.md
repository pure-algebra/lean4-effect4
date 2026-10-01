# State of the work

One page: what is true at HEAD, where the current documents are, what is next, what the owner
must decide. Replaced at every landing; history is `git log` and `docs/research/`.

## What this is

An agent-first language of algebraic effects whose engine is reified in Lean. One machine,
three faces: Lean proves it (the reference, the machine, the certificates), OCaml runs it
natively (the same machine compiled through LCNF), TypeScript interoperates with the Effect
ecosystem (the printer and readers). Programs are data: a canonical `Eff` tree with a digest,
a computed typing certificate, folds, a journaled run with replay, and a printed image that
reads back.

## Current milestone (2026-09-23; the milestone is M5–M7, system map §3)

Phase A, placement, the Phase B skeleton and the Phase C fills of the skeleton-first redirect
are landed; the phase-by-phase account is
`docs/research/2026-09-20-skeleton-first-receipt.md`, the review of that landing is
`docs/research/2026-09-20-codex-landing-review.md`, and the close of Phase C with its numbers
and its open residue is `docs/research/2026-09-20-phase-c-close-receipt.md`. Its historical
65 gate reports / 393 counted statements / 351 closed / 42 open include repeated scopes;
they are not a count of unique obligations. The banks are `Effect4.Stores`,
`Effect4.StoreKernel`, `Effect4.Fibers` and `Effect4.TypedState`.

The current foundations review and proposed execution plan is
[`docs/core/post-phase-c-synthesis.md`](core/post-phase-c-synthesis.md), checked against
`10d5c009`. A retained Lean counterexample refutes the former `M1Origin.actionAt_raceAll`
statement because it omitted the source-location premise of its backing theorem. Slice 1
restores that premise and checks the backing proof; no false theorem was accepted. The review also found that the then-generated resume checks
ignored target/token and capture checks ignored source path/root, and identified the missing
shared type between current code and its saved stack. Slice 2 now states these correlations;
connecting them to reachable execution remains the main typed-state proof.

Slices 1 and 2 are merged at `2bcb99ff`; slices 3 and 4 (Codex, `codex/foundations-slices-3-4`,
head `ef38bf11`) are fast-forwarded onto this branch at the commit carrying
[`slices 3–4 review and the FR-08 ruling`](research/2026-09-21-foundations-slices-3-4-review-and-fr08-ruling.md).
Slice 3 landed exact world validity, allocation/token freshness, external spelling transport,
completion transport and `park_extension`
([receipt](research/2026-09-21-foundations-slice3-receipt.md)). Slice 4 landed the independent
D12/C2–C4 foundations ([receipt](research/2026-09-21-foundations-slice4-receipt.md)) and the
M3a residual: strong values/exits, D13 source admission, control admission with marker
payload inversion, `Ψ_S` over the 31 `SyncOp` rows, `Ψ_F` over the 40 `FiberOp` rows under
`#answer_gate`, concrete `TypedProg`, and the two settling cases
([receipt](research/2026-09-21-foundations-slice4-m3a-receipt.md)). The review's once-over
lists what those landings left as `True` (most `Ψ_F` rows, the hook contracts) and what was
not declared (the M6 adequacy obligations); slice 5 is briefed to fill or name each.

The brief's interrupt repair was refuted by Codex's preflight
([amendment](research/2026-09-21-foundations-contract-preflight-amendment.md),
`E4-SCHED-CE-006/007`). The coordinator then showed the refuting state is **source-reachable
and is rc.112's behaviour**: `catchAll(uninterruptible(await >> fail 42), _ => succeed 0)`
checks at answer `nat`, error `never`, and exits `Fail 42` on the frame machine, the term
evaluator and the pinned vendor source when an interrupt is recorded during the masked
region (`E4-SCHED-CE-008`, `Test/Counterexamples/Machine/Semantics/InterruptEscape.lean`,
evidence in `research/2026-09-21-foundations-fr08-evidence/`). A re-masked walk runs a
`nat`-typed catch on a string and dies with the bad-shape defect from defect-free source.
The owner ruled the same day (ruling §4): the machine does **not** adopt the regression. At
a preempted skip of a catch that would have run, both walks pass on the failure stripped of
its `Fail` reasons and combined with the recorded interrupt, which is Effect 3's rule; this
is a signed divergence, `U-01` in [`docs/UPSTREAM-BACKLOG.md`](UPSTREAM-BACKLOG.md). The planned typed-state statements have no run premise; their proof is still open.

The divergence landed at `5f33fe3c`, with its receipt and evidence at `7c3b62ea`, and was
fast-forwarded onto this branch on 2026-09-23 after the
[once-over](research/2026-09-23-foundations-divergence-integration.md). The approved CE-009
amendment carries the sanitized cause through the compiled walk and its three consumers.
The unchanged runtime agreement statements remain at `[propext, Quot.sound]`. The receipt
records green `make check`, `check-ocaml`, `check-truth` and `check-census`; the once-over
verified the retained evidence hashes and reran the exact-exception controls. The unique
production ledger was 342 total, 333 proved, 9 open on 2026-09-21 (the architecture map measures
the ledger at HEAD: 403 declared, 370 proved, 33 open over all roots at `dceae006`).

[Foundations slice 5](research/2026-09-21-codex-brief-foundations-slice-5.md) was retargeted to
`fc638550`. Its preflight stopped on three checked admission counterexamples, retained at
`2a00ce29` with the [stop receipt](research/2026-09-21-foundations-slice5-receipt.md): a
checker-typed `sleep(1)` reached a cleanup stack the frozen contracts refused. The owner
approved the [contract ruling](research/2026-09-23-foundations-slice5-contract-ruling.md) on
2026-09-23 and the coordinator landed it. The async hook takes the incoming typed failure; the
guard row certifies its intermediate type; `TypedProg` is one inductive judgment that shares
each operation's certificate and types a guard's body at that type, and the old separate
control judgment is retired; the R3 frame contract and the concrete hook protocols are in
place. The exact reachable sleep stack is now accepted, and the three old contracts stay
refuted in the counterexample file. A wider finding is recorded for M6: every fiber row whose
answer feeds a leaf under a `True` post makes its programs untypable, so those posts are stated
with the M6 declarations. The typed-state modules now layer as the world, validity, admission,
then the residual protocols, with the stack contracts a parametric interface only the residual
module instantiates. The regenerated [architecture map](core/architecture-map.html) found three
upward imports that arrived after 2026-09-20 (the answer gate, the trace-origin obligations and
the protocol ledger file); all three are repaired, so the map shows no import against the
declared direction beyond the two accepted ones, and no pair of areas importing each other. The production ledger was unchanged then at 342 total, 333 proved, 9 open. Slice
5's stack and delivery proofs, assembly and M6 declarations remain Codex's, on the recorded head.

The five chat rulings of 2026-09-20 (rows 20, 48, 51, 52, 79) are written into
`decisions.md` as of 2026-09-21. The Codex packet that sequences the divergence slice and
slice 5, with every tracking item's end state, is
[`codex packet: divergence and slice 5`](research/2026-09-21-codex-packet-divergence-and-slice-5.md).

**Slice 6 (2026-09-30).** Three of its four items are landed on this branch: the five source-site
connectors and the observation erasure (`40e3bfa3`), the memo write-back deletion (`be15b062`).
The last, the trace agreement, is to hold by construction: the fork record moves from the fiber to
an append-only list on the machine that only `spawn` writes. The plan,
[`origin ledger and step invariants`](research/2026-09-30-origin-ledger-and-step-invariants-plan.md),
is reviewed three times and its decisions are rows 91–94. The ledger landed on 2026-10-01 (Codex
item C, merged at `bc77e97f`): every reader moved, the old field and the comparison runner retired
together, the engine regenerated. The trace agreement through it landed the same day (item D,
merged at `9ad8a7c0`, rows 93–94). Slice 6 is complete.

**Foundation completion (2026-09-30).** The same reviews, and a probe of the external-reply lane,
found three things:
- M6's capstone is false as written: a `sleep` answered with `42` finishes with `42`.
- The proof's value predicate checks nothing inside pairs, Results or successful exits, and a
  closed program exercises that.
- The runtime's reply check admits a fiber handle of the wrong type on the live host session.

The Codex contract proposes, and the coordinator recommends, that the external-reply lane
belongs to the foundation's completion (row 99, open). On the owner's word to consolidate, the
documentation is cut over:
- [`system-map.md`](core/system-map.md) is the frame: the goal, the ten layers with their owners
  and status, the sorts and arrow kinds. It replaces `ontology.md`, whose dated sections are
  history.
- [`host-boundary.md`](core/host-boundary.md) is the authority for the lane.
- `machine-state.md` §7 holds the six storage interfaces.
- `lcnf-route.md` §8 holds the compilation stages and the number policy.
- The open choices are decisions rows 95–101.
- The [architecture map](core/architecture-map.html) is regenerated from the tree.

**Right-sized by the owner the same day:** the route stands (`system-map.md` §1, §3).
- **Near term:** slice 6, plus three bounded fixes: rows 95, 96, and 97's interim rule.
- **Then:** M5–M7.
- **Then expansion on the proven route:** queues first, ergonomic run APIs, MCP authoring after
  LCNF, and WASM through the generated OCaml.
- **Parked until needed:** the full host-services contract.

**The design pass, finished the same day.** Five seats probed the design, and a verifier attacked
each one ([synthesis](research/2026-09-30-pass/synthesis.md)).
- **What holds.** Three building blocks: a fiber's declared type computed from where it was forked,
  the `Fits` judgment, and the generic step lifts.
- **What is false.** M5's and M6's statements, even on programs that use no host:
  - two layer typing gaps let a checked program finish outside its type, through the live API;
  - the value judgment cannot type `Ref.make(5)`;
  - M6's queue fact accepts a resume for a token not yet made.
- **The fixes.** The bounded repairs are rows 104–107, with row 96.
- **Numbers.** One checked program gives three different answers on Lean, OCaml and TypeScript
  (row 108).

**Implementation, go-ahead the same day.** Codex holds the near term in its own worktree
(`/Users/pooks/Dev/lean4-effect4-slice6`, branch `codex/slice6-fixes`) by the
[slice 6 brief](research/2026-09-30-codex-brief-slice6-and-fixes.md):
- A: host rows and replies carry no internal handle (`E4-HOST-CE-007`);
- B: M6 counts runs with no host answer (`E4-SCHED-CE-015`);
- C: the fork ledger's runtime steps.

[Addendum 1](research/2026-09-30-codex-brief-slice6-addendum-1.md) amends A–C after the pass:
- one test fixture changes on purpose;
- the failure-arm change is withdrawn;
- M6's restriction is necessary but not sufficient;
- the eight silent site defaults go.

The owner ruled rows 96, 104–107 and 110 the same day.
[Addendum 2](research/2026-09-30-codex-brief-slice6-addendum-2.md) gives Codex, after A–C:
- D: the generic lifts and slice 6's last proofs, the trace agreement among them;
- F and G: the two layer bugs;
- E: the `Fits` judgment;
- H: fresh tokens and the exit clause in M6's statement.

[Addendum 3](research/2026-09-30-codex-brief-slice6-addendum-3.md) follows Codex's
[side audit](research/2026-09-30-side-audit/audit.md); its probes were rerun clean.
- G moves two provision fixtures.
- H splits in two:
  - H1: M6's queue fact types every queued command and carries the guard's per-command
    conditions;
  - H2: "never goes wrong" lives in the exit judgment that every typed position reads.

The M5–M7 proofs are the next brief. Row 108 (numbers) is open, with the audit's two additions.

**Codex's first receipt, merged (2026-09-30).** The
[receipt](research/2026-09-30-seat-codex-slice6-receipt.md) at `3c2609f4` landed B, D's
independent parts and E, each narrowly built with its axiom output at the ceiling; the
coordinator reran the final build (421 jobs, clean) and merged the branch.
- **Landed:** M6 counts runs with no host answer (row 95); the generic lifts, the guard driver
  re-derived through them, and memo-map identifiers proved valid on native reachable states
  (row 110); `Fits` is the production value judgment and the old judgments are retired (row 96).
- **Stopped on scope, repairs written and checked:** A (the generated `RunnerDerived` codec), C
  (one reader outside the checklist; the eight site defaults stay, by addendum 1's fallback), F
  (two generated closure manifests), G (a third existing fixture flips on purpose). All four are
  permitted by [addendum 4](research/2026-09-30-codex-brief-slice6-addendum-4.md).
- **Stopped on design:** H1 found that a token must be typed by what its observer delivers, not
  by the fiber it waits on (ruled in addendum 4; `E4-SCHED-CE-018`). H2 measured eight proof-body
  repairs and a false helper; it is held until the model-probe synthesis.

**Real programs, as theory (owner, 2026-09-30).** The owner asked for real, full programs to be
formalized as requirements of the proof architecture, building on the research already done.
[The model of a full program](research/2026-09-30-full-program-model-requirements.md) is that
synthesis, for review.
- **The model was built for an open signature.** The typing layer is stated over any
  signature.
- **The rest is pinned.** Admission, the soundness theorems and the typed state are fixed to
  the built-in one. Service, cell and data types are closed.
- **The recommendation.** State the milestone over a signature parameter before proving M5–M7.
  Then later services, cell types and data types add obligations instead of reopening proofs.

**Probed the same night.** Four seats and four adversarial verifiers probed R1–R9
([synthesis](research/2026-09-30-model-probe/synthesis.md), the entry; seat notes and verifier
notes beside it). The direction holds; the note as written does not:
- "lawful Σ" and "Σ ⊆ Σ′" are undefined;
- "extension is additive" is false as written (six failures, proved or tested) and becomes eight
  named conservativity conditions;
- nothing asked what a program *does*, so four requirements are added: library code inherits
  theorems, resources are released, frontiers name what they await, a run has load inputs;
- several supports were wrong or superseded (`interpret_pinned` is uniqueness, not extension;
  `Ψ_S ⊕ Ψ_F` no longer builds the concrete judgment; `build_total` was landed and cut).

The revised list is R1–R13 (synthesis §2) with its pedigree traced (§3) and a plan to refresh
`DESIGN-BASIS.md` into one basis with sources (§3.3, §4). Thirteen decision rows are proposed
(§6); six gate the next brief. H2 can go on two conditions (§5.1).

**Codex's audit of that plan, and the rulings (2026-10-01).** Codex reviewed the synthesis
read-only ([audit](research/2026-09-30-codex-review-model-probe/audit.md); its four load-bearing
probes rerun clean in the main checkout). It upholds the direction and refutes two things with
checked counterexamples: H2's part two (a saved loop frame carries `die missingService` from a
scope-requiring type to one requiring nothing; row 117) and D5 as written (no `Package.install`
order appends on the assembled table; row 115). It also corrects the Σ_app slice's count (27
existing sites, lawfulness on the source) and the shapes of R10–R13 (lexical well-scoping; a
completed-cleanup receipt, since the closed bit is set before cleanup runs; no whole-machine
fixed point for deadlock; load inputs as a congruence law). The owner ruled: H2 part one go, D1–D6
as amended. Recorded: rows 111–118, row 107 and row 21;
[addendum 5](research/2026-09-30-codex-brief-slice6-addendum-5.md) to Codex. Meanwhile Codex
landed A (`90df5d21`) and C (`be6631ab`, `e5cc184b`, `f05a6ace`) on its branch, merged at
`bc77e97f` with the audit; then D (`fa5add20`) and F (`d20f3292`, row 104, `E4-PROV-CE-005`
repaired), merged at `9ad8a7c0`. G, H1 and H2 part one each stopped on a checked counterexample;
the owner ruled all three on 2026-10-01 ("ratify as accepted"), recorded in
[addendum 6](research/2026-09-30-codex-brief-slice6-addendum-6.md) and rows 105, 107 and 133:
G's fourth refused fixture (`TemplatesContract.layerSamples[1]`) is expected; a fiber with a
queued `finish` is typed by that finish and its code slot is inert (H1); H2's two false test
statements (`cancel_typed`, `lookup_typed`) are amended and the bounded migration authorized.
The same ruling accepted the data probe's rows 119, 122, 127 and 128; rows 120–121, 123–126 and
129–132 are open with their recommendations. A formalization pass (four seats, four verifiers,
one synthesis; `docs/research/2026-10-01-formal-pass/`) runs before the remaining landings.
Codex then landed all three with row 39 (G `57c93ba4`, H1 `d554cd71`, H2 part one `abc7b124`,
row 39's four deletion slices `f0591f36`–`8cdc931b`, verification `bd142695`), merged at
`0c534f06` after the full build and gates, the producer chain (byte-identical), dune,
`check-ocaml`, `check-cases` and schema-ts passed in its worktree and the build was rerun in
main. H1 carries one extension Codex made under the owner's "resolve the issues" instruction
(row 133: current code is also inert on a halted machine, and `StepPreserves` takes the dispatch
premise `m.stuck = none`, as `Lift.StepKeeps` does), which awaits the owner's explicit
ratification. The M6 ledger stands at 20 open, 0 proved.

**The formal pass and the landing (2026-10-01).** Four seats (algebra, proofs, types, organization)
and four verifiers probed the plan at `ea5b28b5` (`docs/research/2026-10-01-formal-pass/`; the
synthesis is `synthesis.md`). Four declared M5–M6 obligations are false, proved on checked
host-free programs, each repaired by a statement change and no runtime change: `Fits` compares
declared handle types in the raw order while the checker uses the normalized one (row 137);
eight protocol posts contradict their handlers (row 136); saved frames and hook protocols are
typed at one world (row 135); the capstone and `decision_preserves` read the typed state at a
budget cut (row 134). The rest is rigor (M7 undeclared, row 138; halting-freedom and liveness,
row 139; the ledger as the one list, row 140; the Σ_app slice; inhabitance) and tidiness (the
names, the census instrument, the registers; rows 141–148). The owner's instruction: resolve
every finding and work to full completion, no shortcuts, no gaps. The landing plan is
[`2026-10-01-landing/plan.md`](research/2026-10-01-landing/plan.md): Opus seats in their own
worktrees, briefed per file ownership (A values and the signature; B frames, posts and the walk;
C the assembled state, M7 and the ledger; E the algebra laws; F the instrument, registers and
imports; H the DESIGN-BASIS refresh), then wave 2 (row 117's contract, the adequacy instances,
M5, the eighteen commands, M6c, M7) and wave 3 (data stage 1, the renames, the glossary). The
owner ratified rows 134, 137, 138 and 149 as recommended on 2026-10-01; the other owner-level
choices proceed on the coordinator's recommendation (plan §1). Merged so far: seat E
(`a561d604`, the algebra laws), seat F (`efcf1ae2`, the census instrument, the registers, the
`Effects`-free core root, the `ExitHasTy` rename and its connector, host-boundary §7) and seat B
(`b9d0d19f`, rows 135 and 136: frames closed under world growth, every post at the machine's
answer, the handler-adequacy rule proved with 63 instances and 8 declared). Seat B found that the
exact close post is not fulfilled for a lone finalizer outside `⟨unit, never⟩` nor by the close
walk through reified exits: rows 151 and 152, recommended (a) and (a), proceeding in wave 2 with
ratification owed. Four rulings the owner gave Codex directly on 2026-10-01 are
recorded in addendum 5's amendments and rows 91 and 107: part one's clause excludes `badName` and
`notImplemented` only (the addendum had stated the full clause, which part two holds); the engine
prelude and the engine tests join C's checklist; two more closure manifests and the `ForkRecord`
type root are permitted. The same day the system map gained §1.1, what a full program
is, and §8, the requirements R1–R13 with their status, the one place status lives; R10–R13 are
stated as the audit corrected them. The design-basis refresh is briefed as a docs-only seat
([brief](research/2026-10-01-design-basis-refresh-brief.md)): one row shape, two new rows (DB-16
typing as a protocol over a world, DB-17 the requirement row calculus), three stale sections
retired to history, one bibliography, the eight ruling-bearing notes force-added. Landed on
`seat/H` and merged (`c72f27e9`, receipt
[`2026-10-01-design-basis-refresh/receipt.md`](research/2026-10-01-design-basis-refresh/receipt.md)):
DB-01 … DB-17 in one row shape, status by link to §8, every citation checked at `dceae006` by the
seat's script; the re-pin after seat C's split is row 154.

**Seats C and I merged (2026-10-01, `38686e44`).** Seat C landed row 134's split (`J = MachineTyped`,
`I = ConfigTyped`), M7 declared over `M7Fragment` with its route proved (row 138), the liveness
clauses (row 139), the ledger as one list (row 140), and the register's CE-011 and CE-014
repaired; seat I integrated it with seats B, E and F: `M6Stack` folded into `M3bWorld` (row 87),
`E4-TYPED-CE-010` flipped against M5 over `J` (`AwaitLoad.loadsTyped`), `fiberPre`'s halting arms
with their refusal controls, `storeTyped_of_typedState`; `lake build Effect4.Laws Test.All` green
with both gates. Two checked refutations stand and are one row, 156 (recommended (a), authorized
for pass I2, ratification owed): the `scopeExit` constructor reads no scope liveness, so
`step_deliver` stays refuted (`E4-SCHED-CE-020`, re-opened); and Codex's second-eyes review
([`codex-second-eyes/review.md`](research/2026-10-01-landing/codex-second-eyes/review.md)) shows
the scope-handle posts carry no presence, so the checked program "make a scope, fork into it" has
no `TypedProg` derivation and M5's `DenotesTyped` is false there (`E4-TYPED-CE-018`). Pass I2
(seat A on top of seat I, [brief](research/2026-10-01-landing/brief-I2.md)) runs on `seat/I2` with
row 156 as its step 10; row 154's re-pin follows I2's merge. Seat G landed row 150 (`FoldLift`,
[brief](research/2026-10-01-landing/brief-G.md), merged `2a99f045`: the six fold-level Guard
inductions gone, statements unchanged), the exhaustiveness printer, and row 8's key half; row 8's
dedupe is a store-identity choice (it moves the genesis and every CAS address), recommended (C)
in receipt G, ratification owed. Wave 2 is briefed: D1 (rows 117, 151, 152, 153,
[brief](research/2026-10-01-landing/brief-D1.md)) and D3 (the eighteen commands, the six edits,
M6c, `exitHandles_valid`, [brief](research/2026-10-01-landing/brief-D3.md)) in parallel after I2
merges, then D2 (M5's `denoteR_typed`, [brief](research/2026-10-01-landing/brief-D2.md)) after D1.
In parallel, on the owner's instruction to finish the type language once (records and every other
form the target profile needs), five probe seats run the
[type-language probe](research/2026-10-01-type-language-probe/README.md) on copies, no production
edits: P (records and the algebra), Q (generators, lowering, conservativity), R (terms, faces, the
p2 harness), S (the Schema arms and a readable profile), T (the completeness census); their notes
become the data-wave briefs (synthesis §7's commit series extended), dispatched after wave 2 by
default (row 119).

**Pass I2 merged (2026-10-01, `c898ad04`).** Seat A integrated on seat I's union: rows 111–116,
127, 137 and 149 landed, `E4-TYPED-CE-009` and `-015` repaired, runner admission refuses empty
columns with the runner group regenerated in the fixed order, `dune build` and `make check-ocaml`
green; and row 156 landed (`ScopeLive`, one predicate for scope presence at the world;
`E4-TYPED-CE-018` repaired by the `forkAfterMake` and `makeThenClose` controls; `step_deliver`
open and no longer refuted). The ledger: 37 open, 447 proved, 484 total. Next from this base: D1
and D3 in parallel, J, and seat H's row-154 re-pin.

**The data probe (2026-10-01).** The owner asked whether to explore full typing with records and
JSON, and whether native schema support was ever determined. Four seats and four verifiers probed
it ([synthesis](research/2026-10-01-data-probe/synthesis.md), the entry). The design is not one we
have: tracked files hold the rule (AGENTS.md "Schema and program") and DB-15's refusals; the
boundary rulings of 2026-09-10 live only in gitignored notes; records, their value encoding,
decoding inside a program, error payloads, signed numbers and recursive types have no ruling. The
probe narrows records to one design (proposed row 119: `Ty.record` with fields in canonical order,
positional values, exact subtyping, width projected at the boundary), restates R3 as theorem
shapes with a staged plan and measured costs, finds DI-67's inhabitance check enforced for `int`
only (`prod never nat` and `except never never` admitted though empty: a counterexample to
register), and proposes rows 119–132. Nothing changes for Codex; the first data slice starts after
F is merged (it is) and, by default, after the M5–M7 milestone. The owner decides.

## What the owner must decide

Decision row 90 is ruled and landed (2026-09-24): contexts are typed by their keys' static
service types, which is what the checker uses (the recommendation's per-fiber premise was wrong
and is corrected in the register). Slice 5 landed the same day ([landing record](research/2026-09-24-foundations-slice5-landing.md)):
the stack walk is proved type-preserving with no run premise, delivery and the hook laws are proved,
the typed state is assembled, and the transition ledger is declared per command. Slice 6's fork
ledger landed on 2026-10-01 (rows 91–92), and the trace agreement with it (rows 93–94, closed). The open choices from 2026-09-30 are the host boundary and its connections (rows 95–101); rows 102–103 (the documentation homes) are ruled. Background: the [typed-state admission audit](research/2026-09-23-typed-state-admission-audit.md)
found that the program judgment refused most programs the checker admits; the census and the
dynamic lane landed on your ruling (8,584 typed programs, 34,336 runs, no exit outside its
checked type), and the [protocol repair](research/2026-09-24-typed-state-protocol-repair.md)
landed on 2026-09-24: every consumed row certifies its answer's type, source admission reads the
program's row table, fiber handles are covariant, and five loaded programs are proved admitted.
The other corpus entries' admission proofs are briefed to Codex. The checker, meaning soundness
on the straight and looped fragments and runtime agreement were never affected. Reporting
`U-01` upstream remains the owner's decision; its reproduction and Effect 3 comparison are in
`docs/UPSTREAM-BACKLOG.md`.

The register [`docs/core/decisions.md`](core/decisions.md) is the one owner of each row's
recommendation and status. The copy of its recommendations that stood here until 2026-10-01 is
removed: it had drifted (row 21 read "keep" after the ruling "thread it"), and the formal pass's
organization seat named it as a second owner (its §4.2). Read the open rows there, in the order
its history section gives, and the owner-level choices of 2026-10-01 in
[`2026-10-01-landing/plan.md`](research/2026-10-01-landing/plan.md) §1.


The preceding review is retained in
[`monotonicity and refinement findings`](research/2026-09-21-foundations-monotonicity-and-refinement-review.md)
and its [historical controls](research/2026-09-21-foundations-review-evidence/README.md).
Abstract store contracts remain target-neutral. OCaml is the first implementation;
C compilation, a separate C representation and TypeScript need distinct named connections.
The research packet's C1–C4 statements have now been promoted and proved: C1 as
`Typed.completion_transport`, C2 as `indexed_ref_step_preserves`, C3/C4 as
`Refinement.projects_compose` and `projects_induces_refines`. Their research copies retain
the original checkpoint. These conditional abstract laws do not certify a backend implementation.
Decisions 86–88 record the technical questions; the five chat rulings of 2026-09-20 were written
into `decisions.md` on 2026-09-21 (rows 20, 48, 51, 52, 79).

The foundations plan and slice briefs are in
`docs/research/2026-09-20-foundations-plan-and-next-two-slices.md`: the review's findings
hold; the false statement is one of seven obligations declared inside `include` sections (a
`def` never receives an included hypothesis, a `theorem` always does), so slice 1 makes
`ProofGraph.Obligation` a `Prop`, declares every obligation as a theorem, records the seven
amendments with their counterexamples, and adds the explicit reference `#obligation_proved`;
slice 2 adds owner-level source rows so the skeleton states `SavedOk`, `ResumeOk` and
`CaptureOk` whole, puts the ghost token table on the world, and declares the typed-stack
interface parameterised in `TypedProg`; slice 3 (world validity and transport) is written
and disjoint. Decisions D1–D11 of that note are the coordinator's; the five chat rulings of
2026-09-20 were written into `decisions.md` on 2026-09-21.
Slice 1 is landed as `3aa1a9f1`
(`docs/research/2026-09-21-foundations-slice1-receipt.md`): 329 obligation declarations
in 40 files now use theorem binders, seven statements have their approved premises restored,
and 32 explicit references close former markers. The fresh unique Effect4 ledger is
309 obligations, 300 checked, nine open. The namesake audit reports zero unadapted mismatches;
four pre-existing argument reorderings keep their statements. The counterexamples also
refute all three premise-free Actions statements. `make build` and `make check` pass.
Slice 2 is landed in the commit carrying
`docs/research/2026-09-21-foundations-slice2-receipt.md`. Whole-owner rows now pass the entire
saved state and capture, and all resume arguments. The gate retains 85 positions and the
same two refusals, now through 86 rows; 17 generated predicates use 10 carrier predicates.
The token table is per fiber, the world order retains its declarations, and the stack
interface composes through a shared middle type. `TypedProg`, named-frame protocols and the
capture environment relation remain parameters; no operational preservation is claimed.
The unique ledger has 309 obligations, 299 checked and ten open: the removed saved-field
assembly is replaced by the explicitly open `park_extension`. `make check-typed-state`,
`make build` and `make check` pass. The older look-ahead's namesake-first closure forecast and
M2b-before-M3 sequence are superseded.

The owner's broader direction is captured in the review's §11: all 452 pinned TypeScript
source files and all 137 public modules have a planning disposition, including the remaining
core library families, host semantics, translation and publication. This is inventory coverage,
not a claim that their semantics are all implemented or proved. All 194 entries (88 decisions,
101 design issues and five Config questions) are routed in the review's linked planning map.
Prioritize semantic organization, reusable relations
and focused proofs; add tools or repeat broad checks only when they serve concrete work.

## Earlier full-check landing (2026-09-17)

- Branch `refactor/phase1-phase3`. `make check` green (build, roots, generated drift,
  catch-all arms, native, the TypeScript reader, the corpus pin); axioms `[propext, Quot.sound]`
  everywhere but the four meta modules the axiom gate names; the oracles are `check-full`'s
  since 2026-09-19. CI: the workflow-file error that stopped every run since `78684a8` is repaired
  (`3a394912`, row 37), unverified until the owner pushes.
- The surface: `Api.Author` (`Author.build : Module → Except BuildRefusal Built`), `Effect4.Run`
  (`Run.open` cannot refuse; every convenience is a `List Command`; `journal_replays`,
  `drive_eq_play`), `Api.Supervision` (daemons as data), `Api.Inspection`. The alphabet is
  settled (`select`, `iterate`, `Decision`; `branch`/`whileLoop`/`callback`/`yieldError`
  retired; `gen` stays). Wire tags are stable (`tools/Effect4Gen/wire-tags.json`).
- Proved: `run_eq_meaning` on `Straight`, `loopAgreement` on `Looped`, meaning and loop type
  soundness, laws 11/12 and completeness of the printer/reader over the template table, scope
  safety by construction, the journal as a free monoid (`replay_unique`); the checker sound and
  complete against `HasTy` at every path, `explain = none ↔ effTy.isSome` and weakening as
  corollaries of one `Except`-valued fold (`CheckSound.lean`, `Typing/Agreement.lean`), the
  two hand inductions that proved them deleted.
- Measured (`#traversal_census`, `docs/core/traversal-census.md`) on 2026-09-18: 78 hand traversals of the
  five free objects (`Eff` 28, `Ty` 17, `Term` 11, `Representation` 5, `Val` 17), down from
  93 once the hand blame walk, the hand checker and the hand term block were deleted. The
  converter `fold_of` (`Program/FoldOf.lean`, five shapes) has given 65 of them a fold and a kernel-checked
  connector beside the hand definition, at `[propext, Quot.sound]`. The checker is one
  `Except`-valued fold (`Program/Checker.lean`): `effTy` and its siblings are its success at
  the root by definition (`Program/Typing.lean`), `explain` its refusal, and the typing proof
  graph is stated for it at every path (`Laws/Program/Typing/CheckSound.lean`; census §7.5,
  §7.7, §7.8); the term typer is the fold `argTy`, `termTy` its projection at `false` (§7.6,
  §7.9). The thirteen without were the ruled exemptions, `valCode`/`ofSchema`, and a derived
  instance (§7.4). On 2026-10-01 the instrument was repaired to read a definition's own code
  (row 143): at `dceae006` it counts 84 hand traversals, 60 with a fold and connector, 24
  without, each named in census §7.4 (§7.11 has the before/after table).

## The documents (read these; the rest is history)

| file | what it holds |
| --- | --- |
| `docs/core/system-map.md` | the frame: the goal, the ten layers with their owners and status, the sorts with one representation each, the five arrow kinds and what each owes, coherence, scope-correct composition, generation as a fixed point |
| `docs/core/host-boundary.md` | the external-reply lane: how host answers flow today, the known holes with evidence, the boundary contract (lifecycle, handle declarations, membership matrix, entry paths, controls), the interim profile and the order |
| `docs/core/coherence-principle.md` | scout F: the principle in full, the seven squares, the arrows lacking obligations |
| `docs/core/traversal-census.md` | the census numbers, every hand traversal by root, the converter design |
| `docs/core/decisions.md` | every open decision, one list (status by row; rows 44–45 record the approved world and rows 78–85 the state/refinement proposals and 86–88 the foundation contracts) with the order |
| `docs/core/language-cut.md` | the historical language-cut analysis and profile/cut distinctions; live whole-pin dispositions and remaining work are in the post-Phase C plan §11 |
| `docs/core/api-surface.md` | the consolidated API and its awkward constructs |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses; the LLVM-shaped architecture |
| `docs/core/machine-state.md` | The state and log owners, proposed representation changes, conditional transaction profile, and shared basis for the surveyed stateful modules. Approved world and open choices are separated; the implementation plan and supporting research are tracked under `docs/research/` |
| `docs/DESIGN-ISSUES.md` | the DI register (rulings are made only when written here) |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/DESIGN-BASIS.md`, `docs/DESIGN-MAP.md`, `docs/RUNTIME-COVERAGE.md` | the tree, the generated groups, the DB register, the earlier five-layer map (superseded in substance by `docs/core/system-map.md`), the runtime census |
| `docs/core/architecture-map.html` | the measured architecture map: the roots at their declared heights, the import matrix, every import against the direction, the typed-state stack with its planned modules, the file map by role; regenerated from the tree by `make gen-architecture`, roles declared in `tools/Tools/ArchitectureRoles.lean` |
| `docs/core/post-phase-c-synthesis.md` | the checked post-Phase C review and full proposed execution plan: false pending statement, relational predicate gaps, decision reconciliation, slice contracts, controls and evidence; not an owner ruling |
| `AGENTS.md` | the operating rules and the vocabulary |

## Next, in order

The active sequence is the foundations review above. Phase C's existing receipt remains
historical evidence; the dated notes below explain the redirect and its earlier plans. They
do not override the corrected protocol-before-assembly order or constitute a new pause instruction.

**Design review before implementation resumes (2026-09-19).** The completed STM and stateful-API
research is reconciled in `docs/core/machine-state.md`, with the detailed contracts, retained
finite controls and proposed D0–D7 sequence in `docs/research/2026-09-19-state-refinement-plan.md`.
Rows 44–45 record the approved typed world; rows 78–85 remain proposals. The tooling branch
`codex/typed-state-tooling` was checkpointed as three commits and merged on 2026-09-19
(`de27095d`; it had built green at its last edit in its worktree). Set the storage/observation contract before pinning
the concrete obligation count; fast backends and new API families do not all block the milestone.

**M1 kickoff (2026-09-20).** `docs/research/2026-09-20-m1-kickoff-confidence-and-design-representations.md`
checks the forward scout brief against `f9d3112b` (six corrections: `completionPrim` is at
`Stores.lean:1813`; the census rows are keyed by field name so only row 61 is edited; `make
gen-lcnf` and `gen-cas` exist and `generate.py --only` takes one family; there is no
`Effect4.World` aesop bank; replay is one of row 80's options, not a ruling; the placement
moves go between M1 and M2, not inside M1), records what each of rows 44/45, the world order,
the store record, the heap kernel and the promise table stands on, states the design as one
shape at four levels (interaction tree + Hazel protocol; world ordered as persistent tables
plus owned cells; the store as a comodel; the observation in CompCert's contract shape), and
organizes the verified-abstraction research (CompCert/CakeML, Coq extraction, LLVM/MLIR
legalization, data refinement, DimSum, handler fusion, Alive2/ISLE) into the shape of a
lowering-module API: carrier interfaces with laws, one `Layout` reader, legalization rules
with an obligation and an evidence tier. Codex holds M1–M2; the design focus stays on rows 84
and 85 next.

**The open design issues in order (2026-09-20).**
`docs/research/2026-09-20-open-design-issues-order-and-observation-packet.md` ranks the open
register by core stability, ergonomics and utility (row 79 with R3 and row 20 first; the
park-handshake invariant; row 85; rows 48/51/52 as M3 content; then L4 of rows 42/43, row 2,
DI-24's repair half, Config D1–D5; then rows 84/80, 81, 82/83, groups B and D) and carries the
first packet: the three views named (semantic `Obs` unchanged, holder through state and ledger,
diagnostic through the sink), R3 as one `origin` field on the fiber replacing the trace read in
`statusOf`, the representation connector in projection and relation form (one module, instanced
by M1's memo condition now and `Arena` next), agreement profiles as data, and the park-handshake
invariant stated. Rulings R79.1–R79.5, R3, row 20 and rows 48/51/52 are asked of the owner.
**The deep-dive review** `docs/research/2026-09-19-plan-deep-dive-review.md` (2026-09-19) re-cut
D0–D7 into slices with files, statements, deletions and red controls (plan §14): the tooling
merge T1–T5 first; then D2 as the first machine change (a deletion: completion cells hold data),
layer 1 as one world record ordered by `Stores.le`, the residual protocol under an answer gate,
`Keeps`, S1, S2 with the ledger's ceiling pinned there, S3. Proposals: row 84 (a first
transaction profile on the straight fragment, so row 80 does not block it) and row 85 (D5 as the
`Arena` interface over which the store kernel's laws are restated; no Lean `Array` instance).
The landed-architecture review (`docs/research/2026-09-19-landed-architecture-review.md`,
`f4404923`) is addressed in the deep-dive note's §9: the generator's three omission shapes and
the ledger's stale-marker gap are fixed with controls; the world-order, straight-profile and
predicate-deletion claims are withdrawn; M2 and M3 are re-cut and row 84's rationale amended.
The M1 specification review (`docs/research/2026-09-19-state-refinement-deep-dive-and-m1-specification.md`)
is addressed in §10: row 84's budget is the proved bound already in the tree, row 85 is confirmed,
the seven placement resolutions are accepted or amended for the owner, M1's radius is 38 files and
`DeferredOk` goes whole. Its ratchet finding rebuilt the instrument: the trust gate's source scan
parses each source as the compiler did and counts tactics by syntax kind (`Test/Audit/AxiomGate.lean`),
which made five `local macro` tactics `scoped`. The refinement follow-up
(`docs/research/2026-09-19-refinement-followup.md`, `60b7d0da`) is addressed in §11: the generator's
coverage follows fields and column occurrences (two new controls), `E4-STORES-CE-003` stays as M1's
reference-validity boundary, row 84 owes the transaction connector, the map says presence not
completion. The owner then retired the proof-shape ceiling and the source scan (the gate reads the
compiled environment), collapsed the tiers to `check` and `check-full`, and cut the citation,
compatibility, known-red and script-test lanes. The tree's 254 warnings were cleared and every
library builds with `-DwarningAsError=true`.
The immediate priority is shared representations and composition laws. Known future modules
can reserve contracts with explicit missing implementations using the existing wanted machinery.
Supporting reviews and the paused tooling handoff are tracked in
`docs/research/2026-09-19-state-refinement/closeout.md`; none depends on retaining the design worktree.
The critique follow-up is tracked in `docs/research/2026-09-19-critique-response.md`, with Lean
proofs and reproducible probes beside it. It corrects the composition/compilation account and
identifies the driver-continuation contract needed before ownership across fuel frontiers.
The implementation/fusion audit is retained in
`docs/research/2026-09-19-implementation-audit-and-fusion-analysis.md`; its reviewed disposition
is in the current plan §13. D1–D7 now make replay budgets, DI-97 poll, wake/progress obligations
and actual target storage explicit. Existing fold laws remain available for local reuse;
decisions 34/40 still close the fusion/conversion campaign. No open semantic choice is ruled.

0. **The tooling-first waves, 1 and 2 landed** (2026-09-19). Wave 1: `f8517fa7`, `dfd94366`,
   `9e20cf9b`, `ee88efe2`, rows 59–66 (`1f1cc8e3`), the policy re-seed (`ba5286d3`); the coherence
   review `docs/research/2026-09-19-wave1-review-and-next-slice.md` (C1–C9). Wave 2: seat D
   `f6db74cf` (one compiler: tsgo drives every typing lane; the assignability differential, 600 pairs
   594 agree 6 cut 0 defect; rows and atoms against their exports; C6 answered by the target),
   seats E and V `5a44d83b` (the engine at twenty constructors through a one-pass chain and a mirror
   that refuses a lag; `fold_of` keeps the source's matcher, so `Val.hasTy_admitsSub` closes and
   `hasTy_sub` is the fold's corollary in the Laws with the core free of theorems about the order;
   `argsBelow_trans/antisymm`, the six `sub_*_of_ne` deleted), with the two seats' last slices inside the same
   commit (template laws, `matchTemplateArgs` home, hygiene 0.5/0.8/0.9; closure manifests, fatal
   frontier and module check, `roots.json`). Rows 67–72.
   The atoms slice landed (`49543b83`, `694f02d3`, `0b6b99a1`): all 33 atoms as rows; row 69
   option atoms as subsumption rows (`isSome` mono, `getOrElse` poly); the four L4-blocking atoms
   (`ite`, `some`, `none`, `mul`) and nine L3 atoms (`nil`, `cons`, `get`, `length`, `append`,
   `sub`, `div`, `mod`, `concat`); repeated parameters infer at TypeScript's common supertype;
   generic soundness is proved once through `Fits.instantiate`; template atoms checked at explicit
   instantiation in the rows lane (26 agree, all callable atoms judged); prelude unit list bug
   repaired. Receipt: `docs/research/2026-09-19-atoms-slice-receipt.md`. Rows 73–75.
   Receipts: `docs/research/2026-09-19-seat-D-receipt.md`; E and V have none (stopped by the owner
   for speed; their commit messages are the record).
   Tier 3 item 3.1 landed (`8f56ff1b`..`eea33606`): the store step kernel `refStepOf` and
   `SyncOp.refKernel` in `Laws/Machine/RefKernel.lean` (`refStep_eq_refStepOf`), with `step_typed`
   (from 229 to 51 lines), `refStep_length`, `refStep_valid`, and `refStep_keys` walking the
   twelve heap rows in one case through `refStepOf_keeps` and per-row kernel tables (−146 net
   lines); Row 76.
   Tier 3 item 3.5 landed: split `NativeOp.kind` off `row`; `compileEff` and `Straight` use
   `op.kind`; `Ty.scope` and `NativeOp.row` exit the LCNF engine closure manifest (`NativeOp.kind`
   at 13 instructions replaces `NativeOp.row` at 279); `roots.json` and `cases-policy.json`
   updated; Row 77.
   Scanner hardening for 3.3/3.4: type instances are visited separately; exhausted scans and
   unsupported recursive carriers fail; reads include opaque whole values and matchers;
   a copied field is unchanged only relative to an explicit source. The census now has 87
   positions and 95 source rows: 13 captured-name positions were previously skipped. The
   new rows use the existing stack, pending, journal and hook sources. Focused controls:
   `Test/Audit/PositionAnalysis.lean`; receipt `docs/research/2026-09-19-typed-state-tooling-receipt.md`.
   Direct declaration generation, structural frames and the shared evidence API now accompany
   the scanner repair. `#typed_state` replaces the source-file writer; the named TypedState
   bank has a red control. `Typed/Frames.lean` generates 60 checked frame rules: 159 clauses
   are reused and 40 are explicit premises across those rules. `ProofGraph` owns theorem
   references, search and the obligation join for Laws and Conform. The declaration-backed
   `#typed_state_obligations` checker rejects missing/stale entries and exceeded ceilings;
   its executable controls pass. No new TSV or generated source file is required.
   **These are structural tools, not the completed machine-preservation ledger.** Deriving
   the transition-specific goals and pinning their open count still needs the concrete
   predicate/world instantiation. The 40 premises are not a count of those future proofs.
   Still open from the plan: 1.11a span pinning, 4.4, 4.8/4.9 and Q4–Q6 with seat I's survey;
   from Tier 3: 3.2, 3.3, 3.4, 3.7. L2–L7 resume after Tier 3.
1. **The fold work stops here** (owner, 2026-09-18): the checker, the term typer and the
   fragments landed (census §7.5–§7.10); the exemptions (thirteen on 2026-09-18; twenty-four
   at `dceae006` under the repaired instrument, row 143) stay as they are and are tracked in
   census §7.4. No census gate, no fusion, no conversion for uniformity's sake.
2. **Row 39** (landed 2026-10-01, merged `0c534f06`): `EffectfulField` first, then
   `Check`/`Accepts`/`Image`/`schemaOf`, the `Annotations` trim, the `render` move, all done.
   Then the simple rows still open: 8 (now in `Schema/OfShape.lean`), 23 as a delete, 24, 17, 16.
3. **The Schema layer** re-cut (`docs/research/2026-09-17-ontology-and-do-now-probe.md` §3): the five files that carry the two real claims
   stay; the rest is converted where it is a fold or an embedding and deleted where it is
   neither; `Store.render` leaves `Shape.lean` first.
4. Group B of `decisions.md` (the digest, the Lean MCP driver) with the observation dogfood as
   the receipt; then group D (the TypeScript rules, the rung-3 reader, the vendoring order).

Scout G (third-party Lean tooling for this work) is out: `docs/research/2026-09-17-scout-brief-G-lean-tooling.md`.

## Owner decisions open

Row 39 (the Schema wipe) landed on 2026-10-01; row 41 (the typed-state invariant on the reference
machine, the core milestone, no shortcuts; design `docs/research/2026-09-18-typed-state-plan.md`,
scouted, §6) is ruled (2026-09-18); rows 34 and 40 are ruled out. HandlesFit with Val.hasTy unchanged and
per-cell Ref/Deferred typing, including memo cells, were approved on 2026-09-19 (rows 44–45).
The release rule is implemented (DI-94/row 47), and layer 0 exists in `Laws/Effects/Protocol.lean`;
its future upstream publication remains separate. Storage, observation, transactions and future
API choices are proposals in rows 78–85, consolidated from the completed research and the
deep-dive review. Step 0 of the milestone is landed
(`docs/research/2026-09-18-position-census-design.md` §3a): the position census, the source
table under a totality gate (87/87, two refusals named), layer 0, and the generated skeleton
`Laws/Program/Typed/State.lean`, elaborated in place and parametric in the carrier predicates
(the source-file writer is retired; `make check-typed-state` owns the focused group).
The concrete transition-obligation set and its pinned count were declared at slice 5 (2026-09-24):
`M6Ledger`, 20 goals, ceiling 20 (`Laws/Program/Typed/Assembly.lean`). Open, in the order `decisions.md`'s last section
gives: group D (26–29, 32, 30's `compileEff`), then group B (14, 15) and 2, 7, 10, 11; then 1
with 3, and 19–22. Row 5 has the restatement `docs/research/2026-09-17-ontology-and-do-now-probe.md` §2 gives.

## What row 39 did (for the owner, 2026-09-18; landed 2026-10-01)

- *Trim `Annotations.lean` to the carrier*: of its 1,193 lines the estate uses `AnnotationKey` (a
  typed key: a name and the codec of its payload, two laws), the two keys `identifierKey` and
  `refKey`, and the lens `Representation.nodeAnnotations` — all from `Store/Shape.lean`'s
  `renderDef`. The rest is the "annotation data plane": bag operations, lenses on every node
  kind, and a 650-line `AnnotationTraversal` with four laws that nothing calls. The carrier types
  themselves (`AnnotationEntry`, `Annotations`) already live in `Payload.lean`. Kept: about 150
  lines. `Data/Optic.lean` stays (`Document.lean`'s two lawful traversals use it). Row 2(c) puts
  record and sum names in annotations, through exactly the `AnnotationKey` that is kept.
- *Move `render`*: `Store.render : Shape → Representation` is the schema arrow out of the store's
  value descriptions (the Q5 table: `nat` to `number` with `isInt`, `bytes` to a hex-pattern
  string, a `sum` to a union of tagged structs). Not a visual rendering. It lives in
  `Store/Shape.lean`, so the Store module imports the whole Schema tree; the sort order runs the
  other way. It moves to `Schema/OfShape.lean` beside `Bridge` (the arrow out of `Ty`); Store
  becomes a leaf (`Val`, `Shape`, the byte codec, `ShapeDoc.print`); row 8's key dedupe lands in
  the move.
- *Landed* as four deletion slices (`f0591f36`, `d75f5c25`, `3d5ea883`, `8cdc931b`), deletion
  only: row 8's key dedupe did not land in the move and stays open in `Schema/OfShape.lean`.

## Process

- Speed over ceremony: build what you touch (`lake build <Module>`), `make check` once per
  step, `make check-full` per slice; nothing pushed without the owner.
- One Lean process per checkout; a parallel seat runs in its own worktree on disjoint files with
  a brief the owner has seen; scouts read `docs/research` from the main checkout by path and
  never copy it (2 GB of evidence trees).
- Build in parallel, slot in, delete at a good place: a new representation is a second file
  beside the old one with the connector (the agreement theorem), never an edit in place.
- `docs/core/` is tracked and is the current authority; `docs/research/` is gitignored, with the
  notes that matter force-added; `docs/agents/` and `COORDINATION.md` are gone.
