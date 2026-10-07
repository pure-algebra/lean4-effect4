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

## Data-language development

The implementation starts from `82d34358` on `codex/data-language-wave`.
It adds record construction, required and optional reads, overwrite, tag selection, string maps and fixed tuples.
Raw formation precedes program admission, including checks after row type arguments instantiate.
Schema representations and JSON codecs cover these data shapes with their existing reconstruction laws.

The [integration receipt](research/2026-10-03-data-language/integration-receipt.md) records the checked modules, generated reports and finite target comparisons.
The [implementation plan](research/2026-10-03-data-language/plan.md) retains the dependency order and printer rulings.
`generated/semantics.md` reports the proof claims from their declarations.
These results establish no general target execution, progress or liveness theorem.

The next host-session step needs the checked type instance at each external call site.
The [host-instance note](research/2026-10-03-data-language/host-instance-follow-on.md) records the missing relation and proposed metadata boundary.
Inferring that instance from a runtime value loses information, including the element type of an empty list.
That representation change precedes the host correspondence proof and later lowering work.

## Proof graph and infrastructure (2026-10-04)

The [proof graph audit](research/2026-10-04-proof-graph-audit/audit.md) found that the ledger
held no goals and that no tool recorded edges between them. The
[reference scout](research/2026-10-04-reference-scout/synthesis.md) read 17 pinned outside
projects (`vendor/refs/MANIFEST.tsv`). What landed on this branch:

- **The plan** (`tools/ProofGraph/Plan.lean`). Planned goals and named theorems are nodes. A
  planned goal is a theorem whose body is `sorry` (`proof_goal`, decisions row 203), and
  downstream proofs use it. A node's status is read from its proof, with goals as leaves: goal,
  modulo or proved. `#plan_status` works in the editor.
- **The plan in the report.** `generated/semantics.md` has a plan section. Per requirement it
  shows a derived status, the open parts, the next goals and a Mermaid graph. Per proved node it
  shows what the proof brings in. Edges are read from proof terms; R9 and R12 stay open through
  their listed open parts.
- **All thirteen requirement rows** are plan rows, each with its checked top nodes and its open
  parts. Four stale cells of the system map's §8 (R1, R2, R3, R6) were corrected with evidence.
- **Proofs.**
  - R12-a (`fairTape_unarmed`): a fair finite tape that suffices leaves nothing armed at its live
    end. It is the finite endpoint only.
  - `build_total` restored (decisions row 147's first half).
  - Meaning, loop and run soundness at an application's signature (R1, `SoundAnySignature.lean`).
  - Every shared form has its typing lemma (R10, `Laws/Codegen/Forms.lean`).
- **`E4-SCHED-CE-021`**: repaired by decisions row 201 (b) (seat R); R12-b is proved
  (`frontier_empty_iff_deadlocked`). See the [seat R receipt](research/2026-10-04-seat-R-receipt.md).
- **`proof_sketch`**: a proof sketch's open goals become planned goals, and the sketch a theorem
  proved modulo them.
- **The battery is green again** after the data wave (the `formed` field, the native alphabet).
- **One population filter** (`ProofGraph.isAuxiliary`) for the census, the report and the
  architecture map. The old string filter dropped authored theorems such as `eq_cata`.
- **`make check-kernel`** (the sweep tier): every compiled declaration replayed through the
  kernel in one environment.
- **The proof-style ratchet** (`Test/Audit/ProofStyle.lean`): no new `simp_all`, `first`, `try`
  or `simp` without `only` under `src/Effect4`.
- **The module system** (decisions rows 200 and 202). 116 core modules outside `Laws` are modules:
  the 96 that reach no package (`cb8f510a`) and the 20 whose package closure is only `hash` (chain
  E). M1 holds, and M2 holds as amended. `hash` is pushed (branch `module-system`) and re-pinned
  at `ab7eda4`. Seven specialization sites stay non-module (row 202, ruled (a)): as modules
  they lose the compiler's cross-module specialization. See the
  [seat M receipt](research/2026-10-04-seat-M-receipt.md) and the
  [row 202 receipt](research/2026-10-04-seat-M-row202-receipt.md).
- **The Σ_app slice** (decisions row 21, R1). The
  [slice plan](research/2026-10-04-claude-lead/sigapp-slice-plan.md) threads the application's
  signature through program admission in six steps. Step 0 landed
  (`Laws/Program/Typed/AdmittedSource.lean`): `m7_admitted`, `lawfulSig_of_admitted` and
  `reachable_typed_admitted` are proved. Steps 1 and 2 landed (seat S, merged `9a56167c`):
  `SigApp` and `admitSig` are in the core (`Program/SigApp.lean`), program admission runs at Σ_app
  and checks the signature, and `E4-TYPED-CE-041` is repaired. Every program the API admits
  denotes a lawful source, with no premise. See the
  [seat S receipt](research/2026-10-04-seat-S-receipt.md).
- **Four empty aesop banks deleted** (decisions row 65): `Inversion`, `Reader`, `Rows`, `TyOrder`.

## Next, ruled 2026-10-04

The owner ratified the coordinator's recommendations (decisions rows 21, 120, 201, 204–207):

- **The order** (row 204): finish the Σ_app slice through step 2, then state at any type (rows
  42–43, steps 3–5), then queues, then streams. Error payloads (row 120, ratified) and derived forms
  with behaviour laws (DI-89) land alongside. Lowering and the host-session guarantee stay parked.
- **The Σ_app slice** (row 21): the session header keeps the row table only; code generation moves
  to the application's signature before authoring accepts declared services.
- **Streams** (row 205): a stream's end is a value carrying its leftover, apart from failures.
- **Acceptance** (row 206): the probe programs become tracked tests, in a dogfood folder of `Test/`.
- **Planned goals** (row 207): `proof_goal` carries its requirement and concept.
- **The host protocol** (row 201): armed work with no runnable fiber reads `parked`.

The evidence is in the [roadmap note](research/2026-10-04-claude-lead/next-after-sigapp.md).
State at any type runs in seven slices, T0–T6, in the
[state plan](research/2026-10-04-claude-lead/state-any-type-plan.md). The owner ruled its four
questions as recommended: rows 208 and 209, and rows 155 (a) and 183 ratified. T1 landed
(seat T1, merged `236df2ff`): the straight soundness holds at the typed world, and `HeapNat` is
deleted. T0 landed (seat T0, merged `c8f01acf`): the scope check reads an operation's own data. T2 landed
(seat T2, merged `89e41ae9`): the store runs binder terms, behind the function names' connector.
T3a landed (seat T3a, merged `ba7e2de0`; rows 210–213): `Ref` and `Deferred` rows are templates, and
p4's and p5's record cells build. Error payloads run
in two parts, E1 (the carrier) before T3 and E2 (the face), in the
[error payloads plan](research/2026-10-04-claude-lead/error-payloads-plan.md). E1 landed (seat E1,
merged `db504f03`): a program fails with a tagged record; p1, p2, p3 and p5 build their errors. E2
landed (seat E2, merged `a917b768`): payloads print and read back as `Data.TaggedError` classes.
The derived forms (DI-89, R10) are planned in the
[derived forms plan](research/2026-10-04-claude-lead/derived-forms-plan.md). The owner ruled its
seven questions on 2026-10-05 (rows 130 and 214 to 218). Queues (DI-11) were planned in the
[queues plan](research/2026-10-04-claude-lead/queues-plan.md). The review of 2026-10-05 below
replaces its four questions.

## Next, ruled 2026-10-05

The owner ruled the foundations of the composed modules (decisions rows 214 to 234). The rulings
rest on finite runs, finite models, source reading and literature; none is a Lean proof.

- **The Queue** (rows 219 to 222). It serves in strict request order. A message is consumed at
  the taker's atomic step. The signal is posted, as Effect 4 does. When cancellation wins
  before consumption, nothing is consumed; a commit stays after it.
- **The shared foundations** (rows 221, 223 to 227, 230 and 234):
  - one waiting wrapper with a checked body profile;
  - a restricted atomic body;
  - posted work as an `Eff` body with task metadata;
  - an embedded budget first, and a retained driver suspension later;
  - a mask that restores the caller's state;
  - a module's public behaviour, defined before its private state is hidden;
  - the contract of a retained behaviour, designed now.
- **The term groundwork** (rows 228 and 229). Seat T3b finishes. Then come a list fold with two
  binders and the identity of handles.
- **The clock and the pin** (rows 231 and 232). The clock counts nanoseconds inside, and every
  millisecond input keeps its meaning. The release 4.0.1 is audited before the pin moves.
- **The order** (row 233):
  1. the contracts;
  2. the term groundwork;
  3. one Queue path with a positive capacity;
  4. batches, strategies, terminal operations and rendezvous;
  5. Semaphore;
  6. restricted transactions.

  The design of waiting, tasks, masks and the atomic frontier comes before the Queue. The clock
  slice and the release audit run beside these.
- **The module procedure** (the owner's direction of 2026-10-05, relayed by Codex in three
  messages). The Queue is the first worked example of a factory of composed modules.
  - The contract cards of Semaphore, Pool and Cache are prepared now. They do not wait for
    step 4 of the order.
  - Every module follows one procedure, and its repeated parts are generated or applied.
  - Every receipt accounts for the requirements R1 to R14 (R14 since row 282). No module
    slice closes one by association.
  - Row 233's order of implementation stands until the owner changes it.

  [The plan](research/2026-10-05-claude-lead/module-factory-plan.md) holds the procedure, the
  card's template, the order and the accounting.
  [Semaphore's card](research/2026-10-05-claude-lead/module-cards/semaphore.md) is written
  from the pinned source. It proposes a first profile and puts four choices to the owner.
  A host probe ran its cases on rc.112, 4.0.1 and Effect 3.22.2 on 2026-10-06
  (`research/2026-10-05-claude-lead/module-cards/semaphore-probes/`). The card now recommends
  the live scan: a resumed waiter takes inside the wake's walk, on the pin and on our machine.
  Its first recommendation, a grant at the wake, rested on a wrong reading of our machine.
  [Pool's card](research/2026-10-05-claude-lead/module-cards/pool.md) and
  [Cache's card](research/2026-10-05-claude-lead/module-cards/cache.md) are written since
  2026-10-06. Each rests on the two vendored sources, a host probe on rc.112 and 4.0.1, and
  Codex's proposed card. **Both profiles are ruled** since 2026-10-06 (rows 267 to 272,
  below): the owner answered "yes to all" to the nine choices of the two cards. Two findings
  came from the probes. In both Effect 4 builds the close of a
  pool's scope does not wait for a borrowed item, and in Effect 3 it does. On the pin a
  cache's reader who arrives during a lookup's cleanup is interrupted, and the release
  repairs that. `UPSTREAM-BACKLOG.md` records both as candidates.

  [The rulings note](research/2026-10-05-claude-lead/owner-rulings-2026-10-06.md) gives a
  recommended ruling for each open question of this stretch, with its evidence. The owner
  ruled its eight questions as recommended on 2026-10-06 (rows 259 to 265, below). The eighth
  was a command of the owner's, and it is run.

Where to read:

- [the foundation contracts](research/2026-10-05-claude-lead/foundation-contracts.md): the
  obligations in one table, the acceptance cases, and an owner for each slice;
- [the queues review](research/2026-10-05-claude-lead/queues-review.md),
  [the transactions note](research/2026-10-05-claude-lead/transactions-and-clock.md) and
  [the groundwork plan](research/2026-10-05-claude-lead/groundwork-plan.md): the evidence and the
  probes on rc.112, 4.0.0, 4.0.1 and Effect 3.22.2;
- [Codex's packet](research/2026-10-05-codex-foundation-packet/README.md): the selections as
  ratified, the foundation audit and the literature notes;
- [the landing review](research/2026-10-05-claude-lead/landing-review.md): what the session of
  2026-10-04 landed.

More rulings of the same day (rows 235 to 248):

- the Queue's TypeScript face prints the expansion by default, and the native queue only under a
  narrower named profile;
- 4.0.1's source is vendored beside rc.112's for citation, and the pin does not move;
- the coordinator staffs one seat for each slice in row 233's order, at most two at once;
- the posted signal is a detached fork with a deferred start, and no construct is added (row
  238);
- the mask is a saved Boolean, with one fiber action that reads the interruptibility (row 239);
- a second note, on the mask's check at program admission and its printed form, comes before
  any seat;
- a recognized `restore` may escape its mask (row 227, amended);
- every signal of the Queue is posted, a waiting offerer's too (row 240);
- `dropping` at capacity zero is not formed (row 241);
- `poll` and `clear` pass no waiting taker (row 242);
- `flush` and the `Unsafe` family are refused by name (row 243);
- the mask's saved state has a type of its own, and typing is its check (row 244);
- a restore site is one node, and the mask prints as two rows of public API (row 245);
- the saved value may be passed as data (row 246);
- the Lean TypeScript package is upgraded as needed (row 247);
- the pin moves to 4.0.1 in increments, and development does not pause (row 248);
- `Scope.close` on a forked scope keeps `void`, the tree's answer to `U-02` (row 249);
- the release's SQLite driver is downloaded, with a tracked install recipe (row 250);
- after the fold come the faces of a binder term, then the mask, then the Queue (row 251);
- a second seat lands Codex's follow-ups of the OCaml route (row 252);
- the migration follows the features: a cut-over runs when a feature needs it, and a release
  case that waits is deferred with its reason (row 253);
- dogfooding is rigorous, runs through the lowering, and is placed in the proof graph (row 254);
- the Queue's cell and steps are a library slice: a composed module lives in a new layer of
  the runtime root, above `Program`, and its laws in the law graph. The abstract model moves
  into the law graph, each step has one planned goal, and no binding form is added (row 255).

Ruled on 2026-10-06, each as recommended (rows 259 to 265):

- Semaphore's wake is the live scan: one visit at a time, and a wake reserves nothing (row
  259);
- Semaphore's first profile has six operations at a fixed total, without `resize` and
  `releaseAll` (row 260);
- the profile's law covers a release of at most what is taken, and the step releases no more
  (row 261);
- the target evaluator comes under the trust ceiling, by two string rules in byte form (row
  262). The slice has no date;
- the compiler checkpoint joins the local sweep by one marker rule (row 263; landed
  `0acec081`);
- a TypeScript compiler client stays inside `tools/target`, and no package is published (row
  264);
- Semaphore's cell and steps start now, as a third seat (row 265). Seat SEM has them since
  2026-10-06 (branch `seat/semaphore`;
  [its brief](research/2026-10-05-claude-lead/briefs/seat-sem-brief.md)). Its first step ran
  the card's cases on our machine, where no Semaphore program had run before the ruling. The
  cases P1 to P4, P7 and P9 give the pin's answers, and three changed walks are red
  (`Test/Program/SemaphoreScenarios.lean`). Its first three steps are merged (`c685aa71`):
  that battery, the packet `Test/contracts/semaphore.contract.md`, the model and its profile
  (`src/Effect4/Laws/Modules/Semaphore/`). Three theorems are proved there: `profile_closed`,
  `visit_selects_earliest` and `visit_stops_iff`. Its fourth step is merged too (`c17f0be7`):
  the cell and five step terms (`src/Effect4/Modules/Semaphore/`), and six typing statements,
  each proved at every scope of names. **Each step's agreement with the model is proved**
  (`85a8e587`; `src/Effect4/Laws/Modules/Semaphore/Steps.lean`): five theorems, and
  `semaphore_steps_agree`, which assembles them. They are parts of the proposed claim
  `semaphore-expansion-agrees` and close no requirement. **The seat is finished** (`a9806b3b`;
  [the receipt](research/2026-10-06-seat-SEM-receipt.md)): the cases P1 and P3 replay on the
  generated engine, on both carriers. The registry names four claims with their witnesses.
  No planned goal was added. The seat used the Queue's typing and reading pieces as they
  are. Fourteen general statements waited in Semaphore's folder for the move of the shared
  helpers. **That move is merged** (`b199c15f`;
  [the receipt](research/2026-10-06-seat-MOVE-receipt.md),
  [the brief](research/2026-10-05-claude-lead/briefs/seat-move-brief.md)). Each shared piece
  has one home that names no module. The words of a step term are in
  `src/Effect4/Modules/Words.lean`. The encoding table, the reading rules, the typing rules
  and the store connectors are four files of `src/Effect4/Laws/Modules/`. The seat's
  comparison finds 192 moved declarations with equal statements and no other difference, and
  no step term moved. Fourteen list facts are in `Effect4.Constructive`. The operations that
  wait and the protected form are a later slice.

Ruled later on 2026-10-06, each as recommended (rows 267 to 272; no Lean statement of
either module exists yet):

- Pool's first profile is a fixed size, `make size acquire` that acquires every item before
  it answers, and `use pool body`. Time to live, `invalidate` and the scoped `get` are
  excluded by name (row 267);
- Pool's close waits for every borrowed item, as Effect 3 does. Both Effect 4 builds do not
  wait, and the profile signs the difference (row 268);
- a returned item joins the front, as the release does (row 269);
- Cache's first profile is a fixed capacity with string keys, and `make`, `get`, `has` and
  `invalidate`. The lookup is given at each `get` (row 270);
- Cache follows the release where the two builds differ: a reader that arrives during an
  abandoned lookup's cleanup starts a new lookup (row 271);
- Cache's capacity bounds the keys, and not the lookups that are alive (row 272).

**Who implements (row 277).** The owner approved a handover of the implementation to Codex
on 2026-10-06, and its point was reached at `f6fa54e7`. **The owner suspended it the same
day**: Codex's quota ran out, and the implementation finishes with the coordinator's seats.
The owner named the order. First comes the planned work that lands without strain. Then a
review of the whole graph. Then the authoring and inspection work of Codex's capability
packet. The
[transition account](research/2026-10-05-claude-lead/2026-10-06-transition-account.md) keeps
the state at the handover point and the integration procedure as practiced.

**The close-out set, in work since the suspension:**

- the workers over the public Queue (seat WORKQ);
- the bracket of a region, the next proof slice of R11 (row 278, point 3): **landed** by
  seat BRACKET (row 280);
- the exit column of the truth lane's runner (row 279, point 1): **landed** by the
  coordinator. The column compares the fork entry on both faces. The lane has 63 programs,
  with Semaphore's cases P1 and P4 as the batteries write them;
- Pool's public operations (rows 276 and 279), after the owner's ruling on a closed pool;
- two small repairs of proofs. The first is **landed** by seat REPAIR: the Queue's typing
  through the shared rule, with two general statements in the lift module. The second is
  **landed** by seat TAPE: the tape and its laws stand in the library (row 287).

The set is landed, and the sweep ran on `ea0f584a` (row 289). `make check` and
`make check-slow` pass, and the release ledger matches. Three targets of `make check-full`
were red. Two are repaired (seat LANES, row 295). `check-ingest` was red since seat MASK's
merge: the constructed foreign corpus built no `restore` form. `check-tsdiag` was red because
its harness had drifted, and it measured nothing. `check-schema-ts` still asks for an input
that is not set. The law of a whole run for a module's operation is not in the set. It is the
main open theory, and it starts with a design question. The owner asked for a discussion of
it when the set has landed: its obligations, and the base abstractions that it needs first.

**The focus after the set (row 281).** The owner named it on 2026-10-06: the program as
data. A program's regions are selected, observed, shown and proved, and that work serves the
tools, authoring, MCP, composing and the lowering, which must start. A region is a derived
view of the stored program with proof data: no marker is added to the stored program or to
the machine. The owner also asked for a plan of how the focus meets bidirectional type
slicing. [The plan](research/2026-10-06-type-slicing-plan.md) reads the vendored paper,
maps it to the checker and lists ten proposed claims, four probes and six slices. The
owner said to go ahead with its recommendations and to run its probes, and asked for a deep
exploration of a true gap with holes. Two research seats took them, and neither edits a
tracked source. Seat CENSUS measured the checker's graduality on the two corpora;
[its receipt](research/2026-10-06-seat-CENSUS-receipt.md) is merged (row 290). An omission
to an assumed answer keeps the answer and shrinks the error and the requirement at 4833
single omissions, on a premise wider than the plan's, with none refused. A fold to `never`
is refused 6133 times by 18 rules: the uniform eliminators repair 4148, a rule that takes
its expectation from a part gives 1886, and a cell's invariance gives 99. Every count is a
finite census over 201 programs. Seat GAP studied what a gap with holes would give, from the papers and from what
the algebra already gives; [its study](research/2026-10-06-seat-GAP-study.md) is merged
(row 288). Two of the plan's questions were answered under row 282.

**The gap with holes is first-class work (row 282).** The owner authorized it on
2026-10-06: the coordinator ratifies the plan's recommended answers, approves the
obligations and lands the groundwork, with no shortcut and with Lean's metaprogramming
where it makes a thing generated, fast or ergonomic. Three answers are ratified. Candidate A
is the first stage, and a true gap with holes is the direction. Explanations have a
requirement of their own, **R14: a partial program checks and explains its types**. A slice
view promises one minimal slice and never a minimum size. The first groundwork slice is
landed: the generic theory of type slices (seat LATTICE, row 286). The second is landed too:
one combinator for a rule that reads a union member by member (seat UNION, rows 285 and 293).
Its first conversion has landed: the fiber rule is the extended rule of its member rule
(seat PILOT, row 298).

**What the study found (row 288).** A hole needs no new constructor and no new type. A hole
is a host row with a declared type, in a hole table that is appended after the row table.
The checker admits a program modulo its holes, as the kernel accepts a theorem modulo its
planned goals. One law is new: a program of a hole's declared type stands in the hole's
place, and the whole keeps its type. The true gap is the second step: the type of a hole
whose type is not stated. It costs one appended leaf of `Ty`, with one name per hole, and it
pays where a value reaches a cell. The study's plan has nine stages and seven slices. Three
need no ruling and no append: the hole table (SKETCH), the replacement law (REPLACE) and
formation at a type variable (FORM). All three have landed. The first (row 291): a sketch is a
program with its hole table (`src/Effect4/Program/Sketch.lean`), and its language is a
conservative extension of the program's (`src/Effect4/Laws/Program/Sketch.lean`). The
replacement law has landed too (row 294): a program of the focus's type stands in the
focus's place, over the six typing judgments, with no rule added
(`src/Effect4/Laws/Program/Typing/Replace.lean`). A filling has no further premise. An
omission with three columns keeps the type where the focus's columns are closed, formed and
in normal form. The focus function has landed too (row 296): `focusAt` answers the
sub-program at an address, its typing environment and its type
(`src/Effect4/Program/Typing/Focus.lean`), and the replacement law holds at its answer with
no existential. One answer costs up to one check of the program. One pass that answers every
address waits for total marking. Nothing else of the study is a theorem of the tree yet.

A second model reads beside the seats, as Codex did. The owner hands it bounded probes.
[The probe questions](research/2026-10-06-probe-questions.md) lists fifteen: what today's
work took by reading, the facts that the law of a whole run will stand on, and the evidence
that rests on one schedule.

In work since the suspension of the handover:

- **Seat BOUNDS probes the match by bounds** (branch `seat/bounds`;
  [its brief](research/2026-10-05-claude-lead/briefs/seat-bounds-brief.md); row 292, point
  4). A template binds a type parameter at its first occurrence today, so a verdict depends
  on the order of the arguments. The probe measures the rule by polarity against it on the
  two corpora, proves what scratch allows, and runs tsgo on the prelude's signatures. It
  edits no tracked source.
  [The design input](research/2026-10-06-repeated-parameter-by-polarity.md) reads the paper.
- **Seat LANES repairs the two lanes that the sweep found red** (branch `seat/lanes`;
  [its brief](research/2026-10-05-claude-lead/briefs/seat-lanes-brief.md); row 289). The
  diagnostics lane measures again on its branch: no program that the checker admits is
  refused by tsgo. The ingest's census is in work.
- **Seat SKETCH's hole table is merged**
  ([its receipt](research/2026-10-06-seat-SKETCH-receipt.md); rows 288 and 291). A sketch is
  data, and three claims are in the registry: `sketch-conservative`, `sketch-weakening` and
  `hole-rule`. `Sketch.check` is the checker's answer: it admits no sketch to a later stage.
  A stored sketch is pinned to the row count of its application, and its renumbering is an
  open part of R14.
- **Seat LANES is merged** ([its receipt](research/2026-10-06-seat-LANES-receipt.md); rows
  289 and 295). The diagnostics lane measures again. One file holds a printed module's
  imports (`harness/truth/module-imports.ts`), and the truth lane and the diagnostics lane
  both read it. The lane copies the prelude's files as the compiler names them, it refuses
  to write a table when its own project has a defect, and it runs eleven controls on every
  run. The promoted table has 408 programs and no program that the checker types and tsgo 7
  refuses. The ingest's census holds the `restore` form: the foreign corpus builds four mask
  programs, both foreign engines read the mask's two printed rows, and three hand walkers
  have a case for every constructor, held by the type check. The ingest's script installs
  nothing now: it compares the installed versions with the lock
  (`scripts/check-lock-install.py`). One probe of the seat made bun fetch a package manifest
  from the registry, against the owner's rule. The owner heard of it the same day.
- **Slice REPLACE is merged** ([its receipt](research/2026-10-06-seat-REPLACE-receipt.md);
  rows 288 and 294). The replacement law is one statement over a judgment of nodes
  (`NodeHasTy.replace`, the registry claim `typed-replacement`), with one step for each arm
  of the generated `Node.child`. A sketch has two edits with their laws: `Sketch.fillAt` with
  `Sketch.check_fill`, and `Sketch.omitAt` with `Sketch.check_omit`. One finding changes the
  order of work. The checker refuses the normal form of a type that it admits raw, at an
  atom whose scheme infers on the raw type (a red control on `mapFromEntries`). So the
  conversions of candidate N alone do not make the checker read a type up to its normal
  form: the match of a template must change too, which seat BOUNDS probes.
- **The focus function is merged** ([its receipt](research/2026-10-06-seat-TRACE-receipt.md);
  rows 292 and 296). It is the first half of the study's slice TRACE. `Node.childEnv` is the
  step: the typing environment that a node gives its child, with one case for each arm of
  the generated `Node.child`. `Node.envAt` folds it along a path, and `focusAt` adds the
  checker's type (the registry claim `focus-function`, pointer `NodeHasTy.replace_envAt`).
  The two edits of a sketch hold at the computed focus, so a tool has every premise in hand.
  The checker does not change, and nothing is stored. The dictionary's trace stays the
  machine's, so this is no trace. Its first consumer is the TypeScript printer: the receipt
  says what the printer reads at an eliminator, and three open items are the printer's.
- **Seat FORM is merged** ([its receipt](research/2026-10-06-seat-FORM-receipt.md); rows
  288 and 297). A type variable is formed in a template only (`Formation.HeadFormed`, the
  reason `FormationReason.typeVariable`). A formed program that the checker admits has
  closed types (`check_closed`, the registry claim `checked-types-closed`), and an admitted
  program has them with no premise (`AdmittedProgram.closed`). Two things narrow what is
  admitted. A program that holds a type variable in an annotation is refused at formation:
  the pin of row 212 moved. A declared service carrier is a strict formation site now, so
  program admission refuses a carrier with a type variable, a repeated field name, a map key
  that is no string, or a deferred's error column outside the error alphabet. No typing
  signature of the tree declares such a carrier, and none of 560 stored programs moves. The
  owner heard of the carrier step with the merge.
- **Seat LATTICE's renaming is merged**
  ([its receipt](research/2026-10-06-seat-LATTICE-words-receipt.md); row 286, point 5). The
  slice module says "omitted" where it said "folded", and the dictionary has eight entries
  for its words: type slice, site, slice view, valid slice, minimal slice, descent,
  contribution slice and mask. The follow-up also found that the proof graph's population
  skips eight authored theorems by the spelling of their names: a repair candidate.
- **Seat UNION is merged** ([its receipt](research/2026-10-06-seat-UNION-receipt.md); rows
  285 and 293). `src/Effect4/Program/UnionRule.lean` holds one combinator for a rule that
  reads a type by its union members. A member rule answers at one union member, or refuses
  it. `UnionRule.lift` asks it at every union member of the target's normal form and joins
  the answers. The record field read and the overwrite are written through it, and each
  equals its earlier definition by `rfl`. No statement changed, and no generated file moved.
  The laws are proved once (`src/Effect4/Laws/Program/UnionRule.lean`; the registry claim
  `union-rule-lift`). An eliminator of one covariant constructor owes three member facts,
  and the order laws follow (`Eliminator`). The owner's two more statements are proved. At
  types, the lifted rule is the one map with its four properties (`lift_unique`). An
  eliminator's lifted rule answers exactly below the constructor's image
  (`Eliminator.adjoint`). The fiber rule is its first conversion (row 298).
- **The next slices wait for the owner's word** (2026-10-06). The owner hands some of them
  to a second model. The coordinator starts no new seat: it merges the two seats that still
  run, seat PILOT and seat BOUNDS, and stops there. One brief is written and not dispatched:
  [seat ORDER](research/2026-10-05-claude-lead/briefs/seat-order-brief.md), the order of a
  lifted rule in Lean core's classes, with
  [its compiled probe](research/2026-10-06-order-classes-probe.lean.txt). It starts after
  seat PILOT's merge, since both edit one law file. The open slices beside it are in rows
  293 to 297: the other conversions, the typed print, total marking with the one pass, the
  match by bounds after its probe, and the small repairs of row 297, point 8.
  [The refined plan](research/2026-10-06-next-slices-plan.md) orders eleven slices for the
  second model's review, with two compiled probes. It rules nothing. It checks the second
  model's report against the pinned sources. Its critical path is the address table of a
  program, the typed print and the guard's removal.
- **Seat PILOT is merged: the fiber rule is converted**
  ([the landing note](research/2026-10-06-seat-PILOT-receipt.md); rows 285, 292, 293, 296
  and 298). `fiberTy` is `UnionRule.extend Member.fiber`, in one line: the member rule's own
  answer where it answers at the raw target, and the guarded rule elsewhere. So no admitted
  program moves at the rule: the 473 programs of the two corpora keep their verdict and their
  type, by spelling. The checker admits more: `never` at every site that asks the fiber rule,
  and a raw union whose normal form has one union member. It keeps today's refusal at a
  proper union, by the guard that the owner ruled (row 292). The contract of a converted
  eliminator is stated once, for every eliminator (`Eliminator.extend_laws`, the registry
  claim `union-rule-extend`), and a conversion writes its member facts in
  `src/Effect4/Laws/Program/Eliminators.lean`. The judgment names the rule as before, so no
  statement of it changes, and each use site reads an inequality in `Ty.subN`
  (`fiberTy_upper`). The guard and the raw answer are interim, and each goes by one line.
  The coordinator finished the slice at the owner's word to wrap the seats up: the merge of
  main, the repair of one closed-types lemma, the cut of five unused theorems, the pin of
  the case policy and the records.
- **Seat LATTICE is merged** ([its receipt](research/2026-10-06-seat-LATTICE-receipt.md);
  row 286). `src/Effect4/Laws/Slice/Lattice.lean` holds the generic theory of type slices. A
  type slice is the list of its kept sites. A view is a monotone map from the type slices of
  one program to one column of types, and it owes that one fact. For every view, a minimal
  valid slice exists below each valid slice, the one-pass descent returns one with one
  question for each site, a refined query has a minimal slice below, and the join of two
  valid slices is valid (`SliceView.lattice_minimal`, the registry claim
  `slice-lattice-minimal`; the paper's Theorems 4.5, 4.6 and 4.7). No statement names `Eff`,
  `Ty` or the checker, and no view of a real program exists yet.
- **Seat TAPE is merged** ([its receipt](research/2026-10-06-seat-TAPE-receipt.md);
  row 287). Forty-four declarations left the scenario support for the library, under the
  namespace `Effect4.Run`. The sixteen executable definitions are core
  (`src/Effect4/Run/Tape.lean`): the machine's view, the raw replay, the tape, a funded run
  and rest. The laws are in `src/Effect4/Laws/Run/Rows.lean` and
  `src/Effect4/Laws/Run/Tape.lean`. No statement changed, and no generated file moved.
- **Seat POOLOPS has Pool's public operations** (branch `seat/poolops`;
  [its brief](research/2026-10-05-claude-lead/briefs/seat-poolops-brief.md)): `make`, `use`
  by the protected form, and the close that waits, with the closer as a request. It follows
  seat SEMW's procedure. A borrow at a closed pool interrupts the borrower itself, as both
  Effect builds do on one schedule each (row 279, point 2). Its first step is merged: the
  closer's step, which is the model's sixth transition (`Model.drain`, `Pool.drainStep`). It
  is typed, and it agrees with the model. The closer's step answers true exactly where no
  lease is outstanding, and it enrols the closer otherwise (`drain_waits`, the registry
  claim `pool-drain-waits`). So Pool's model has six transitions and six step terms now.
  Its second step is merged too: `Pool.make`, `Pool.use` and `Pool.close` are library
  programs (`src/Effect4/Modules/Pool/Ops.lean`). Ten cases give the profile's answer on the
  Lean machine, one schedule each, with four changed policies red
  (`Test/Program/PoolPublic.lean`). A pool is made inside a scope: outside one, the built
  program requires the scope's service. Its third and fourth steps are merged
  (`src/Effect4/Laws/Modules/Pool/Ops.lean`). Each operation keeps scope and is typed at
  every scope (`use_types`, `make_types`, `close_answers`). Eleven attempt statements relate
  one store step to the model's step, with no planned goal. Its fifth step is merged: nine
  acceptance traces on the Lean machine, each with a fault that fails the promised property
  (`Test/Program/PoolTraces.lean`). A borrow at a closing pool leaves the items and the idle
  list as they were. A borrow at a closed pool under a masked caller still exits with the
  interrupt of its own fiber. One finding: at Pool a missing withdrawal loses a wake, so the law of a run needs
  the withdrawal as a premise of the wake. Its sixth step is merged: each operation prints
  and reads back (`Test/Program/PoolFaces.lean`), and ten programs run on rc.112 in the
  truth lane. Three of them settle on two exits under the two entries, and their sync runs
  are pinned apart (`lateSightsSync`, `harness/truth/Truth.lean`). No program is kept out by
  row 268's signed difference: both faces run the module's expansion. Its seventh step is
  merged: the ten public cases run on the generated engine, and each gives Lean's exit on
  both carriers (`ocaml/engine/test/pool/`). The fixture is 1.79 MB, the largest of the
  lanes: a term has no binder, so each step's bytes hold the cell's source many times
  (row 276, point 3). Its eighth step is merged: the contract's sections on the operations
  and on the ten cases (`Test/contracts/pool.contract.md`), the README's section with one
  checked example, and the architecture rows.
  [Its receipt](research/2026-10-06-seat-POOLOPS-receipt.md) is merged, with three claims
  of typing in the registry and the corrections that it made to five sentences of the main
  line. Row 283 records what it leaves open.
- **Seat WORKQ has the workers over the public Queue** (branch
  `seat/workq`; [its brief](research/2026-10-05-claude-lead/briefs/seat-workq-brief.md)). It
  is the first recommendation of Codex's dogfood review. The two-worker crew takes its jobs
  from the Queue's public operations, as a second scenario. The first scenario stays as the
  control of the host protocol. The slice also shares one `note` through `Ref.updateWith`,
  and it gives the typed empty cell one home with two laws. Its first part is merged: the
  two helpers. The scenarios share one `note` (`Test/Dogfood/Scenario.lean`), with a control
  of a name collision. A term at a declared type is `ascribe`
  (`src/Effect4/Program/Authoring/Ascribe.lean`): a record with one declared field and a
  read of it, which is no cast. Four laws place it: scope, typing, its refusal and its
  reading (`src/Effect4/Laws/Modules/Ascribe.lean`,
  `src/Effect4/Laws/Program/Authoring/Ascribe.lean`). Its second and third parts are
  merged. The record `queue-workers` (`Test/Dogfood/Scenario/QueueWorkers.lean`) has 31
  named runs and 35 controls, 18 green and 17 red, and four planned goals under the premise
  `funded`: the tape
  of the run's own journal leaves no row unread. Its lowered runs replay on the generated
  engine, and 25 scripts run on rc.112 in the keyed lane, with the Queue's cell read
  through a writer of its own (`cellJson`). One finding is for the owner. Where the fuel
  ends inside a reply's application, `stepDecisionState` keeps the receipt `settled` and
  drops the commands that the fuel left. One measured run then stands at rest with no exit
  of the root (the named run `dropped`), and 25,260 bounded continuations of it give the
  root no exit. [Its receipt](research/2026-10-06-seat-WORKQ-receipt.md) is merged, and row
  284 records what it leaves open.

Merged on 2026-10-06, after the seats above began:

- **Seat REPAIR is merged: two small repairs of proofs**
  ([its receipt](research/2026-10-06-seat-REPAIR-receipt.md); `1504ae65` and the merge
  after it). `Queue.take_types` is one application of `waitRetry_answers`, and
  `Queue.offer_types` one of the new rule `waitAnswer_answers`, the typing of the wrapper
  with no loop (`src/Effect4/Laws/Modules/Waiting.lean`; row 279, point 5). `Waiter.Typed`
  served both forms with no change. The lift of `flushRootState` is general
  (`Lift.FoldLift.flushRootState_lift`, `src/Effect4/Laws/Machine/Lift.lean`), and the
  mask's statement is its instance. `Lift.admittedReplay_true` holds at every invariant,
  and the mask's copy is cut (row 278, point 5). No statement that a consumer reads changed.
- **Seat BRACKET is merged: a region ends at its entry's stack and at its entry flag**
  ([its receipt](research/2026-10-06-seat-BRACKET-receipt.md); row 280). A region is no
  syntax of the machine. Its entry is a cut of a run, and a later cut is inside it where the
  fiber's stack is own frames over the entry's stack. The region's end is the fiber that the
  pop of the own frames leaves, where no own frame answers. It has the entry's stack and the
  entry flag, for an arbitrary body (`compiled_region_bracket`,
  `src/Effect4/Laws/Program/MaskBracket.lean`; the registry claim
  `saved-mask-region-bracket`, R11). Its general form is over two machines that hold the
  chain's invariant (`saved_mask_region_bracket`,
  `src/Effect4/Laws/Machine/MaskBracket.lean`). A second claim is proved with it: at each
  cut of a compiled command loop, a fiber that a pending command steps has not exited
  (`stepped_live`; the registry claim `stepped-fiber-live`). Seat LIFT took that fact by
  reading, and it is false at a hand-written interpreter. No planned goal. The later cut's
  stack shape is a premise. So R11 keeps one open part of the mask, the carrying fact: a
  body's run keeps that shape until the command that ends the region. It is a slice with no
  seat, of the size of seat LIFT's second part.
- **Seat SEMW is merged: Semaphore's public operations**
  ([its receipt](research/2026-10-06-seat-SEMW-receipt.md); `aa70b078`, `4b57609c`,
  `ea036307`, `5fc17c3f`, `75ad13b7`, `831a76f3`). The two forms are `waitRetryAt` and
  `protectedBy` (`src/Effect4/Modules/Waiting.lean`; row 276, point 1), and the Queue's trees
  did not move. Both forms are typed once, for every module's part (the registry claims
  `waiting-wrapper-typed` and `protected-form-typed`). The six operations are library
  programs (`src/Effect4/Modules/Semaphore/Ops.lean`). Each keeps scope and is typed at every
  scope. Nine attempt laws relate one store step to the model's step, with no planned goal
  (`src/Effect4/Laws/Modules/Semaphore/Ops.lean`; R4, R10). The traces run on the Lean
  machine, with the two red controls of the protected permit
  (`Test/Program/SemaphoreTraces.lean`). Each operation prints and reads back. Ten programs
  agree with rc.112 in the truth lane, which has 63 programs. The case P9 replays on the
  generated engine, with its tape as data. No law of a run is stated: the wrapper's run, the
  walk across visits and the protected form's run stay open. Row 279 records what the
  receipt leaves open, with the runner's rule of the truth lane.
- **Seat LIFT is merged: the mask's chain at every live fiber of a run** (`d734aa6a`;
  [its receipt](research/2026-10-06-seat-LIFT-receipt.md)). A table of start flags is proof
  data: the machine stores no base. Each live fiber holds the chain at its own flag of the
  table (`MaskRuns`, `src/Effect4/Laws/Machine/MaskRuns.lean`). Each command keeps the
  invariant under one condition, on `Cmd.exitDone` alone, and the command loop discharges
  it. So every decision, tape and fuel keeps the invariant, at the compiled program's
  interpreter (`compiled_mask_chain_runs`, `src/Effect4/Laws/Program/MaskRuns.lean`; the
  registry claim `saved-mask-chain-runs`, R11). Each entry outside the machine that returns a
  machine keeps it, with no premise for the condition
  (`src/Effect4/Laws/Api/MaskRuns.lean`). Along a run, a live fiber's flag is a function of
  its stack. No planned goal. The bracket of a region was its open part, and seat BRACKET
  proved it since. Row 278 records what the receipt leaves open.
- **Seat CHECK is merged** (`0c4f9774`;
  [its receipt](research/2026-10-06-seat-CHECK-receipt.md)), in the seat that seat QINV
  freed. `typeOfProgram` tests the references' formation only
  (`src/Effect4/Program/Typing.lean`). `Api.explain` has no arm for a kept reference site
  (`src/Effect4/Api.lean`; row 273, point 2). No statement changed, and no program's answer
  changes. One statement is new: `Api.explain_eq_if_refsWF`
  (`src/Effect4/Laws/Api/Codegen.lean`). The seat proved it against the old definitions
  first, so it records that no refusal changed. The runtime root still imports no law.
- **Seat POOL is merged: Pool's cell and steps** (branch `seat/pool`;
  [its brief](research/2026-10-05-claude-lead/briefs/seat-pool-brief.md)), since seat REFS's
  merge freed a seat. It first runs the card's cases on our machine. Then it writes the
  contract, the model with its profile, and the cell with its five steps. It ends with the
  steps' typing and their agreement with the model. The public `make` and `use`, the close
  that waits and the finalizers' runs are a later slice. **Its eight steps and its receipt are
  merged** (`e212766f`, `e87777e9`, then `0cd730ca`). Every case of the card gives the profile's answer on the Lean
  machine, one schedule each (`Test/Program/PoolScenarios.lean`). The contract is
  `Test/contracts/pool.contract.md`. The model's profile is closed under its five
  transitions, with no planned goal (`src/Effect4/Laws/Modules/Pool/`). An idle item beside
  enrolled waiters is a state of the profile. The cell and the five step terms are typed,
  with no planned goal (`src/Effect4/Modules/Pool/`, `src/Effect4/Laws/Modules/Pool/Typing.lean`).
  Each step term agrees with the model's step, on every state of the model. The law is
  `pool_steps_agree`, with its five parts (`src/Effect4/Laws/Modules/Pool/Steps.lean`; R10).
  Each part was proved in place of its planned goal. They state no order of the wake across helpers, no
  cancellation law, no close that waits and no wrapper. Two cases replay on the generated
  engine (`ocaml/engine/test/pool/`; merged `c9428f73`). [Its receipt](research/2026-10-06-seat-POOL-receipt.md) is merged with its claims
  (`4667df9a`), and row 276 records what it leaves open.
- **Seat QINV is merged** (`13a77be6`;
  [its receipt](research/2026-10-06-seat-QINV-receipt.md)). On the first profile, one step of
  the Queue's model keeps its run invariant (`first_step_inv`). Both flags hold after every
  list of first operations from the empty queue (`first_run_flags`,
  `src/Effect4/Laws/Modules/Queue/Invariant.lean`; R12). Lean accepts Codex's invariant as
  written. It is the model's half of two open parts. The wrapper's run stays open.
- **Seat CUTS is merged** (`f3568844`;
  [its receipt](research/2026-10-06-seat-CUTS-receipt.md)), Codex's priority 4. A journal's
  tape has its cut and position connectors (`src/Effect4/Laws/Run/Tape.lean`, since row 287).
  The machine after a position is the raw replay of the decisions up to it (the registry
  claim `journal-position-replay`, R13). The first consumer is a lowered run's views at a
  fresh open (`shown_views_opened`, R8). Lean accepts Codex's four statements and its helper
  as written. The laws say nothing about the machine after a stopped row.
- **Seat MASKPOP is merged** (`2266ec30`;
  [its receipt](research/2026-10-06-seat-MASKPOP-receipt.md)), the third seat of the day. The
  saved mask's chain is kept through a pop of the stack: `saved_mask_pop_discipline`
  (`src/Effect4/Laws/Machine/MaskDiscipline.lean`; the registry claim
  `saved-mask-pop-discipline`, R11). It was proved in place of its planned goal. Lean accepts
  Codex's predicate and its three statements as written. The law is local to the frame
  machine. R11's open part is now its lift to runs, with a condition just before a command
  clears a fiber.
- **Seat PUB is merged: the Queue's first public operations** (branch `seat/pub`;
  [its brief](research/2026-10-05-claude-lead/briefs/seat-pub-brief.md)). The operations
  become library programs that capture no name of a caller. Each runs on the Lean machine, on
  the generated engine and on rc.112. The slice states no law of a whole run. **Its six steps
  and its receipt are merged** (`f046975b`, `c957bfab`, `5701a5dc`, `41be5ef3`, `c46e3ca1`
  and `bc0ee4c1`; [its receipt](research/2026-10-06-seat-PUB-receipt.md)):
  - the shared pieces of a module that waits (`src/Effect4/Modules/Waiting.lean`), and the
    five operations (`src/Effect4/Modules/Queue/Ops.lean`: `Queue.bounded`, `offer`, `take`,
    `poll`, `size`), each with its scope law. The wrapper has two forms over one `Waiter`: a
    wake invites another attempt, or the wake carries the decided answer. Every binder is
    minted;
  - seven attempt laws: each operation's own step is the model's step
    (`src/Effect4/Laws/Modules/Queue/Ops.lean`: `take_attempt` and its six siblings), and
    four forms over minted names. The facts about names hold for every caller environment.
    The comparison with the actual operation trees is a finite battery;
  - seven acceptance traces and the hygiene controls (`Test/Program/QueueTraces.lean`). Each
    trace is a finite control of one open part. Trace 7 measures the embedded budget. At one
    unit of fuel less than the measured least, the remaining work is lost, and later flushes
    do not end the root. That is the cut that row 226 excludes. No bound is claimed. The
    registry now names that open part `embedded-budget-sufficient`, under R12;
  - five Queue programs in the truth lane, and the control `pLateSeen` (`harness/truth/Truth.lean`).
    Each of the six agrees with Lean on rc.112 and on 4.0.1, on every field of the build
    ledger. The lane's Lean face now writes a fiber under its number in the recorder's order
    of first sight (row 274). The lane no longer checks the machine's allocation order. Two
    cells of the generated corpus's results moved, and no outcome moved;
  - each operation prints and reads back (`Test/Program/QueueFaces.lean`). Five runs replay
    on the generated engine on both carriers (`ocaml/engine/test/queue/`): R1, R4, a taker
    that waits, an interrupted taker and a masked caller.

  - each operation is typed at every scope (`bounded_types`, `size_types`, `poll_types`,
    `offer_types`, `take_types`; R4; merged `c46e3ca1`). The laws hold for every message
    type and every kept term of a caller. A string literal is not covered. The contract's seven connectors,
    the README's example and the architecture rows came with it.

  Row 275 records what the receipt leaves open. No law of a whole run is stated: the
  connectors 3 to 6 of the Queue's contract stay open.
- **Seat REFS is merged** (`c957bfab`;
  [its receipt](research/2026-10-06-seat-REFS-receipt.md)). It is the independent foundation
  proof of the owner's roadmap, as Codex's audit corrected it. A program whose layer
  references are well formed expands to a program with no reference site. The bound is that
  of `Eff.expandRefs` (`expanded_refs_nil_of_wf`,
  `src/Effect4/Laws/Program/ReferenceExpansion.lean`; the registry claim
  `reference-expansion-complete`, R5). The theorem landed as a planned goal and was proved in
  place. `typeOfProgram_expandRefs` and `checkTypedProgram_of_hasTy` each lose a premise, by
  the checker's equation `typeOfProgram_eq_if_refsWF`. A battery holds nine real programs,
  with four red controls. Seven old lemmas are now instances of one law, with their
  statements unchanged, and the proof-style baseline loses 16 lines. Row 273 records what the
  receipt leaves open.

Candidates with no seat, each with its place:

- the scenario driver's general laws in the law graph, with seat CUTS's five statements;
- the run-level law of the Queue's wrapper (row 275, point 2);
- Pool's public slice: `make`, `use` by the protected form, and the close that waits, with
  the closer as a request (row 276);
- two points of Codex's dogfood review of 2026-10-06
  (`research/2026-10-05-codex-foundation-packet/implementation-audit/dogfood-review-1406/`).
  Seat WORKQ's brief has the review's other two points:
  - the exact Routing example has no printed twin in the host lane. Two errors of tsgo 7
    keep it out. The repair carries the checked types of the branches to the printed
    Boolean select, with the reader's laws;
  - Atomic makes two commits and no transaction. A control of an interruption between them
    needs a reachable checkpoint first. The controls of a timeout under a mask and of one
    registration's cleanup are missing too;
- the carrying fact of a region, R11's open part of the mask (row 280, point 2);
- the byte forms of row 262, and the control files generated from Lean pins (rows 258 and
  264);
- two small repairs of the foreign readers (row 258, points 5 and 6).

Candidates for the plan after the handover (row 277), from Codex's capability packet of
2026-10-06. The packet is filed with a coordinator's note
(`research/2026-10-05-codex-foundation-packet/implementation-audit/capability-design-2026-10-06/`).
It is research: nothing is dispatched, and every new statement is uncompiled. Its evidence
is source inspection and finite models. Seat WORKQ's prepared slice stays first.

- **The checked focus** (`next-slices/focus/brief.md` there): a view of one program location
  that the checker itself derives. It shows the inherited bindings, the inferred type and the
  named constraints of each parent rule. Its domain is the admitted source route without
  references, with Routing and nested `iterate`. Four laws are proposed. A view's refusal is
  no refusal of the program.
- **One rewrite for straight programs and loops** (`next-slices/loop-rewrite/brief.md`):
  the removal of administrative suspensions by the identity fold. Its proposed law compares
  the bounded meaning at every budget, with the stores of an unfinished loop.
- **Exact selection, an edit of the same sort and a whole rebuild**, over `Node.replaceAt`
  and `Built.rebuild`.
- **A completed prefix's inspection and offline branches**, over `Run` and seat CUTS's laws.
- **A clock plan against one snapshot**, beside the clock-unit lane of row 231.
- **Later:** the insertion of a stored fragment under a scope, a claim's applicability to
  given subjects, causal views and the transport of live state.

Three repairs of 2026-10-06, outside any seat:

- the install rule of the `Makefile` keeps a linked package folder (`6e629bb4`). A seat's
  `make` had lost its `-o` flags and run `bun install` in the seat's worktree. The seat
  reported it, and its receipt records it. The coordinator's install did not change;
- the slow lane's fixture names `Term.fold` (`3f4cba07`). The census battery had not built
  since seat FOLD's append, and no sweep had run. The rest of the slow lane is not built;
- the dictionary gains "scenario" and "named run" (`c33d1b7d`).

Two relays of Codex came on 2026-10-06, after the owner asked it for deeper proof support and
for a watch on the proof graph. Both packets are filed with a coordinator's note, under
`research/2026-10-05-codex-foundation-packet/implementation-audit/`
(`heartbeat-1023-held-findings/` and `deeper-proof-support/`).

- Cache's card is corrected. An entry that left the map while its lookup was pending keeps
  an owner for its count: the detached records of the cell. The probe's new case CP9 gives
  one answer on both builds (`8b471a8a`). No ruling changed;
- the keyed lane's checked result has two aggregates: no entry waits, and the host itself
  measures every entry. The second is false for all four scenarios (`34db7582`);
- three evidence labels are narrowed. The minted builders promise a variable's reading
  (`1b2679f6`). The mask probe and seat MOVE's receipt say what each check holds
  (`d61522d3`);
- the proof graph shows a node's own placement: Codex's patch, applied unchanged
  (`27f6e5d6`). 27 placed nodes had no concept in the drawing before.

A third relay came later on 2026-10-06, at main `2ee2aa91` (`heartbeat-1136-pool-and-questions/`
under the same folder, with a coordinator's note).

- **Two actions waited for the owner's own word.** Codex recommended on each, and its relay
  said that a recommendation is no approval. The owner answered later that day:
  - the census row `interrupt.uninterruptible-mask`. Codex recommends the coverage `partial`.
    The row's comment then keeps two missing connections. No law relates a compiled mask to
    the native one. No law of runs gives the restoration after a nested body. The owner
    answered by voice: go with the recommendation. The coordinator read the transcript as
    the census row of the mask, and it told the owner that reading. The row is added, with
    five witnesses of `src/Effect4/Laws/Program/Typed/Mask.lean` and the two missing
    connections in its comment (`Test/Audit/RuntimeCoverage.lean`);
  - the install that seat CONTROLS's `make` made by mistake (95 MB, in that seat's scratch
    folder). The owner left the choice to the coordinator. The copy stays where it is.
    Nothing reads it, and no evidence rests on it. The incident's record is the seat's
    receipt;
- **Pool's brief is corrected before any dispatch.** It asked for an invariant that is
  false: no waiter while an item is idle and the pool is open. A return makes its item idle
  at once, and its helper selects later. The host's output shows two waiters at that point on
  both builds. The brief now asks for the rule of the step. Lease or enrol adds a waiter only
  when the pool is open and no item is idle. The case PP5 is no public schedule of the first
  profile, because `make` acquires every item first (row 267). It stays as a control whose
  state and count are premises, beside a public case. The card has both corrections. No
  ruling changed;
- Codex's reviews of the two running seats name no blocker. One label is to keep at seat
  PUB's merge. The facts about names hold for every caller environment. The comparison with
  the actual operation trees is a finite battery.

Landed later on 2026-10-05:

- **Seat T3b is merged** (`57b261a0`;
  [its receipt](research/2026-10-04-seat-T3b-receipt.md)). The eight read-modify-write rows
  carry a binder term, and the store step runs it with the node's environment. The faces
  spelled a term by one of five names until seat T5's part A, below.
- **Seat M0 is merged** (`ba0b6d38`;
  [its receipt](research/2026-10-05-seat-M0-receipt.md),
  [the lane note](../harness/truth/RELEASE-LANE.md)). `make check-truth-release` runs the truth
  harness on effect 4.0.1 beside the pin, and one build ledger holds each program's expected
  agreement. The target is in no sweep: the tracked recipe `ts/release` installs the release with
  its driver, and the lane does not pass on that install yet.
- **The builtin table of the OCaml route is data** (`8b236fa7`;
  [`lcnf-route.md`](core/lcnf-route.md) §9;
  [the note](research/2026-10-05-claude-lead/lowering-table/lowering-table.md)). A Lean binder
  named as a form's temporary captured a reference, and three definitions gave wrong answers.
  No generated module held such a binder. A form now binds nothing at a call site, and a check
  reads each translated declaration. The numbers did not move.
- **The compiler checkpoint passes again** (`21b7da47`). It was red since the generator merge
  reached five constants with no source rule.
- **The semantics registry follows the mask's rulings** (`cdf7551f`): two parts reworded and
  three added, all as proposed claims.
- **The compatibility policy names two host-lane rows** that the sweep moved (`d226d7a1`), and
  `check-conservativity` passes on the range again.
- **Seat FOLD is merged** (`87c9b562`;
  [its receipt](research/2026-10-05-seat-FOLD-receipt.md); rows 228 and 229). `Term.fold` is
  one constructor of `Term`, and the atoms `take`, `drop` and `sameHandle` are added. Both
  claims are proved: `fold-typed-atomic-update` and `handle-identity-laws`
  (`src/Effect4/Laws/Program/Typed/ListFold.lean`). The raw annotation collector reads an
  operation's binder term. A fold prints and reads back in a term position, and one printed
  fold agrees with both builds. The coordinator pinned the case policy again and promoted the
  build ledger.
- **Seat LOWER is merged** (`c09826c0`;
  [its receipt](research/2026-10-05-seat-LOWER-receipt.md); row 252). The conformance runner
  declares its roles and keeps a refused attempt. The target evaluator runs a list scan with a
  callback. `E4_be` forwards to `Eff_frame`. The law of `let x = e in x` is kernel-checked in
  the tool library, outside the trust ceiling: the target evaluator reaches `Classical.choice`
  through two `String` rules.
- **The Queue's abstract contract is in the tree** (`9abf99b6`): the packet
  `Test/contracts/queue.contract.md`, the model and its small controls, and the first general
  statement. Codex prepared them, and the coordinator built them. `acceptLoop_length_le`
  (`src/Effect4/Laws/Modules/Queue/Capacity.lean`) is proved. `positive_suspend_step_capacity` is proved too:
  one step of the model under `suspend` keeps the configuration and the buffer's bound. Its
  proof does not use the positive capacity.
- **Seat T5's part A is merged** (`b145687a`; rows 43, 212 and 251). A read-modify-write row
  prints its term as a function of the current value, `Ref.update(cell, (a1) => succ(a1))`.
  Lean's reader, `ts/eff/read.ts` and both foreign readers read it back. `read_print` and
  `read_exact` keep their statements and stay proved. No face spells one of the five names.
  The pinned truth check compiles the tuple control. Two truth programs are new, `pModifyFold`
  and `pQueueOffer`, and the lane agrees on 42. The coordinator pinned the case policy again,
  added `pFold` to the target selection and promoted the build ledger. The seat's receipt
  comes with part B.
- **Seat DOGFOOD is merged** (`b8c6ab2d`;
  [its receipt](research/2026-10-05-seat-DOGFOOD-receipt.md); row 254). Four scenarios run on
  the acceptance programs (`Test/Dogfood/Scenario.lean` and `Test/Dogfood/Scenario/`):
  - two workers with two pending replies;
  - exact handler routing;
  - atomic state with a failure and a cleanup;
  - replies at a timeout's boundary.

  A shared driver plays a script of moves. A gate ties each control to a clause of a placed
  claim. Four laws of the session are proved: `replays`, `receipt_inert`, `applied_selects` and
  `control_retires`. The last two stand in the law graph since row 287
  (`src/Effect4/Laws/Run/Rows.lean`). Each scenario's claim is proved modulo its planned goals. Eleven planned
  goals are new, all in batteries, and the goal gate counts 24. Nineteen lowered runs replay
  on the generated engine, on both instances: the engine's machine view is Lean's at each of
  101 positions (`ocaml/engine/test/scenarios/`). Every run is finite. No host run of a
  scenario existed at that merge; two scenarios run on a host since 2026-10-06, below.
- **A journal's machine is the raw replay of its tape** (`tape_replays`,
  `src/Effect4/Laws/Run/Tape.lean` since row 287; R8, the claim `run-tape-replay`). The coordinator proved the
  first of the scenarios' planned goals, at `[propext, Quot.sound]`. It holds for every run and
  every journal whose tape reads to its end. The tape holds the decision that the session
  hands the machine: for a reply application, the reply's own answer decision. So the
  statement needs no premise on the session. The goal as first stated named the selected key.
  That form needs each slot to hold a reply of its own key, and an arbitrary session record
  need not. The four fixtures did not move. The gate's own controls are a battery of their own
  with a fixture goal (`Test/Dogfood/Scenario/Gate.lean`), so the goal gate still counts 24.
- **The Queue's cell and its six steps are in the tree** (`3d9d935c`, the first part of seat
  QSTEPS; row 255). `src/Effect4/Modules/Queue/` is the first composed module, in a new layer
  of the runtime root above `Program`: the cell's type at a message type, its initial value
  and six step terms (`Cell.lean`, `Steps.lean`). Five steps are terms for one `Ref.modify`,
  and `sizeStep` is a term over the value that a `Ref.get` answers. The laws are beside the
  model, in `src/Effect4/Laws/Modules/Queue/`:
  - `Relation.lean`: the encoding table, the message map and the cell's value of a state;
  - `Steps.lean`: three proved connectors to the store (`step_updates`, `step_keeps_cell`,
    `cell_read`) and six planned step goals on `FirstProfile`;
  - `Typing.lean`: seven typing statements, each a planned goal.

  Since seat MOVE the table is `src/Effect4/Laws/Modules/Table.lean`, and the three connectors
  are `src/Effect4/Laws/Modules/Store.lean`.

  Four batteries under `Test/Program/` run the steps: eight scenarios on the machine, each
  step against the model on a finite universe, and each goal's conclusion on that universe.
  Thirteen planned goals came with it. **All six step goals are proved since,** each in
  place of its planned goal and with its statement unchanged (`c77376fe`, `75e4a688`):
  `takeStep_agrees`, `offerStep_agrees`, `pollStep_agrees`, `sizeStep_agrees`,
  `withdrawTake_agrees` and `withdrawOffer_agrees`, on the reading lemmas of `Reading.lean`.
  Each step term reads the model's reply, its next state through the table, and its signals
  in order, on every state of the first profile. `queue_steps_agree` assembles the six, and
  the registry's claim `queue-steps-agree` points at it (`962150af`). Two of the seven typing
  statements are proved too, `empty_typed` and `sizeStep_typed`. Five stay planned goals, by
  the seat's stop and by no counterexample. The checker answers the stated type for each at
  27 message types, by evaluation. So the goal gate counts 29. One workload runs in two
  spellings (`Test/Program/QueueWorkload.lean`). The seat's last part is merged (`80d73226`).
  Five runs replay on the generated engine on both carriers since seat PUB's step 5
  (`ocaml/engine/test/queue/`). `Test/Program/QueueFaces.lean` pins what prints and reads
  back. Each of the eight scenario modules prints and reads back since seat T5's second step.
  Five Queue programs run on rc.112 and on 4.0.1 since seat PUB's step 5, in the truth lane.
  Each of the six printed steps type-checks on the target there
  (`harness/truth/queue-steps.typecheck.ts`), and so does each of those five programs' modules.
- **`Deferred.make<A, E>()` prints from the operation and reads back** (`9600fa63`, step a of
  seat T5's part B; rows 212 and 251). An operation's type arguments are data of the
  operation: the printer prints each through the type printer, and Lean's reader,
  `ts/eff/read.ts` and both foreign readers read them back. One checked type reader serves
  them, with a named readable-type domain. An operation's types are program annotations, so
  raw formation and the integer scan reach them. p3's gate prints as
  `Deferred.make<void, never>()` and reads back. The coordinator pinned the case policy again
  for two new matches. No stored form changed its type.
- **A loop's stated cursor type reads back** (`98b56e62`, step b of seat T5's part B; DI-91's
  amendment). The checked type reader reads it, on the readable types. `read_print` and
  `read_exact` keep their statements. `ts/eff/read.ts` and both foreign readers read it
  through the same reader. p1's program, the timeout scenario's fetch and the Queue's eight
  scenario modules read back. `Test/Dogfood/Scenario/Faces.lean` pins that each of the four
  scenarios' programs prints and reads back.
- **The literal rule of `pair` and `tuple` is landed, and seat T5 is finished** (`cbd2ec57`,
  `1eadc78b`, `e9a3b1af`; row 256; [the receipt](research/2026-10-05-seat-T5-receipt.md)).
  The two helpers widen a number or a Boolean type in an immediate slot, and a string literal
  keeps its literal type. Six tuple pins moved, and the three registered differences are
  positive controls. Two truth programs are new: the rate limiter's request and a gate at
  `Deferred<void, never>`. The lane agrees on 43 programs, and p4 no longer waits on R4. The
  truth runner's import header is derived from the generated atom names. The coordinator
  promoted the corpus lane's results and the build ledger. The baseline policy names the 21
  corpus rows that moved in one column each. No verdict column moved.
- **The Queue's five typing goals are theorems** (`0b048da4`, part 1 of seat QTYPES; rows 255
  and 257). Each step has its stated type at every message type with `MessageTy`, proved in
  place with its statement unchanged. Each is the instance of a theorem at every scope, which
  the wrapper applies at its own scope. The checker's rules stand in their introduction form
  in `src/Effect4/Laws/Program/Typing/TermIntro.lean`, and they name no Queue. A name that
  `bindWith` mints is a caller's term under a step's folds (`captured_minted`). The goal gate
  counts 24: ten scenario goals, and fourteen fixture goals in the tooling's own controls.
  **The seat is finished** (`4834760e`, its last part;
  [the receipt](research/2026-10-05-seat-QTYPES-receipt.md)). The last part adds no node and
  no statement. It proves the positional read of a reply (`types_tupleAt`) and two facts of
  minted names for the capture's premise. Its battery types a take at a scope of three minted
  names. The registry places the two new modules under `store-typing`. Not proved: a string
  literal as a caller's term, and the wrapper's law at its own scope.
- **Two tooling repairs** (`e6d63ddb`, `db54a849`, `d5b4d9cb`, `34e9423a`). The engine's
  fixtures are a generated group, and a fixture that changes alone is written again. The check
  form refuses an output that aliases a lane, and a fixture folder with no writer. The plan's
  dependency walk gives no answer from an unfinished stack.
- **The retry form of the first acceptance program sleeps its base first** (2026-10-06; seat
  DOGFOOD's finding). It doubled its delay before its first sleep. The builds rc.112 and 4.0.1
  sleep 100, 200 and 400 ms at a base of 100
  (`research/2026-10-05-claude-lead/retry-probe/`, one host run each). `Test/Dogfood/P1HttpCache.lean` now pins the sleeps' deadlines, which no guard
  read before. The timeout scenario's scripts and its engine fixture follow.
- **The fixtures group runs while the build is red on a stale fixture** (2026-10-06). Its
  marker depended on traces whose rule is `build`. A changed program then made the build
  fail on the old fixture, and the group could not write the new one.
- **The conservativity check's verdict clause judges verdicts** (`7f77bd03`, `0b214886`; row
  172's amendment). A corpus row that moves in printed length alone is reported and not
  refused, under one validated header. Codex found a false acceptance in the first repair,
  and three controls hold its correction.
- **Seventeen worktrees of finished seats are removed,** on the owner's word. Their unique
  notes and one uncommitted patch are kept under
  `research/recovered-worktrees/2026-10-05/` (on disk, not tracked).

Open at this landing:

- the Queue's whole transition contract is written
  ([the contract](research/2026-10-05-claude-lead/queue-contract/queue-contract.md), with its
  model). Its choices are ruled (rows 240 to 243), and it was corrected after Codex's review.
  The Queue's path lands in three parts:
  1. **The pure contract and its capacity proof.** Landed on 2026-10-05 (`9abf99b6`), and the
     step's capacity statement is proved since. The model and its proved statements are in the
     law graph since the same day (row 255), and the registry names two of them:
     `queue-step-capacity` and `queue-first-profile-closed`. Codex keeps the proof's route
     ([its review](research/2026-10-05-codex-foundation-packet/implementation-audit/open-questions-review/queue/review.md));
  2. **The cell's encoding and each step as one term,** which agrees with the contract's step.
     The fold and part 1 are in the tree, so it can start. It needs neither T5 nor the mask.
     Its design is [written](research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md)
     and twice revised after Codex's reviews. Its five choices are ruled (row 255). Its step
     goals quantify
     over a closed predicate, the first profile's states: `FirstProfile`, with its closure
     proved (`first_profile_closed`, `src/Effect4/Laws/Modules/Queue/Profile.lean`). Seat QSTEPS has
     it since 2026-10-05 (branch `seat/qsteps`;
     [the brief](research/2026-10-05-claude-lead/briefs/seat-qsteps-brief.md)). A service error
     stopped its first run before any commit, and it started again the same evening from
     `7f77bd03`. The seat is finished and merged in five parts, the last at `80d73226`
     ([its receipt](research/2026-10-05-seat-QSTEPS-receipt.md)). They hold the cell, the
     six steps, the relation, the six step theorems and two typing theorems. They also hold
     two scenarios on the engine, the faces' pins and the documents. Open: five typing
     statements. Seat QTYPES had them
     from 2026-10-05 (branch `seat/qtypes`;
     [the brief](research/2026-10-05-claude-lead/briefs/seat-qtypes-brief.md); row 257), and
     all five are theorems since 2026-10-06. It
     states the checker's rules in their introduction form and a typing judgment beside
     `Reads`. It proves the capture of a minted name, and it types each step at every scope. The wrapper's
     law takes a step's typing equation as a proof parameter. A concrete application
     discharges it by the checker's own answer on its actual body (row 257, after Codex's
     review). The owner ruled the design's five proposals as recommended
     (row 255). Codex's design research
     ([its synthesis](research/2026-10-05-codex-foundation-packet/implementation-audit/queue-dogfood-design-research/recommendations.md))
     is taken into the design and the brief. `Authoring.foldWith` mints a fold's two names,
     so a step's helper cannot capture its caller's variable
     (`Test/Program/FoldHygiene.lean`). The accept pass is the model's closed form, and the
     first cell holds four fields;
  3. **The public path:** the operations that wait, the posted signal, the module's rows and
     its law, and the printed form. It follows T5 and the mask (row 251). Codex's research
     proposes a private helper for the take's loop, whose last arm never runs.

  Two probes ran `take` and `offer` as programs on the machine
  ([the note](research/2026-10-05-claude-lead/queue-readiness/queue-readiness.md); finite
  probes). The second uses the real steps: one `Ref.modify` whose term folds, the posted helper
  of row 238, strict order, an offer that waits at capacity, and a withdrawal that keeps the
  interruptor. Eight scenarios answer as expected. Each of the six steps is compared with the
  model's step: the reply, the stored value and the ordered notifications. The comparison
  agrees on 200 states of the first profile, and it refuses a state outside it (revised twice
  after Codex's reviews). The
  cleanup is the pin's `onInterrupt`: `onExit` with `causeIsInterrupt` on the exit. Not
  probed: the generated engine, a masked caller, batches, and the printed module on a host,
  which waits for T5;
- the four scenarios of the acceptance programs are merged (row 254), and these parts are open
  ([the receipt](research/2026-10-05-seat-DOGFOOD-receipt.md), items 8 and 9):
  - ten planned goals, each in its battery with its placement. The eleventh, `tape_replays`,
    is proved;
  - the host half: a scenario's whole observation on the printed module, on the keyed lane.
    The four programs print and read back (`Test/Dogfood/Scenario/Faces.lean`). The keyed
    recorder needs one extension, an operation that completes after its cancellation.
    Seat HOST has it since 2026-10-06 (branch `seat/host`;
    [its brief](research/2026-10-05-claude-lead/briefs/seat-host-brief.md)). It took the slot
    that seat QTYPES freed. **The seat is finished, and all four scenarios run on a host**
    (`11616581` and `aef8f049`; [the receipt](research/2026-10-05-seat-HOST-receipt.md),
    [the design note](research/2026-10-05-seat-HOST-design.md)). Each script of a battery is
    performed on the scenario's printed module on rc.112, and Lean replays the host's
    recording. The receipt's table gives each entry of each observation with its source of
    evidence: the host, the ledger, a reader, or the replay alone. Three limits stand:
    - a reader is a spy in the harness. The lane runs each script with no reader, with its
      readers and with each reader alone, and it compares the recordings byte for byte;
    - timeout's whole observation waits on `timers` in 5 scripts, where a timer's fiber has no
      call to name it. One atomic script has no host run for the same reason;
    - the host driver restated each control's script, because a battery held the script
      inside a Boolean expression. A changed script of a battery did not reach the host
      runs. **The repair is merged** (`4ffdf83f`, row 266;
      [the receipt](research/2026-10-06-seat-CONTROLS-receipt.md),
      [the brief](research/2026-10-05-claude-lead/briefs/seat-controls-brief.md)). A
      scenario's record lists each script once, as a named run, and a control names the runs
      that it reads. The gate plays each run once. The host driver and the engine's lane take
      their runs from the records, so one name has one script on every lane. Five runs of the
      engine's fixtures took the batteries' scripts: two were stale copies that the retry
      repair had missed. The lane's red control reads the last decision that moves the view.
      Three follow-ups are merged too (`1ffa7438`). The run `timeout/parked` has its control.
      The gate refuses a run that no control reads. The script of `timeout/before` has one
      name, so the host lane performs 14 timeout scripts;
  - the semantics report loads the five scenario modules that hold a claim, so the plan shows
    the ten open goals as its next goals. A requirement with a placed scenario goal is proved
    only when that goal is. Every requirement was open before, and none changed status;
  - the driver's general laws are still in the battery: `tape_replays` with its tape, and the
    three session laws. The seat proposes their move into the law graph, beside
    `play_controls_eq_replay` and the session's laws (its receipt, item 9.5);
  - a fixture edited alone is not bound by `lake build`: Lake does not take an `include_str`
    file as an input. A fresh elaboration of `Test/Dogfood/Scenario/Lowered.lean` binds it.
    The Queue's engine fixture had the same gap (`Test/Program/QueueEngine.lean`). The
    generated group `fixtures` closes it for both lanes (`docs/GENERATED.md`). Its marker
    depends on the fixtures themselves. `make gen-fixtures` writes a changed fixture again
    from Lean, and `make check-gen` refuses a committed fixture that Lean does not write;
  - two controls are not written: a cleanup replayed under one registration, and a timer that
    fires inside a masked region;
- the faces of an operation's type arguments, part B of the state plan's T5, are landed, and
  seat T5 is finished ([the receipt](research/2026-10-05-seat-T5-receipt.md)). One checked
  type reader serves an operation's type arguments and a loop's stated cursor type, on the
  readable types. Open from that slice:
  - a list fold's stated accumulator type is printed and not read (the receipt's item 11.2);
  - `Ref.make<A>` needs an appended constructor (row 210). It is a slice of its own after the
    Queue's path, and the receipt names the constructor to append and the one to retire;
  - the receipt proposes ten decisions rows and one text for R4's row of the system map, for
    the owner;
  - `harness/tsdiag/run-tsdiag.mjs` keeps its own hand copy of the import list;
- seat FOLD left three points for the owner or for T5
  ([its receipt](research/2026-10-05-seat-FOLD-receipt.md), item 9): the argument order of
  `take` and `drop`, the typing of `sameHandle` by the raw head, and a list of number literals
  on the target. Seat T5's part A repaired the third: `cons` has a second type parameter, and
  its ratification is among the seat's proposals;
- the mask's second note is [written and ruled](research/2026-10-05-claude-lead/mask-second-note.md)
  (rows 244 to 246). Seat MASK has its slice since 2026-10-06 (branch `seat/mask`;
  [the brief](research/2026-10-05-claude-lead/briefs/seat-mask-brief.md)). Its first step is
  merged (`811ac973`). It appends `Eff.restore` and `ActionTerm.getInterruptible`, and it
  adds the saved state's type. Every proved theorem that matches on the two has its case.
  The engine has a lane, `ocaml/engine/test/mask/`. At that merge the coordinator pinned the
  case policy again and moved one pinned count of the reader's tests. The coordinator also
  wrote the truth modules again and named the two constructors in the baseline policy. **The seat is finished** (`8528496f`;
  [the receipt](research/2026-10-05-seat-MASK-receipt.md)). Five registry claims are theorems
  (`src/Effect4/Laws/Program/Typed/Mask.lean`, `src/Effect4/Laws/Codegen/Mask.lean`). Three
  truth programs run the mask on rc.112 and on 4.0.1, and each agrees with Lean. Four points
  stay open:
  - the mask's law is proved at the boundaries of regions. One statement is an invariant of
    runs: a region that changes no flag ends with its entry flag. It is tested, not proved,
    and an open part of R11. The first wrapper under a masked caller is its consumer. A
    candidate invariant has a finite probe since 2026-10-06
    (`research/2026-10-05-claude-lead/mask-probes/MaskStack.lean`). On each fiber's stack the
    mask frames alternate from the negation of its flag, and the flag under them is constant.
    The probe runs 16 scenarios of the mask and of the Queue, with cuts at scheduling
    points. It compares a fiber's base only while the fiber is live, so it says nothing of
    the flag at a fiber's exit. It is no check that the cuts cover a whole run. No goal
    states the invariant yet;
  - the runtime census has a row for `uninterruptibleMask` since 2026-10-06, with the
    coverage `partial`: `interrupt.uninterruptible-mask`. The owner approved it as Codex
    recommended. Its comment names the two missing connections;
  - no law relates the compiled form to a release's own mask;
  - the truth lane's row `resumed k` means a parked fiber that runs again, whatever woke it.
    Lean's reduction wrote it for a token's resume alone. The repair moved no corpus row;
- the design of waiting, tasks and the atomic frontier is
  [written and signed off](research/2026-10-05-claude-lead/waiting-design.md);
- the migration plan to 4.0.1 is [written](research/2026-10-05-claude-lead/migration-plan.md)
  (row 248), and the owner accepted its mechanics (row 253; the plan's F8). Its first slice
  landed with seat M0. No slice is scheduled: a cut-over runs when a feature, a semantics or a
  proof needs it. The census by row and the impact query run with the first one;
- the release's driver is installed by the tracked recipe `ts/release`. It changes one type:
  `SqliteClient.make` can fail with `SqlError`. Four of the five SQL modules then fail the
  release's type check. The five ledger lines are deferred with their reasons, and the row
  `sqliteOpen` keeps the pin's `never`. The release lane runs on an install without the driver
  ([the lane note](../harness/truth/RELEASE-LANE.md); the plan's F7). Whether opening a
  database fails with a typed error is open;
- the release audit, landed on 2026-10-05
  ([the audit](research/2026-10-05-seat-A401/audit.md),
  [its receipt](research/2026-10-05-seat-A401-receipt.md)). For this tree 4.0.1 is a new runtime
  revision. The seat's proposals A, B and D to I stay open inside the migration plan. Three
  small repairs wait for a seat:
  - the citations that miss in the pin itself;
  - one census row that holds its digest twice;
  - a role row for `vendor/effect-4.0.1`;
- one small cleanup from Codex's review of 2026-10-05 is landed with seat MOVE (`b199c15f`;
  `research/2026-10-05-codex-foundation-packet/implementation-audit/list-lemma-review/recommendations.md`):
  - five general list facts move from `src/Effect4/Laws/Program/Template.lean` to
    `Effect4.Constructive.List` in `src/Effect4/Data/Constructive.lean`, with their statements
    and proofs unchanged;
  - `lookup_weaken` of `src/Effect4/Program/Typing/Rules.lean` is exposed, and the copy
    `getElem?_weaken` in the fold's law module goes.

  The seat made the shared data module's edit once, with nine more list facts of the two
  modules;
- the OCaml route, after seat LOWER's merge:
  - the target evaluator is outside the trust ceiling. Its rules for the length of a string
    and for the order of two strings reach `Classical.choice`. The seat proposes their byte
    forms as a slice of its own, with a control for the order of strings. Then a lowering law
    is a declaration of a battery. The owner ruled the byte forms (row 262), and the slice
    has no seat and no date;
  - the registry's claim for the law of `let x = e in x` waits on that slice;
  - seven callback names of the builtin table have no rule in the evaluator, and a call is a
    refusal;
  - the compiler checkpoint runs in the CI job `check-ocaml`, at a push, a pull request or a
    manual run (`.github/workflows/lean_action_ci.yml`). That is a reading of the
    configuration, and no remote run is checked. Since `0acec081` it also runs in the local
    sweep, as `make check-compiler` (row 263). The runner's own script tests run by hand;
  - the emitted OCaml read back by the compiler's own parser waits for a design of its own;
- the proposed decisions rows of four seats' receipts (T3b, M0, LOWER and DOGFOOD), for the
  owner;
- Codex's research on the TypeScript compiler boundary is filed
  ([its recommendations](research/2026-10-05-codex-foundation-packet/implementation-audit/tsgo-research/recommendations.md);
  source reading, and no compiler run). It proposes an optional compiler client beside the
  Lean `typescript` package, extracted from the target oracle and its checker. The Effect
  admission and the comparison of answer, error and requirement types stay in this tree. The
  owner ruled its boundary (row 264): the client is built inside `tools/target` with its next
  caller, and no package is published. Its one small finding landed with seat T5's part A:
  the pinned truth check compiles the tuple control;
- Codex's research on macros and declarations is filed
  ([its report](research/2026-10-05-codex-foundation-packet/implementation-audit/macro-research/report.md);
  source reading, and no Lean run). It proposes four small changes and no macro framework:
  - a row builder that mints the current value's name, `performTermWith`, beside
    `Authoring.performTerm`, with generated `Ref.modifyWith cell fun current => …` wrappers
    and their scope laws. A fixed name around a caller's term can capture a variable:
    `Test.Dogfood.Scenario.Atomic.note` is such a helper, and no present caller meets it. It
    is landed (`0a10ca6d` and `8e9b9736`, 2026-10-06). `Authoring.performTermWith` mints the
    name. Each of the eight rows of `Ref` that carry a term has a second generated wrapper,
    with the suffix `With`: `Ref.modifyWith cell fun current => …`.
    `selectOptionWith` and `onExitWith` are the same form for an option's payload and for an
    exit. Each has its scope law, and `Test/Program/AuthoringContract.lean` holds the
    controls. The checks were narrow builds, and the default build runs at the next merge;
  - a record's type derived from its one field declaration, in p4 as in p5;
  - one identity record beside each vendored source, read by the census and the variances;
  - one host adapter, `kvGet`, generated from explicit contract data.

  The last three have no seat and no date;
- Codex's six reviews of 2026-10-05 and 2026-10-06 are filed, each with the owner's relay
  as pasted. The first is
  `research/2026-10-05-codex-foundation-packet/implementation-audit/decision-probes/`. Beside
  it are `next-proof-review/`, `module-factory-review/`, `heartbeat-0451-fixtures-semaphore/`,
  `graph-tree-research/` and `heartbeat-0553-semaphore-qtypes/`. Their evidence is source reading, compiler probes
  and finite controls, with no Lean run:
  - the first probes the literal repair and the typing of the Queue's steps (rows 256 and
    257);
  - the second orders the next proofs. Seat QTYPES has the shared typing rules and the
    capture of a minted name. The mask comes next, then the Queue's public path. Fixture
    freshness joins the generation graph. `Routing.infrastructure_escapes` is the first
    scenario goal to prove. One stale reading is corrected: the admission gap is closed, and
    `Api.Built` retains a program's admission;
  - the third asks for breadth and a module factory, and it keeps R1 to R13 on the plan. It
    proposes first profiles for Semaphore, Pool and Cache, which no one has ruled;
  - the fourth found two gaps in the fixtures group, which are repaired. It also found one
    wrong reading in Semaphore's card: a resumed waiter runs inside the wake's walk. The card
    is revised;
  - the fifth proposes one foundational slice with no seat yet: well-formed layer references
    give an expansion with no reference left, at the existing bound. Its claim would be
    `reference-expansion-complete`, under `initial-algebras-folds`, for R5 and R8. It also
    proposes cut laws for a journal's consumed prefix, for the scenarios' tapes. Both are
    candidates when a seat is free, beside the module slices. Codex's audit of the owner's
    roadmap corrects both targets (`roadmap-audit/`, filed beside the others):
    - a checked caller already has the fact, by `TypedProgram.expanded_refSites`
      (`src/Effect4/Laws/Program/CheckedTyping.lean`). The proof's consumers are the converse
      `checkTypedProgram_of_hasTy` in that file and `typeOfProgram_expandRefs`
      (`src/Effect4/Laws/Program/ReferenceTyping.lean`). It keeps the layers' sharing at run
      time;
    - a cut gives the prefix before a stopped command, and that command may already have
      changed the machine. `driveState_add` (`src/Effect4/Laws/Machine/Approximation.lean`)
      splits the command loop's fuel, and row 226 still owes the driver's outer continuation. The first connector of `Lowered.shown` is stated
      at a fresh `Run.open`;
    - a transaction's body stays the admitted part of `Eff` that row 223 rules, and no second
      representation;
  - the sixth reads the coordinator's Semaphore probe. A grant at the wake is a policy of its
    own: on the pin a resumed caller's next request takes inside the walk. A visit of the
    live scan reaches the resumed caller's work up to its own cut. The card follows both. The
    same review found no new defect in seat QTYPES's last part;
  - the owner's guidance came with all three. Automate the repeated checks. Keep a question
    for the owner to a change of meaning, of the supported domain or of a representation;
- two red lanes of the sweep of 2026-10-05:
  - `check-tsdiag`: its harness copied the prelude without `prelude-atoms.gen.ts`, so every
    typed program reported a module error (seat T3b's reading). It is repaired (row 295);
  - `check-schema-ts`: its host packages are not installed.

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
[`docs/research/history/post-phase-c-synthesis.md`](research/history/post-phase-c-synthesis.md), checked against
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
module instantiates. The regenerated architecture map (`make gen-architecture`) found three
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
- The architecture map (`make gen-architecture`, a build artifact under `.lake/gen`) is regenerated from the tree.

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
and D3 in parallel and J. Seat H2's row-154 re-pin landed (merged `84bdf454`): the design basis is
exact at `6b3f2c92`, and the system map's glossary sites are re-pinned there.

**Wave 2's first landings (2026-10-01).** Seat J merged (`93360b3a`): rows 24 (every binder the
authoring surface names is minted), 16 (`Await` a record) and 17 in part (codecs for the reading
types, a `Refusals` group); seat G's owed items; `check-host-protocol` on tsgo 7; the ingest's parser
ruled to the native API or oxc (row 168, seat J2). Seat D1 merged (`a3db653c`): rows 152 (membership
at an exit type excludes shape defects; the close walk typed at the exact post) and 153 (M5 over the
expansion through the redirect lemma) landed; row 117's side condition landed, its presence clause
proved not walk-invariant and stopped; row 151 measured and stopped: both need the owner's ruling
(rows 117 and 151). Probe S merged (`4bb22835`): the Schema side of every form on a copy, the
readable profile (row 169), the defect-id counterexample (`E4-SCHEMA-CE-061`), row 8's (C) clean.
Seat W0 landed lean4-typescript 0.7.0 in the package's own worktree (`wave/typescript-0.7` at
`f5878bf`, row 164): the push to `pure-algebra/lean4-typescript` and the pin at the wave's commit 8
are owed. Seats D2 (M5's denotation lemma, brief-D2 with its amendments) and J2 (row 168, `check-tsgo`
into `check`, seat J's owed items, brief-J2) dispatched from `bd5462df`. Codex's 20:16 review folded: the
name-set shortcut for union branch separation is refuted at optional fields (`E4-SCHEMA-CE-062`, row
122 amended) and `DenotesTyped` plausibly lacks the reference-formation premise (row 170, seat D2
measures first). The owner ratified row 151 (a″) and row 117 as recommended and had the package branch
and tag pushed (`v0.7.0` at `f5878bf`); seat D4 lands row 151 (a″) and the closed-row premise.
Probe Q merged (`818c26ff`): the generator work lands alone before the append with byte-identical
outputs (row 171, seat W2), conservativity as one command (row 172; the promotion of the four stale
`Ty` constructors is the owner's), the per-constructor tables' cut-over (row 173), two tooling gaps
(row 174). Probe P merged (`714d2601`): every law the wave needs proved on one
production-shaped copy; row 128's exactness theorems proved by construction (W1's route (b)); the
leaf-order table (row 177, ruled); required-below-optional (row 178) and the `N_S` annotation policy
(row 179) ruled; the number images must nest, so the wave's commit 3 lands the two frames after all
(rows 121, 109 amended twice). lean4-typescript 0.7.0 is pinned on main with W0's consumer diffs
(row 164 closed); seats W1 (commit 1, route (b)) and W2 (commit 2, the generator) dispatched from the
pinned head. Codex's 20:46 and 21:16 reviews folded: the conservativity checker's invalid-revision
false PASS (row 172 amended, W2) and the check-annotation profile mismatch (row 179 amended, W1). Seat D3 merged (`7d50cfe6`): sixteen ledger goals closed (the ledger 21 open of
484), eight refuted with five clauses ruled as row 134 (a)–(e) for the next command seat (D5); the
registered-handle-bytes premise of M7 is row 180. Probe U merged (`b5501b82`): every `Ty` traversal is an
algebra of one fold over two per-constructor tables or the signature (row 182, ruled with D-U1 (a), D-U2
JSON, D-U3 the clause as written); the machinery lands in commit 2 (W2, amendment 4), the rule's gate at
commit 4 (W4); three latent findings seeded (`E4-FACE-CE-001`–`003`). Codex's 22:16 review folded: U's rule checker
passes missing evidence (row 182 amended; W2 adds evidence validation and three controls); W1's
branch confirmed repaired on the check-annotation profile. Seat W1 merged (`cdd62673`): row 128 landed by
route (b) (`decode_iff`, `ofSchema_exact`, both at `[propext, Quot.sound]`), the defect id repaired
(`E4-SCHEMA-CE-061`), row 179's one policy at every annotation bag with nine erased keys; S7 holds at
today's forms. Seat J2 merged (`b15d57b3`): row 168 landed (the ingest on oxc and tsgo 7's own
API; `typescript@5.9.2` gone; `check-tsgo` in `check`), the ingest lane green again, the authoring syntax
scoped (row 17 landed; `E4-AUTHOR-CE-002` repaired). **The owner's instruction (2026-10-01 evening): nothing new starts; the four
seats in flight (D2, D4, J2, W2) stop at a coherent place and hand back; then the coordinator's
documentation and focus pass** (`docs/research/2026-10-01-landing/status-2026-10-01-evening.md`
holds the read: what landed, where both lines stand, what is in the way, the pass's seven steps).

**The type-language probe's first result (probe T, 2026-10-01, merged `8036f0b4`; rows 157–164).**
The data wave can finish `Ty` once only if its single append also carries a structured nominal
reference, `Ty.app name args` (row 3 revived as row 158): the corpus names Effect module types 1,928
times across all 15 projects, and the handle spelling cannot carry a record argument, a parameter or
covariance. The wave's set (one `Val` append, then one `Ty` append, row 162): records with optional
fields (157), tagged unions of records (130), error payloads printed as `Data.TaggedError` classes
(120), keyed maps (125), tuples (159), `app` (158), `int` inhabited and a binary64 `number` (121,
recommended (a)), `null` and `undefined` (160), `bytes` by the owner's choice (161). After it, `Ty` is
closed: later named types enter as Σ_app declarations through `app`. What full reification still
lacks is outside the type language. Probe T's largest count, 26,175 of 59,987 corpus units shaped as
functions of their inputs, is the ingest lane's statistic about foreign TypeScript, not a product gap:
the language cut rules no function values (a program's inputs are its environment, its parameterised
rows are templates), and DI-21 stays deferred until foreign lift is a goal (row 163, ruled by the
owner). Decoding inside a program (row 123) is next after the wave, and
`Schedule`, `Stream`, `Config`, the stateful modules and the host packages have no admitted member.
The runtime coverage report counts the fiber runtime only. Its block, from the working tree
of the commit that adds the mask's row (2026-10-06):

```
Effect rc.112 runtime coverage: denominator 136; owned-with-green 8/136;
green 132, partial 3, absent 0, diverged 1; census 138 rows, 2 excluded
partial: op.Failure interrupt.uninterruptible-mask layer.launch-holds-scope
divergence: checkpoint.exit-failcause-skip; U-01; Test/Counterexamples/Machine/Semantics/InterruptEscape.lean
```

Probe R (merged `1b2bd11d`; rows 165–167, register `E4-RECORD-CE-001`–`012`) found that row 119's
positional record values make projection type-directed while every evaluator and reader is
type-blind, and one positional value fits two branches of a union of records; it recommends values
that carry their canonical names in the existing frames (row 165 (a), the owner's ruling owed), two
`Term` constructors for construction and projection (166), and the field-name domain with computed
keys for `__proto__` (167). Probes P, Q and S are running with that shape in hand. **The data wave started 2026-10-01** on
the owner's instruction, in parallel with wave 2 ([the series and its seats](research/2026-10-01-data-wave/README.md));
its `Ty` append follows D1's merge; seat W0 (the lean4-typescript bump, row 164) is first.
The system map's new §10 states the five constructions the tree rests on and the seven stability
criteria with their status; "stable" is a theorem of the tree once S1–S7 hold, and the open counts are
the distance.

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
assembly is replaced by the explicitly open `park_extension`. The focused typed-state check (since
retired), `make build` and `make check` pass. The older look-ahead's namesake-first closure forecast and
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
| `docs/core/semantics.md` | the language's judgments by concept (ten): the literature each adopts or adapts, the cuts by decisions row, the definitions in the tree, the required properties (the glossary moved to `docs/core/controlled-english.md`); the statuses are generated (`generated/semantics.md`, `make gen-semantics`) from `tools/Tools/SemanticsRegistry.lean` |
| `docs/core/host-boundary.md` | the external-reply lane: how host answers flow today, the known holes with evidence, the boundary contract (lifecycle, handle declarations, membership matrix, entry paths, controls), the interim profile and the order |
| `docs/research/history/coherence-principle.md` | history: scout F's principle in full, the seven squares, the arrows lacking obligations |
| `docs/core/traversal-census.md` | the census numbers, every hand traversal by root, the converter design |
| `docs/core/decisions.md` | every open decision, one list (status by row; rows 44–45 record the approved world and rows 78–85 the state/refinement proposals and 86–88 the foundation contracts) with the order |
| `docs/research/history/language-cut.md` | history: the language-cut analysis and profile/cut distinctions; live whole-pin dispositions and remaining work are in the post-Phase C plan §11 |
| `docs/core/api-surface.md` | the consolidated API and its awkward constructs |
| `docs/core/lcnf-route.md` | what the LCNF lowering handles and refuses; the LLVM-shaped architecture |
| `docs/core/machine-state.md` | The state and log owners, proposed representation changes, conditional transaction profile, and shared basis for the surveyed stateful modules. Approved world and open choices are separated; the implementation plan and supporting research are tracked under `docs/research/` |
| `docs/DESIGN-ISSUES.md` | the DI register (rulings are made only when written here) |
| `docs/ARCHITECTURE.md`, `docs/GENERATED.md`, `docs/DESIGN-BASIS.md`, `docs/research/history/DESIGN-MAP.md`, `docs/RUNTIME-COVERAGE.md` | the tree, the generated groups, the DB register, the earlier five-layer map (history) (superseded in substance by `docs/core/system-map.md`), the runtime census |
| `.lake/gen/architecture-map.html` | a build artifact, not committed: the measured architecture map: the roots at their declared heights, the import matrix, every import against the direction, the typed-state stack with its planned modules, the file map by role; regenerated from the tree by `make gen-architecture`, roles declared in `tools/Tools/ArchitectureRoles.lean` |
| `docs/research/history/post-phase-c-synthesis.md` | history: the checked post-Phase C review and full proposed execution plan: false pending statement, relational predicate gaps, decision reconciliation, slice contracts, controls and evidence; not an owner ruling |
| `AGENTS.md` | the operating rules, with one line per core term pointing into `docs/core/controlled-english.md` |
| `docs/core/controlled-english.md` | the writing rules for every Markdown artifact and the dictionary: one meaning per word, its tree anchor and its literature term (`make check-language`) |

## Next, in order

The active sequence is the foundations review above. Phase C's existing receipt remains
historical evidence; the dated notes below explain the redirect and its earlier plans. They
do not override the corrected protocol-before-assembly order or constitute a new pause instruction.

**Short-term backlog, 2026-10-03 (owner): the core documents cleaned up.** The documents that
development, meta tooling, PL design and semantics read are brought to the writing rules. Scope:
- this file, as an entry point true at HEAD (tooling map item 3.4);
- the eight authorities under `docs/core/` that do not yet pass;
- `docs/DESIGN-BASIS.md`, `docs/DESIGN-ISSUES.md`, `docs/ARCHITECTURE.md` and `docs/GENERATED.md`.

These 13 documents hold 932 of the 1,776 findings (`python3 scripts/check-language.py`). Done when
each passes `python3 scripts/check-language.py --strict` and `make check-docs` stays green. Method:
one time-boxed dynamic workflow, one agent per document group, run when the owner confirms it.
Two owner decisions come first: the language seat's P4 (the design basis cites witnesses by name
and path) and the shape of this file (3.4). The contract packets and the READMEs come later.

**Scheduler Contract Hardening & Milestone Status, 2026-10-02 (current).** Four command contracts
are repaired and ratified, eliminating checked refutations without weakening theorems:
1. **Queued enrollment bound** (decisions row 134 (e), `E4-TYPED-CE-032`): `EnrollRaceOk` bounds queued children
   below `nextId`, preventing unallocated fibers from passing compatibility vacuously before `launch`.
2. **Scope-exit callback position** (row 188 (a), `E4-TYPED-CE-034`): The raw `scopeExit` marker remains in
   the semantic program carrier, but ordinary `TypedProg` admission excludes it. The scope callback is admitted
   at the `scoped` guard's run position and saved slot (`scopedGuard`, `scopedResume`). This repairs the typing
   contract around the evaluator's explicit `badShapeExit` fallback; it does not remove syntax or prove general
   loop/delivery preservation.
3. **Registration callbacks under injected yields** (row 188 (b), `E4-TYPED-CE-033`): The host-stack judgment
   composes ordinary frames and registration arrows that carry race existence, the matching host and token typing.
   It admits the injected-callback shapes while requiring those correlations. Preservation by the actual
   injected yield and subsequent walk is part of the loop and delivery proofs, proved 2026-10-03
   (`loop_preserves`, `deliver_preserves`).
4. **Queued observe sources** (row 189, `E4-TYPED-CE-035`): `QueueOk.observer` bounds sources below `nextId`,
   closing an antitone $\Gamma$-read loophole where naming future unallocated fibers bypassed typing checks.

Saved-stack judgments are unified through `Contracts.FramePath Edge` (row 48), a Prop-valued typed-path
relation over frame lists, interpreting composition through existential middle types. It provides generic
identity, append, splitting and transport along edge implications. `HostStack` and `PositionStack` instantiate
it; the unchanged `StackAccepts` is connected by the two conversion theorems.

**Current Milestone Progress** (measured at HEAD, 2026-10-03: `make status` reports 0 open ledger
goals, and the proved ledger is retired, `0821bb2d`):
- **M5 (Denotation & Load Typing)**: **Closed** (0 open of 5). Both `denoteR_typed` and `typedState_load`
  hold unconditionally; the layer family arm (`provideLayerArm`) is proved across all sources.
- **M3bAdequacy (Store Rows)**: **Closed** (31 of 31 store rows, including memo table operations under row 187 (c)).
- **M6Edits (Lift Edits)**: **Closed** (0 open of 13).
- **M6Ledger (Command Preservation)**: **Closed** (20 of 20). The last proved are
  `loop_preserves` and `deliver_preserves` (over the waiter column, `E4-TYPED-CE-025`),
  `decision_preserves` and `typedState_reachable`
  (`src/Effect4/Laws/Program/Typed/Commands/Clauses/All.lean`), and `launch_preserves`
  (`src/Effect4/Laws/Program/Typed/Commands/Launch.lean`).
- **M7 (Capstone on its fragment)**: **Proved** (`m7_proved`, decisions row 138): on the
  empty host table, a checked closed source and answer-free tapes, the frame machine's observation
  is typed and its run never halts. The frame machine only: not the OCaml engine, not a TypeScript run.
- **Open claims** (`generated/semantics.md`): `scheduler-progress`, `fair-scheduling`, `store-safety`
  and `record-codec-layout` are absent; `host-progress` is assumed; `bind-closed` is refuted.
The unchanged registration-completion obligation is proved across all three branches (`registrationDone_preserves`,
`Test/Program/RegistrationColumn.lean`, CE-028 controls). The general wake proof is verified in
`Test/Program/WaiterColumn.lean` (CE-026 controls). Full details in `docs/research/2026-10-02-claude-lead/receipt.md`.


**Earlier M5 closure, 2026-10-02 (pre-integration snapshot).** The layer family's arm is proved at every source (`provideLayerArm`,
`src/Effect4/Laws/Program/Typed/LayerArm.lean`), so M5's two goals hold with no fragment premise:
`denotesTyped` (`M3bAssembly.denoteR_typed`) and `loadsTyped` (`typedState_load`); `M3bAssembly` reads
0 open of 5, `M6Ledger` 7 open of 20, `M7` 4 open. The repairs it needed are decisions rows 176 (b),
185, 186 and 187 (`E4-TYPED-CE-023` and `-031` repaired). Also on the branch: Codex's park handshake
and proof-feature graph, the `check-ty-rule` repair, the generator's nested extras, and the data
wave's rulings (decisions rows 8, 121, 125, 157–161, 166, 167, 169, 180 (a)). Built:
`lake build Effect4 Effect4.Laws` (565 jobs), the touched batteries, the lcnf faces regenerated with
`dune build` and `dune test`. Since then, on the same branch: Codex's proof-infrastructure branch
(the semantics cache's freshness; `--extras` reusing a generated structure map; the full `derived`
group regenerated on this head, every output byte-identical); five round lemmas as `List.foldl_hom`;
slice C of row 182 (`Ty`'s generic fold families generated into the core; the classifier and face
tables as values of the generated `TyTable`, the Schema column Schema IR templates filled by a fold
over the Schema AST, its agreement with `Bridge.schema` proved; `handleFree` on the table's column);
row 8 (C) (the emitter writes each reference key once and refuses a conflicting repeat; the three
fixtures byte-identical). Deferred to the next pause: `make check-gen`, `git:0821bb2d:scripts/test-generators.py` (since retired),
the semantics report and the architecture page. Next: M6 (row 187's memo-table store clause, which
makes `memoGet_implements` and `memoComplete_implements` provable; row 180 (a); the open commands),
then M7; row 182's C.3 and C.4 (the key and TypeScript faces; `Bridge.schema` onto the fold) and the
optics row 182 records, each with its caller.

**Integration, late 2026-10-01 (the base to build on; read first).** Merged into
`refactor/phase1-phase3`: seat D4's merge completed (Bookkeeping's scope clauses, `04956067`);
Codex's metaprogramming branch (the audit's cleanups and the semantics report's first slice); seat
W2 (the generator for variable arity, the conservativity and `Ty`-rule checkers on demand); seat D2,
reconciled by hand with D4 (rows 170 and 175 landed; M5's arm groups 1–3 and every guard shape's
compatibility lemma). The sweep passes: `lake build` 758 jobs, the trust gate 536 modules and 75 032
declarations, `make check-gen` (W2's interaction check: every Lean-only generated file is what its
generator emits), after decisions row 184 (the gate admits the `semantics` attribute's
initializer-set handle by exact name; owner-ratified, row 184). The language's judgments are described by
concept in `docs/core/semantics.md` (promoted from Gemini's draft, every locator checked), and their
status is measured in `generated/semantics.md` over the ten concepts: 57 claims, 43 proved, 7
wanted, 5 absent, 1 refuted, 1 assumed (`make gen-semantics`; `python3 scripts/check-semantics.py`
passes). Next, in this order (Gemini, `docs/research/2026-10-01-semantics/brief-gemini-proofs.md`):
M5's `evalTerm_fits`, group 4 and the assembly for layer-free programs (receipt D2); then M6 as seat
D5's brief has it (row 134 (a)–(e), row 181, the eight goals, M6b, M6c, row 180); then M7. The two
owner decisions then in the way are settled: row 176 (b) landed on 2026-10-02, and row 184 (a) is ratified. The review
record of the pass: `docs/research/2026-10-01-semantics/review-codex-gemini-2026-10-01-late.md`.

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
(the source-file writer is retired, and so is its focused check).
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
  notes that matter force-added; the agents folder and the coordination file are gone.
