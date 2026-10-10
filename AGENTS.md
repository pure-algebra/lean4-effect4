# Effect4 — agent operating rules

This file is the router that every session loads. Read it in full, then open only the authority
documents that the current task names.

## Authority map

| Path | Owns |
| --- | --- |
| `README.md` | what the product is, the application face, how to build |
| `docs/STATE.md` | the entry point: true at HEAD, the documents, what is next, what the owner must decide |
| `docs/core/` | the current authorities: `system-map.md` (the goal, what a full program is, the layers and their owners, the sorts and arrow kinds, the requirements R1–R14 and their status: the frame), `controlled-english.md` (the writing rules for every Markdown artifact; the dictionary, one meaning per word with its tree anchor, its literature term and the words not to use; the seven judgments and the boundary behaviours; the artifact skeletons; checked by `make check-language`), `semantics.md` (the language's judgments by concept: what the literature defines, our adaptation and cuts, the definitions in the tree, the required properties; statuses are generated, `generated/semantics.md`), `host-boundary.md` (the external-reply lane: host answers, handle declarations, the session lifecycle and its contracts), `traversal-census.md`, `decisions.md` (every open decision, one list), `api-surface.md` (the live surface and its open decisions), `lcnf-route.md`, `machine-state.md` (what state the machine holds, its logs, transactions, and how the rest of Effect's stateful modules land) |
| `docs/ARCHITECTURE.md` | the source tree, module boundaries, dependency direction, the API seam |
| `docs/GENERATED.md` | the generated groups: producers (`make gen-<group>`), inputs, consumers and checks |
| `docs/DESIGN-BASIS.md` | the representation decisions (DB-01 … DB-17): decision, rationale, witnesses, refusals, sources and literature marks; status only by link to the system map's §8 |
| `docs/DESIGN-ISSUES.md` | the open design questions (DI-nn): status, what each would force to be redone, the milestone to decide by; a ruling is made only when written into a tracked file |
| `docs/research/history/` | superseded authorities kept for citation (force-added): the five-layer design map, the language cut, the coherence principle, the post-Phase C synthesis, the 2026-09-17 API assessment; history, never authority |
| `docs/RUNTIME-COVERAGE.md` | the rc.112 runtime mechanism census, its rows, and the one coverage report format |
| `Test/contracts/` | frozen contract packets and their executable falsifiers |
| `Test/Counterexamples/REGISTER.md` | stable IDs of every declaration-changing counterexample |
| `Test/fixtures/baseline/<commit>/` | retained pre-change baselines of the descriptions and alphabets, the independent authority a compatibility gate compares against (DI-47). No generator writes here; it changes only by a named promotion command, and a diff in it is a review event, not drift; the mirror census reads it, and no comparator runs against it |
| `src/Effect4/` | API and functional utilities through `Effect4`; the proof graph through `Effect4.Laws`, with declaration namespaces unchanged |
| `Test/` | batteries, counterexamples and proof receipts; `Test/Audit/AxiomGate.lean` holds the gates: the axiom gate, the module-closure gate and the library-root gate |
| `generated/` | deterministic projections only; never hand-edited |
| `docs/research/` (gitignored; the notes that matter are force-added) | working notes, scout briefs and notes, receipts, evidence trees; history, not authority |

If two files appear to own the same fact, stop and repair the ownership map.

## What the tree is

The product is Effect codegen (`README.md`). `Eff` is the one program IR, and `Effect4.Api` is the
program interface that an application imports. The Machine module is the semantics under it, and
Schema is the data plane beside it.

The Flow route of earlier work is at `606918e` in main's history and on branch
`archive/flow-route`. Do not re-import it, and do not write a second program representation.

The OCaml estate is `ocaml/`, one dune workspace, with its Lean half `src/OCaml5` (lake library
`OCaml5`). `ocaml/README.md` is its map, and `ocaml/STANDARDS.md` holds it to four rules:

- libraries with thin drivers;
- a property list at the head of every component;
- generated files marked and regenerable;
- every number in a report behind a command.

## Representation rules

- Canonical program content is first-order data. Lean functions, `Expr`, host closures, promises
  and runtime objects are not stored program syntax.
- Every Effect behaviour that a declaration models names the line it transcribes, in the pin
  (`vendor/effect-4.0.0-rc.112/src/…`) or in latest (Effect 4.0.1) under
  `vendor/effect-4.0.1/src/…` (row 331).
- A theorem that witnesses a census row names the row id in its docstring, and
  `Test/Audit/RuntimeCoverage.lean` joins it. The theorem alone moves no number.
- Fuel exhaustion and unanswered choices are live frontiers, never typed errors, causes or
  refusals.
- Full meaning is relational over explicit decisions. Determinism is claimed only after fixing a
  compatible decision tape that answers every decision, or after proving that a fragment contains
  no decision source.
- State produced before failure remains available to finalization.
- Effect TypeScript is one target profile, not the identity or semantic owner.
- Names are data: an alphabet instantiated at a function type fails the separation gates at the
  foot of the machine modules.

## Writing rules

Every Markdown artifact follows `docs/core/controlled-english.md`. Its §2 owns the rules, and
`make check-language` checks that file and this one. The summary:

- Write one idea per sentence. A description has at most 25 words, an instruction at most 20.
- Use the active voice, the present tense for facts and the imperative for procedures.
- Use each dictionary word in its one meaning. Never use a synonym, and define a new word first.
- Keep the evidence when you shorten. Keep every hypothesis, the observation, the fragment and
  the evidence kind.
- Cite a declaration by its name and its path, never by a line number.
- Take counts, statuses and dates of a run from the tool that measures them.
- Draw an order, a state machine, a pipeline or a concept map as a Mermaid diagram.
- Keep proof role, evidence status and scope as separate labels.

`python3 scripts/check-language.py` reports the findings of every other document.

## Vocabulary

Each line below points to its entry in the dictionary, `docs/core/controlled-english.md` §3. A new
representation enters the tree only by naming its sort's syntax signature and the kind of each of
its arrows. Anything else is a leak.

- **Free object**: the one representation of a sort, an inductive family whose signature is
  data. The free objects are `Eff` (with `binders.json` and `LayerView`), `Ty`, `Term`,
  `Store.Val`, `Representation` and `List Command`, one per sort (§3.5).
- **Algebra** and **fold**: an algebra is a carrier with one field per constructor (`EffAlgebra`,
  `TyAlgebra`, …; generated). Its fold is the unique map out of the free object (`cataFam`,
  `cata_eff`, `cata_ty`, …; §3.5).
- **Traversal**: every traversal is a fold or is generated from the signature. A hand `match` is
  an exemption that the census (`#traversal_census`, `docs/core/traversal-census.md`) lists by
  name.
- **Agreement of folds**: two folds agree when their algebras do (`hom_eq_cata_eff`). Write no
  pairwise agreement proof.
- **Exact embedding**: a write/read pair `write : A → F`, `read : F → Option A` with three laws:
  total on its domain; retraction `read (write a) = some a`; exactness
  `read v = some a → v ≡ write a` modulo a named normaliser (§3.5).
- **Widening**: a read without exactness is a widening, not an embedding. Same endpoint types do
  not make a pair exact, and a decoder with an encoder is not by itself a lawful optic.
- **Simulation**: two behaviours related on one observation over a named fragment (§3.2). Its
  statement is an equal-observation theorem, proved through a simulation relation (the book's
  `ReplayRel` and `BMeans`).
- **Equal-observation theorems**: `run_eq_meaning` on `Straight`, `loopAgreement` on `Looped`, and
  `run_eq_ref` at the empty row table. The Conform rungs and the truth lane are finite checks of
  one.
- **Equivalent**: never write it without its observation. A simulation is the only statement
  about two behaviours.
- **Located refusal**: a total-by-refusal map `Src → Except Refusal F` whose refusal names a path
  and a reason. It is complete against the judgment: `explain = none ↔ wellTyped` (§3.2).
- **Monoid action**: the journal `List Command` acting on the run (`replay_unique`,
  `journal_replays`). A run is data because its journal is (§3.5).
- **Schema and program**: Schema is a data language. Every effectful slot in it is filled by an
  `Eff` program with a typing certificate. `Ty` and the schema carriers never mention `Eff`.
- **Foreign transformation**: a name with a type signature. Any operation that needs its meaning
  refuses it.
- **The seven judgments**: formation, canonical form, membership, inhabitance, profile support,
  codec admission and reply admission. Keep them distinct, and use only the implications that a
  definition or a named theorem establishes (§4).

## Trust

- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.
- No `sorry`, except as the body of a planned goal (`proof_goal`, decisions row 203):
  - the command adds the theorem with a `sorry` body and tags it; the token stays out of source;
  - a goal lives in `Effect4.Laws` or a `Test` fixture, never in a module the `Effect4` root reaches;
  - a goal in `Effect4.Laws` carries its placement:
    `@[semantics "concept" (requirement := R4)] proof_goal G : P` (decisions row 207);
  - proving it changes `proof_goal` to `theorem`, and the placement stays;
  - the axiom gate admits `sorryAx` only as a goal's own body and counts what rests on goals;
  - a claim or a requirement's top node is proved only when it rests on no goal.
- The axiom gate audits every declaration of every `Effect4.*` and `Test.*` module at
  `[propext, Quot.sound]`.
- So a battery holds no `#print axioms` line, and it pins no status of a proved statement.
  Each line of a battery is one of three things (decisions row 301):
  - a reader: a law applied at a real carrier, or at a real rule of the checker;
  - a control: a red case that shows why a premise stands, or where a law stops;
  - a finite evaluation that no theorem covers.
- A battery restates no theorem. A frozen contract may pin a statement that no registry claim
  holds.
- A rendering declaration that must traverse a `String` is exempted by its exact name in
  `AxiomGate.lean`, never by module.
- A battery `def` over rendered text reaches `Classical.choice`: keep rendered bytes inside
  `#guard`s.
- A new core module outside `Laws` whose packages are at most `hash` opens with `module`,
  `public import` and `@[expose] public section` (decisions row 200). The seven specialization
  sites of decisions row 202 and their importers stay non-module.
- Every library source must be reachable from `Effect4` or `Effect4.Laws`, and `Effect4` must never
  import the Laws graph. The library-root gate checks both roots.
- Every battery file under `Test/` must be reachable from `Test/All.lean`, or the module-closure
  gate refuses the build.
- The slow lane is the one exception: the files `slowLane` lists in `Test/Audit/AxiomGate.lean`,
  reached from `Test/Slow.lean` and built at a sweep (`make check-slow`).
- Name the exact judgment, observation, theorem or gate before you say "sound", "equivalent",
  "preserves", "fully reified" or "complete". Name its assumptions and the remaining host
  boundary too.
- Report a compiling finite probe as a finite probe.
- Audit a landing's modules with `#axiom_audit M …` (`tools/ProofGraph/AxiomAudit.lean`), never with
  `#print axioms`: Lean's collector misses axioms behind a cycle.
- **Every proof obligation is placed in the theory before it is worked** (owner, 2026-10-02: no
  proofs to nowhere). Before a theorem is stated, proved, repaired or put in a brief, write down
  five things:
  1. its concept, the one of the ten in `docs/core/semantics.md`, and the required property there
     that it is or serves;
  2. its question: a registry claim with its role (`tools/ProofGraph/Registry.lean`,
     `generated/semantics.md`), whose pointer is the theorem that states it. While the claim is
     open, the pointer is a planned goal: `proof_goal G : P`, a theorem whose body is `sorry`.
     Downstream proofs use `G` as a theorem. Its proof replaces the `proof_goal` in place, with no
     second statement. A helper names the claim it is a step of, and the consumer that uses it.
     A decomposition is an ordinary theorem whose proof uses goals: it is proved modulo them.
     The plan (`tools/ProofGraph/Plan.lean`) derives each node's status from its proof: goal,
     modulo or proved. `proof_sketch` turns a proof sketch's open goals into goals.
     `#plan_status` shows a node's status and the goals it rests on. A requirement row lists the
     parts that no goal states yet as its open parts;
  3. its reach: the exact judgment, observation, fragment and hypotheses, with the decisions rows
     and register lines that bound it;
  4. what it does not establish:
     - a conditional theorem leaves its premises open;
     - an invariant is not progress;
     - safety is not liveness;
     - an equal-observation theorem holds only on its fragment;
     - the host boundary stays where `docs/core/host-boundary.md` puts it;
  5. what it unlocks on the M5 → M6 → M7 spine, or which requirement it serves (R1–R14,
     `docs/core/system-map.md`).

  Do not start a lemma that has no consumer on a path to a planned goal or a registry claim. If the
  theory lacks a property, add it to `semantics.md` and the semantics registry, or propose it in
  the receipt. Do it in the slice that proves the property. A receipt gives each landed theorem's
  placement, and a brief gives each assigned obligation's. No open planned goal does not mean the
  semantics is finished.
- Coverage of the Effect runtime is stated only in the block that
  `scripts/report-effect-runtime-coverage.sh` writes, after `scripts/check-effect-runtime-census.sh`
  passes.

## Working

- Design first, then land in slices. A change to the machine or the program syntax starts as a plan
  or a research note in `docs/research/`.
- The change lands as commits by explicit paths, each after a narrow build of the modules it
  touches. A narrow build is `lake build <Module>` and its direct dependents, or
  `lake env lean <file>` for a test.
- A landing owes two things (owner, 2026-10-10):
  - the proofs: the narrow build, then `#axiom_audit` over the landing's modules;
  - the behaviour gates the change reaches: the runs that compare with an outside implementation.
- The behaviour gates are the targets of `make check-full` (`make check` is the build alone):
  - the codec against rc.112: `check-schema-codec`, `check-schema-ts`;
  - the machine and the OCaml route: `check-compiler`, `check-native`, `check-ocaml`;
  - the meaning against the Effect runtime: `check-truth`, `check-host-protocol`;
  - the printed TypeScript under tsgo: `check-target`, `check-ts-reader`, `check-corpus`, `check-tsdiag`.
- No other run is owed. The batteries (`lake build Test`) and the whole-tree axiom gate run when
  the owner asks. So do the ratchets, the policies, the drift and the document checks.
- A gate depends on its sources and builds exactly what its tool imports (`build_imports` in the
  `Makefile`).
- A docstring or comment edit needs no build of a dependent module.
- An agent commits the same way, on its own branch in its own worktree. It starts from the base the
  coordinator names and edits the files its brief names.
- `git add` names files. Never run `git add -A` without reading `git status`. The owner's untracked
  `docs/*.md` and `README.md` stay as they are.
- The root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) and
  `Test/Audit/AxiomGate.lean` are edited at the anchor the brief names, so parallel branches merge
  clean.
- `lakefile.toml` and `docs/core/decisions.md` are the coordinator's. An agent proposes a decisions
  row in its receipt (`docs/research/<date>-seat-<X>-receipt.md`) and never edits the register.
- A worktree never copies `docs/research` (2 GB).
- A new worktree clones the dependency packages copy-on-write
  (`cp -c -R .lake/packages <worktree>/.lake/packages`) and then runs `lake build`. Lake's artifact
  cache (`lakefile.toml`) restores each output that some worktree has already built, in seconds.
  `lake cache clean` prunes the cache and rebuilds nothing.
- `make status` gives what is true at HEAD, measured:
  - the build and check markers against their inputs;
  - the size of Lake's artifact cache, and the part of it that no worktree uses;
  - the claims by status and the open planned goals;
  - the registers;
  - the documents' stale references.
- `make check-docs` refuses a path, link, `git:<rev>:<path>` citation or make
  target that an authority document names and that does not resolve. A cited research note must be
  tracked (force-added).
- History (`docs/research/`, the archives, `ATTACKS.md`) is not checked. What these tools measure
  is not written by hand anywhere else.
- One `lake` at a time in a working tree, run as `LEAN_NUM_THREADS=3 lake build <Module>` or through
  a `make` target, which exports the same bound. A bare `lake build` starts one compilation per
  core, and the machine swaps (measured 2026-10-03).
- In `src/Effect4/Laws/**` proof search is `aesop`
  (`https://github.com/leanprover-community/aesop`), a dependency of the law graph only. The core
  root never imports it.
  - Register a lemma in the named bank that fits (`src/Effect4/Laws/Auto/RuleSets.lean`).
  - For a definition, use `@[aesop norm simp (rule_sets := [X])]`. For a fact, use `safe` or
    `unsafe` with the builder that fits it.
  - The builder is `constructors` or `cases` for an inductive predicate, and `forward` or
    `destruct` for an implication.
  - Introduce induction hypotheses by hand and hand them to the call
    (`aesop (add safe forward [ih1, ih2])`).
  - Keep a rule that creates metavariables (a transitivity) in the call that needs it, never in a
    bank.
  - A bank lands with a theorem that closes only with `(rule_sets := [X])`. It lands with a `Test`
    fixture too, which omits the clause under `#guard_msgs (error)` (decisions row 65).
  - `#auto_census Some.Module using aesop` (`src/Effect4/Laws/Auto/Census.lean`) reports which
    theorems of a module the search already closes from their statements. Run it before you
    rewrite proofs against a bank.
  - Prefer a short searched proof to a long unpacked one. Take a proof's case list from the
    definition it is about (`fun_induction`, `fun_cases`), not from `cases a <;> cases b`.
  - The axiom gate holds a searched proof to `[propext, Quot.sound]` like any other. `simp` at
    `(x == x) = true` for `String` or `Nat`, and aesop on a catch-all's negative hypotheses, both
    reach `Classical.choice`.
  - Not written by hand in a new or touched proof, anywhere under `src/`: `simp_all`, `first | …`
    and `try`. A fallback that fails silently into an unsolved goal hides a missing lemma. The
    proof-style ratchet (`Test/Audit/ProofStyle.lean`) refuses a new use, and a `simp` without
    `only`, against the recorded uses in `Test/fixtures/proof-style/baseline.tsv`.
  - Every warning is an error (`-DwarningAsError=true` in the lakefile, 2026-09-19). An unused
    `simp` argument, a dead tactic or a `sorry` in an `example` fails the build where it is
    written.
  - A hand-written `simp` names its lemmas as `simp only [...]`.
- Pass a table as data. Never bind one with `let` before a closure that a definition returns.
  Lean compiles the closure's argument as one more parameter, so the table is built at every
  call. `Test/Audit/ClosureAudit.lean` refuses the shape (`#closure_audit`).
- Regenerate what a change reaches, so the behaviour gates run the current code:
  - `python3 scripts/generate.py --only <family>` after a generator or its input;
  - `dune build`, only through `opam exec --switch=effect4`, after the OCaml estate.
- On Windows the shell is PowerShell, and the bash gate scripts run through WSL.
- TypeScript is checked by one compiler, tsgo 7 (owner, 2026-09-18, restated 2026-10-01):
  - the pinned `@typescript/native-preview` 7.0.0-dev.20260629.1 in `ts/eff` and `harness/truth`;
  - `typescript@7.0.2`, patched by `effect-tsgo`, in `harness/schema-host`.
- tsgo 7 is the oracle of `check-target`, `check-truth` and the corpus lane. `tsc` and
  `typescript@5.x` are never run, in a gate, a probe or a review.
- A TypeScript result names its compiler and version. `scripts/check-host-protocol.py` runs tsgo
  (seat J, 2026-10-01).
- The ingest parses with `oxc-parser` (one entry, `ts/eff/ingest/oxc.ts`). `check-styles.ts` asks
  tsgo's own API (`unstable/sync`, under node) for the oracle's grammar (decisions row 168, seat J2).
- No `typescript` below 7 is installed under `ts/`, `harness/` or `tools/`. `make check-tsgo`
  refuses one.
- A proof graph is mandatory only for these kinds of work:
  - an admission or a refusal of any input (a program, a table, a reply, a codec value, …);
  - judgments or denotations;
  - interpreters or handlers;
  - reification or generated-code relations;
  - nontrivial composition or recursive invariants;
  - an equal-observation claim against an outside implementation.

  A passive finite alphabet closes with its local receipts.
- Build in parallel, slot in, and delete at a good place. A new representation is a second file
  beside the old one, with its connector (the agreement theorem). The callers move, then the old
  one goes.
- Never edit in place in a way that throws away work to be repeated.
- A handoff or receipt records, first, the one thing the coordinator must know before merging. Then
  it records:
  - the base and head commits;
  - the changed files;
  - the exact commands and their results;
  - the axiom output;
  - the open obligations;
  - whether any evidence is bounded or host-only.

## Registers

Open decisions: `docs/core/decisions.md` (one list) and `docs/DESIGN-ISSUES.md` (the DI register:
a ruling is made only when written there). Settled representation decisions:
`docs/DESIGN-BASIS.md`. Contracts and counterexamples: `Test/contracts/`,
`Test/Counterexamples/REGISTER.md`. No external tracker, no ADR directory.
