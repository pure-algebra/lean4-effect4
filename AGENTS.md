# Effect4 — agent operating rules

This file is the always-loaded router for work in this repository. Read it in
full, then open only the authority documents named for the current task.

## Authority map

| Path | Owns |
| --- | --- |
| `README.md` | what the product is, the application face, how to build |
| `docs/STATE.md` | the entry point: true at HEAD, the documents, what is next, what the owner must decide |
| `docs/core/` | the current authorities: `ontology.md` (the frame and the vocabulary's definitions), `coherence-principle.md`, `traversal-census.md`, `decisions.md` (every open decision, one list), `api-surface.md`, `lcnf-route.md`, `machine-state.md` (what state the machine holds, its logs, transactions, and how the rest of Effect's stateful modules land) |
| `docs/ARCHITECTURE.md` | the source tree, module boundaries, dependency direction, the API seam |
| `docs/GENERATED.md` | the generated groups: producers (`make gen-<group>`), inputs, consumers and checks |
| `docs/DESIGN-BASIS.md` | the representation decisions (DB-01 … DB-15), their status and sources |
| `docs/DESIGN-ISSUES.md` | the open design questions (DI-nn): status, what each would force to be redone, the milestone to decide by; a ruling is made only when written into a tracked file |
| `docs/DESIGN-MAP.md` | the earlier five-layer map, cited by section from code; superseded in substance by `docs/core/ontology.md` §5 |
| `docs/RUNTIME-COVERAGE.md` | the rc.112 runtime mechanism census, its rows, and the one coverage report format |
| `Test/contracts/` | frozen contract packets and their executable falsifiers |
| `Test/Counterexamples/REGISTER.md` | stable IDs of every declaration-changing counterexample |
| `Test/fixtures/baseline/<commit>/` | retained pre-change baselines of the descriptions and alphabets, the independent authority a compatibility gate compares against (DI-47). No generator writes here; it changes only by a named promotion command, and a diff in it is a review event, not drift |
| `src/Effect4/` | API and functional utilities through `Effect4`; the proof graph through `Effect4.Laws`, with declaration namespaces unchanged |
| `Test/` | batteries, attacks and proof receipts; `Audit/AxiomGate.lean` is the gate |
| `generated/` | deterministic projections only; never hand-edited |
| `docs/research/` (gitignored; the notes that matter are force-added) | working notes, scout briefs and notes, receipts, evidence trees; history, not authority |

If two files appear to own the same fact, stop and repair the ownership map.

## What the tree is

The product is Effect codegen (`README.md`): `Eff` is the one program IR,
`Effect4.Api` the program interface an application imports, the Machine module the
semantics under it, Schema the data plane beside it. The Flow route of
earlier work is at `606918e` in main's history, also on branch `archive/flow-route`; do not re-import it, and
do not write a second program representation. The OCaml estate (`ocaml/`, one
dune workspace, and its Lean half `src/OCaml5`, lake library `OCaml5`) is
held to `ocaml/STANDARDS.md`: libraries with thin drivers, a property list at
the head of every component, generated files marked and regenerable, every
number in a report behind a command; `ocaml/README.md` is its map.

## Representation rules

- Canonical program content is first-order data. Lean functions, `Expr`, host
  closures, promises, and runtime objects are not stored program syntax.
- Every rc.112 behaviour a declaration models names the line it transcribes
  (`vendor/effect-4.0.0-rc.112/src/…`); a theorem that witnesses a census row
  names the row id in its docstring and is joined in
  `Test/Audit/RuntimeCoverage.lean`. The theorem alone moves no number.
- Fuel exhaustion and unanswered choices are live frontiers, never typed
  errors, causes, or refusals.
- Full meaning is relational over explicit decisions. Determinism is claimed
  only after fixing a complete compatible decision tape or proving a fragment
  contains no decision source.
- State produced before failure remains available to finalization.
- Effect TypeScript is one target profile, not the identity or semantic owner.
- Names are data: an alphabet instantiated at a function type fails the
  separation gates at the foot of the machine modules.

## Vocabulary

The words below have one meaning each (`docs/core/ontology.md` §5 defines them against the
tree). A new representation is admitted by naming its sort's signature and the kind of each of
its arrows; anything else is a leak.

- **Free object**: the one representation of a sort, an inductive family with its signature as
  data (`Eff` with `binders.json`/`LayerView`; `Ty`; `Term`; `Store.Val`; `Representation`;
  `List Command`). One per sort.
- **Algebra** and **fold**: a carrier with one field per constructor (`EffAlgebra`,
  `TyAlgebra`, …, generated) and the unique map out of the free object (`cataFam`, `cata_eff`,
  `cata_ty`, …). Every traversal is a fold or generated from the signature; a hand `match` is an
  exemption the census (`#traversal_census`, `docs/core/traversal-census.md`) lists by name.
  Two folds agree when their algebras do (`hom_eq_cata_eff`); no pairwise agreement proof.
- **Exact embedding**: a write/read pair `write : A → F`, `read : F → Option A` with three
  laws — total on its domain, retraction `read (write a) = some a`, exactness
  `read v = some a → v ≡ write a` modulo a named normaliser (`Canonical`; `print`/`read`;
  `Ty.schema`/`ofSchema`; the JSON codec). A read without exactness is a widening, not an
  embedding.
- **Simulation**: two behaviours related on one observation over a named fragment
  (`run_eq_meaning` on `Straight`, `loopAgreement` on `Looped`, the Conform rungs, the truth
  lane). The only statement about two behaviours; never "equivalent" without the observation.
- **Located refusal**: a total-by-refusal map `Src → Except Refusal F` whose refusal names a
  path and a reason, complete against the judgment (`explain = none ↔ wellTyped`).
- **Monoid action**: the journal `List Command` acting on the run (`replay_unique`,
  `journal_replays`); a run is data because its journal is.
- **Schema and program**: Schema is a data language; every effectful slot in it is a hole
  filled by an `Eff` program with a typing certificate; `Ty` and the schema carriers never
  mention `Eff`; a foreign transformation is a name with a typed signature that any
  meaning-needing operation refuses.

## Trust

- No `sorry`, `partial`, `unsafe`, `native_decide`, `axiom`, `extern`,
  `implemented_by`. The gate audits every `Effect4.*` and `Test.*`
  declaration at `[propext, Quot.sound]`; a rendering declaration that must
  traverse a `String` is admitted by exact name in `AxiomGate.lean`, never by
  module. A battery `def` over rendered text reaches `Classical.choice`: keep
  rendered bytes inside `#guard`s.
- Every library source must be reachable from `Effect4` or `Effect4.Laws`; `Effect4`
  must never import the Laws graph. The module-closure gate checks both roots.
- Every battery file under `Test/` must be reachable from
  `Test/All.lean`, or the module-closure gate refuses the build.
- Do not say "sound", "equivalent", "preserves", "fully reified", or
  "complete" without naming the exact judgment, observation, theorem or gate,
  assumptions, and remaining host boundary. A compiling finite probe is
  reported as a finite probe.
- Coverage of the Effect runtime is stated only in the block printed by
  `scripts/report-effect-runtime-coverage.sh`, after
  `scripts/check-effect-runtime-census.sh` passes.

## Working

- Design first, land in slices: a change to the machine or the syntax starts as a plan or a
  research note in `docs/research/`, then lands as commits by explicit paths, each after a
  narrow build of the modules it touches (`lake build <Module>` and its direct dependents;
  `lake env lean <file>` for a test). No closure or battery run is owed for an integration; the
  whole battery (`lake build Test`, the trust gate) and `make check`/`make check-host` run when
  the owner asks for a sweep. A docstring or comment edit needs no build of a dependent module.
- An agent commits the same way, on its own branch in its own worktree, from the base the
  coordinator names, on the files its brief names. `git add` names files (never `git add -A`
  without reading `git status`); the owner's untracked `docs/*.md` and `README.md` stay as they
  are. The root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) and
  `Test/Audit/AxiomGate.lean` are edited at the anchor the brief names, so parallel branches
  merge clean; `lakefile.toml` and `docs/core/decisions.md` are the coordinator's — an agent
  proposes a decisions row in its receipt (`docs/research/<date>-seat-<X>-receipt.md`), never
  edits the register. A worktree never copies `docs/research` (2 GB).
- One `lake` at a time in a working tree.
- In `src/Effect4/Laws/**` proof search is `aesop`
  (`https://github.com/leanprover-community/aesop`, a dependency of the law graph only; the core
  root never imports it). Register a lemma in the named bank that fits
  (`src/Effect4/Laws/Auto/RuleSets.lean`; `@[aesop norm simp (rule_sets := [X])]` for a
  definition, `safe`/`unsafe` with the builder that fits the fact: `constructors`/`cases` for an
  inductive predicate, `forward`/`destruct` for an implication), introduce induction hypotheses
  by hand and hand them to the call (`aesop (add safe forward [ih1, ih2])`), and keep a rule that
  creates metavariables (a transitivity) in the call that needs it, never in a bank. A bank lands
  with a theorem that closes only with `(rule_sets := [X])` and a `Test` fixture with the clause
  omitted under `#guard_msgs (error)` (decisions row 65). `#auto_census Some.Module using aesop`
  (`Laws/Auto/Census.lean`) reports which theorems of a module the search already closes from
  their statements; run it before rewriting proofs against a bank. Prefer a short searched
  proof to a long unpacked one, and take a proof's case list from the definition it is about
  (`fun_induction`/`fun_cases`) rather than from `cases a <;> cases b`. The axiom gate holds a
  searched proof to `[propext, Quot.sound]` like any other; `simp` at `(x == x) = true` for
  `String`/`Nat` and aesop on a catch-all's negative hypotheses both reach `Classical.choice`.
  Not written by hand in a new or touched proof, anywhere under `src/`: `simp_all`, `first | …`
  and `try` (a fallback that fails silently into an unsolved goal hides a missing lemma);
  `generated/proof-shape.tsv` pins their count per module as a ceiling that only falls. A
  hand-written `simp` names its lemmas as `simp only [...]`.
- The gates that run with a commit are the ones the change reaches: `make check-cases` after a
  new match on a policy family, `python3 scripts/generate.py --only <family>` after a generator
  or its input (the output must be byte-identical or committed), `dune build` (only via
  `opam exec --switch=effect4`) after the OCaml estate.
- On Windows the shell is PowerShell; the bash gate scripts run through WSL.
- A proof graph is mandatory only for admission or refusal, judgments or
  denotations, interpreters or handlers, reification or generated-code
  relations, nontrivial composition or recursive invariants, and external
  semantic equivalence; a passive finite alphabet closes with its local
  receipts.
- Build in parallel, slot in, delete at a good place: a new representation is a second file
  beside the old one with its connector (the agreement theorem), the callers move, then the old
  one goes. Never an edit in place that throws away work to be repeated.
- A handoff or receipt records base and head commits, changed files, exact commands and
  results, axiom output, open obligations, and whether any evidence is bounded
  or host-only — and, first, the one thing the coordinator must know before merging.

## Registers

Open decisions: `docs/core/decisions.md` (one list) and `docs/DESIGN-ISSUES.md` (the DI
register; a ruling is made only when written there). Settled representation decisions:
`docs/DESIGN-BASIS.md`. Contracts and counterexamples: `Test/contracts/`,
`Test/Counterexamples/REGISTER.md`. No external tracker, no `docs/adr/`.
