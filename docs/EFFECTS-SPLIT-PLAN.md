# Plan: `Effects`, a standalone effect algebra, and `Effect4` as its Effect TypeScript reification

Status: **EXECUTED THROUGH S4, 2026-09-02.** S5 (streams acceptance probe) and S6 (composition extensions) remain open by design. This is the living
Effect4-side plan for RS-D1. It supersedes the Effect4 copy of
[ALGEBRA-PACKAGE-PLAN](ALGEBRA-PACKAGE-PLAN.md) and applies the repairs in the
[2026-09-02 review](research/2026-09-02-algebra-package-review.md) (R1–R7).
Every `EP-*` ruling below was put to the operator on 2026-09-02 and is
recorded as ruled: EP-9 by explicit choice (reading 1), EP-2 by explicit
choice (option 1), and the rest by the operator adopting the recommended
default. The hold on extraction is lifted for S1 by that confirmation; S4
still waits on its own coordination claim.

Facts below were read at Effect4 commit `217d3e4` with an uncommitted working
tree (`COORDINATION.md`, `README.md`, `docs/research/` untracked). Re-read
them at slice S0 before any step runs.

## 1. Naming and the shape of the split

| Object | Name | Rationale |
| --- | --- | --- |
| New repository | `mepuka/lean4-effects` | sibling of `lean4-effect4`; ruling EP-1 |
| Lake package | `effects` | lower-case package id, matching `effect4` |
| Production library and declaration namespace | `Effects` | the generic algebra; not wedded to Effect TypeScript |
| Test library | `EffectsTest` | mirrors `Effect4Test` |
| This repository | unchanged: `effect4`, `Effect4`, `Effect4Test` | the Effect TypeScript reification: Flow, Semantics, Schema, Runtime, Concurrency, Target, host harness |

`Effects` owns exactly what the review calls the "standalone algebra" layer:
signatures, well-founded programs, handlers, sums, the morphism wrapper,
interpretation and the universal laws, with meaning unchanged. `Effect4`
depends on `Effects` at an exact commit and never conversely. A WHATWG
standard library depends on `Effects` for its algebra. What else it may
depend on is ruling EP-9, the boundary question, and is deliberately not
settled here.

### 1.1 What moves

The nine modules under `Effect4/Algebra/` (38,459 bytes), read at `217d3e4`,
importing nothing outside the tree:

| Effect4 module | Effects module | Imports |
| --- | --- | --- |
| `Effect4/Algebra/Signature.lean` | `Effects/Algebra/Signature.lean` | none |
| `Effect4/Algebra/MonadLaws.lean` | `Effects/Algebra/MonadLaws.lean` | none |
| `Effect4/Algebra/Program.lean` | `Effects/Algebra/Program.lean` | Signature |
| `Effect4/Algebra/Handler.lean` | `Effects/Algebra/Handler.lean` | Program |
| `Effect4/Algebra/Laws.lean` | `Effects/Algebra/Laws.lean` | Handler, MonadLaws |
| `Effect4/Algebra/Sum.lean` | `Effects/Algebra/Sum.lean` | Laws |
| `Effect4/Algebra/Universal.lean` | `Effects/Algebra/Universal.lean` | Sum |
| `Effect4/Algebra/Handler/Composition.lean` | `Effects/Algebra/Handler/Composition.lean` | Universal |
| `Effect4/Algebra/Handler/Category.lean` | `Effects/Algebra/Handler/Category.lean` | Handler.Composition |

Module paths sit under `Effects/Algebra/` because `Effects` is the umbrella
for general effect implementations (EP-9) and sibling areas will arrive:
S6's transport packets, and any piece a later EP-9 ruling moves in. The
declaration namespace stays `Effects`, so consumers write `Effects.Program`,
not `Effects.Algebra.Program`. This is the module-versus-namespace split
Effect4 already uses.

With them move their evidence: the two batteries and the axiom report under
`Effect4Test/Algebra/` (33,099 bytes), the two contracts
`test/contracts/algebra-extraction.contract.md` and
`algebra-retained-closure.contract.md`, the eight register rows
`E4-ALG-CE-001`..`008`, and `test/counterexamples/algebra/ATTACKS.md`.

### 1.2 The declaration namespace (repair for R5)

The nine modules declare names in namespace **`Effect4`**, not
`Effect4.Algebra`: `Effect4.Signature`, `Effect4.Program`,
`Effect4.Handler`, `Effect4.interpret`, `Effect4.ModelMorphism`, the
notation `⊕ₛ`, the `Monad (Program S)` and `LawfulMonad (Program S)`
instances, and `Effect4.identityHandler`. After the move every one of them is
declared in namespace `Effects`. The only textual edits to the nine modules
are `namespace Effect4` → `namespace Effects`, `end Effect4` →
`end Effects`, and `import Effect4.Algebra.X` → `import Effects.Algebra.X`. No
definition body, theorem statement, binder, universe, or docstring changes.

### 1.3 Consumer inventory in Effect4 (read at `217d3e4`)

| Consumer | How it reaches the algebra | Cutover edit (S4) |
| --- | --- | --- |
| `Effect4/Schema/EffectfulField.lean` | `import Effect4.Algebra.Laws`; inside `namespace Effect4` uses unqualified `Signature`, `Program`, `Handler`, `interpret`, `Program.perform` | `import Effects.Algebra.Laws`; add `open Effects` |
| `Effect4Test/Schema/EffectfulFieldContract.lean`, `Effect4Test/Counterexamples/Schema/EffectfulField.lean` | `open Effect4` only | add `open Effects` |
| `Effect4.lean` root | nine `import Effect4.Algebra.*` lines | delete them; the dependency is reached through `EffectfulField` |
| `Effect4Test.lean` root | three `import Effect4Test.Algebra.*` lines | delete them |
| `Effect4Test/Audit/AxiomGate.lean` | audits by module prefix `Effect4`/`Effect4Test`; walks `Effect4/` and `Effect4Test/` | no edit needed; `Effects` declarations are outside its tree by construction and are gated in their own repository |
| `workshop/EffectfulFieldSemantics.lean`, `workshop/EffectfulFieldWildtype.lean` | import algebra modules directly | scratch; repoint or delete |
| `PORT-MANIFEST.md` rows for the nine Foldlab spans, the two narrow gates, and the algebra axiom report | prose | disposition becomes `moved to Effects@<rev>` |
| `PLAN.md` P3, `docs/ARCHITECTURE.md` "Planned source tree", `docs/DESIGN-BASIS.md` DB-01, `README.md`, `AGENTS.md` "Reuse and compatibility" | prose | see S4 |

`Effect4Test/Counterexamples/Runtime/Frames.lean` mentions `interpret` as a
bound variable, not the algebra; it is not a consumer.

## 2. Rulings owed (the grill list)

All rows were ruled on 2026-09-02. The "ruling" column is what the plan
executes.

| Id | Question | Ruling | Cost of the alternative |
| --- | --- | --- | --- |
| EP-1 | Repository, package, library, namespace | **RULED (default):** `mepuka/lean4-effects`, `effects`, `Effects`, `Effects` | none material; a different repo name only changes the `[[require]]` |
| EP-2 | Module layout | **RULED: option 1.** Module paths under `Effects/Algebra/`; declaration namespace `Effects` | flat paths would have to move once the umbrella gains a sibling area; namespacing declarations under `Effects.Algebra` lengthens every theorem name for nothing |
| EP-3 | Compatibility shim in Effect4 | **RULED (default):** **none**; every consumer is in-tree and is rewritten in the S4 commit | an `export`-based alias shim needs one alias per public declaration (about 80), its own parity test, and a removal release; it buys nothing while Foldlab's P12 adapter is unwritten |
| EP-4 | History | **RULED (default):** `git filter-repo` with `--path-rename`, so `git log --follow` and blame survive | fresh copy with a provenance pin is faster and loses blame; `git-filter-repo` is not installed on this Mac (`brew install git-filter-repo`) |
| EP-5 | Counterexample IDs | **RULED (default):** keep `E4-ALG-CE-001`..`008` verbatim in the Effects register with an `origin` column | renumbering to `EFX-*` adds a mapping table and breaks every existing citation for no gain |
| EP-6 | Foldlab-pinned witnesses (CE-002, 003, 004, 006, 007) | **RULED (default):** re-derive 002/003/004/006 as local executable witnesses in `EffectsTest`; keep the Foldlab pin as provenance; 007 stays a design row | leaving them external means a clean `lean4-effects` checkout cannot review five of eight rows |
| EP-7 | License | **RULED, revised 2026-09-02: MIT**, the Effect TypeScript license, unified across the whole family (`effects`, `effect4`, `whatwg`, `hash`, `nlp`). Apache-2.0 was the first ruling and shipped in `effects` `v0.1.0`; both repositories switched to MIT the same day. Foldlab evidence stays cited under Foldlab's own Apache-2.0 | any OSI license; the choice must precede the first public tag |
| EP-8 | Pin policy | **RULED (default):** Effect4 requires an exact `rev` equal to a tagged commit; bumps are a one-line PR in Effect4 | tracking a branch defeats the assurance chain |
| EP-9 | **Boundary question**: what may a WHATWG standard library depend on besides `Effects`? | **RULED 2026-09-02: reading 1.** A standard library depends on `Effects` only. `Effects` is the umbrella for general effect implementations; WHATWG reification builds against it; Effect4 later imports the WHATWG effectful instances from its Channel/Stream modules. A standard library therefore never imports Effect4. What RS-1, RS-3, and RS-5 borrow from Effect4 (Schema values, checked Flow, TypeScript lowering) is rebuilt in the standard library, moved into `Effects` by its own ruling, or applied on the Effect4 side after the import | pre-moving `Data`, `Flow`, or `Schema` into `Effects` now would move unreviewed surface |
| EP-10 | Gate depth in Effects | **RULED (default):** port the axiom, module-closure, and source-trust gate in full, minus the Target-only exemptions; port the gate self-test | a lighter gate is cheaper per run and is exactly what the coordination log says never caught anything |
| EP-11 | Hosts | **RULED (default):** build on this Mac and ubuntu CI; the Windows clone is optional | the streams plan's "dual-host" step was written for a Windows seat that is not this one |
| EP-12 | Effects working discipline | **RULED (default):** same breaker/builder/reviewer order and routers as Effect4, with two routers (`AGENTS.md`, `EffectsTest/AGENTS.md`) instead of five | five routers for nine modules is ceremony without a distinct owner per boundary |

Dependency direction after EP-9:

```text
Effects  ─►  WHATWG standard libraries (streams first)  ─►  Effect4 (Channel/Stream modules import the WHATWG instances)
Effects  ─►  Effect4 (everything else, from S4 onward)
```

The boundary question mattered most because the reification strategy is
inconsistent on it: RS-D1 says no standard library depends on lean4-effect4,
while RS-1 places Stratum V in "Effect4's Schema layer", RS-3 uses checked
`Flow`, and RS-5 lowers through "Effect4's TypeScript target". This plan
does not resolve that; it moves only what both readings agree on.

## 3. Slices

Each slice is one packet: a fence, an entry condition, the work, an exit gate
with exact commands, and what must not change. S1–S3 touch only the new
repository and can proceed without a coordination claim here. S4 is the one
edit to Effect4 and needs claims on files that are currently claimed by
other lanes in `COORDINATION.md`.

### S0 — Boundary refresh and rulings (Effect4, documents only)

Fence: `docs/EFFECTS-SPLIT-PLAN.md`, one pointer line in
`docs/ALGEBRA-PACKAGE-PLAN.md`, one row in `COORDINATION.md`.

Entry: this document exists. Work: the operator answers EP-1..EP-12; the
answers are recorded in §2; the nine-module import table and consumer
inventory are re-read at the commit S1 starts from and that commit is
recorded here.

Exit: every EP row shows `RULED` (done 2026-09-02); the start commit for
S1 is recorded in §6; `git diff --check` and
`./scripts/check-internal-citations.sh` pass. No Lean file changes.

### S1 — Effects skeleton (new repository)

Fence: everything in `lean4-effects`.

Work:

- `lakefile.toml`: `name = "effects"`, libraries `Effects` (globs
  `["Effects"]` in S1 because Lake refuses a glob over a directory that
  does not exist yet; S2 widens it to `["Effects.*"]`) and `EffectsTest`, `defaultTargets` both, no `[[require]]`;
  `lean-toolchain` = `leanprover/lean4:v4.33.1`; empty roots `Effects.lean`
  and `EffectsTest.lean`.
- `LICENSE` per EP-7 (Apache-2.0; the same text was added to Effect4 on 2026-09-02).
- `AGENTS.md` and `EffectsTest/AGENTS.md` derived from Effect4's, with the
  representation rules that concern only the reification (first-order flow,
  fuel, Schema, Effect TypeScript) removed and the claim rules retained.
- `EffectsTest/Audit/AxiomGate.lean` ported from
  `Effect4Test/Audit/AxiomGate.lean` with `findProjectRoot` looking for
  `Effects.lean`, `belongsToAuditedTree` on `Effects`/`EffectsTest`,
  `auditedSources` walking those trees, and the exemption lists reduced to
  the gate module itself. `scripts/test-trust-gate.sh` ported without the
  `Effect4/Target/TypeScript/EffectfulField.lean` planting step and with a
  planted-choice fixture that targets an `Effects` module instead;
  `test-trust-boundaries.sh` loses its `Effect4Test.Schema.StructuralAssurance`
  import. `test/fixtures/trust-gate/` copied; `known-red.txt` empty.
- `.github/workflows/ci.yml`: `lake build`, `./scripts/test-trust-gate.sh`.
- `docs/CLAIM-BOUNDARY.md` (repair for R1 and R3): what `Effects` claims and
  does not. It claims structural equality of programs, the constructor,
  monad, interpretation, sum, freeness, initiality-in-models, interpreter
  pin, and `through` laws under the stated target-monad hypotheses. It has
  no equation field on `Signature`, no behavioural quotient, no host
  correspondence, and no theorem transfers between two handlers merely
  because they share a signature. Law satisfaction, observation relations,
  and host conformance are downstream records.

Exit: `lake build` green on the empty skeleton; `./scripts/test-trust-gate.sh`
green, including the planted `partial`, `unsafe`, and unadmitted-choice
rejections; CI green on the first push.

### S2 — History-preserving move and namespace rename (new repository)

Fence: `Effects/Algebra/**`, `Effects.lean`.

Entry: S1 green; EP-4 ruled; `git-filter-repo` installed.

Work:

1. From a fresh clone of `lean4-effect4` at the S0-recorded commit, run
   `git filter-repo` keeping `Effect4/Algebra/`, `Effect4Test/Algebra/`,
   `test/contracts/algebra-*.contract.md`, and
   `test/counterexamples/algebra/`, with `--path-rename` of
   `Effect4/Algebra/:Effects/Algebra/` and
   `Effect4Test/Algebra/:EffectsTest/Algebra/`.
2. Merge that history into `lean4-effects` with `--allow-unrelated-histories`.
3. One commit, "rename namespace Effect4 to Effects", containing only the
   three textual edits from §1.2 in the nine modules and the root
   `Effects.lean` importing them. The batteries are left red in this commit
   (they still `open Effect4`); they are repaired in S3.

Exit:

- `lake build Effects` green with `--wfail`.
- **Signature-and-axiom parity receipt** (repair for R6): a Lean script in
  `EffectsTest/Audit/Parity.lean` prints, for every constant declared in the
  nine `Effects` modules, the pair `(name, type)` with `Effects.` rewritten
  to `Effect4.`, plus its axiom set. The same script run against Effect4 at
  the S0 commit over the nine `Effect4.Algebra` modules must produce
  byte-identical output. Equal declaration counts are not accepted as a
  substitute. The receipt file is committed as
  `generated/algebra-parity.tsv` in Effects with the Effect4 commit named.
- `#print axioms` for the sixty receipts in `AxiomReport.lean` remain within
  `propext` and `Quot.sound`.

Must not change: any definition body, theorem statement, binder name,
universe, notation, or docstring in the nine modules.

### S3 — Evidence port and first release (new repository)

Fence: `EffectsTest/**`, `test/**`, `docs/**`, `generated/**`,
`EffectsTest.lean`.

Entry: S2 exit receipts committed.

Work:

- The two batteries and the axiom report: `open Effect4` → `open Effects`,
  `import Effect4.Algebra.X` → `import Effects.Algebra.X`, the twelve qualified
  `Effect4.` references → `Effects.`; `AxiomReport.lean` imports `Effects`,
  not a whole-repository root; `EffectsTest.lean` imports all three and ends
  with `#effects_axiom_gate`.
- Contracts: the two packets moved verbatim with a status line added
  ("moved from lean4-effect4 at `<commit>`; implementation fence
  `Effects/**`"). Their Foldlab source rows and digests stay as provenance.
- Register: `test/counterexamples/REGISTER.md` with the eight rows verbatim,
  an `origin` column (`lean4-effect4 <commit>`), and a `disposition` column
  per EP-6: `ported executable witness` (001, 005, 008 today; 002, 003, 004,
  006 after re-derivation), `retained external evidence` with the Foldlab
  commit, path, span, and whole-file SHA-256 (any not re-derived), or
  `design row` (007). Foldlab source and any license attribution preserved.
- `EffectsTest/Counterexamples/Algebra/*.lean`: the re-derived witnesses of
  EP-6, each a local Lean statement attacking the same weakened claim the
  Foldlab witness attacked, linked from its register row.
- `docs/DESIGN-BASIS.md` in Effects: DB-01 verbatim with attribution, plus
  the universe policy and the "no implicit lift" rule. DB-02..DB-07 are
  cited as Effect4-owned, not copied.
- `docs/ALGEBRA-DAG.md`: the proof graph for the nine modules only, derived
  from the two contracts and the sixty receipts. Edges from Effect4's design
  basis that concern Flow, semantics, or targets are not carried over.

Exit: `lake build` green; `./scripts/test-trust-gate.sh` green with an empty
`known-red.txt`; every register row has a disposition and a resolvable link;
axiom union is `propext`, `Quot.sound`; `lake env lean` on each battery from
a clean clone exits 0. Then tag `v0.1.0` and record the tag commit here.

### S4 — Effect4 cutover (this repository)

Fence: `lakefile.toml`, `lake-manifest.json`, `Effect4/Algebra/**` (delete),
`Effect4Test/Algebra/**` (delete), `Effect4/Schema/EffectfulField.lean`,
`Effect4.lean`, `Effect4Test.lean`, `Effect4Test/Schema/EffectfulFieldContract.lean`,
`Effect4Test/Counterexamples/Schema/EffectfulField.lean`,
`test/contracts/algebra-*.contract.md`, `test/counterexamples/algebra/`,
`test/counterexamples/REGISTER.md` (eight rows), `PORT-MANIFEST.md`,
`PLAN.md`, `docs/ARCHITECTURE.md`, `docs/DESIGN-BASIS.md` (DB-01 note),
`README.md`, `AGENTS.md`, `.github/workflows/lean_action_ci.yml`,
`scripts/test-trust-gate.sh`, `workshop/EffectfulField*.lean`.

Entry: Effects `v0.1.0` tagged; a `COORDINATION.md` claim on every fenced
file. Several of them (`Effect4.lean`, `Effect4Test.lean`, `REGISTER.md`,
`PLAN.md`, `PORT-MANIFEST.md`, the CI workflow) carry live partial claims by
other lanes; S4 waits for a quiet window or an explicit release, and lands as
one commit so the tree is never half-cut.

Work:

1. `lakefile.toml`: `[[require]] name = "effects"`, `git =
   "https://github.com/mepuka/lean4-effects"`, `rev = "<tag commit>"`.
   `lake update effects` writes the single manifest entry.
2. Delete the nine modules and the three test modules. Remove their import
   lines from both roots.
3. `EffectfulField.lean`: `import Effects.Algebra.Laws`, `open Effects` after
   `namespace Effect4`. The two Schema test files add `open Effects`.
4. Contracts: replace each algebra packet with a two-line pointer file
   naming the Effects repository, tag, and path. Register: the eight rows
   stay, status `MOVED`, pointing at the Effects register. `ATTACKS.md`
   likewise.
5. `PORT-MANIFEST.md`: the nine source rows' destination becomes
   `Effects/Algebra/<module>` at the tag; the two narrow-gate rows and the algebra
   axiom-report row point at the Effects commands. `PLAN.md` "Current phase":
   P3 is satisfied by the dependency, with the parity receipt cited.
   `docs/ARCHITECTURE.md`: the `Effect4/Algebra` row becomes "provided by
   `effects@<tag>`" and the dependency direction gains `Effects -> Effect4`.
   DB-01 gains one sentence naming the owner. `AGENTS.md` "Reuse and
   compatibility" gains: Effect4 depends on Effects, never conversely; a
   change to the algebra goes through the Effects breaker process.
6. `scripts/test-trust-gate.sh` copies `lakefile.toml` and
   `lake-manifest.json` into a throwaway project; with a dependency that
   copy must also receive `.lake/packages/effects` (or set `packagesDir`)
   or every gate run re-clones. Do this in the same commit and prove the
   gate still runs offline.
7. Workshop files: repoint imports or delete; they are scratch.

Exit: `lake build` green; `./scripts/test-trust-gate.sh`,
`./scripts/test-schema-structural-assurance-gate.sh`,
`./scripts/check-effect-runtime-census.sh`,
`./scripts/check-internal-citations.sh`, `git diff --check` all exit 0;
`#print axioms Effect4.interpret_set` (the Schema consumer's algebra-facing
theorem) unchanged; `lake-manifest.json` has exactly one package at an exact
commit; CI green from a clean clone. Effect4 then has no module under
`Effect4/Algebra`.

Must not change: any Effect4 theorem statement outside the fence; the axiom
ceiling; the runtime coverage number (the census does not touch the algebra).

### S5 — Streams acceptance probe (lean4-WHATWG-streams; out of this plan's fence)

Recorded for sequencing only. The streams repository runs its own P3
dependency-policy probe against `effects@v0.1.0`: exact pin, license,
transitive cost (zero packages), build on its toolchain. Any piece of Effect4
it finds it also needs is raised as an EP-9 ruling, not taken silently.

### S6 — Composition extensions (Effects; deferred)

Entry: a typed consumer example from S5 that the current `Handler.through`
cannot express. Not part of the split.

Work, in this order and only as far as the example forces: the three small
examples the review names (a disjoint pair with explicit embeddings; a
stateful handler over a residual signature; a scoped body that fails after
changing state needed by cleanup) as `EffectsTest/Examples/*`, each stating
what is compared before and after interpretation; then, if two independent
consumers need it, one packet for explicit signature maps with answer
transport and one for transporting an interpreter through `StateT`, each
with a conversion from the existing `ModelMorphism` rather than a second law
predicate. `Handler.through` is not changed.

## 4. Order and parallelism

```text
S0 ─► S1 ─► S2 ─► S3 ─► tag v0.1.0 ─► S4 ─► S5 ─► S6
      └────── new repository only ──────┘    └ this repository, one commit
```

S1–S3 can run while the concurrent Effect4 lanes continue, because they do
not write here. S4 is serialized behind a coordination claim. S6 is gated on
a consumer and may never open.

## 5. What must not change anywhere in the split

- No definition body or theorem statement in the nine modules; the namespace
  rename is the only edit, and the parity receipt proves it.
- The axiom ceiling stays `propext`, `Quot.sound`; Effects admits no
  `Classical.choice` outside its own gate module.
- Zero third-party Lake dependencies in Effects. "Zero dependencies" means
  no `[[require]]`; the Lean toolchain, core, and Std are the stated
  substrate.
- The eight counterexample IDs and their attacked statements.
- Test and audit tooling stay out of the `Effects` public import graph.
- Nothing from Effect4's Flow, Schema, Data, Semantics, Runtime, or Target
  moves in this plan (EP-9).

## 6. Verification ledger

Filled in as slices close.

| Slice | Commit | Commands | Result |
| --- | --- | --- | --- |
| S0 | `217d3e4` + working tree | `./scripts/check-internal-citations.sh`; `git diff --check` | rulings EP-1..EP-12 recorded 2026-09-02; `git-filter-repo` installed; Effect4 `LICENSE` added (Apache-2.0, uncommitted) |
| S1 | `lean4-effects` `27f777f`, pushed, CI green | `lake build` (gate: 3 modules, 35 declarations, ceiling `propext`/`Quot.sound`, one module admits `Classical.choice`); `./scripts/test-trust-gate.sh` | both green 2026-09-02: build exit 0; self-test 13 PASS lines (planted `partial`, `unsafe`, unadmitted `Classical.choice` rejected; seven tokenizer fixtures). S1 exit met: pushed and CI green |
| S2 | `lean4-effects` `57f570c` (merge of the filtered history) and `04e8af7` (rename), pushed; source `217d3e4` | `git filter-repo` (9 commits, 15 files); `lake build --wfail Effects` exit 0; `./scripts/check-algebra-parity.sh` PASS, 215 constants byte-identical; `./scripts/test-trust-gate.sh` 13 PASS with the three batteries excised as declared red | S2 exit met; the nine modules changed by exactly 26 namespace/import lines |
| S3 | `lean4-effects` `5611c3a`, tagged `v0.1.0` locally (tag not yet pushed) | `lake build` (gate: 18 modules, 367 declarations, ceiling `propext`/`Quot.sound`); `./scripts/check-algebra-parity.sh` PASS; `./scripts/test-trust-gate.sh` 13 PASS with an empty red list; `lake env lean EffectsTest/Algebra/AxiomReport.lean` union `propext`, `Quot.sound` over 60 receipts; from a clean `--no-local` clone at the tag: build green, each battery exit 0, parity PASS, `lake-manifest.json` has zero packages | S3 exit met. Register: eight rows with origin and disposition; CE-002/003/004/006 re-derived locally (`EffectsTest/Counterexamples/Algebra/`), CE-007 a design row. DB-01 and the universe policy in `docs/DESIGN-BASIS.md`; ten closed edges in `docs/ALGEBRA-DAG.md` |
| S4 | Effect4, this commit; `effects` pinned at `5611c3a` (tag `v0.1.0`) | `lake build Effect4` and the Schema consumers exit 0 (108 jobs); `#print axioms Effect4.EffectfulField.interpret_set` and `.get` unchanged (no axioms); default `lake build` fails on exactly the two modules already in `known-red.txt`; `./scripts/test-trust-gate.sh` PASS with those two excised and the probe copy resolving `effects` offline; `check-effect-runtime-census.sh` PASS (coverage unchanged: denominator 79, green 49); `check-fiber-assurance.sh` and `check-environment-context-key-evidence.sh` PASS after regeneration; `check-internal-citations.sh` and `git diff --check` PASS; `lake-manifest.json` has exactly one package at an exact commit; `Effect4/Algebra` and `Effect4Test/Algebra` no longer exist | S4 exit met. Left as found, both failing at `217d3e4` before the cutover and unrelated to the algebra: `check-schema-structural-assurance.sh` (stale pinned hash of the annotation attack file) and `check-data-row-assurance.sh` (optic `Lawful` declarations missing from its census). Frozen contracts that mention `Effect4.Algebra` in prose (flow-admission, schema-representation, schema-payload, environment-context-key) were not edited |
