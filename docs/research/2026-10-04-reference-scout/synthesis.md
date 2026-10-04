# Reference scout: synthesis (2026-10-04)

**The one thing to know first.** No reference project can enter `Effect4` or `Test` as a library.
Every candidate either needs Mathlib, uses `Classical.choice`, trusts an outside prover, or closes
goals with `sorry`. What transfers is patterns, plus machinery the toolchain already ships. The
module system can be cut over without touching the axiom gate, provided the gate's roots stay
non-module.

## The pass

- Base `682ea1fd`; the reference repos are pinned in `vendor/refs/MANIFEST.tsv` (`53640d85`).
- Six read-only seats, run as one workflow with one skeptical verifier per pair of seats: nine
  agents in all, 57 minutes.
- The notes:
  - [modules](modules.md): Lean core, Mathlib, Batteries, Aesop and the three packages;
  - [automation](automation.md): grind, Aesop, Mathlib's tactic frameworks, lean-auto, plausible;
  - [proof graph](proof-graph.md): LeanArchitect, leanblueprint, import-graph, doc-gen4;
  - [environment](environment.md): leanchecker, lean4lean, repl, Pantograph, jixia;
  - [semantics](semantics.md): cslib, iris-lean, loom, veil, `Std.Do`;
  - [compilation](compilation.md): lean-mlir, Aeneas, Lean's LCNF.
- The verifiers checked 368 claims against source and refuted 13. Every refutation is minor: a
  count, a file location, or a decisions-row citation. The verifications are
  [modules and automation](verification-modules-automation.md),
  [proof graph and environment](verification-proofgraph-environment.md) and
  [semantics and compilation](verification-semantics-compilation.md).
- Read a note together with its verification. The corrections that matter are listed in §6.

## 1. The module system: cut over, with one stop

The owner asked why a pilot is needed instead of a cutover. The modules seat's answer: none is.
Convert as one wave, and stop once after the first package to take five measurements
([modules](modules.md) §3(e)).

Most failures of this change are loud: the narrow build of each file catches them one by one.
Three failures are silent:

- the rebuild payoff is lost;
- the gate audits less;
- public names disappear.

The measurements M1 to M5 exist to catch these three.

**The gate is safe if its roots stay non-module.** A non-module file, and any `importModules`
call left at its default level, reads the private part of each module's `.olean`. That part holds
every kernel constant, so `Test/All.lean`, `Test/Slow.lean`, `ProofGraph.Audit`,
`ProofGraph.Axioms` and the reach probe keep seeing every proof body, with no code change. In a
*module* root, imported theorems arrive as `axiomInfo`, and the gate would refuse them. So the gate
should refuse to run in a module root. Both verifiers confirmed this against
`Lean/Elab/Import.lean`, `Lean/Environment.lean`, `Lean/AddDecl.lean` and Lake's
`Lake/Build/Module.lean`.

**The payoff is narrower than tooling map §1.10 says.** Lake skips rebuilding a module's importer
only when the import's exported `.olean` comes out byte-identical (`ModuleImportInfo.addImport`).
A proof edit keeps it identical. Under the expose-everything idiom, an edit to a definition's body
does not. Narrowing exposure to win that too is a later, measured step (§7, question 2).

**Correction to the tooling map.** None of the three packages has a module file today: `effects`
0 of 46, `hash` 0 of 54, `typescript` 0 of 12. The earlier "3 of 46" and "3 of 54" counted
doc-comment lines that begin with the word "module".

**The size of the tree.** At `682ea1fd` there are 425 `Effect4` modules, 269 under `Laws`. Of
these, 197 reach none of the packages, so they can convert first (verifier's recount).

**The per-file transformation** follows Batteries and Mathlib (8,241 of Mathlib's 8,311 files
are modules):

1. `module` comes first, and every `import` becomes `public import`.
2. Definition and theorem files get `@[expose] public section`, which keeps today's unfolding;
   only proofs become private.
3. Tactic and command code goes in `public meta section`, with `public meta import`; initializers
   become `meta initialize`.
4. A `#guard` or `#eval` over imported code needs `meta import`.
5. Mixed files split: `Effect4.Laws.Auto.Semantics` is the known case.
6. A private helper that an exposed body calls is de-privatized, or passed through
   `backward.privateInPublic` (with `.warn false`, because every warning is an error here).
7. A core definition that a proof unfolds and the core does not expose needs `import all Init.…`.

Sixteen traps are listed in [modules](modules.md) §3(d).

**What else changes in the tree:**

- the ten emitter sites of the generators write the new header;
- the projection guard reads imports with `Lean.Elab.parseImports`, since today it keeps only
  lines that start with `import `;
- the gate refuses a module root;
- `Test`, `tools` and `OCaml5` stay non-module;
- after the wave, `lake shake Effect4 Effect4.Laws --explain` narrows `public import` to `import`
  where only proofs use a module. That multiplies the payoff.

**Order:**

1. `hash` (the most traps: 302 theorem lines, 108 `private` lines, 39 `#guard` lines, a meta
   audit command), then stop for M1–M5;
2. `typescript`;
3. `ProofGraph.Proof`, `Search` and `Ledger`;
4. `src/Effect4`, leaves first; repeat M1 on the first `Laws` chain that carries `@[semantics]` and
   `@[aesop]` attributes;
5. `effects`, before the `Laws` modules that import it.

## 2. The planning graph

- **LeanArchitect's statuses do not fit.** Its `\leanok` is the absence of `sorryAx`, and
  leanblueprint builds every status on `\leanok`. The estate's ledger is sorry-free. Copy only
  LeanArchitect's stop-at-node dependency walk (`CollectUsed.collect`).
- **Edges are kernel-checked implications.** Build them from the conditional theorems the estate
  already writes, in `m7_of_ledger`'s pattern. A matcher indexed by the head constant proposes
  premise-to-goal matches by `isDefEq`, and the kernel checks the implication. "Proved" still
  means an `X.checked` theorem ([proof graph](proof-graph.md) §4).
- **What each proof brings in is already on disk.** The `.olean` holds the proof terms. The
  `.ilean` holds every source reference, tagged with its enclosing declaration. A profile per
  theorem needs no elaboration and no new dependency. Aesop's statistics file adds the bank detail
  on demand ([environment](environment.md) §3(c)).
  - Verifier's caveat: what the term shows is elaboration and automation together. Only a mapping
    from lemma to bank attributes a lemma to automation.
- **A defect found by reading.** Three string filters for auxiliary declarations
  (`semanticsNoise`, `Tools.Architecture.isNoise`, the probe's copy) drop 23 real theorems, of
  which 22 are recoverable. Replace them with one helper over Lean's own predicates, and keep the
  estate's extra spellings, which Lean's predicates do not cover.
- **The first ledger goals.**
  - R12-a, "a fair finite tape leaves nothing armed". It consumes `FairTape` as a premise, which
    no theorem does yet. It is an hours-sized slice ([semantics](semantics.md) §4).
  - Then R11 over the whole run, with reduction edges.
  - For invariants, generate one goal stub per (command, clause) pair, as veil's
    verification-condition matrix does.

## 3. Trust and automation

- **Not under the ceiling: `grind` and lean-auto.** `grind` applies `Classical.byContradiction`
  to every goal that is not `False`, and its case splits use `Classical.em`. No configuration
  removes the first step. lean-auto does the same, and it accepts outside provers only through the
  axioms `autoTPTPSorry` and `autoSMTSorry`.
- **plausible** closes its goal with `sorry`. It fits only a tools lane that tries to falsify
  stated ledger goals before anyone proves them.
- **The kernel rung.** Never run a bare `leanchecker` here: it replays every matching module at
  once, one imported environment per core, and lean4lean's CI reports out-of-memory kills for that
  shape. Write a safe sequential driver over `Lean.Environment.replay` for the sweep tier. lean4lean
  as a second kernel comes later.
- **Linters.**
  - A proof-style syntax linter (the ban on `simp_all`, `first` and `try`) is cheap.
  - An axiom-ceiling linter for narrow builds is real, but its cost is not established.
  - The bank lint stands. Its proposed `-X` red control contradicts decisions row 65 and is dropped.
- **Pantograph.** Trial it as an outside tool before writing an estate-native proving session for
  agents.

## 4. Semantics vocabulary

- **cslib** offers transition systems, simulation, fairness and stuck states. Copy the definitions
  into one law module and rewrite the proofs without `grind`. Verifier's caveat: some pieces rest
  on Mathlib (`ωSequence`, `List.TFAE`, `Relation.Comp`), so the slice is larger than the note says.
- **`Std.Do` and `mvcgen`** stay right for checkers that return `Option`. They do not fit R11 over
  the whole run, R12, or the congruence half of R13. `tools/Conform/Spec/Reflect.lean` reflects only
  `Option` leaves, so an `Except` leaf needs new tooling.
- **Later:** bundle world monotonicity into the world-indexed predicates, as Iris's `MonPred` does.

## 5. Verified compilation

- **No template exists for rows 28, 29 and 31.** lean-mlir proves rewrites inside one denotation.
  Its two stages across semantics rest on an axiom that proves every proposition, or end in `sorry`.
  Aeneas assumes its translator is correct.
- **What transfers:**
  - rewrite rows that carry their own proofs, lifted by one driver theorem, starting with the LCNF
    route's 50-row builtin table, where DI-56's bound becomes each row's premise;
  - a specification registry with a stepping tactic for `TypedProg`, `eff_step`, in the pattern of
    Aeneas's `progress`.
- **The module cutover touches LCNF.** Across modules, LCNF exports a body only when it is
  template-like, or small and exposed. Regenerate the `lcnf` family after each converted chain and
  diff it.

## 6. Corrections the verifiers made

| Note | Claim | Correction |
| --- | --- | --- |
| modules | 459 `Effect4` modules, 229 reach no package | 425 and 197 |
| modules | `Test.lean` runs the gate | only `Test/All.lean` and `Test/Slow.lean` do |
| modules | `replayFromImports` avoids the private level | it imports at the private level |
| automation | `#bank_control` red control with `-X` | contradicts decisions row 65; aesop throws on an inactive set |
| proof graph | LeanArchitect as a dependency brings `Cli` into the law graph | only its executable imports `Cli` |
| proof graph | `exportedAxiomsExt` costs every module build time | it is built into core and already computed |
| semantics | no theorem reads `FairTape` | one does (`empty_queue_empty_tape_fair`); none takes it as a premise |
| semantics | `Reflect.lean` covers `Except` leaves | `Option` only |
| compilation | Aeneas's loader is in `SpecInfo.lean` | it is in `Aeneas/Std/Spec.lean` |

## 7. Order of work, and the owner's questions

The order:

1. The module wave: `hash` and M1–M5; the gate's module-root refusal and the emitters; then
   `src/Effect4` bottom-up (decisions row 200).
2. The planning slice: `ProofGraph.Reach` with the stop-at-node walk, one population filter and
   kernel-checked edges; then R12-a and R11 as the first ledger goals.
3. The brought-in profile from `.olean` and `.ilean`.
4. `check-kernel` through a safe replay driver.
5. Later: the transition-system vocabulary module, `eff_step`, the rewrite-row driver for LCNF
   builtins, the plausible lane and the linters.

The owner's questions:

1. **The exposure default for definition files.**
   - `@[expose] public section`, recommended for the wave: it keeps today's unfolding, and only
     proof edits stop rebuilding importers.
   - Plain `public section`, with `@[expose]` per definition where `Laws` unfolds: definition-body
     edits stop rebuilding too, but it changes what `Laws` can unfold.
2. **The 1,050 library `#guard` lines** in 48 `src/Effect4` files. Either keep them in place with
   `meta import`, so a body edit in what they import rebuilds them, or move them to non-module
   `Test` files.
3. **Private helpers that exposed bodies call.** Either de-privatize them, which renames them and
   touches the gate's exemption lists, or pass them through `privateInPublic` as a temporary escape.
4. **The three packages** are separate repositories. Converting one means a commit and a push
   upstream, then a new pin here.
