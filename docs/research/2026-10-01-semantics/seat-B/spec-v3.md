# The semantics report: implementation spec v3 (seat B, 2026-10-01)

Base: branch `refactor/phase1-phase3`, HEAD `198dd533` (the brief's; no git command run). Inputs:
Gemini's `gemini/domain-model-spec.md` v2 and `gemini/note.md` §§3–4; Codex's
`/private/tmp/codex-second-eyes-2026-10-01/domain-spec-review/review.md` and
`/private/tmp/codex-second-eyes-2026-10-01/domain-spec-ledger-review.md`; the coordinator's
`review-gemini-v2.md`; the owner's plan, `docs/research/2026-10-01-landing/status-2026-10-01-evening.md`
§§7, 7b, 7c. Paths below are repository-relative unless absolute. Evidence words: **proved** (a
Lean theorem), **tested** (a run with an exit code, in this folder's `probe/`), **reading** (a
file:line read tonight), **assumed** (not checked). Every file:line was read at `198dd533`.

## 0. Before anything else

1. **The slice cannot land green until the coordinator adds a register row.** The refuted item's
   witness, `Test.Program.TypedProgBindRed.typedProg_not_bind_closed`
   (`Test/Program/TypedProgBindRed.lean:32`), has no row in `Test/Counterexamples/REGISTER.md`
   (grep: 0 hits; reading). The next free TYPED id is **030**, not 023: 023 is earmarked by
   decisions row 176 ("`E4-TYPED-CE-023` if it holds", `docs/core/decisions.md:269`; reading).
   The proposed row is in `receipt.md` §5. The driver refuses an id the register lacks (§3), so
   until the row exists the producer exits 1 by design.
2. **The wanted item is contested.** `denoteR_typed`'s proposition `DenotesTyped root` is the
   attacked statement of three register rows whose leading status is SEEDED
   (`E4-TYPED-CE-020`, `-021`, `-022`, `REGISTER.md:249-251`; their witnesses are on `seat/D2`
   or "reading, not compiled", not in this tree). A report that shows `wanted` and nothing else
   tells a reader the goal is open and believed. The model carries `contestedBy` (§2.3); the
   slice shows the three rows.

## 1. What is built, and what is not

One generated report of the language's claims and their evidence, measured from the Lean
environment and two registers, never drawn:

- **Built:** a Lean registry of concepts, claims and cuts (`tools/Tools/SemanticsRegistry.lean`);
  a declaration attribute and census command (`src/Effect4/Laws/Auto/Semantics.lean`); a driver
  that joins the registry with the environment, the counterexample register and the decisions
  register (`tools/Tools/Semantics.lean`, a library without `main`) and its two `main`s, the
  producer `tools/Drivers/Semantics.lean` and the refusal controls
  `tools/Drivers/SemanticsControls.lean`; the committed outputs `generated/semantics.json` and
  `generated/semantics.md`; an Effect Schema of the report and a decode check in `ts/eff/`
  (`semantics.ts`, `check-semantics.ts`, the pinned cases `test/semantics.test.ts`); the Makefile group
  and check; one `docs/GENERATED.md` row.
- **Not built:** no `Effect4.Document`/`Representation` encoding of the report (Codex review §1:
  the report is a plain record; a schema *document* of its shape is a later dogfooding step); no
  new annotation key and no change to `erasedKeys` (`src/Effect4/Schema/Bridge.lean:105-108`,
  nine keys; Codex review §2); no architecture-map section (a later slice reads
  `generated/semantics.json`); no `docs/core/semantics.md` (the coordinator writes its prose); no
  literature locators (seat A's `citations-audit.md` and `sources/README.md` own them; the slice
  carries none).
- **Superseded wording of the owner's plan** (reading, status note §7b–§7c, lines 184–248):
  `@[chapter …]`/`#chapter_census` become `@[semantics …]`/`#semantics_census`, organized by
  concept, with book chapters as many-to-many literature references (Codex review §6);
  `tools/architecture/chapters.json` becomes the Lean registry (R1, §2.1); "the document is a
  `Representation` … keys erased by `N_S`" is not done (Codex review §2: the bridge refuses an
  unknown key, `Bridge.lean:111-117,181`; reading through Codex).
- **What a zero unplaced count means:** every eligible theorem of the stated universe has a
  concept, nothing more (Codex review §3). It does not show that every required claim exists;
  the registry's claims, with `absent` visible, are that list.

## 2. The model: three records, one owner per field

Codex's boundary (ledger review, "Suggested model boundary"): (1) an inventory with its
provenance, (2) validated evidence from the existing ledger and trust policy, (3) authored
assignments. Every field below names its one source: **registry** (authored, §2.1),
**environment** (the loaded Lean environment), **register** (`Test/Counterexamples/REGISTER.md`
or `docs/core/decisions.md`, read as text), or **derived** (computed by the driver from the
others). Nothing is authored twice: a register status, a decision's owner, a statement, a
proposition, an axiom list or a count is never written in the registry.

### 2.1 The registry (`tools/Tools/SemanticsRegistry.lean`, namespace `Tools.Semantics`)

First-order data only: structures and inductives with `deriving Repr, Inhabited` (the precedent's
form, `tools/Tools/ArchitectureRoles.lean:50-58`), no function fields, no `Expr`. Names are
single-backtick `Name` literals, unchecked at compile time and checked against the loaded
environment at run time (a double-backtick literal would make the registry import the declaring
modules, and a tool may not import `Test`, `ArchitectureRoles.lean:192-195`). The module imports
`Lean` only (for `Name`).

```lean
namespace Tools.Semantics
open Lean

/-- The proof role a claim plays. The first ten are the owner's lemma list (status note §7b,
line 195); `adequacy`, `simulation` are Codex's (review §6); `compatibility` and
`fundamentalProperty` are the tree's own words for the slice's claims
(`Laws/Program/Typed/Seq.lean:55`, `Laws/Program/Typed/Assembly.lean:1636`). -/
inductive Role
  | inversion | canonicalForms | weakening | substitution | progress | preservation
  | monotonicity | transitivity | antisymmetry | decidability | adequacy | simulation
  | compatibility | fundamentalProperty
deriving Repr, Inhabited, BEq

/-- What the claim points at. Authored; never a status (§3 derives the status). -/
inductive Pointer
  /-- a plain theorem stating the claim (not `theorem`, a keyword, which v2 had to escape) -/
  | witness (name : Name)
  /-- a ledger goal: a theorem whose type concludes `ProofGraph.Obligation p` -/
  | goal (name : Name)
  /-- a theorem refuting the claim, and the register row that records it -/
  | refutedBy (registerId : String) (witness : Name)
  /-- no witness, no goal, no refutation; the reason is required -/
  | absent (reason : String)
  /-- an external statement with no local evidence -/
  | assumed (source : String) (reason : String)
deriving Repr, Inhabited

/-- A key into seat A's source index (`docs/research/2026-10-01-semantics/sources/README.md`)
with a locator read off that file; never a locator from memory (owner, 21:30). -/
structure LiteratureRef where
  work : String
  locator : String
  relation : String   -- definitionUsed | proofTechnique | adaptedResult | analogy | excludedFeature
deriving Repr, Inhabited

structure Claim where
  id : String                     -- kebab-case, unique
  concept : String                -- a `Concept.id`
  role : Role
  title : String                  -- words; the statement itself is printed from the environment
  pointer : Pointer
  /-- register rows whose attacked statement is this claim's, kept open beside the status -/
  contestedBy : List String := []
  literature : List LiteratureRef := []
deriving Repr, Inhabited

structure Concept where
  id : String                     -- kebab-case, unique
  title : String
  /-- modules whose untagged theorems default to this concept (`inherited`, provisional) -/
  defaultModules : List Name := []
deriving Repr, Inhabited

/-- An applicability decision (R6): what a concept's claims exclude, by a decisions row.
The row's owner (`who`) is read from the register, not written here. -/
structure Cut where
  concept : String
  decisionRow : Nat
  excluded : String
  reason : String
deriving Repr, Inhabited

structure Registry where
  roots : List Name               -- loaded with `importModules`; stated in the report
  concepts : List Concept
  claims : List Claim
  cuts : List Cut
deriving Repr, Inhabited

def registry : Registry := { … }  -- §9.1 holds the slice's value

end Tools.Semantics
```

### 2.2 Environment facts (driver-internal, tooling only; never serialized as `Expr`)

The driver keeps the checked references the ledger already defines: `ProofGraph.Goal`
(`tools/ProofGraph/Ledger.lean:17-21`: id, levels, proposition `Expr`, dependencies) and
`ProofGraph.ProofRef` (`tools/ProofGraph/Proof.lean:13-16`). These stay inside the driver
("This reflection data is tooling only", `Proof.lean:8`). What reaches the report is a display
projection: the name, the module, the universe names, the printed statement, the sorted axiom
list and the Boolean `withinSemanticAxiomCeiling` (Codex ledger review §4).

### 2.3 The report (`generated/semantics.json`), field by field

| Field | Source | How |
| --- | --- | --- |
| `format` = `"effect4-semantics-report"`, `schemaVersion` = 1 | derived | constants of the driver |
| `producer` | derived | `Tools.GeneratedStamp.note "tools/Drivers/Semantics.lean (make gen-semantics)"` (`tools/Tools/GeneratedStamp.lean:14-15`) |
| `command` = `"make gen-semantics"` | derived | the exact regeneration command (`generated/AGENTS.md:22-23`) |
| `inputs` | derived | the canonical inputs, repository-relative: the registry, the driver, the attribute module, `Test/Counterexamples/REGISTER.md`, `docs/core/decisions.md`, `lean-toolchain` (`generated/AGENTS.md:22-23`) |
| `provenance.toolchain` | environment | the content of `lean-toolchain`, trimmed (`leanprover/lean4:v4.33.1`; reading) |
| `provenance.roots` | registry | `Registry.roots` |
| `provenance.policy` | derived | `{ gate: "Test/Audit/AxiomGate.lean", ceiling: ["propext", "Quot.sound"] }`: the semantic/test ceiling (`AxiomGate.lean:66-67`, the same pair `Proof.lean:26` uses) |
| `concepts[].{id,title,defaultModules}` | registry | as authored, registry order |
| `concepts[].counts` | derived | the claims of the concept tallied by status; `claims` = their number |
| `claims[].{id,concept,role,title,literature}` | registry | as authored, registry order |
| `claims[].status` | derived | §3; carries the evidence's display projection (§2.2) |
| `claims[].contestedBy[]` | registry + register | each id authored; `registerStatus` read (the first word of the row's status cell); `witness` null in this version: the registry names ids only, the register's witness cell is prose, and the slice's three witnesses are not in this tree |
| `cuts[].{concept,decisionRow,excluded,reason}` | registry | as authored |
| `cuts[].who` | register | the `who` cell of the row in `docs/core/decisions.md` (header at `decisions.md:20`) |
| `placement.universe` | derived | the stated population (§4.4) |
| `placement.declarations[]` | environment + registry | tagged (attribute) or inherited (module default), sorted by name |
| `placement.unplacedCount`, `unplacedByModule[]` | derived | eligible theorems with neither, per module, sorted |

No wall clock and no commit in the bytes. The commit cannot be: a committed file cannot name the
commit that contains it, and the tree removed embedded revisions from generated files on
2026-09-13 (`tools/Tools/GeneratedStamp.lean:1-9`; `docs/GENERATED.md:13-23`; the map's footer,
"No commit or date is embedded", `tools/Tools/Architecture.lean:747`; reading). The run's commit,
dirty count and the gate verdict (`notAudited`: the producer never runs the gate) go in a per-run
receipt that is not committed (§7.1).

## 3. The status of a claim, derived (R2)

The driver runs in `MetaM` over the loaded environment, as the tree's generators do
(`importModules … {} 0`, a `Core.Context`, `(act.run' {}).toIO ctx { env := env }`:
`tools/Effect4Gen/Check.lean:251-259`, `tools/Drivers/ProgramStructureCheck.lean:10-28`).
`ceiling` below means `collectAxioms n ⊆ [propext, Quot.sound]` (the Boolean
`withinSemanticAxiomCeiling`); it is not the trust gate's verdict, which also refuses unsafe,
partial, extern, implemented-by and bodyless-opaque declarations and admits named exceptions
(`Test/Audit/AxiomGate.lean:423-490`; Codex ledger review §2). The report never says "passes
the gate".

| Pointer | Environment facts | Register facts | Status | Otherwise: refusal (location: the claim id) |
| --- | --- | --- | --- | --- |
| `witness n` | `n` is a `thmInfo`; `ProofRef.validate ⟨n, levels, type⟩` is `ok` (`Proof.lean:18-28`: theorem, closed, universes, axioms at the ceiling) | — | **proved** (`by: "theorem"`) | `n` missing or not a theorem; open type; axioms beyond the ceiling (the validator's message) |
| `goal g` | `g` is a theorem whose type concludes `ProofGraph.Obligation p` under its binders (the shape of `readGoal`, `src/Effect4/Laws/Auto/Obligations.lean:15-24`, private, so the driver repeats its eight lines and cites them); `g.checked` exists and `ProofGraph.check #[goal] #[⟨g, .proved g.checked⟩] 0` returns (`Ledger.lean:58-90`, which runs `ProofRef.validate` at the goal's proposition, `:75-78`); `g.wanted` does not exist | — | **proved** (`by: "ledger"`; `witness` = `g.checked`, `goal` = `g`) | `g` missing; not an obligation; `.checked` fails validation |
| `goal g` | `g.wanted` exists and `ProofGraph.check #[goal] #[⟨g, .wanted g.wanted⟩] 1` returns (`Ledger.lean:79-81` runs the private `validateWanted`, `:46-55`: a `ProofWanted` definition at the same proposition and universes, axioms at the ceiling); `g.checked` does not exist | — | **wanted** (`goal`, `placeholder`) | the placeholder fails validation |
| `goal g` | both `g.checked` and `g.wanted` | — | — | stale placeholder (the ledger's own refusal, `Obligations.lean:87-89,95-96`) |
| `goal g` | neither | — | — | missing evidence (`Obligations.lean:91-93,97-98`) |
| `refutedBy id n` | `n` validates as for `witness n` | `id` is a row of `REGISTER.md` whose status word is not `RETIRED` | **refuted** (`counterexample: {id, registerStatus, witness}`) | `n` as above; `id` not in the register; a `RETIRED` row (its attacked statement no longer exists, `REGISTER.md:26-28`) |
| `absent r` | — | — | **absent** (`reason`) | `r` blank |
| `assumed s r` | — | — | **assumed** (`source`, `reason`) | `s` or `r` blank |
| any, `contestedBy` ids | — (ids only in this version) | each id is a register row; status word read | `contestedBy[]` beside the status | an id not in the register |

Whole-registry refusals, each with its location: a duplicate concept id, claim id or default
module; a claim, cut or tag naming no concept; one ledger goal named by two claims (Codex review
§8, condition 3: a goal is counted once); a decisions row the register lacks; a default module or
witness module not loaded from the stated roots (a missing module is never a measured zero,
Codex ledger review §3). A run with any refusal writes nothing and exits 1 with every refusal
listed (the ledger's "every mismatch is collected" rule, `Obligations.lean:70`).

**Statements** are printed at emit time, never typed: `ppExpr` of the constant's type (a goal:
of its extracted proposition) under `pp.fullNames := true`, rendered at a fixed width
(`Format.pretty` with width 100); axioms are `collectAxioms` sorted by `Name.toString`.
Determinism of the printer across two runs is assumed and is what the check's two-run byte
comparison tests (§7.2).

**Register parsing.** A row of the live register is a line beginning ``| `E4-`` (the register's
own count rule, `REGISTER.md:11`); its first cell is the backticked id, the first word of its
second cell the status word (one of `SEEDED`, `PINNED`, `RESERVED`, `MOVED`, `REPAIRED`,
`RETIRED`, `REGISTER.md:13-28`; anything else is a refusal). Only the live file is read, not
`Archive/REGISTER.md`. A decisions row is a line `| N |` with `N` a number; its fifth cell is
`who` (the header, `decisions.md:20`).

## 4. A declaration's concept: the attribute, the default, the census (R4)

### 4.1 The attribute

`src/Effect4/Laws/Auto/Semantics.lean`, namespace `Effect4.Laws.Auto`, beside `#auto_census`
(`Laws/Auto/Census.lean`) and the ledger commands (`Laws/Auto/Obligations.lean`). It imports
`Lean` only, as four instrument modules of the Laws graph do at HEAD (`Laws/Auto/AnswerGate.lean:1`,
`Laws/Auto/Positions.lean`, `Laws/Program/Authoring/Tactic.lean`,
`Laws/Program/Typed/TypedSources.lean`), all on the gate's implementation list. DI-18's text
(ruled 2026-09-09, `docs/DESIGN-ISSUES.md:91`) says "no `import Lean` in the audited closure", and
the script it names, `scripts/check-library-roots.sh`, no longer exists (reading): the tree and the
ruling's text disagree; the coordinator may want that row updated before a fifth module follows.

- **Syntax:** `syntax (name := semanticsAttr) &"semantics" ppSpace str : attr`. The `&"…"` form
  is a non-reserved symbol: the word `semantics` stays an identifier everywhere else (Lean's own
  attributes with arguments use `nonReservedSymbol`, `Lean/Parser/Attr.lean:45,48-49,53-54` in
  the 4.33.1 toolchain source; the DSL form is used at `Init/Notation.lean:627`; reading). A
  reserved keyword would break every later identifier spelled `semantics`.
- **Arity:** exactly one string, the concept id, kebab-case (refused otherwise at the attribute).
  One concept per declaration: its primary home. The `add` that `registerParametricAttribute`
  builds does not itself refuse a second entry (`Lean/Attributes.lean:281-288` inserts into a
  `NameMap`; only `setParam`, `:307-313`, checks "Attribute has already been set"), so the
  implementation's `getParam` refuses when `getParam?` already answers for the declaration
  (reading; the fixture's red control tests it). A theorem's further relationships come from
  claims, which may name it under any concept (Codex review §6).
- **Storage:** `registerParametricAttribute` (`Lean/Attributes.lean:263-291`) with
  `ParametricAttributeImpl String`, registered by `initialize`. Lean refuses the attribute on a
  declaration of an imported module (`:284-285`), so a declaration is tagged where it is declared;
  declarations in modules the author does not edit get their concept from a registry default
  (§4.2). The attribute cannot check the id against the registry (Laws may import, from the tool
  roots, only `ProofGraph`: `tools/Tools/ArchitectureRoles.lean:190`); the driver refuses a tag
  naming no concept, with the declaration and its module.
- **Reading it in the driver:** `ParametricAttribute.getParam?` (`Attributes.lean:295-305`)
  reads an imported declaration's tag from `getModuleEntries`. The tree's drivers call
  `importModules imports {} 0`, whose `loadExts` defaults to `false` (`Lean/Environment.lean:2438-2440`);
  imported entries are nevertheless set for every extension registered in the process at
  `finalizeImport` (`Environment.lean:2376`, `setImportedEntries` `:1931-1949`). So the driver
  must import `Effect4.Laws.Auto.Semantics`, so that the `initialize` has run before
  `importModules` (allowed: a tool imports the proof graph, `ArchitectureRoles.lean:193`).
  **Assumed** from that reading; commit C2 (§11) carries the control that tests it (the
  controls driver loads `Test.Audit.SemanticsCensus` with `importModules` and must read the
  fixture's two tags).
- **The trust gate:** the module's `initialize` and command elaborator are `MetaM` code; like
  `Effect4.Laws.Auto.Census` (`AxiomGate.lean:90-92`) and `Effect4.Laws.Auto.RuleSets`, whose
  `initialize` "crosses to `Classical.choice`" (`:100-104`), it joins
  `auditImplementationModules` (`:85-117`). The gate fails a listed module that no longer reaches
  `Classical.choice` (`:474-482`), so the entry is **assumed** needed until the gate runs at the
  owner's next sweep; if the gate calls it stale, the entry goes.

### 4.2 The module default

`Concept.defaultModules` (registry). An eligible theorem (§4.4) with no tag, in a default module,
is `inherited`: provisional, shown as such in the report and the table (Codex review §8,
condition 3). A module listed under two concepts is a refusal. A tag wins over a default.

### 4.3 `#semantics_census`

    #semantics_census                      -- every loaded module under Effect4.Laws
    #semantics_census Effect4.Laws.Program.Typed.Seq   -- one module

Prints, from the environment alone (the registry is tool-side, §4.1): per concept string, sorted,
each tagged declaration as `name<TAB>kind<TAB>axioms` with the axioms `collectAxioms` reaches;
then the line `untagged: N theorems in M modules (universe: …)` and, per module, the untagged
names. The claims and their statuses are not printed here: they need the registry, so the driver
prints them (the report and `generated/semantics.md`). Its fixture is
`Test/Audit/SemanticsCensus.lean` (§6), `#guard_msgs` over the output, in the shape of
`Test/Audit/Obligations.lean:10-16`.

### 4.4 The census universe, stated in the report

"Theorems (`thmInfo`) of the modules under `Effect4.Laws` loaded from the roots, excluding the
names `isNoise` excludes (the copy of `tools/Tools/Architecture.lean:163-172`, §6), ledger goals
(a type concluding `ProofGraph.Obligation`, `Architecture.lean:70-72`) and their published
`<goal>.checked` witnesses, which are counted through claims, once" (Codex ledger review §1: name
the population so a proved goal is not counted as both marker and witness).

## 5. Cuts: applicability decisions, never a status (R6)

A cut says what a concept's claims do not cover and which decisions row says so (Codex review §4,
last paragraph: "a cut is an applicability decision with a reason and owner; it is not a proof
status"). Registry: `{ concept, decisionRow, excluded, reason }`; the driver reads the row's
`who` from the decisions register and refuses a row it lacks. The rows the owner's §7 names that
are cuts (reading, `docs/core/decisions.md`):

| Row | Status in the register | Excluded | Concept (proposed id) |
| --- | --- | --- | --- |
| 163 (`decisions.md:256`) | ruled 2026-10-01, owner | function values, function types, parameterized declarations: "not represented. The language cut rules it" (`docs/core/language-cut.md` §1, line 21: "There is no lambda and no function value") | `residual-program-typing` and the typing concept |
| 128 (`decisions.md:221`) | ruled 2026-10-01, owner | exactness claimed only at the bridge modulo `normS`; the retraction only on closed types whose handles avoid `effect/schema/TypeParameter` (AGENTS.md, vocabulary, exact embedding) | `exact-codecs` |
| 138 (`decisions.md:231`) | ruled 2026-10-01, owner | M7 only at the empty host table, on answer-free tapes; the OCaml engine outside M7 until row 28 | the machine-agreement concept |
| 117 (`decisions.md:210`) | open, recommended | open root requirement rows: M5/M6c/M7 take `rootTy.requires = ∅` (rc.112 runs closed rows, `Effect.ts:17494-17497` as the row cites) | `residual-program-typing` |

Not cuts: the planned type constructors of §7 (rows 119, 130, 158, 159, 160, 165, 177, 178) are
features not yet landed; they are claims (absent until declared), not exclusions. Statement
repairs pending on a goal (rows 170, 175 on `DenotesTyped`) are not cuts either: they reach the
report through `contestedBy` (§2.3) while their register rows stay open.

## 6. Files, each with its precedent

| Path (new unless marked) | What | Precedent |
| --- | --- | --- |
| `tools/Tools/SemanticsRegistry.lean` | the registry, §2.1; the second hand input beside `ArchitectureRoles.lean` | `tools/Tools/ArchitectureRoles.lean:1-17` (one hand input of a measured report), `:50-58` (structures, `deriving Repr, Inhabited`), `:201-214` (roots as data) |
| `tools/Tools/Semantics.lean` | the library, no `main`: `importModules` of `Registry.roots`, the `MetaM` join, the refusals, the JSON and Markdown emitters; it repeats `isNoise` (`Architecture.lean:163-172`) and `readGoal`'s shape (`Obligations.lean:15-24`) with citations, because `Tools.Architecture` defines a top-level `main` (`Architecture.lean:752-753`) and two modules with `main` cannot share an environment (`ArchitectureRoles.lean:199-200`), and `readGoal` is private | `tools/Tools/Architecture.lean:175-178` (roots, `importModules`), `tools/Effect4Gen/Check.lean:251-259` (`MetaM` over a loaded env), `tools/Tools/HostProtocol.lean:3,59` (`Lean.Data.Json`, `Json.pretty ++ "\n"`), `Architecture.lean:753-781` (`main`, exit codes) |
| `tools/Drivers/Semantics.lean` | the producer's `main (args : List String) : IO UInt32`: `<outdir>`, writes `semantics.json` and `semantics.md`, exit 1 with every refusal | `tools/Drivers/ProgramStructureCheck.lean:1-3,9` (a thin `main` over a `Tools` library) |
| `tools/Drivers/SemanticsControls.lean` | red controls: each a mutated `Registry` (or a synthetic register index) that must refuse with the expected location and reason | `tools/Drivers/ProgramStructureCheck.lean:5-7,17-27` (`expectRefusal`) |
| `src/Effect4/Laws/Auto/Semantics.lean` | the attribute and `#semantics_census`, §4 | `src/Effect4/Laws/Auto/Census.lean:63-101` (a command over the environment), `:69` (an `initialize` in an Auto module) |
| `Test/Audit/SemanticsCensus.lean` | fixture: two tagged fixture theorems, the census output under `#guard_msgs`; red controls under `#guard_msgs (error)`: a non-kebab id, a second tag on one declaration | `Test/Audit/Obligations.lean:1-39` |
| `ts/eff/semantics.ts` | the report's Effect Schema, hand-written, flat | `ts/eff/read.ts` (a hand library, `ts/eff/README.md:37`); API forms of `ts/eff/eff.gen.ts:42,66,393-399` |
| `ts/eff/check-semantics.ts` | decode a given report file with excess keys refused; print the refusal's path and reason; exit 1 on refusal | `ts/eff/check.ts:1-10,87` (a `bun run` checker with an exit code), `ts/eff/check-styles.ts` |
| `ts/eff/test/semantics.test.ts`, `ts/eff/test/semantics.fixture.json` | the decode controls of `probe/decode.mts` as pinned cases over a hand fixture (the probe's `slice.json` plus `command` and `inputs`); `bun test` in `ts/eff` runs them, so `check-ts-reader` does too (`Makefile:341`) | `ts/eff/test/read.test.ts` ("the pinned cases", `ts/eff/README.md:46`) |
| `scripts/check-semantics.py` | two fresh runs into a temporary directory, byte comparison, tsgo 7, bun, the controls driver | `scripts/check-host-protocol.py:27-49,59` |
| `generated/semantics.json`, `generated/semantics.md` | the committed projections | `generated/AGENTS.md:10-25` (admitted kinds: obligation ledgers, theorem and axiom receipt indexes, counterexample coverage; provenance fields; no timestamps) |
| `Makefile` (edit) | the group, the paths, the check, §7 | the `census` and `host-protocol` rules, `Makefile:167-184,469-475` |
| `docs/GENERATED.md` (edit) | one row in the groups table, §7 | `docs/GENERATED.md:82,84` |
| `ts/eff/README.md` (edit) | three rows in the file table | `ts/eff/README.md:35-46` |
| `src/Effect4/Laws/Program/Typed/Seq.lean` (edit) | the slice's two tags and the import | — |
| anchors (edit) | `src/Effect4/Laws.lean` after line 93 (`import Effect4.Laws.Auto.Obligations`): `import Effect4.Laws.Auto.Semantics`; `Test/All.lean` after line 151 (`import Test.Audit.Obligations`): `import Test.Audit.SemanticsCensus`; `Test/Audit/AxiomGate.lean` after line 116 (`` , `Effect4.Laws.Auto.AnswerGate ``): the new module with a two-line comment, §4.1 | the neighbouring lines |

Not touched: `lakefile.toml` (the `Tools` library globs `Tools.+` and `Drivers.+`,
`lakefile.toml:56-60`, so the new tool files build with `lake build Tools`), `docs/core/decisions.md`,
`Test/Counterexamples/REGISTER.md` (the coordinator adds row 030), `tools/Tools/ArchitectureRoles.lean`
(every new Lean file falls under a declared area: `tools/Tools`, `tools/Drivers`,
`src/Effect4/Laws/Auto` (`:80`), `Test/Audit` (`:124`); reading).

## 7. Wiring: the Makefile and `docs/GENERATED.md`

### 7.1 The group

After the `census` rule (`Makefile:183-184`), in its style:

```make
# The semantics report (docs/GENERATED.md, group `semantics`): the registry's concepts, claims
# and cuts joined with the loaded environment (ledger evidence through ProofGraph, theorems at
# the axiom ceiling, the `semantics` tags), the counterexample register and the decisions
# register. No commit or date in the bytes; the run's receipt is .lake/gen/semantics.receipt.
SEMANTICS_INPUTS := tools/Tools/Semantics.lean tools/Drivers/Semantics.lean tools/Tools/SemanticsRegistry.lean \
  src/Effect4/Laws/Auto/Semantics.lean Test/Counterexamples/REGISTER.md docs/core/decisions.md lean-toolchain
$(GEN)/semantics: $(SEMANTICS_INPUTS) $(LAWS) | build
	$(LAKE) build Drivers.Semantics
	$(LAKE) env lean -DwarningAsError=true -M6144 --run tools/Drivers/Semantics.lean generated
	@mkdir -p $(GEN) && { git rev-parse HEAD; git status --porcelain | wc -l; \
	  echo 'gate notAudited (Test/Audit/AxiomGate.lean; ceiling propext Quot.sound)'; } > $(GEN)/semantics.receipt && touch $@
```

`Makefile:190` becomes
`GEN_GROUPS := variances derived lcnf eff wire cas ts readme truth host-protocol schema-ts census semantics`.
The marker is not a link of the chain (no `$(GEN)/census` prerequisite): no upstream group's
output is an input, so a link would re-cut the report whenever the truth or host groups are
re-cut; lcnf is the documented precedent of a group in the order that is not a link
(`docs/GENERATED.md:35-41`). `HERMETIC_GROUPS` (`:187`) is unchanged: it lists the groups
`scripts/generate.py` regenerates, and this producer is a Lean driver outside it, as lcnf is
(`docs/GENERATED.md:80`). So
`check-gen` diffs the two files without re-cutting them, and `check-gen-full` (`make -B gen`,
`Makefile:291-294`) re-cuts them. The last line of `GENERATED_PATHS` (`Makefile:212`) gains
`generated/semantics.json generated/semantics.md`.

### 7.2 The check

`Makefile:270-271` gains `semantics` in `CHECKS`; `Makefile:276` gains `check-semantics` in
`check-full` (the tiers are `check` and `check-full`, `Makefile:275-276`; there is no `check-host`
target, so "the host tier" is `check-full`). After `$(CHK)/census` (`Makefile:473-475`):

```make
# The semantics report against two fresh runs, its schema under tsgo 7, its decode with excess
# keys refused, and the driver's refusal controls (docs/GENERATED.md, group `semantics`).
$(CHK)/semantics: $(SEMANTICS_INPUTS) generated/semantics.json generated/semantics.md \
    ts/eff/semantics.ts ts/eff/check-semantics.ts ts/eff/test/semantics.test.ts ts/eff/test/semantics.fixture.json \
    tools/Drivers/SemanticsControls.lean \
    scripts/check-semantics.py $(LAWS) | build ts/eff/node_modules
	$(PY) scripts/check-semantics.py
	@mkdir -p $(CHK) && touch $@
```

`scripts/check-semantics.py`, in the shape of `scripts/check-host-protocol.py`: `lake build
Drivers.Semantics Drivers.SemanticsControls`; run the producer twice into two temporary directories
and refuse unless the two outputs and the committed files are byte-identical (Codex condition
5); `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit -p ts/eff/tsconfig.json`
(the invocation of `Makefile:405` and `check-host-protocol.py:59`; never `tsc`); in `ts/eff`,
`bun run check-semantics.ts ../../generated/semantics.json` and `bun test test/semantics.test.ts`;
`lake env lean -M6144 --run tools/Drivers/SemanticsControls.lean`. It prints one `PASS check-semantics: …` line.

### 7.3 `docs/GENERATED.md`

One row after the `census` row (`docs/GENERATED.md:84`), in its columns:

```
| semantics | `tools/Drivers/Semantics.lean` over the library `tools/Tools/Semantics.lean` (`make gen-semantics`) | the registry `tools/Tools/SemanticsRegistry.lean` (concepts, claims, cuts, module defaults, roots), the roots loaded with `importModules`, the `semantics` tags (`Effect4.Laws.Auto.Semantics`), the ledger evidence through `ProofGraph` (`ProofRef.validate`, `ProofGraph.check`), the id and status columns of `Test/Counterexamples/REGISTER.md`, the row and `who` columns of `docs/core/decisions.md`, `lean-toolchain` | `generated/semantics.json`, `generated/semantics.md`; the schema `ts/eff/semantics.ts` | `make check-semantics` (two fresh runs byte-identical to the committed files; tsgo 7 over `ts/eff`; bun decodes the report with excess keys refused; the driver's refusal controls); `check-gen` diffs without re-cutting, `check-gen-full` re-cuts | reproduced (the bytes); tested (the decode and the controls); proved where a claim's status is `proved` |
```

## 8. The schema in `ts/eff/semantics.ts` and what `check-semantics.ts` checks

The probe copy is `seat-B/probe/semantics.mts` (158 lines); `ts/eff/semantics.ts` is that file
with the import `import { Schema } from "effect"` (as `ts/eff/eff.gen.ts:42`) and the two fields
§2.3 adds after the probe ran: `command: Text` and `inputs: Schema.Array(Text)` (untested; a plain
string and a string list). Design points, each from a finding:

- API forms as `ts/eff/eff.gen.ts` uses them: `Schema.TaggedUnion` for the status (`:66`),
  `Schema.Literals([…])` (Codex review §5: the variadic `Schema.Literal` accepts only its first
  literal), `Schema.NullOr` for nullable JSON (not `Schema.Option`, which wants a runtime Option,
  Codex review §5), `.check(Schema.makeFilter(…))` (`:393`). `Schema.NonNegativeInt`, which v2
  §5 uses, does not exist in the pinned `effect` (0 occurrences in
  `ts/eff/node_modules/effect/dist/Schema.d.ts`; reading), so a count is
  `Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))` (`Schema.d.ts:5901`).
- Referential integrity in the schema, one root filter: duplicate concept, claim and placement
  ids; a claim, cut or placement naming no concept; one goal counted by two claims; per-concept
  counts equal to the claims' tally. The driver refuses all of these first; the schema refuses
  them again at the boundary (Codex review §1: validate uniqueness and link targets before a map).
- Excess keys refused: `Schema.decodeUnknownSync(SemanticsReport, { onExcessProperty: "error" })`.
  The default is `"ignore"`, which strips unknown keys (`effect/dist/SchemaAST.d.ts:365,403`;
  reading), so without the option a wall-clock `timestamp` passes silently; the probe's control
  shows exactly that (tested).

**Probe (tested, `seat-B/probe/commands.json`):** tsgo 7.0.0-dev.20260629.1 type-checks
`semantics.mts` and `decode.mts` with ts/eff's strictness flags (`--strict
--exactOptionalPropertyTypes --noUncheckedIndexedAccess --verbatimModuleSyntax`, bundler
resolution, `--skipLibCheck`): exit 0, no output. One bun run of `decode.mts`
(`/Users/pooks/.local/share/mise/installs/bun/1.3.14/bin/bun`, which reports `--version` 1.4.2):
exit 0, 16 of 16 controls agree with their expectation: the slice instance accepted; 14 red
mutations refused, each with a path and a reason (wall-clock key, dangling concept, duplicate
claim id, proved without a witness, malformed nested name, unknown status tag, malformed register
id, a status word not in the register's vocabulary, counts that disagree with the claims, a
negative count, one goal under two claims, a placement outside `tagged`/`inherited`, a blank
absent reason, a malformed nested counterexample witness); and the default decoder accepting the
wall-clock key, the control that makes the option load-bearing. Bounded: one instance, one
schema version, the TS half only; nothing here runs the Lean driver.

## 9. The slice

One concept over two modules, one proved claim, one wanted goal, one absent claim, one retained
refutation (Codex review §8; R5 as corrected in §12).

### 9.1 The registry's value

```lean
def registry : Registry where
  roots := [`Effect4.Laws, `Test.Program.TypedProgBindRed]
  concepts := [
    { id := "residual-program-typing"
      title := "Residual program typing: TypedProg, the protocol-indexed judgment on residual programs"
      defaultModules := [`Effect4.Laws.Program.Typed.Residual, `Effect4.Laws.Program.Typed.Seq] }]
  claims := [
    { id := "seq-typed", concept := "residual-program-typing", role := .compatibility
      title := "The seqR compatibility lemma: the shape denoteR sequences with is typed"
      pointer := .witness `Effect4.Program.Typed.seq_typed },
    { id := "denote-typed", concept := "residual-program-typing", role := .fundamentalProperty
      title := "The denotation of a checked program is TypedProg at its certificate (M5)"
      pointer := .goal `Effect4.Program.Typed.M3bAssembly.denoteR_typed
      contestedBy := ["E4-TYPED-CE-020", "E4-TYPED-CE-021", "E4-TYPED-CE-022"] },
    { id := "bind-closed", concept := "residual-program-typing", role := .compatibility
      title := "TypedProg is closed under bind"
      pointer := .refutedBy "E4-TYPED-CE-030" `Test.Program.TypedProgBindRed.typedProg_not_bind_closed },
    { id := "on-failure-typed", concept := "residual-program-typing", role := .compatibility
      title := "The onFailure-shape compatibility lemma beside seq_typed"
      pointer := .absent "owed beside seq_typed under M5's ledger with the all and onExit shapes (decisions row 148); no declaration and no goal at 198dd533" }]
  cuts := [
    { concept := "residual-program-typing", decisionRow := 163
      excluded := "function values, function types and parameterized declarations: a continuation is a program, not a function value"
      reason := "the language cut, docs/core/language-cut.md section 1" },
    { concept := "residual-program-typing", decisionRow := 117
      excluded := "open root requirement rows: M5, M6c and M7 take the premise rootTy.requires = empty"
      reason := "rc.112 runs closed rows (Effect.ts:17494-17497, as the register row cites)" }]
```

Names, each checked tonight (reading): `seq_typed` is declared at
`src/Effect4/Laws/Program/Typed/Seq.lean:59` inside `namespace Effect4.Program.Typed` (`:34`),
module `Effect4.Laws.Program.Typed.Seq`; `denoteR_typed` at
`src/Effect4/Laws/Program/Typed/Assembly.lean:1637` inside `namespace M3bAssembly` (`:1634`)
within `Effect4.Program.Typed` (`:75`), statement `ProofGraph.Obligation (DenotesTyped root)`
(`DenotesTyped` at `:1075`), placeholder by `#proof_wanted` at `:1839`, scope checked by
`#typed_state_obligations … M3bAssembly ceiling 3` at `:1841`; `typedProg_not_bind_closed` at
`Test/Program/TypedProgBindRed.lean:32` inside `namespace Test.Program.TypedProgBindRed` (`:20`),
imported by `Test/All.lean:41`. No `TypedProg` compatibility lemma for the `onFailure`, `all` or
`onExit` shapes exists (grep over `src` and `Test`; the one `onExit_typed` hit,
`Laws/Codegen/Forms.lean:81`, is the codegen template's, unrelated).

The two tags: `@[semantics "residual-program-typing"]` on `close_typed` (`Seq.lean:40`) and
`seq_typed` (`Seq.lean:59`), with `import Effect4.Laws.Auto.Semantics` added to `Seq.lean`.
Every other eligible theorem of `Residual` (and none of `Seq`, both tagged) is `inherited`.

### 9.2 The expected report

`seat-B/probe/slice.json` is the instance the probe decoded (its `producer` string names
`tools/Tools/Semantics.lean`, written before the split into a library and a driver, §6; it lacks
`command` and `inputs`, added after the run). The emitted file differs from it otherwise only
where the environment speaks: each `statement` (`EMIT: …` there) is the printed type, each
`axioms` list is `collectAxioms`' sorted answer, and `unplacedCount`/`unplacedByModule` are the
measured census (the probe's `0` and `[]` are stand-ins). The placement list also gains the
`inherited` declarations of `Effect4.Laws.Program.Typed.Residual`, measured. Object keys come out
in the order Lean's `Json` renderer gives them (`Json.mkObj` builds a `Std.TreeMap`,
`Lean/Data/Json/Basic.lean:186,225-226`; the committed `harness/truth/session/tape.schema.json`
shows the renderer's order, descending; reading); no consumer depends on key order. Its content:

```
format "effect4-semantics-report", schemaVersion 1, command "make gen-semantics"
producer "GENERATED by tools/Drivers/Semantics.lean (make gen-semantics); do not edit"
inputs [tools/Tools/Semantics.lean, tools/Drivers/Semantics.lean, tools/Tools/SemanticsRegistry.lean,
        src/Effect4/Laws/Auto/Semantics.lean, Test/Counterexamples/REGISTER.md,
        docs/core/decisions.md, lean-toolchain]
provenance { toolchain "leanprover/lean4:v4.33.1", roots [Effect4.Laws, Test.Program.TypedProgBindRed],
             policy { gate "Test/Audit/AxiomGate.lean", ceiling [propext, Quot.sound] } }
concepts [ residual-program-typing, defaultModules [….Typed.Residual, ….Typed.Seq],
           counts { claims 4, proved 1, wanted 1, refuted 1, absent 1, assumed 0 } ]
claims
  seq-typed        proved  by theorem  witness Effect4.Program.Typed.seq_typed
                   (module Effect4.Laws.Program.Typed.Seq, levels [], statement EMIT, axioms EMIT,
                   withinSemanticAxiomCeiling true), goal null
  denote-typed     wanted  goal Effect4.Program.Typed.M3bAssembly.denoteR_typed
                   (module Effect4.Laws.Program.Typed.Assembly, statement EMIT: the extracted
                   proposition, ∀ root, DenotesTyped root, printed), placeholder ….denoteR_typed.wanted
                   contestedBy [E4-TYPED-CE-020 SEEDED, -021 SEEDED, -022 SEEDED], witnesses null
  bind-closed      refuted counterexample E4-TYPED-CE-030 (status word as the coordinator writes the
                   row), witness Test.Program.TypedProgBindRed.typedProg_not_bind_closed
                   (module Test.Program.TypedProgBindRed, statement EMIT, axioms EMIT, ceiling true)
  on-failure-typed absent  reason "owed beside seq_typed … (decisions row 148) …"
cuts [ 163 who "owner" …, 117 who "owner" … ]
placement { universe "theorems of loaded modules under Effect4.Laws, roots [...], isNoise names,
            ledger goals and their .checked witnesses excluded",
            declarations [close_typed tagged, seq_typed tagged, <Residual's theorems> inherited],
            unplacedCount EMIT, unplacedByModule EMIT }
```

`withinSemanticAxiomCeiling true` for the three witnesses is **assumed**: the axiom gate holds
every `Effect4.*` and `Test.*` declaration to `[propext, Quot.sound]` (`AxiomGate.lean:66-67,
454-469`), and `TypedProgBindRed.lean:153` prints the axioms of the refutation; the driver
measures it.

### 9.3 The rendered table (`generated/semantics.md`)

Header `<!-- GENERATED by tools/Drivers/Semantics.lean (make gen-semantics); do not edit -->`;
per concept one table `claim | role | status | evidence | at the ceiling | contested by`, then the
cuts (`row | who | excluded`), then the placement counts (`tagged`, `inherited (provisional)`,
`unplaced`); statements below the table as a list (a printed statement has line breaks). Prose
about the language stays in `docs/core/semantics.md`, which the coordinator owns (Codex
condition 6).

## 10. The gate: Codex's six acceptance conditions, verbatim, and the check for each

Quoted from `/private/tmp/codex-second-eyes-2026-10-01/domain-spec-review/review.md:106-111`.

1. "Every proved badge resolves to validated evidence for the specific proposition, while a
   wanted/absent/refuted claim stays visibly distinct."
   — `proved` only through `ProofRef.validate` or `ProofGraph.check` (§3), never by name
   existence (the map's `.checked` existence test, `Architecture.lean:191`, is not used: Codex
   ledger review §1); the status is a tagged union, one tag per state (schema, §8). Checked by
   the controls driver (a `.checked` that fails validation refuses) and the decode controls.
2. "A stale theorem ID, missing module, malformed nested entity, duplicate ID, dangling link or
   failed producer is rejected with a location and reason."
   — Lean side: `tools/Drivers/SemanticsControls.lean`, one mutation each (stale witness name;
   a root or default module not loaded; duplicate claim, concept and default-module ids; a claim,
   cut and tag naming no concept; a register id the register lacks; a `RETIRED` id; a decisions
   row the register lacks; a goal with both or neither ledger markers); a refusing run writes
   nothing and exits 1. TS side: the decode controls (tested in the probe, §8).
3. "An inherited category is visibly provisional and a multi-topic theorem is not double-counted
   as two discharged goals."
   — `placement: "inherited"` in the report and "inherited (provisional)" in the table; one goal
   under two claims refuses (driver and schema; the schema half tested, §8).
4. "Approved harmless annotations preserve the chosen decoding behavior; unknown annotations remain
   refused. No global erasure-policy change is needed merely to render metadata."
   — No annotation key is added; `src/Effect4/Schema/Bridge.lean` is not in the slice's diff
   (`erasedKeys`, `:105-108`, stays the nine keys). Checked by the diff's file list.
5. "The same pinned input yields identical output bytes. Omit wall-clock time from the committed
   content, or derive an explicitly reproducible timestamp and keep run time in a separate receipt.
   Include schema version, source pin, roots, toolchain and policy identity."
   — Two fresh runs byte-identical to each other and to the committed files
   (`scripts/check-semantics.py`); no timestamp key (the schema refuses one, tested); `schemaVersion`,
   `provenance.{toolchain, roots, policy}`, `inputs`, `command` in the bytes; the commit and run
   in `.lake/gen/semantics.receipt` (§7.1), not committed. "Source pin" is met by `inputs` plus the
   receipt's commit, not by a commit in the bytes (§2.3).
6. "Handwritten prose remains in owned regions; generated tables are projections. Reuse the
   existing ledger, source-closure check, trust gate and generator registry.
   `generated/semantics.json` is a reproducible report, not a competing authority for decisions
   or completion."
   — The tables are a whole generated file (`generated/semantics.md`), no prose; the ledger is
   reused through `ProofGraph` (§3); the trust gate is named, not re-implemented (the report's
   ceiling Boolean is not the gate's verdict, §3); the group is registered in `GEN_GROUPS` and
   `docs/GENERATED.md` (§7); the report reads the registers and writes none.

## 11. Landing order: commits by explicit paths, each after its narrow build

One `lake` at a time. Base `198dd533`, branch `gemini/semantics-slice`.

| Commit | Paths | Narrow build and run, with the expected result |
| --- | --- | --- |
| C1 the attribute and its census | `src/Effect4/Laws/Auto/Semantics.lean`, `Test/Audit/SemanticsCensus.lean`, `src/Effect4/Laws.lean` (anchor §6), `Test/All.lean` (anchor §6), `Test/Audit/AxiomGate.lean` (anchor §6) | `lake build Effect4.Laws.Auto.Semantics`; `lake env lean -DwarningAsError=true Test/Audit/SemanticsCensus.lean` (as `Makefile:310` runs a test file; exit 0: the `#guard_msgs` blocks match, the red controls error as written) |
| C2 the registry, the library, the two drivers | `tools/Tools/SemanticsRegistry.lean`, `tools/Tools/Semantics.lean`, `tools/Drivers/Semantics.lean`, `tools/Drivers/SemanticsControls.lean` | `lake build Tools.SemanticsRegistry Tools.Semantics Drivers.Semantics Drivers.SemanticsControls`; `lake env lean -M6144 --run tools/Drivers/SemanticsControls.lean` (exit 0: every mutation refused with its expected location; the extension read from an imported fixture module, §4.1) |
| C3 the slice's tags | `src/Effect4/Laws/Program/Typed/Seq.lean` | `lake build Effect4.Laws.Program.Typed.Seq` and its direct dependents (`Effect4.Laws.Program.Typed.Adequacy`, `Effect4.Laws.Program.Typed.Commands.Bookkeeping`, `Test.Program.TypedProgBindRed`, `Test.Program.ProtocolPosts`, `Test.Counterexamples.Machine.Semantics.ScopePresence`, `Test.Counterexamples.Machine.Semantics.AwaitLoad`; grep of `import Effect4.Laws.Program.Typed.Seq`; the root `Effect4.Laws` is built at C4) |
| C4 the outputs (after the coordinator adds row 030) | `generated/semantics.json`, `generated/semantics.md` | `lake build Effect4.Laws Test.Program.TypedProgBindRed Drivers.Semantics`; `lake env lean -DwarningAsError=true -M6144 --run tools/Drivers/Semantics.lean generated` (exit 0; before the row exists: exit 1 naming `bind-closed` and `E4-TYPED-CE-030`, which is the expected red) |
| C5 the schema, the check, the wiring | `ts/eff/semantics.ts`, `ts/eff/check-semantics.ts`, `ts/eff/test/semantics.test.ts`, `ts/eff/test/semantics.fixture.json`, `ts/eff/README.md`, `scripts/check-semantics.py`, `Makefile`, `docs/GENERATED.md` | `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit -p ts/eff/tsconfig.json` (exit 0); `cd ts/eff && bun test test/semantics.test.ts` (every control agrees); after C4: `cd ts/eff && bun run check-semantics.ts ../../generated/semantics.json` (exit 0) and `python3 scripts/check-semantics.py` (one `PASS` line; `make check-semantics` order-only depends on `build`, the whole tree, as `gen-architecture` does, `Makefile:380`, so it runs at the owner's sweep) |

C1, C2, C3 and C5 do not depend on the register row and land in that order; C4 depends on it and lands last. The whole battery, the trust gate
(`lake build Test`) and `make check`/`check-full` run when the owner asks for a sweep, not per
commit (AGENTS.md, Working); the AxiomGate entry of C1 stays **assumed** until then.

## 12. The coordinator's rulings, confirmed or refuted

- **R1 confirmed.** A Lean registry beats `tools/architecture/chapters.json`: the driver already
  loads Lean, so the registry needs no second parser and no schema of its own (a JSON registry
  would need a reader in Lean and a shape check, and §7c's "one source" would then sit beside a
  hand JSON file); `lake build Tools` checks its fields and types; names are `Name` values checked
  against the loaded environment at run time; it is the second hand input beside
  `ArchitectureRoles.lean`, which is already a Lean file for the same reasons. Refinement: the
  registry authors no fact another file owns (no register status, no decision owner, no
  statement, no count; §2).
- **R2 confirmed, with three refinements:** `wanted` is validated by `ProofGraph.check`
  (placeholder type, universes and axioms), not by existence; a `RETIRED` register row cannot
  refute; `contestedBy` keeps open register rows against a claim visible beside its status (§0.2).
- **R3 confirmed except the commit:** the report, the flat schema (`ts/eff/semantics.ts`, after
  `read.ts`; the checker `check-semantics.ts`, after `check.ts`) and `check-semantics` in
  `check-full`. Refuted: "provenance = git commit" in the committed bytes (§2.3); the report
  carries `inputs`, `command`, `schemaVersion`, toolchain, roots and policy, and the commit goes
  to the run's receipt. Probe: tsgo exit 0, bun 16/16 (§8).
- **R4 confirmed, with refinements:** `@[semantics "<id>"]` with a non-reserved keyword, one
  string, one concept per declaration, current module only (Lean refuses imported declarations);
  module defaults shown `inherited`; `#semantics_census` prints the environment half only (tags,
  untagged theorems), because the claims live tool-side and Laws cannot import them; the driver
  imports the attribute module (assumed to load the tags, tested in C2); the module joins the
  gate's implementation list (assumed until the gate runs).
- **R5 confirmed in its names, refuted in two details:** the next free TYPED id is 030 (023 is
  earmarked by decisions row 176); and the absent item should not be `typedProg_bind_closed`,
  which is the same statement as the refuted item (one statement as two claims): the absent slot
  is the `onFailure`-shape compatibility lemma owed by decisions row 148. The wanted item carries
  `contestedBy` CE-020/021/022.
- **R6 confirmed, refined:** `who` is read from the decisions register; the cut rows are 163,
  128, 138 (ruled) and 117 (open); the planned type constructors are claims, not cuts.
