# Brief for Codex: the metaprogramming surface audited against Lean's own layers (2026-10-01)

Repository `/Users/pooks/Dev/lean4-effect4`, base `198dd533` on `refactor/phase1-phase3` (the
coordinator names a later base in the dispatch message if one has landed). Own branch
`codex/metaprogramming`, own worktree (`~/Dev/lean4-effect4-codex-meta`; a worktree never copies
`docs/research`, so read this folder and the vendored book at the absolute paths below).

## Why (the owner, 2026-10-01 ~22:00)

The formalization pass is writing a language description in which "syntax", "elaborate" and
"print/read" are our words for our objects. Where the tree uses Lean's own layers (`Syntax`,
`MacroM`, `TermElabM`, `CommandElabM`, `MetaM`, `Expr`, the delaborator and formatter), the use
should be idiomatic (built-ins over hand-rolled), organized (one home, not nineteen), and the
docs' words consistent with Lean's: when a document says a thing is syntax, or that a function
elaborates or prints, the reader must know which layer is meant, Lean's or ours. This is
concrete coding work landed in concert with a documentation section the semantics spec takes.

## Rules

- `AGENTS.md` in full (vocabulary, trust, working rules): no `sorry`/`partial`/`unsafe`/
  `native_decide`/`axiom`/`extern`/`implemented_by`; every warning an error; no `first | …`,
  `try`, `simp_all` written by hand in a new or touched proof; `#guard_msgs` for every fixture;
  the gate holds every declaration to `[propext, Quot.sound]`.
- Design first, land in slices: the audit note first (read only), then slices by explicit paths,
  each after a narrow build of the modules it touches and `lake env lean <file>` for each touched
  test. One `lake` at a time in your worktree. `git add` names files; the root imports
  (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) and `Test/Audit/AxiomGate.lean`
  are edited only at an anchor the coordinator names; `docs/core/decisions.md` never (propose
  rows in the receipt).
- The owner's standing rule: use the real APIs, look at them. Every built-in you adopt is cited
  from the toolchain's source, `file:line` under
  `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean/` (`Lean/PrettyPrinter/`,
  `Lean/PrettyPrinter/Delaborator/{Basic,Builtins,Attributes}.lean`, `Lean/Elab/`, `Lean/Meta/`,
  `Lean/Parser/`, `Lean/ToExpr.lean`, `Lean/Attributes.lean`, `Lean/Environment.lean`,
  `Init/Tactics.lean`, `Init/Meta.lean`). The book is the map; the toolchain is the authority.
- Evidence words on every claim: proved, tested, reading, assumed. Plain words.

## Sources, vendored

`docs/research/2026-10-01-metaprogramming-audit/sources/`: the Lean 4 metaprogramming book's
chapter sources (Apache-2.0, `book-LICENSE`), repository `leanprover-community/lean4-metaprogramming-book`
at commit `f47f6042ce10d451ec639e30e004407371ddbec2` (2026-09-28), `SHA256SUMS` beside them:
`lean-main-03_expressions.lean` (Expr), `04_metam.lean` (MetaM), `05_syntax.lean`,
`06_macros.lean`, `07_elaboration.lean`, `08_dsls.lean`, `09_tactics.lean`, `10_cheat-sheet.lean`,
`lean-extra-01_options.lean`, `lean-extra-03_pretty-printing.lean` (the chapter the owner named,
rendered at `https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html`).
`lean-extra-02_attributes.lean` is empty upstream: for attributes and environment extensions the
toolchain source and the tree's aesop rule-set registration (`src/Effect4/Laws/Auto/RuleSets.lean`)
are the references.

## The surface as measured (coordinator, grep over `src tools Test harness`, `*.lean`, 2026-10-01)

| Construct | Files | Occurrences | Where |
| --- | --- | --- | --- |
| `syntax` declarations | 18 | 34 | `Laws/Auto/*` (commands), `Laws/Machine/{Handles,Approximation,Scheduling}.lean` (tactics), `Laws/Program/Typed/{PositionGate,TypedStateDecl}.lean`, `Program/FoldOf.lean`, `tools/Conform/Spec/Reflect.lean`, `Test/Audit/RuntimeCoverage.lean` |
| `@[command_elab]` | 11 | 19 | the same command files; plus `elab "#…" : command` ×2 in `Test/Audit/AxiomGate.lean:376,515` |
| `elab … : term` | 1 | 1 | `tools/ProofGraph/Proof.lean:70` (`checked_theorem%`) |
| `macro` / `macro_rules` | 3 / 4 | 8 / 10 | tactic macros: `Laws/Machine/Approximation.lean:297-598`, `Scheduling.lean:42-116`, `Laws/Program/Authoring/Tactic.lean:49`; `Program/Authoring/Sugar.lean` |
| `@[delab]`, `@[app_unexpander]`, `Delaborator`, `DelabM` | 0 | 0 | none anywhere |
| `PrettyPrinter` | 2 | 2 | comments only (`OCaml5/Lcnf/Dump.lean:12`, `tools/Conform/Lcnf/Validity.lean:368`) |
| `ppExpr` | 9 | 17 | messages in `Program/FoldOf.lean` (8), `Laws/Auto/Positions.lean:99`; generated text as `toString (← ppExpr e)` in `tools/Effect4Gen/{Rows,LayerView,View,Fold,Authoring}.lean`, `tools/Conform/Layout/Reflect.lean:121`, `OCaml5/Lcnf/Types.lean:290` |
| `MetaM` / `TermElabM` / `CommandElabM` / `MacroM` | 33 / 18 / 2 / 1 | 158 / 63 / 6 / 1 | |
| `Expr` / `Syntax` / `TSyntax` | 60 / 43 / 2 | 721 / 82 / 19 | `TSyntax` only in `TypedStateDecl.lean`, `Sugar.lean` |
| `Lean.Parser.*` by hand | 3 | 20 | `Handles.lean:1114-1184` (the simp-argument grammar re-listed five times), `TypedStateDecl.lean:305-541` (quoted `structSimpleBinder`, `matchAltExpr`), `Sugar.lean:96-108` (`getKind` string compares on `doSeq`) |
| environment walks (`env.constants.toList` / `map₁.fold`) | 10 | 12 | `Laws/Auto/{Census:78, Obligations:55,113, Traversals:176, Exhaustive:156,180}`, `tools/Tools/Architecture.lean:180`, `tools/Effect4Gen/Check.lean:190`, `tools/Conform/Lcnf/Cases.lean:333`, `Test/Audit/AxiomGate.lean:424,518`, `Test/Program/LayerSharingContract.lean:203` |
| `collectAxioms` | 5 | 8 | the ceiling filter `[propext, Quot.sound]` written three times (`tools/ProofGraph/{Ledger:54, Proof:26, Search:116}`), the gate's policy (`AxiomGate.lean:455-521`), a test's own check (`LayerSharingContract.lean:206`) |
| hand quotation of `Level`/`Expr` into `Expr` | 1 | ~40 lines | `tools/ProofGraph/Proof.lean:30-75` (`quoteLevel`, `quoteClosed`) |
| registered attributes / env extensions | 0 | 0 | none; the semantics registry (seat B's spec) will add the first |
| `#guard_msgs` | 49 | 192 | the fixture idiom, keep |
| `importModules` / `withImportModules` | 23 | 26 | drivers and gates |

The authorities' words (grep over `AGENTS.md`, `README.md`, `docs/ARCHITECTURE.md`,
`docs/DESIGN-BASIS.md`, `docs/core/*.md`): **syntax** means our object language (`Eff` "first-order
program syntax", `Ty`, `Term`, `Store.Val`, `Representation`; "target syntax" `TypeScript.Expr`,
`Ml.Syntax`; "Schema syntax"), never Lean `Syntax`, and no document says so. **Elaborate** has
three senses: Lean's (`docs/ARCHITECTURE.md:96,101`; `docs/DESIGN-BASIS.md:784-801`, the rule
that raw `Expr`, syntax trees, metavariables and elaborator state never enter semantic data);
the authoring surface's `elaborate`/`elaborateModule` (`Authoring.lean:306`; K4 "total by
refusal", `docs/core/coherence-principle.md:110,127`; `docs/core/system-map.md:86,182`); and
`denoteR` as "elaboration of scoped syntax into first-order effects" in the hefty-algebra sense
(`docs/core/system-map.md:284`, `docs/DESIGN-BASIS.md:572-580`). **Delaborate** appears nowhere;
our words for that direction are print, render, reader, printer (Rendel–Ostermann). The one
"pretty-prints" is a negative (`TypedStateDecl.lean:7`).

## Audit questions

- **A1 Layer fit, per site.** For every row above: the Lean layer used, the layer the job needs
  (a `macro` for a syntax rearrangement; an `elab` only when the environment or types are
  inspected; `syntax` + `@[command_elab]` pairs versus `elab` sugar: pick one house style and
  say why), typed `TSyntax` categories versus raw `Syntax.getKind` string compares
  (`Sugar.lean:96-108`), `m!`/`MessageData` versus string concatenation in errors.
- **A2 Hand-copied grammar.** `Handles.lean:1114-1184` re-lists the simp-argument alternatives
  five times. Find the built-in category in `Init/Tactics.lean` (the `simpArgs` family) and
  reuse it once.
- **A3 Tactic macros that expand to `first | …`.** `Approximation.lean:386,440,560,598`,
  `Scheduling.lean:116`. `AGENTS.md` bans `first` and `try` written in a proof because a silent
  fallback hides a missing lemma; a macro that hides `first` is either a named instrument
  (registered like a bank, decisions row 65's pattern, with a fixture showing what it closes) or
  a loophole. List each macro, its arms, where it is called, and which arm fires where
  (instrument, do not guess). Propose per macro: keep as a named instrument, replace by a rule
  set and an aesop call, or inline. The coordinator rules; land nothing here before the ruling.
- **A4 One helper module for the environment.** Twelve walks and eight axiom checks, each with
  its own filter. Propose `declsUnder (scope : Name)`, `theoremsOfModule`, `withinCeiling`
  (the `[propext, Quot.sound]` filter once), one `isNoise` (today `Architecture.lean:163` and the
  censuses each have their own), a `readGoal` shared by the ledger and the semantics census
  (`Obligations.lean:15-24`). Say which root the module belongs to (`Laws/Auto/`, or a tool
  root), given that `Effect4` never imports the Laws graph and the gate audits every module.
  The gate's policy stays the gate's; it may share the walk.
- **A5 Printing.** (a) Generated text produced by `toString (← ppExpr e)` (`tools/Effect4Gen`,
  `Conform`, `OCaml5/Lcnf/Types.lean:290`): what fixes the bytes (options `pp.*`, universe names,
  open namespaces, `pp.explicit`)? Read `Lean/PrettyPrinter/` and the book's options and
  pretty-printing chapters; if the generated bytes depend on defaults, say which and pin them
  explicitly (`withOptions`), or replace `ppExpr` text with a fold over our own data where the
  generator already has it. (b) No delaborator or unexpander exists for `Eff`, `Ty`, `Term` or
  `Val`; goals and `#guard_msgs` fixtures show raw constructors. Propose whether unexpanders for
  the authoring surface's shapes would help, with one before/after from an existing fixture and
  the count of fixtures whose expected output would change. Propose only; the diff would touch
  the battery.
- **A6 Hand quotation.** `tools/ProofGraph/Proof.lean:30-75` quotes `Level` and `Expr` into
  `Expr` by hand. Check `Lean/ToExpr.lean` in the toolchain for `ToExpr Level`/`ToExpr Expr`;
  if present, replace; if absent, say so and whether `deriving ToExpr` exists in core.
- **A7 Where metaprograms live.** `Program/FoldOf.lean` (903 lines, the `fold_of` command) and
  `Program/Authoring/Sugar.lean` are in the runtime root `Effect4`; `docs/ARCHITECTURE.md:101`
  says the law graph's command elaborators live in `Laws/Auto`. Measure which `Effect4` modules
  import `Lean.Elab`/`Lean.Meta` (appendix below) and propose one home for metaprograms with the
  dependency direction stated, or a reason the split is right.
- **A8 The glossary.** A table: our word → Lean's layer → our type → where used → consistent or
  not. At least: syntax (object language vs Lean `Syntax`), elaborate (the three senses, with a
  proposed distinct word for each where the docs blur them), print/render/read (exact
  embeddings) vs delaborate/format, lift and sugar (the authoring macros), census and gate
  (commands). Propose the wording for `docs/core/semantics.md`'s glossary and an amendment to
  `AGENTS.md`'s vocabulary bullets; the coordinator lands them.

## Produce

1. `docs/research/2026-10-01-metaprogramming-audit/audit.md`, first and read-only (about two
   hours): the per-site table (A1), findings A2–A8 with file:line and the toolchain citation for
   every built-in, and proposals P1…Pn, each with: files, the built-in, what changes for callers,
   which fixtures' expected output changes (count), build cost, risk, and whether it needs a
   ruling (A3, A5b, A7) or not.
2. Then the slices that need no ruling and change no statement and no fixture output: the
   helper module and its callers (A4), the simp-argument grammar (A2), typed syntax in
   `Sugar.lean` (A1), the quotation (A6) if the instance exists, pinned printing options (A5a) if
   bytes were unpinned. Each slice its own commit by explicit paths with the narrow build named
   in the message; regenerate (`python3 scripts/generate.py --only <family>`) when a generator is
   touched and commit byte-identical output or the diff with its reason.
3. A documentation section for the semantics spec (`audit.md` §"For the spec"): the glossary
   (A8) and "the metaprogramming surface" (every command and tactic macro, its layer, its module,
   its fixture), written so a census command could print it later (measured, never drawn: the
   owner's rule for tracking artifacts).
4. The receipt (`AGENTS.md` format): first the one thing the coordinator must know before
   merging; base and head; files; exact commands and results; `#print axioms` output for any
   touched theorem; open obligations; bounded or host-only evidence; proposed decisions rows.

Stop at coherent places: the audit note is a deliverable on its own; the first slice with its
build is a second.

## Appendix: `Effect4` root modules importing Lean elaboration or meta APIs (measured at dispatch, 2026-10-01)

```
src/Effect4/Program/FoldOf.lean
```

And in the Laws graph:

```
src/Effect4/Laws/Auto/AnswerGate.lean
src/Effect4/Laws/Auto/Positions.lean
src/Effect4/Laws/Program/Authoring/Tactic.lean
src/Effect4/Laws/Program/Typed/TypedSources.lean
```

(Direct `import Lean…` lines only. The command elaborators of `Laws/Auto/Census.lean`, `Obligations.lean` and the rest reach `Lean.Elab` through `Aesop` and `ProofGraph`; the full import closure of each metaprogram is yours to measure in A7.)

## Addendum (coordinator, 2026-10-01 ~22:30): DI-18 and the parallel slice

- **DI-18 is contradicted at HEAD.** `docs/DESIGN-ISSUES.md:91` rules (2026-09-09, S0) "no
  `import Lean` in the audited closure", enforced by `scripts/check-library-roots.sh`. That
  script no longer exists (`ls scripts/check-library-roots.sh`: no such file; `make check-roots`
  is a different check), and five audited modules import Lean directly today:
  `src/Effect4/Program/FoldOf.lean` (the runtime root) and, in the Laws graph,
  `Laws/Auto/AnswerGate.lean`, `Laws/Auto/Positions.lean`, `Laws/Program/Authoring/Tactic.lean`,
  `Laws/Program/Typed/TypedSources.lean` (seat B's reading, confirmed by the appendix above). A7
  therefore ends in one of two proposals for the owner's ruling, written as a DI-18 amendment:
  (a) instrument modules of the Laws graph may import Lean's elaboration APIs, the gate audits
  them like any other module, and the runtime root never does (then `FoldOf.lean` moves); or (b)
  the ruling stands and every metaprogram moves to a tool root that emits ordinary declarations.
  Measure what each costs before proposing.
- **Gemini lands the semantics report's first slice in parallel** (its brief:
  `docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md`). It owns
  `src/Effect4/Laws/Auto/Semantics.lean` (the first registered attribute and census of the tree),
  `tools/Tools/Semantics*.lean`, `tools/Drivers/Semantics*.lean`, `ts/eff/semantics.ts`,
  `ts/eff/check-semantics.ts`, their tests, `scripts/check-semantics.py`, and the Makefile and
  `docs/GENERATED.md` lines of its spec §7. Touch none of those; your audit note (read-only) runs
  beside it, and your A4 helper module lands first among your slices so Gemini's census can be
  moved onto it afterwards. The attribute pattern Gemini uses (a parametric attribute with an
  `initialize`, one `auditImplementationModules` entry) is the one to review in A1.

## Addendum 2 (coordinator, 2026-10-01 ~22:55): DI-18 is ruled; the base

The owner re-ruled DI-18 before dispatch (`docs/DESIGN-ISSUES.md`, row DI-18; `docs/ARCHITECTURE.md`,
the roots paragraph; commit `8c9be258`): the `import Lean` ban is dropped. The risk it guarded, a
Lean meta object entering the runtime representation by accident, is owned by the representation
rules (`AGENTS.md`; `docs/DESIGN-BASIS.md` DB-08) and the separation gates, not by an import list.
A7 therefore no longer ends in a choice between (a) and (b). It ends in two measured proposals:
where `Program/FoldOf.lean` belongs (the runtime root's one metaprogram), and whether a check
should replace the former ban (no declaration of the runtime root `Effect4` mentions `Lean.Expr`,
`Lean.Syntax` or an elaborator monad in its signature), with the cost of each. Base your branch
on `8c9be258` (it holds this ruling, register row `E4-TYPED-CE-030` and tonight's notes).
