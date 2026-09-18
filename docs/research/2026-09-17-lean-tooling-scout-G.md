# Scout G — third-party Lean 4 tooling for the coherence refactor (2026-09-17)

Brief: `docs/research/2026-09-17-scout-brief-G-lean-tooling.md`. Eight needs, one table each, then the
five adoptions ranked. Repositories are cited by URL, files by path. Behaviour claims come from
reading the named source file; compatibility claims come from reading the candidate's
`lean-toolchain` and its tag list.

## Method, and the one compatibility fact that governs everything

The estate is on `leanprover/lean4:v4.33.1` (`lean-toolchain`). The ecosystem's head has moved on:
mathlib4, batteries, aesop, doc-gen4, verso, lean4export, plausible, quote4, import-graph,
LeanSearchClient, repl and lean4-cli all carry `leanprover/lean4:v4.35.0-rc2` on their default branch
as of 2026-09-18 UTC. **That is not a blocker**: every one of those keeps a `v4.33.0` (doc-gen4: also
`v4.33.1`) release tag, and the estate pins revisions anyway (`lakefile.toml` pins aesop at
`3448c0b` = tag `v4.33.0`, batteries at `4488d40` = tag `v4.33.0`). The tools that *are* blocked are
the ones with no 4.33 tag and a stale toolchain: QpfTypes (v4.25.0), loogle (v4.30.0-rc1), alloy
(v4.21.0), CanonicalLean (v4.34.0, tags jump v4.32.0-rc1 → v4.34.0), Paperproof (v4.29.0-rc8).

Two things the brief listed as third-party turn out to be **in the toolchain the estate already
runs**, which changes the ranking: the environment-linter framework plus `lake lint`, and
`leanchecker`. Both are verified below by running them.

Probes live in
`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/3add7740-cd10-45f4-b704-4e58cf67e01a/scratchpad/lean-tooling/`
(`probe/` is a v4.33.1 package with no dependencies; `src/` holds fetched sources). Nothing was built
in the checkout.

## 1. Environment census and linting

Today: `#traversal_census` (`src/Effect4/Laws/Auto/Traversals.lean`, 223 lines) hand-rolls the walk
(`definitionsUnder`, `moduleOf`, its own sequential loop); the gate is
`Test/Audit/TraversalCensus.lean` (18 lines) and `#effect4_axiom_gate`
(`Test/Audit/AxiomGate.lean`, 714 lines, on `Lean.Util.CollectAxioms`).

| Tool | Where | Last commit | 4.33 | What it actually does (source read) | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| Batteries `#lint` | `.lake/packages/batteries/Batteries/Tactic/Lint/{Basic,Frontend,Misc,Simp,TypeClass}.lean` (1,106 lines) | vendored at v4.33.0 | yes, already in the tree | `Linter := { test : Name → MetaM (Option MessageData), noErrorsFound, errorsFound, isFast }`; `@[env_linter]` registers into a persistent env extension; `@[nolint name]` is a parametric attribute read by `shouldBeLinted`; `lintCore` runs every linter over every declaration **in parallel** (`EIO.asTask`); `formatLinterResults … (useErrorFormat := true)` prints `file:line:col: error:`; `#lint`, `#lint in Pkg`, `#lint only`, `#list_linters` | the census becomes a linter: `structural`/`wf` rows are its failures, the exemption list is data | zero new deps; one import in a `Effect4.Laws.Auto.*` module | **adopt** |
| Batteries `runLinter` exe | `.lake/packages/batteries/scripts/runLinter.lean` (~200 lines), declared `[[lean_exe]] name = "runLinter"` in its `lakefile.toml` | same | same | imports `#[module, Batteries.Tactic.Lint]` (it adds the lint module itself, so the linted module needs no batteries import), lints `getDeclsInPackage module.getRoot`, subtracts `scripts/nolints.json`, `--update` rewrites that file, `--no-build` refuses to build, exits 1 on failure | the CI entry point; `lake exe` resolves executables across the whole workspace (`Lake/Config/Workspace.lean:299`, `findLeanExe?` searches `self.packages`), so no copy is needed | zero | **adopt** |
| Core `Lean.Linter.EnvLinter` + `lake lint` | toolchain: `src/lean/Lean/Linter/EnvLinter/{Basic,Frontend}.lean`, `src/lean/Lake/Lake/CLI/BuiltinLint.lean` | ships in v4.33.1 | yes | same `EnvLinter` shape, driven by `lake lint --builtin-lint <mods>` with `--linters`/`--lint-only` specs and `--record-exceptions`, which **edits the sources**, inserting `set_option <linter> false in -- recorded by …` above each flagged declaration. Which linters run on a declaration is decided by a per-declaration *snapshot* written in `addDecl` (`src/lean/Lean/AddDecl.lean:39`) from `envLinterOptionsRef`, so the linter's option must be registered *before* the declaration is elaborated, i.e. the linter's module must be in the linted module's import closure. No core linter uses `builtin_env_linter` yet | the same census, with the exemption list written for you — but only for declarations in modules that may import Lean, which excludes `Effect4.*` core | zero | **try** (see the caveat) |
| `leanchecker` | toolchain `bin/leanchecker`; `leanprover/lean4checker` is **archived** (2026-03-25) and its README says it was merged into Lean and ships with every toolchain since v4.28.0 | ships in v4.33.1 | yes | replays a module's constants through the kernel from its imports' environment (`--fresh`: from nothing), catching environment hacking | a trust rung beside the axiom gate: the gate says *which* axioms, `leanchecker` says the kernel still accepts the declarations | zero | **adopt** |
| import-graph | https://github.com/leanprover-community/import-graph, tag `v4.33.0` | 2026-09-16 | yes | at that tag: `#min_imports`, `#find_home`, `lake exe graph` (dot/json/html), `lake exe unused_transitive_imports`, `ImportGraph/Imports/Redundant.lean`, `ImportGraph/Util/FindSorry.lean` (`allConstantsWithSorry`, `allModulesWithSorry`). `Shake` (the import shaker) exists only on `main` (v4.35), not at v4.33.0 | the estate's import-closure rules (core must not reach Laws/aesop; the LCNF cut) become checkable instead of asserted | one `[[require]]`, brings `leanprover/Cli` | **adopt** |
| Batteries census commands | `.lake/packages/batteries/Batteries/Tactic/{PrintPrefix,PrintDependents,PrintOpaques,ShowUnused,HelpCmd}.lean` | vendored | yes | `#print prefix Foo` (every declaration under a namespace, with a config for internals), `#print dependents X Y` (declarations in the file depending on X/Y — the inverse of `#print axioms`), `#print opaques X` (opaque/partial/axiom dependencies), `#show_unused`, `#help option/attr/cats/cat` | one-line answers to questions the estate currently answers with new metaprograms | zero | **adopt** |
| Mathlib linter framework | `Mathlib/Tactic/Linter/*` (33 files) | 2026-09-18, v4.35.0-rc2 | tag exists, but Mathlib as a dependency is out of the question | worth reading, not requiring: `MinImports.lean`, `UpstreamableDecl.lean`, `TextBased.lean` (text linters with a JSON exception file), `DirectoryDependency.lean` (which directories may import which — the estate's rule, as a linter) | source to copy | — | **skip as a dependency, read `DirectoryDependency.lean`** |
| LeanInk | https://github.com/leanprover/LeanInk | **archived**, 2024-07-18, toolchain v4.6.0-rc1 | no | — | — | — | **skip** |

Reproduced (probe `probe/Probe/Linter.lean` + `Probe/Decls.lean`): a package that is not core *can*
register a core environment linter at v4.33.1, and `--record-exceptions` works. The recipe is fussy
and undocumented — `public meta register_option linter.X`, `meta initialize addEnvLinterOption
linter.X`, `@[builtin_env_linter linter.X]` on a `public meta def … : EnvLinter`, and the option
module must be imported by whatever is linted. `lake lint --builtin-lint Probe` then printed the two
offending declarations and exited 1; `--record-exceptions` wrote two `set_option … false in` lines and
the next run exited 0.

## 2. Recursion schemes and generic programming over inductives

| Tool | Where | Last commit | 4.33 | What it actually does (source read) | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| Core deriving toolkit | toolchain `src/lean/Lean/Elab/Deriving/{Basic,Util}.lean` | ships | yes | `registerDerivingHandler`, and the reusable pieces a handler is built from: `mkContext`, `mkHeader`, `mkDiscrs`, `mkInductiveApp`, `mkImplicitBinders`, `mkInstImplicitBinders`, `mkInstanceCmds`, `mkLocalInstanceLetDecls`. Handlers shipped: BEq, DecEq, FromToJson, Hashable, Inhabited, LawfulBEq, Nonempty, Ord, ReflBEq, Repr, SizeOf, ToExpr, TypeName — **no `Functor`, no `Traversable`** | write `deriving EffAlgebra` for the estate's families instead of hand-writing `tools/Effect4Gen/Fold.lean`'s emission | zero | **adopt** |
| Mathlib `DeriveTraversable` | `Mathlib/Tactic/DeriveTraversable.lean` (510 lines) | 2026-09-18 | Mathlib only | derives `Functor`, `LawfulFunctor`, `Traversable`, `LawfulTraversable` for an inductive whose **last parameter** is the functor variable. `mapField` throws `"recursive types not supported"` on a field whose head is the type itself; recursion is handled by `withAuxDecl` + `addPreDefinitions`; the map is built with `mkCasesOnMatch` over the constructors; the lawful instances are proved by tactic scripts. No indices, no mutual families | not usable on `Eff` (an indexed, mutually-declared family), but it is the closest worked example in the ecosystem of "emit a structurally recursive function over an inductive's constructors, then prove its laws" | read, do not require | **skip as a dependency, read as the model** |
| QpfTypes | https://github.com/alexkeizer/QpfTypes | 2026-09-16, toolchain **v4.25.0**, no 4.3x tags | **no** | `data`/`codata` commands defining (co)inductives as fixpoints of quotients of polynomial functors, compositional over "live" parameters. Its own README: "intended as a proof-of-concept … not at all ready for serious use", "(co)recursive families of types or even mutually (co)inductive types are not supported yet", and recursion is only via `MvQPF.Fix.drec` | would require re-founding `Eff` on `data` and a port across eight toolchain releases | very high | **skip** |
| Mathlib QPF/`MvQPF` | `Mathlib/Data/QPF/**` | — | Mathlib only | the theory QpfTypes stands on | — | — | **skip** |
| A recursion-schemes library | — | — | — | **does not exist.** No Lean 4 package generates catamorphisms/algebras/`Functor` instances from an inductive declaration, third-party or otherwise (web search plus a GitHub repository search; the only hits are Haskell literature and Mathlib's `W`-types) | — | — | — |

The honest finding for this need: the estate's `cataFam`/`EffAlgebra` generator has no competitor to
adopt. What exists to reuse is the *deriving frontend* (core) so that the algebra and its fold are
produced by `deriving` rather than by a `--run` driver writing text.

## 3. Refactoring by metaprogram — converting 157 hand traversals

| Tool | Where | Last commit | 4.33 | What it actually does (source read) | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| Core functional induction | toolchain `src/lean/Lean/Meta/Tactic/FunInd.lean` (1,554 lines) | ships | yes | for a definition `f`, derives `f.induct` — an induction principle **shaped like `f`'s own recursion** — and `f.fun_cases`; the tactics are `fun_induction f` and `fun_cases f` | this is the conversion's proof engine: for each hand traversal, emit the algebra, state `f x = cata alg x`, prove by `fun_induction f` | zero | **adopt** |
| Mathlib `Translate` | `Mathlib/Tactic/Translate/{Core,Attributes,GuessName,Reorder,ToAdditive,ToDual}.lean` (Core alone 1,345 lines) | 2026-09-18 | Mathlib only | the engine under `@[to_additive]`/`@[to_dual]`: walks a declaration's value substituting constants by a name dictionary, re-elaborates, registers the copy, copies attributes/docstrings/simp sets, supports argument reordering and a "relevant argument" heuristic | the *pattern* for a declaration-to-declaration transport; the estate's conversion is not a renaming, so the engine itself does not apply | read | **skip as a dependency** |
| Mathlib `addRelatedDecl` | `Mathlib/Util/AddRelatedDecl.lean` (146 lines) | 2026-09-18 | Mathlib only | adds a derived declaration beside an existing one with `(attr := …)` propagation and a transparency sanity check; the plumbing under `@[simps]`, `@[reassoc]`, `@[elementwise]` | the shape of "emit the algebra and the agreement theorem beside the definition, inheriting its attributes" | read | **skip as a dependency, read as the model** |
| `lake lint --record-exceptions` | toolchain `Lake/CLI/BuiltinLint.lean` | ships | yes | rewrites source files in place, inserting a line above a flagged declaration (reproduced) | the only *in-tree source rewriter* in the toolchain; a precedent (and a warning) for a converter that edits `src/**` | zero | **try** |
| `leanprover-community/repl` | https://github.com/leanprover-community/repl, tag `v4.33.0` | 2026-09-16 | yes | line-oriented JSON REPL: send commands/tactics, get goals, sorries, environment ids back; pickling of environments | scripted bulk conversion from outside Lean (one environment, many attempts) — the estate drives Lean through `lake env lean --run` today | small | **try** |
| A Lean refactoring tool | — | — | — | **does not exist.** There is no `lean4-refactor`, no rename-across-project tool; the ecosystem's rename mechanism is `@[deprecated (since := "…")]` (core) plus Mathlib's `scripts/fix_deprecations.py` text pass | — | — | — |

Reproduced (probe `probe/Probe/FunInd.lean`): with `T` a two-constructor inductive, `cata` its fold
over an `Alg` record, and `sum` a hand traversal,

```lean
theorem sum_eq_cata (t : T) : sum t = cata sumAlg t := by
  fun_induction sum <;> simp [cata, sumAlg, *]
```

compiles, and `sum.induct : ∀ (motive : T → Prop), (∀ n, motive (T.leaf n)) → (∀ l r, motive l →
motive r → motive (l.node r)) → ∀ a, motive a` is derived on demand from the *definition*. The same
goal with `fun_induction sum <;> grind [cata, sumAlg]` failed — `grind` wants equation lemmas, `simp`
wants the definitions; take `simp`.

## 4. Derive handlers and codegen — writing Lean declarations from data

| Tool | Where | Last commit | 4.33 | What it actually does (source read) | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| Core command elaboration + pretty printer | toolchain `Lean/Elab/Command.lean`, `Lean/PrettyPrinter.lean` (`ppCategory`, `ppTerm:25`, `ppCommand:78`) | ships | yes | syntax quotations build commands; `ppCommand` turns a command's syntax into `Format`, i.e. into the text of a `.lean` file | `tools/Effect4Gen/*` builds its output with `String.intercalate` and `s!"…"` (`Driver.lean`); emitting *syntax* and printing it with `ppCommand` makes the generated file parse-correct by construction | zero | **adopt** |
| quote4 (Qq) | https://github.com/leanprover-community/quote4, tag `v4.33.0` | 2026-09-16 | yes | type-safe `Expr` quotations: `q(…)`, `~q(…)` matching, so a metaprogram builds terms whose types are checked as it writes them | the converter metaprogram of need 3 builds `Expr`s; Qq is how the ecosystem stops that being string-typed | one `[[require]]`, no transitive deps | **try** |
| Verso | https://github.com/leanprover/verso, tag `v4.33.0` | 2026-09-17 | yes | documentation authoring: genres, elaborated code blocks, module docs; it is a document DSL, not a code generator | need 8, not this one | large | **try** (need 8) |
| alloy | https://github.com/tydeu/lean4-alloy | 2025-07-13, toolchain v4.21.0 | **no** | C code embedded in Lean modules with `alloy c …` | the estate emits OCaml and TypeScript, not C | — | **skip** |
| `lean4-derive` | — | — | — | **does not exist** (no such package; deriving handlers live in core and in Mathlib) | — | — | — |

## 5. Extraction and lowering

Today: `src/OCaml5/Lcnf/Dump.lean` takes mono LCNF straight out of the imported environment
(`Lean.Compiler.LCNF.PhaseExt.getMonoDecl?`), which is the right door.

| Tool | Where | Last commit | 4.33 | What it actually does (source read) | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| `leanir` + `<Mod>.ir` | toolchain `bin/leanir`, `lib/lean/Init.ir` | ships | yes | usage `leanir <setup.json> <output.ir> <output.c> [--stat]`; the `.ir` file is an **olean-format artifact** (magic `olean`, version `4.33.1`) holding the module's post-LCNF compiler IR, and C emission is now a separate stage reading it | the seam *below* mono LCNF: nothing to reuse for TypeScript (mono still has types; IR does not), but it is where a post-RC/boxing consumer would attach — relevant if the OCaml engine ever wants allocation facts | zero | **note, not now** |
| lean4export | https://github.com/leanprover/lean4export, tag `v4.33.0` | 2026-09-16 | yes | `lake env lean4export Mod… [-- decls…] > out.ndjson` dumps kernel-level declarations in the NDJSON export format (`format_ndjson.md`), with `--export-unsafe`, `--export-mdata` | a boundary for an external consumer of the estate's *terms* (not its compiled code): e.g. shipping `Ty`/`Eff` declarations to a non-Lean checker | small | **try** |
| lean4lean | https://github.com/digama0/lean4lean, toolchain v4.33.0-rc2 | 2026-08-29 | close enough to try | the Lean kernel re-implemented in Lean, plus metatheory (`Lean4Lean.Theory`) and a verification of the implementation against it; CLI `lean4lean [--fresh] [--compare] [MOD]` run under `lake env` in the target project | a second opinion on the kernel for the trust story; `bugs-found.md`, `divergences.md` document what it has caught | one build of a mid-size package | **try** |
| Out-of-core LCNF consumers | GitHub code search for `Lean.Compiler.LCNF` outside `leanprover/lean4`: 143 hits, almost all vendored copies of the compiler (`dennj/solana-lean`) | — | — | Real consumers: `opencompl/veir` installs LCNF passes (`ExArray/.../InstallPasses.lean`, toolchain v4.35.0-rc1), and `import-graph`'s `ImportGraph/Shake/DeclNeeds.lean` (main only). `leanprover/nerodia` ("write Python modules in Lean", toolchain v4.33.0, pushed 2026-09-17) emits C and `.pyi` but **does not read LCNF** — its only mention of LCNF is a comment about copying `quoteString` | the estate's `OCaml5.Lcnf` has no peer to borrow from; `veir` is the one precedent for installing passes | — | **skip** |
| Lean → wasm / JS | `T-Brick/lean2wasm` (2024-03-17), `argumentcomputer/Wasm.lean` (2023, a wasm *interpreter* in Lean), `leanprover/lean4-wasm` (**gone**, 404) | — | no | nothing maintained; no Lean 4 JavaScript backend exists (repository search returns nothing) | the TypeScript lowering has nothing to reuse and must stay a lowering from the estate's own IR | — | **skip** |

## 6. Proof automation beyond aesop

The machine proofs in question (`src/Effect4/Laws/Program/Agreement/Machine.lean`) are structural
inductions over families with many constructors. That is the worst case for every first-order or
SMT-shaped prover below and the best case for `fun_induction` + aesop + `grind`.

| Tool | Where | Last commit | 4.33 | What it actually does | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| core `grind`, `bv_decide`, `decide +kernel`, `exact?`/`apply?` | toolchain `Lean/Meta/Tactic/Grind/**`, `Lean/Elab/Tactic/{LibrarySearch,Rewrites}.lean` | ships | yes | already the estate's toolkit (memory: `decide +kernel` for typing certificates); `exact?`/`apply?`/`rw?` are core, not Mathlib, since well before 4.33 | — | zero | **in use** |
| duper | https://github.com/leanprover-community/duper, tag `v4.33.0`, toolchain v4.34.0 on main | 2026-09-16 | yes, at the tag | proof-producing superposition prover for first-order goals ("broadly similar to Isabelle's Metis"); depends on batteries **at the same revision as yours** (its README warns about this) and on lean-auto | no inductive reasoning; would help only on the estate's occasional first-order side goals | one require, must match batteries rev | **try later** |
| lean-auto | https://github.com/leanprover-community/lean-auto, tag `v4.33.0` | 2026-09-16 | yes | goal translation to first-order/SMT plus a native prover interface; the front half of a hammer | same | — | **skip** |
| lean-smt | https://github.com/ufmg-smite/lean-smt, no tags, main's toolchain **v4.33.0** | 2026-09-16 | yes (by toolchain) | discharges goals to cvc5: uninterpreted functions and linear integer/real arithmetic with quantifiers; bitvectors experimental; reals need Mathlib (or the `no_mathlib` branch) | the estate's goals are not in those theories | cvc5 binary + possibly Mathlib | **skip** |
| LeanCopilot | https://github.com/lean-dojo/LeanCopilot, tag `v4.33.0` | 2026-09-15 | yes | neural tactic suggestion/premise selection through CTranslate2; needs `moreLinkArgs` for `-lctranslate2` and `lake exe LeanCopilot/download` to fetch models into `~/.cache/lean_copilot` | the suggester in this estate is the agent; a 2021-era tactic model adds nothing and costs a native dependency | high | **skip** |
| Canonical | tactic lives at https://github.com/chasenorman/CanonicalLean (toolchain v4.34.0; the `chasenorman/Canonical` repo is the Rust core) | 2026-09-18 | **no** (no v4.33 tag) | exhaustive term search in dependent type theory (type inhabitation) with a prebuilt Rust dynlib | would suit *constructing* small terms, e.g. filling a generated instance field; blocked on toolchain | — | **skip at 4.33** |
| lean-egg | https://github.com/marcusrossel/lean-egg | 2026-07-29 | — | the repository's own description now reads "A **deprecated** equality saturation tactic for Lean based on egg" | — | — | **skip (deprecated by its author)** |
| a hammer package | — | — | — | **does not exist** as a single package: `leanprover-community/hammer` is a 404; the stack is lean-auto + duper | — | — | — |

## 7. Testing

Today: 96 files under `Test/` use `#guard`, 13 use `#guard_msgs`; `tools/Conform/**` carries 20,387
hand-generated vectors.

| Tool | Where | Last commit | 4.33 | What it actually does | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| plausible | https://github.com/leanprover-community/plausible, tag `v4.33.0` | 2026-09-16 | yes | property testing integrated as a tactic: `plausible` on a goal searches for a counterexample, shrinks it and prints the assignment; `#eval Plausible.Testable.check <| ∀ …` at the command line. A user type needs `Repr`, `Plausible.Shrinkable` and `Plausible.SampleableExt`/`Arbitrary` | the red control the estate keeps asking for: before proving a law, look for its counterexample; and a generator-based replacement for slices of the vector corpus | one require; the real cost is writing `SampleableExt` for an indexed family like `Eff` | **adopt** |
| LSpec | https://github.com/argumentcomputer/LSpec (a.k.a. lurk-lab/LSpec), **`lean-toolchain` = v4.33.1**, no tags | 2026-09-15 | yes, exactly | `TestSeq` values composed with `test "name" prop`, run at elaboration by `#lspec` or in an executable by `lspecIO`; the executable can be tagged `@[test_driver]` so `lake test` runs it; has adapters for plausible (`checkPlausible'`) | a `lake test` entry for the conform rungs, with per-case names instead of one `#guard` per line | one require (no transitive deps) | **try** |
| core `#guard`, `#guard_msgs` | toolchain | ships | yes | in use | — | zero | **in use** |
| a Lean fuzzer | — | — | — | **does not exist.** Repository search for "lean4 fuzz" returns one unrelated project (`welltyped-systems/verified-ledger`, differential fuzzing *of* a ledger). Property testing with plausible is the ecosystem's answer | — | — | — |

## 8. Docs and navigation

| Tool | Where | Last commit | 4.33 | What it actually does | Slot | Cost | Verdict |
|---|---|---|---|---|---|---|---|
| doc-gen4 | https://github.com/leanprover/doc-gen4, tags include **`v4.33.1`** | 2026-09-16 | yes, exact | builds HTML API docs for a package, with a declaration index and a `Find` route (`DocGen4/Output/{Index,Find,Base}.lean`) | an agent's orientation cost is "where is the declaration that does X" — a generated index of every declaration with its type and docstring answers that without a build | builds the whole package plus doc-gen | **try** |
| Verso | https://github.com/leanprover/verso, tag `v4.33.0` | 2026-09-17 | yes | documents whose code examples are elaborated by Lean, so prose cannot drift from the code | the owner calls the docs estate bloat that slows orientation; Verso is the mechanism that would make the remaining docs load-bearing | large dependency | **try** |
| Batteries `#print prefix` / `#print dependents` / `#print opaques` / `#show_unused` / `#help` | vendored (see need 1) | — | yes | navigation commands answered from the environment | cheapest orientation win available | zero | **adopt** |
| import-graph `#min_imports`, `#find_home`, `lake exe graph` | tag `v4.33.0` | 2026-09-16 | yes | see need 1 | where does a declaration belong; what does this module really need | one require | **adopt** |
| lean-lsp-mcp | https://github.com/oOo0oOo/lean-lsp-mcp, v0.30.0 | 2026-08-19 | toolchain-independent (LSP client) | already in use in this estate | — | in place | **keep** |
| loogle | https://github.com/nomeata/loogle, toolchain **v4.30.0-rc1** | 2026-07-09 | **no** | pattern search over an environment (`?a → ?b`, name and subterm patterns), built around a Mathlib index | would be the best local search for this estate's own environment, but it is three releases behind and would need porting | — | **skip at 4.33** |
| LeanSearchClient | https://github.com/leanprover-community/LeanSearchClient, tag `v4.33.0` | 2026-09-16 | yes | `#leansearch "…"` posts a natural-language query to leansearch.net and prints Mathlib results | trained on Mathlib, useless for a private estate, and it sends queries off the machine | small | **skip** |
| Paperproof | https://github.com/Paper-Proof/paperproof, toolchain v4.29.0-rc8 | 2026-09-06 | **no** | visual proof trees in the editor | a human's tool, not an agent's | — | **skip** |

## What does not exist (stated plainly)

- No Lean 4 recursion-schemes / generic-programming library. Nothing derives a catamorphism, an
  algebra, a `Functor` or a `Traversable` from an inductive declaration except Mathlib's
  `DeriveTraversable`, which refuses indices, mutual families and recursive fields.
- No project-wide refactoring tool. `@[deprecated (since := …)]` plus a text pass is the state of the
  art; Mathlib's `Translate` is a renaming transport, not a definition rewriter.
- No `lean4-derive`, no deriving-handler library outside core and Mathlib.
- No Lean → JavaScript backend; no maintained Lean → wasm path.
- No Lean fuzzing library.
- No single hammer package (`leanprover-community/hammer` is a 404); `lean-egg` is deprecated by its
  author; `lean4checker` and `LeanInk` are archived, the first because it moved into the toolchain.

## The five adoptions, ranked, with the first step

1. **The census becomes an environment linter, gated by Batteries' `runLinter`.** It replaces the
   hand-rolled walk, gets parallel execution and `file:line:col: error:` output for free, and turns
   the 157-row exemption list into `scripts/nolints.json` — data, regenerated with `--update`, exactly
   the shape the estate already uses for count pins and `known-red.txt`.
   *First step:* add `src/Effect4/Laws/Auto/Lint.lean` that imports `Batteries.Tactic.Lint` and
   `Effect4.Laws.Auto.Traversals`, and lift the classifier out of `elabTraversalCensus` into
   `@[env_linter] public meta def traversalIsFold : Linter` whose `test` returns `none` for `fold`,
   `delegates` and `opaque` rows and `some m!"reads {domain} by {kind}"` otherwise. Then
   `lake exe runLinter Effect4.Laws.Auto.Lint` (the module's root is `Effect4`, so
   `getDeclsInPackage` covers the whole library; `lake exe` finds batteries' executable in the
   workspace) and `lake exe runLinter --update …` once to write the exemption ledger. Keep
   `#traversal_census` as the human-readable report.
2. **`fun_induction` as the conversion's proof engine.** Every hand traversal converted into an
   algebra needs `f x = cata alg x`, and core derives the induction principle shaped like `f` itself.
   *First step:* take one `structural` row of the census (a small one in
   `src/Effect4/Program/**`), write its algebra by hand, state the agreement theorem and close it with
   `fun_induction f <;> simp [cataFam, alg, *]`. If that shape holds for three rows of different
   arity, it is the template the converter metaprogram emits, and the census count is the burn-down.
3. **Emit through the deriving frontend and `ppCommand`, not through string building.**
   `tools/Effect4Gen` is 4,668 lines that build text with `String.intercalate`; core gives the
   declaration-writing plumbing (`Lean.Elab.Deriving.Util`: `mkContext`, `mkHeader`, `mkDiscrs`,
   `mkInductiveApp`, `mkInstanceCmds`) and `Lean.PrettyPrinter.ppCommand` for the file text.
   *First step:* re-express the smallest generator group (`tools/Effect4Gen/Rows.lean`, 180 lines) as
   a `DeriveHandler` registered with `registerDerivingHandler`, printed through `ppCommand`, and
   diff its output against the committed file with the existing `Effect4Gen.Check` guard.
4. **`lake env leanchecker` as a trust rung.** Zero install, already on the machine, and it answers a
   question the axiom gate does not: does the kernel still accept the declarations in the built
   oleans. *First step:* `lake env leanchecker Test.All` as a new `make check-kernel` target, run in
   the gate sweep rather than per merge (verification-cadence rule). Tested on the probe package:
   `lake env leanchecker Probe` exits 0 in 1.5 s.
5. **import-graph for the import-closure rules.** The estate's architecture rules are import rules
   ("nothing under `Effect4` imports aesop", "the LCNF pipeline's import closure only"), and they are
   currently prose. *First step:* `[[require]] name = "importGraph" … rev = "v4.33.0"` in a tooling
   configuration, then `lake exe unused_transitive_imports` over the `Effect4` roots and
   `#min_imports` in the two modules most suspected of over-importing; if the numbers are useful,
   copy Mathlib's `Mathlib/Tactic/Linter/DirectoryDependency.lean` idea into the linter of adoption 1
   so the layering rule is a gate.

Runner-up, and the one to reach for the moment a law is in doubt rather than in progress:
**plausible** (tag `v4.33.0`) — the red control for a conjecture, once `SampleableExt`/`Shrinkable`
exist for the family being tested. That instance work is the whole cost, and it is the same work a
generator-based replacement of the 20,387 vectors would need.

## Probe receipts

- `probe/` — a dependency-free package pinned to `leanprover/lean4:v4.33.1`.
  - `Probe/Linter.lean`, `Probe/Decls.lean`: reproduced a downstream `@[builtin_env_linter]`;
    `lake lint --builtin-lint Probe` reported both offenders and exited 1; `--record-exceptions`
    edited `Probe/Decls.lean` and the next run exited 0. The recipe needs `public meta
    register_option`, `meta initialize addEnvLinterOption`, and the option's module in the linted
    module's import closure.
  - `Probe/FunInd.lean`: reproduced `fun_induction` proving a hand traversal equal to its fold, and
    printed `sum.induct`.
  - `lake env leanchecker Probe`: tested, exit 0.
- `src/` — fetched sources read for this note: `DeriveTraversable.lean`, `TranslateCore.lean`,
  `AddRelatedDecl.lean`, `QpfTypes-README.md`, the READMEs of lean4export, lean4lean, plausible,
  LSpec, duper, lean-smt, Canonical, lean4checker, import-graph, LeanCopilot.
- `survey.sh`, `survey2.sh`, `tags.sh` — the compatibility sweep (default branch, last push, stars,
  archived flag, `lean-toolchain` at HEAD, and every `v4.3x` tag) over 60 candidate repositories.
