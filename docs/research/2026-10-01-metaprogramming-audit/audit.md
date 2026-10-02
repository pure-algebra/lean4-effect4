# Lean metaprogramming audit and tested cleanups

Initial inspection base: `198dd5331eb6607e1e94f3abad39ebbda90c86dc`, Lean 4.33.1.
Current branch base: `8c9be258` (the coordinator’s recorded DI-18 ruling). No source or
toolchain changed between those bases; the only Test change is a counterexample register row.
Worktree:
`/Users/pooks/.codex/worktrees/metaprogramming-audit/lean4-effect4`, branch
`codex/metaprogramming`. Claude's checkouts and research seats are read-only inputs.
The dispatch is `docs/research/2026-10-01-metaprogramming-audit/brief-codex-metaprogramming.md`
in the integration checkout. This note precedes implementation; the receipt distinguishes
subsequent tests from the source readings below.

Completion for this bounded slice: audit the proposed seams against the pinned compiler,
replace the demonstrated duplicates without changing statements or existing diagnostics,
compile each changed module and focused consumers, retain accepting and rejecting controls,
and commit the changes separately from this audit. The remaining measurements and decisions
are explicit below; a lexical inventory is not a completeness theorem.

## Findings and proposals

**P1 / A1 — use the existing typed sequence reader (reading).**
`Lean/Parser/Do.lean:52–59` defines `Lean.Parser.Term.getDoElems : DoSeq → Array DoElem`.
It uses exactly the bracketed/indented cases duplicated at
`src/Effect4/Program/Authoring/Sugar.lean:96–103`. Preserve the existing public helper's
list-returning signature by delegating to this function. For the one-level nested `do`, use
a typed `(doElem| do $seq:doSeq)` quotation instead of indexing the raw node. Preserve the
one-level behavior, empty/unrecognized fallback, scoped keyword and all refusal messages.
Files: Sugar and the already-reachable `Test/Program/AuthoringScope.lean`. Expected existing
fixture-output changes: zero. Build cost: small module plus direct consumers.
**Initially held after testing (now released by DI-18 at `8c9be258`):** the API is not in the current import closure; it requires
`import Lean.Parser.Do`. DI-18 was unresolved and both alternatives in the coordinator
addendum kept Lean tooling out of the runtime root. The experimental patch was retained
outside the branch while the ruling was pending. The compiled experiment and the
new refusal fixture exposed a pre-existing generic final-binding error, not a repair in
this slice. The owner subsequently dropped the import ban while retaining the first-order representation
rule. Adopting this helper changes the authoring macro only, not stored program fields.

**P2 / A2 — reuse `simpArg`, preserving the grammar (reading).**
`Init/Tactics.lean:707` defines the exact disjunction copied five times at
`Laws/Machine/Handles.lean:1114–1184`. Replace just that disjunction by
`Lean.Parser.Tactic.simpArg`. The larger `simpArgs` syntax at line 710 admits a trailing comma;
blindly substituting it would expand the accepted language. Keeping existing brackets,
separators and optional arguments preserves current macro quotation shapes and callers.
Do not change the tactic bodies or their fallback policy. Add parser controls for the five
forms, plain/reverse/erased/star arguments, omitted lists and a rejected trailing comma.
Expected existing diagnostic changes: zero. Cost: recompiling Handles and narrow consumers.
No ruling needed for grammar reuse; fallback policy is P5.

**P3 / A4 — share evidence policy, not every census (reading).**
The literal semantic axiom filter is identical in `ProofGraph/Proof.lean:26`,
`Ledger.lean:54` and `Search.lean:132–133`. A small policy helper below these three clients is
appropriate. Keep rejection messages and the order of offending axioms unchanged. The
full `Test/Audit/AxiomGate.lean` policy includes implementation exceptions and must remain
separate. A passing axiom subset check is not a whole-tree gate verdict.

`Laws/Auto/Obligations.lean:15–24` has a reusable, precise obligation reader: it opens a
telescope, requires a theorem marker, reconstructs the quantified proposition and refuses
unsupported occurrences. Put that operation beside `ProofGraph.Goal` in Ledger, and have
the old client call it. This gives the forthcoming semantics report an API rather than
a second shape recognizer. Preserve its error messages. Existing obligation controls
exercise the behavior; add direct API controls. No root imports or gate-policy edits needed.

Do **not** merge all inventory filters into one `isNoise`: `Auto/Census.lean:78–91` counts
authored theorems with source ranges, `Traversals.lean:165–190` deliberately includes private
definitions, `Exhaustive.lean:165–190` adds recursion helpers, and
`Tools/Architecture.lean:163–194` hides implementation names for a human map. These universes
are intentionally different. A later shared walk should take an explicit selection policy;
module ownership and declaration-name prefixes must remain separate query operations.

**P4 / A6 — retain the closed-expression quote for now (reading).**
The pinned compiler does not provide `ToExpr Expr`, `ToExpr Level` or `ToExpr BinderInfo`
instances. `deriving ToExpr` exists, but deriving a general expression instance is not the
same operation: the existing `quoteClosed` erases metadata and refuses free/metavariables.
Do not replace that checked boundary with a general serializer. A future small derivation
can be judged separately against metadata and openness controls; this slice needs no change.

**P5 / A3 — fallback instrumentation remains a distinct audit slice.**
Source-read families: Approximation's `trace_leaf`, `trace_chain`, `hops_leaf`,
`hops_observers`, `hops_cmd`, `hops_loop`; Scheduling's `queue_leaf`, `queue_chain`,
`queue_hops`; Handles' `or_search`, `mem_tac`, `close_mem`, `sub_tac`.
The leaf macros normalize then try reflexivity, append or transitivity; the hop macros
dispatch among named helper theorems; the chain macros repeat those steps. This is more
specific than arbitrary backtracking, but includes silent `skip`/`try` cases.
The five requested hop families have now been instrumented in isolated full-source copies;
`evidence-A3/RESULTS.md` gives all 22 arm counts at all nine proof sites, including zeros and
per-macro proposals. Baseline and instrumented runs passed with matching theorem fingerprints
(303/168 declarations). Rollback controls ensure abandoned attempts do not inflate selected
counts. Other listed families remain source readings, not measured firing counts. Keep
production macros unchanged until the coordinator rules; a hidden fallback is not thereby
an approved exemption.

**P6 / A5a — printed source is partially pinned (reading).**
Five `srcOf` functions in `Effect4Gen/{Rows,LayerView,View,Fold,Authoring}.lean` already pin
`pp.fullNames=true` and `pp.universes=false`. They inherit other options, including
`pp.explicit`, `pp.notation` and `pp.all` (`Lean/PrettyPrinter/Delaborator/Options.lean:24,
56–63,163,254–270`). The direct `ppExpr` uses in `Conform/Layout/Reflect.lean:121` and
`OCaml5/Lcnf/Types.lean:290` are diagnostic descriptions of unsupported fields, not emitted
target syntax. The FoldOf occurrences are diagnostics too. Do not call all of them
unstable code generation.
The CLI drivers construct a fresh `Core.Context` with default options and an empty Meta
context (`Rows.lean:171–181`, `Fold.lean:1376–1386`; `Lean/CoreM.lean:217–222`). Thus
inheriting options inside `srcOf` is not evidence that command-line generation inherits an
interactive caller’s settings. With a fixed compiler and imported environment, defaults are
fixed inputs. Before changing producers, distinguish reusable-helper context sensitivity
from the actual driver; require a concrete changed output under a supported invocation. View/Fold
are also in the active data-wave generator work; keep changes to them out of this first slice.
The bounded helper probe in `evidence-A5/` confirms option sensitivity and restoration.
The supported CLI reading above supplies no demonstrated nondeterminism defect; no producer
change or regeneration is warranted on that evidence.

**P7 / A5b — readable Lean goals are a separate output contract (reading).**
No project delaborator/unexpander was found by the named-attribute census. The book's
[pretty-printing chapter](https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html)
explains Expr → Syntax → parenthesizing → Format. An application unexpander can improve
display, but must handle partial applications and return failure for unsupported shapes.
This does not establish Effect4's exact print/read laws. The existing `eff` notation produces `Authoring.Src`, not `Eff`; printing an Eff value
as that authoring block would not by itself re-elaborate at the original type. A goal-display
proposal must preserve this layer distinction. Keep a before/after prototype local;
measure affected `#guard_msgs` fixtures before any global registration. The local Val.nat
prototype in `evidence-A5/` changes one of two message fixtures in TypedProgBindRed and passes
notation elaboration, fallback and scope controls. This is a one-battery measurement, not a
global count. Recommend keeping current display: the new spelling adds little demonstrated
value. A global adoption still needs the coordinator’s ruling; no production display changes
in this slice.

**P8 / A7 — ownership follows dependency direction (reading).**
`docs/ARCHITECTURE.md:100–110` places law-specific commands in Laws and generic evidence in
ProofGraph. `Program/FoldOf.lean` is imported by the runtime umbrella, but its measured command
callers are in Laws (see the A7 follow-up). Moving it requires changing the umbrella edge
and retaining a deliberate tooling import for clients. `Program/Authoring/Sugar` is
an author-facing syntax macro and needs no theorem inspection. `TypedStateDecl` is already
in the Laws graph, contrary to the coordinator's intermediate UI speculation. Direct imports alone do not prove the entire transitive closure; the project-only
closure measurement is recorded below, with external packages explicitly unmeasured.
Prefer functional ownership to one giant Meta module. No file moves without a dependency
graph and an agreed public import seam.

## For the spec: vocabulary

| Word | Lean layer | Effect4 meaning and boundary |
| --- | --- | --- |
| Object-language syntax | ordinary inductive data | Eff, Ty, Term, Val and Representation; inspectable program/data syntax, not Lean Syntax or Expr |
| Lean source syntax | Syntax / TSyntax category | parsed terms, commands and tactics, carrying source and hygiene information |
| Macro expansion | MacroM, syntax quotations | `eff` and `daemon` conveniences expand Lean syntax; no type judgment claimed |
| Lean elaboration | TermElabM / CommandElabM with MetaM | resolves source syntax, types and declarations into kernel expressions/environment entries |
| Authoring resolution | `Authoring.elaborate` / `elaborateModule` | resolves named authoring input to Eff or a located refusal; retain current API names, qualify prose |
| Effect interpretation | `denoteR`, algebras and folds | semantic interpretation of the object language; name the observation and fragment |
| Lean delaboration / formatting | DelabM, Syntax, Format | presents expressions to people; source text and original spelling are not retained inverses |
| Target printing / reading | TypeScript syntax and Effect4 readers | separate exact-embedding contracts with readable-domain and normalization premises |
| Census | command/tool over an explicit environment universe | measurement with exclusions, roots and freshness recorded; not proof completeness |
| Gate | validating command/tool with its policy | accepts/refuses the stated conditions; axiom ceiling, coverage and evidence validation are distinct |

Proposed authority amendment: qualify “syntax”, “elaboration” and “printing” with the
language/layer when first used. Keep Lean Syntax/Expr and tool closures outside stored
Effect4 program data. Do not rename semantic definitions merely to match Lean's API names.
The coordinator can adopt this section in the semantics document and AGENTS vocabulary.

## Surface inventory (reading)

The retained `census.json` records line candidates from `src`, `tools`, `Test`, `harness`.
It includes comments and strings, so raw hit counts are not declaration counts. The actual
command families and their existing fixture homes are:

| Family | Layer / module | Fixture or current consumer |
| --- | --- | --- |
| `#answer_gate` | CommandElabM + MetaM / Laws.Auto.AnswerGate | typed residual answer tables (no standalone Test invocation found) |
| `#auto_census` | CommandElabM + speculative TermElabM / Laws.Auto.Census | Test.Audit.ProofGraph, ProofGraphSearch |
| `#proof_wanted`, `#obligation_proved`, `#typed_state_obligations`, `#obligation_audit` | CommandElabM / Laws.Auto.Obligations | Test.Audit.Obligations |
| `#frame_rules` | CommandElabM / Laws.Auto.Frames | Test.Audit.FrameRules |
| `#position_census`, `#edge_census`, `#write_census`, `#read_census` | CommandElabM + MetaM / Laws.Auto.Positions | Test.Audit.PositionCensus |
| `#traversal_census`, `#traversal_class`, `#exhaustive_gate` | CommandElabM / Laws.Auto.Traversals, Exhaustive | Test.Audit.TraversalCensus |
| `#position_gate`, `#typed_state` | CommandElabM / Laws.Program.Typed.PositionGate, TypedStateDecl | Test.Audit.TypedStateDecl, IndexedColumns, PositionCensus |
| `fold_of` | CommandElabM + MetaM / Program.FoldOf | 62 invocations across 13 Laws files; no direct Test invocation found |
| `reflect_spec`, `harvest_specs` | CommandElabM + MetaM / Conform.Spec.Reflect | conformance specification pilot |
| `checked_theorem%` | TermElabM / ProofGraph.Proof | Test.Audit.ProofGraph and conformance evidence |
| axiom/runtime coverage commands | CommandElabM / Test.Audit | Test.Audit.AxiomGate, RuntimeCoverage |
| `eff`, `daemon` | MacroM / Authoring.Sugar, Services | Test.Program.AuthoringScope, AuthoringContract |
| trace/queue/handle tactic families | tactic syntax macros / Laws.Machine | same modules' theorems; five hop families measured in evidence-A3, others source-only |
| `authoring_scoped_step`, `authoring_scoped` | tactic elaborator and macro / Laws.Program.Authoring.Tactic | authoring laws |
| `close_ref_free` | scoped tactic macro / Laws.Program.ReferenceTyping | mutual reference-expansion proofs in that module |
| `budget`, `layerBudget` | scoped tactic macros / Laws.Program.DenoteR | denotation equations in that module |
| `close_arm` | scoped tactic macro / Codegen.Read | no use found outside its declaration; do not infer external API retirement |

Raw Syntax is justified where a command parser owns fixed indexes. Prefer typed quotations
for stable syntax rearrangements; use elaborators where inspection/validation is needed.
Retain syntax + named command elaborator for named reusable commands. Short `elab` sugar
is appropriate for small one-off commands; changing spelling alone is not consolidation.
Use MessageData (`m!`, `throwError`) for Lean objects in diagnostics; strings remain appropriate
for serializable report/refusal fields. A full per-site and fired-arm census remains separate
from this first safe implementation receipt.


## A7 measured follow-up and the recorded ruling

The import-only ban was dropped by the owner at `8c9be258`; no repeat decision is requested.
The measurement in `evidence-A7/` reads immutable base `198dd533` with `git cat-file`, removes
comments and strings before counting source commands, and records the command, source hashes,
module lists and limitations. The relevant source trees are identical at the new base.

| Measurement | Result |
| --- | --- |
| Tracked project modules in src/tools | 475 |
| Runtime-root project closure | 135 modules |
| Laws-root project closure | 351 modules |
| Direct Lean importers in runtime closure | Program.FoldOf only |
| Direct Lean importers exclusive to Laws | Auto.AnswerGate, Auto.Positions, Program.Authoring.Tactic, Program.Typed.TypedSources |
| FoldOf callers | 14 direct importers; 68 reverse dependents, excluding itself |
| `fold_of` commands | 62 in 13 Laws files; none in runtime/tools source |
| Sugar callers | 5 direct importers; 20 reverse dependents |
| Tested authoring-block source sites | 20 accepting examples and one intended rejection in three Test files (counted, not rerun by this measurement) |

These are project source-import counts, not external package closure measurements or proof
of first-order representations. Macro definitions also occur without a direct `import Lean`,
including `daemon` and `Codegen.Read.close_arm`; imports are a poor proxy for representation.

**Home proposal:** leave FoldOf in place during this consolidation. A later relocation can
remove the runtime umbrella’s FoldOf import and update 13 Laws imports plus the gate’s named
module admission while preserving declaration namespaces. This reduces runtime project closure
by one module, but removes a public command from the runtime umbrella. No lower runtime
consumer needs that command today. It is an API/organization choice, not needed to enforce the
owner’s representation rule. A separate tooling face is another option if external consumers
need `fold_of`; it costs a deliberate compatibility import rather than moving everything to Laws.

**Check proposal:** reject the suggested blanket signature test as currently phrased. Sugar’s
existing `getDoSeqElems` and `expandDoElems` intentionally mention Syntax/MacroM, and FoldOf
intentionally consumes Expr, while neither stores those objects in Eff. Scanning every
runtime-root declaration would reintroduce the import ban under a different name. If repeated
escapes justify a new check, scope it to stored-sort constructor fields and the actual runtime
alphabet instantiations, with accepted tooling controls and rejected Expr/function payloads.
The existing representation rules and separation controls remain the authority. No new gate
or root move was introduced here.

The original strict migration is no longer requested. For cost context it would have replaced
181 explicit obligation commands, 74 search/check commands and 20 placeholder commands, plus
censuses and tactics: a generator migration, not a simple directory move.
