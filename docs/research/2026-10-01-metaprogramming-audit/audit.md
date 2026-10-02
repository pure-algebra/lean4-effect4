# Lean metaprogramming audit — first implementation slice

Base: `198dd5331eb6607e1e94f3abad39ebbda90c86dc`, Lean 4.33.1. Worktree:
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
**Held after testing:** the API is not in the current import closure; it requires
`import Lean.Parser.Do`. DI-18 is unresolved and both alternatives in the coordinator
addendum keep Lean tooling out of the runtime root. The experimental patch is retained
outside the branch; Sugar and its test are unchanged. The compiled experiment and the
new refusal fixture exposed a pre-existing generic final-binding error, not a repair in
this slice. Do not land this additional runtime dependency before the DI-18 ruling.

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
No fired-arm counts have been measured yet. Do not infer them from source or treat these
macros as approved exemptions. Keep unchanged; instrument the current proofs in an isolated
copy before recommending a named bank or explicit arms. The coordinator owns that ruling.

**P6 / A5a — printed source is partially pinned (reading).**
Five `srcOf` functions in `Effect4Gen/{Rows,LayerView,View,Fold,Authoring}.lean` already pin
`pp.fullNames=true` and `pp.universes=false`. They inherit other options, including
`pp.explicit`, `pp.notation` and `pp.all` (`Lean/PrettyPrinter/Delaborator/Options.lean:24,
56–63,163,254–270`). The direct `ppExpr` uses in `Conform/Layout/Reflect.lean:121` and
`OCaml5/Lcnf/Types.lean:290` are diagnostic descriptions of unsupported fields, not emitted
target syntax. The FoldOf occurrences are diagnostics too. Do not call all of them
unstable code generation.
Before changing producers: compare an actual `srcOf` result under default and perturbed
options, pin a reviewed profile, regenerate each affected group, and compare bytes. View/Fold
are also in the active data-wave generator work; keep changes to them out of this first slice.
This is pending testing and coordination, not a proved determinism defect.

**P7 / A5b — readable Lean goals are a separate output contract (reading).**
No project delaborator/unexpander was found by the named-attribute census. The book's
[pretty-printing chapter](https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html)
explains Expr → Syntax → parenthesizing → Format. An application unexpander can improve
display, but must handle partial applications and return failure for unsupported shapes.
This does not establish Effect4's exact print/read laws. Keep a before/after prototype local;
measure affected `#guard_msgs` fixtures before any global registration. Ruling required;
no production display changes in this slice.

**P8 / A7 — ownership follows dependency direction (reading).**
`docs/ARCHITECTURE.md:100–110` places law-specific commands in Laws and generic evidence in
ProofGraph. `Program/FoldOf.lean` is intentionally below generated runtime folds. Moving it
to Laws would introduce the forbidden runtime-to-Laws edge. `Program/Authoring/Sugar` is
an author-facing syntax macro and needs no theorem inspection. `TypedStateDecl` is already
in the Laws graph, contrary to the coordinator's intermediate UI speculation. The measured
direct imports do not prove the entire transitive closure; that measurement remains pending.
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
| `#answer_gate` | CommandElabM + MetaM / Laws.Auto.AnswerGate | typed residual answer tables |
| `#auto_census` | CommandElabM + speculative TermElabM / Laws.Auto.Census | Test.Audit.ProofGraph, ProofGraphSearch |
| `#proof_wanted`, `#obligation_proved`, `#typed_state_obligations`, `#obligation_audit` | CommandElabM / Laws.Auto.Obligations | Test.Audit.Obligations |
| `#frame_rules` | CommandElabM / Laws.Auto.Frames | typed-state frame rules and Test audit fixtures |
| `#position_census`, `#edge_census`, `#write_census`, `#read_census` | CommandElabM + MetaM / Laws.Auto.Positions | typed source and position census fixtures |
| `#traversal_census`, `#traversal_class`, `#exhaustive_gate` | CommandElabM / Laws.Auto.Traversals, Exhaustive | Test.Audit traversal/exhaustiveness fixtures |
| `#position_gate`, `#typed_state` | CommandElabM / Laws.Program.Typed.PositionGate, TypedStateDecl | typed-state fixtures |
| `fold_of` | CommandElabM + MetaM / Program.FoldOf | fold consumers and fold batteries (fixture path to be measured) |
| `reflect_spec`, `harvest_specs` | CommandElabM + MetaM / Conform.Spec.Reflect | conformance specification pilot |
| `checked_theorem%` | TermElabM / ProofGraph.Proof | Test.Audit.ProofGraph and conformance evidence |
| axiom/runtime coverage commands | CommandElabM / Test.Audit | Test.Audit.AxiomGate, RuntimeCoverage |
| `eff`, `daemon` | MacroM / Authoring.Sugar, Services | Test.Program.AuthoringScope, AuthoringContract |
| trace/queue/handle tactic families | tactic syntax macros / Laws.Machine | same modules' theorems; fired-arm audit pending |
| `authoring_scoped` | tactic macro / Laws.Program.Authoring.Tactic | authoring law fixtures |

Raw Syntax is justified where a command parser owns fixed indexes. Prefer typed quotations
for stable syntax rearrangements; use elaborators where inspection/validation is needed.
Retain syntax + named command elaborator for named reusable commands. Short `elab` sugar
is appropriate for small one-off commands; changing spelling alone is not consolidation.
Use MessageData (`m!`, `throwError`) for Lean objects in diagnostics; strings remain appropriate
for serializable report/refusal fields. A full per-site and fired-arm census remains separate
from this first safe implementation receipt.
