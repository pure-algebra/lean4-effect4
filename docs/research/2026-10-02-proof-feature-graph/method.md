# Method for the proof and feature view

The view explains selected parts of Effect4 through their syntax, judgments and rules,
then links that explanation to exact Lean declarations. It adapts three chapters from
*Types for Proofs and Programs, TYPES 2003*, LNCS 3085 (2004). It does not transfer their
metatheorems to Effect4. This note records the tooling method; [semantics](../../core/semantics.md)
and the [system map](../../core/system-map.md) remain the authorities for the language.

## What the chapters contribute

Robin Adams, “A Modular Hierarchy of Logical Frameworks,” §§2–3, printed pp. 3–5 and
Fig. 2 on p. 5, organizes a framework by syntactic classes, constructors, judgments and
deduction rules, with prerequisites between features. We use this organization for the
authored feature groups in `Tools.ProofMapSelection`. A group may include supporting
structures and predicates as well as judgment forms, so the visible headings say “Syntax
sorts / constructors,” “Judgments / supporting definitions,” and “Rules / theorems /
formal goals.” Adams's §3.4, pp. 11–12, states a separate conservativity theorem for his
presented features. Our grouping and prerequisite checks establish no such theorem;
Effect4's extension obligations remain R2/C1–C8 in the system map.

Clemens Ballarin, “Locales and Locale Expressions in Isabelle/Isar,” §§3.2–3.5,
printed pp. 37–41, explains how context parameters and assumptions survive in the facts
exported from a context. We retain a theorem's full quantified statement and list its
top-level propositional hypotheses. Conditions inside definitions and structures remain
visible through definition bodies and constructor signatures. A conditional theorem is
proved as stated; that does not prove its hypotheses for every application. Ballarin's
§4, pp. 42–48, also motivates separating facts available through a context from facts
actually used in a proof. Our direct references come from Lean expressions, not from
module imports. This is not an implementation of Isabelle locales or locale interpretation.

Freek Wiedijk, “Formal Proof Sketches,” §3, printed pp. 383–385, distinguishes a selected
explanatory skeleton from its completed justification. His §5, pp. 386–387, leaves the
selection of significant steps to the author. We likewise choose significant declarations
and link them to checked detail, while exposing that other references are omitted.
Section 9.2, p. 392, distinguishes checking a natural-deduction skeleton from justifying
its large steps. Our metadata checks validate identities, witnesses and prerequisite
structure; they do not check such a skeleton or establish that an open plan has a completion.

These are printed page numbers. In the supplied volume's PDF, the corresponding one-based
PDF page is the printed page plus eight. The source volume is retained in the research
archive at `docs/research/2026-10-01-semantics/sources/types-2003-proofs-and-programs.pdf`;
that ignored source archive is not copied into each worktree.
The chapter spans are Adams pp. 1–16, Ballarin pp. 34–50 and Wiedijk pp. 378–393.

## Reading nodes, arrows and conclusions

### Mechanical presentation

The [metaprogramming book's pretty-printing chapter](https://leanprover-community.github.io/lean4-metaprogramming-book/extra/03_pretty-printing.html)
describes the pipeline from `Expr` through delaboration to `Syntax`, parenthesization
and formatting. `Tools.SemanticsDisplay.expression` uses the pinned Lean 4.33.1
`PrettyPrinter.ppExpr` implementation for both claim and graph statements, hypotheses
and definition bodies. Fixed pretty-printer options and line width isolate report bytes from a
caller's display settings while retaining the extraction resource limits. The exact declaration name, universe parameters and full
quantified statement remain inspectable; a short card label is only a navigation aid.

The standalone report loads constants without running imported initializers. It therefore
keeps canonical names such as `Eq` when an imported notation extension is unavailable.
A bounded probe confirmed this distinction; the repository's prohibition on new unsafe
declarations remains unchanged. A future notation-rich frontend producer needs its own
controlled integration and readback checks.

No second mathematical notation is reconstructed in JavaScript, and this slice registers
no global delaborator or unexpander. New object-language display syntax should follow
the chapter's guidance on existing notation and unexpanders and receive its own
readback checks. In particular, a pleasing display is not itself a proof of re-elaboration
or target-code reconstruction. The interface uses text labels as well as color and line
patterns, supports keyboard selection, and includes the same data as plain text.

### Evidence and connections

The existing semantics registry and `ProofGraph` own claim and witness identity. The
feature selection does not create another status register. A definition is defined, a
validated theorem is proved at its displayed proposition and axiom policy, and a declared
goal without a witness is wanted. A theorem with hypotheses stays a conditional theorem.
Neither a green neighbor nor a feature total supplies evidence for those hypotheses.

| Connection | What it records |
| --- | --- |
| Proof-body reference | A selected constant occurs directly in the stored proof expression, including any annotations or supporting definitions. |
| Definition-body reference | A selected constant occurs directly in a defining expression. |
| Statement reference | A selected constant occurs in the declaration's type; this is vocabulary occurrence, not a use of its theorem or proof of a premise. |
| Declared goal prerequisite | An authored ledger dependency whose names and cycles are checked; this check does not establish entailment. |
| Feature prerequisite | An authored relationship between explanatory groups; it does not prove conservative extension. |
| Proposed work order | An authored sequence for implementation or proof work, with its reason and source. |

Reference arrows point from the referenced declaration to the declaration using it.
Authored prerequisite arrows point from prerequisite to consumer. They are tooling
relations, distinct from the system map's K1–K5 semantic arrows: fold, exact embedding,
simulation, located refusal and monoid action. A displayed path does not create a new
derived theorem. Constructor signatures expose structure fields without inventing
statement-reference edges from those fields.

The conclusion of a selected theorem is read from its full statement, with all binders
and hypotheses retained. For example, `m7_of_ledger` keeps its loading and decision
preservation hypotheses; its conclusions still depend on `M7Fragment`. The internal
`run_eq_ref` observation and module reconstruction laws retain their own domains. Neither
establishes TypeScript execution, OCaml execution or Lean compiler lowering.

## Notation shared with the language documents

Use the existing names below; do not turn a research note's schematic judgment into a
new Effect4 predicate. The merged semantics document owns the judgments. Gemini's
earlier drafts and sample registry strings remain research history.

| Notation or name | Meaning in this view and authority |
| --- | --- |
| `w`, `w' : World` | Typed worlds. `w.Γ` types fibers, `w.«Π»` deferreds, `w.Ρ` references (Greek rho), and `w.Θ` resume tokens. See semantics §2, Store Typing, and `Laws/Program/Typed/World.lean:52`. Uppercase `W` in older notes does not introduce another sort. |
| `Γ` in source composition | The source context in system-map §6. It is distinct from the fiber table `w.Γ`; retain the qualifier or actual declaration when both occur. |
| `Σ` | The language signature `Σ_core ⊕ Σ_app` in system-map §1.1. Store-typing literature in semantics uses `Σ` differently. `Signature Op` is the checker's typed view, and the constructor signature is a third sense; system-map §1.1 names all three. |
| `Fits w v ty`; `TypedProg root w ty p` | Value membership and residual-program typing, respectively. These are exact predicate names, not interchangeable instances of a new generic “well-typed” symbol. See `Membership.lean:113` and `Residual.lean:266`. |
| `DenotesTyped`; `MachineTyped` | The denotation connector and machine-state invariant. Preserve their parameters and expanded conditions; a shorthand invariant symbol cannot replace their declarations. See semantics §§2, Residual Program Typing and Reactive Scheduling. |
| `w.leHost w'` | World extension together with persistence of existing external-handle identities (`Validity.lean:38`). It is distinct from a type's subtyping relation and from a graph prerequisite. |

Stored `Eff` is first-order syntax; its bind stores child trees. `RProgram` is the
proof-side semantic carrier whose operation continuations are Lean functions. Neither
is Lean's host parser syntax (`Lean.Syntax`). The relevant distinction is documented in
semantics §§1 and 4, not inferred from a graph's “Syntax” heading.

For the selected codegen route, `printModule` produces TypeScript declaration trees and
`readModule` reconstructs an `Eff` from declaration trees (`Codegen/Print.lean:142`,
`Codegen/Read.lean:758`). The raw reader ignores declaration annotations, export flags
and the main name. Rendering those trees into bytes, admitting source text and executing
the target are separate boundaries. The view therefore says “module reconstruction”
and preserves the laws' readability, table and printing premises.

## Source and evidence boundary

This method was aligned against the merged theory documents at
`0f1f878bb21201e52740577c46327b63e7cebc5a` and the proof-view tooling in its isolated
worktree. `tools/Tools/ProofMap.lean` owns extraction and validation;
`tools/Tools/ProofMapSelection.lean` owns the authored selection;
`tools/Tools/ProofMapHtml.lean` owns presentation. The generated semantics report carries
the resulting selected view. These documentation additions involved source inspection,
not a new theorem check, compiler run or claim of complete proof coverage.
