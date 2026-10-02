# Define the semantic contracts that guide the next build slices

The documentation defines what Effect4 means to implement. For each concept, connect the verified literature definition to the project's explicit adaptation and language boundary, then to its exact judgment, the obligations that follow, and the implementation slice that satisfies them. Product examples and proof dependencies determine the order of those slices; they do not replace the semantic contract.

A slice advances when it makes a named capability work under that contract, closes a required semantic connection, or removes a concrete blocker. If implementation exposes a mismatch with the documented definition, resolve and record the mismatch before building further on it. Do not rewrite a definition after the fact merely to describe whatever the code happens to do.

This plan follows the owner's clarification on 2026-10-02. It is a planning proposal on `codex/metaprogramming`, not a change to the coordinator's dispatches or decision register. The checked first report is recorded in [receipt.md](receipt.md). Claude's handed-back branches and the owner edits in main remain theirs to integrate.

## What we can use now

The executable report is implemented and checked for the selected four-claim residual-typing slice. It prints the propositions that Lean actually checks, distinguishes evidence states, and strictly validates the report with Effect Schema. Its complete check passed; no implementation rerun is needed for this planning-only change.

Gemini's updated ten-concept draft has repaired the fifteen qualified-name errors and the identified literature keys. Its current registry text contains 50 selected claims: 39 witness pointers, three goal pointers, seven absent entries and one refutation. These are authored selections, not a full obligation census or a measure of product completion. The updated receipt's count of 45 is stale. The adoption snapshot and source checks are retained in [direction-receipt.md](direction-receipt.md).

The full registry is not yet adopted or compiled. It still repeats the model definitions; adoption must take its registry value into the existing `Tools.Semantics` types. Full `Effect4.Laws` preparation is blocked by the unchanged Bookkeeping errors recorded in the first receipt, while main has owner repairs. The selected report works at its explicitly named roots. Do not conceal that distinction by labeling the larger draft checked.

## The definition comes before the task

Cover all ten concepts with an alignment inventory. Each chapter explains the source definition, what Effect4 retains or changes, the project's own definition and judgment, and why the chosen obligations follow. This is where we distinguish an adopted definition, an adapted construction, a borrowed proof technique and an analogy. A citation or shared name alone establishes none of those relationships.

Use audited primary text for substantive source claims. A verified contents page establishes a chapter's title and location, not its definitions or theorems. If the relevant text is unavailable, mark the source claim unverified and state the project's exact definition independently. A theory-backed change needs that gap resolved, or an explicit independent project contract, before dispatch.

Then connect every outstanding obligation to its existing evidence or decision reference, dependencies and owner, and a bounded implementation slice. Keep theorem states and decisions linked to their owners. Do not make a second status ledger.

For example, the current `machineTyped_not_halted` establishes an invariant consequence, `stuck = none`; it does not produce a successor transition. A chapter that asks for operational progress must define the applicable states and required transition result, then name that separate obligation. Calling the existing theorem “progress” would lose exactly the theoretical distinction this documentation is meant to enforce.

The initial map below connects the draft's concepts to existing work. It is not a new list of required theorem statements. The landing plan, data-wave series and decision rows supply the detailed scope; Gemini's next pass should fill missing links and identify uncovered applicable obligations.

| Concept | Implementation question | Existing work to use |
| --- | --- | --- |
| Store typing | Do values produced or consumed by an operation fit its declared type in the correct world? | Membership laws; the data wave's value/type append; D5's missing typed-state clauses and row 180 |
| Residual program typing | Does each admitted source construct produce a typed residual program? | M5's declared goals; D2's constructor groups and hand-back; construct-specific compatibility from row 148; rows 176 and 183 |
| Scope lifetime and finalization | Do scope creation, close and finalizers preserve the required state and return the chosen results? | D4's close/closed-root repair, existing scope controls, row 156; distinguish repaired scope-presence posts from general scope validity |
| Reactive scheduling | Does each command preserve the maintained state, and what service or progress is actually established? | D5's row 134 clauses and row 181 field census; M6's command goals; keep `flush_fair` separate from successor existence and general liveness |
| Exact codecs | Can each admitted data form be written and read under its named normalization law? | Landed exactness for today's forms; data-wave W5 for the new forms; rows 128 and 179 |
| Subtyping algebra | Do the new data forms participate in the intended order and membership laws? | W2's generator/order work, W4's append, declared leaf edges and optional-field rule; rows 177 and 178 |
| Initial algebras and folds | Does extending the syntax require one new constructor account instead of duplicated traversals? | W2/W4 and row 182; existing fold uniqueness and conservativity controls, with evidence validation |
| Context requirements | Are services supplied where the program needs them, including built layer contexts? | Closed-root premise row 117; D2's layer work and row 176; distinguish the stored program from its function-bearing semantic carrier |
| Host session protocol | Is an external answer accepted against the actual request instance, with the host assumptions explicit? | Existing session contracts; row 183's lawful template-row example; the host boundary's separately owned assumptions |
| Translation and simulation | Which named observations agree, on which fragment, and what remains needed by M7? | Existing fragment agreement, M7's declared goals and conditional route theorem; empty-table boundary and registered-handle premise |

Use the textbook roles as questions to test applicability. Do not fill every chapter/role cell with a theorem, or treat the textbook checklist as a proof that all obligations have been found. Separate required-but-unproved work, a refuted statement awaiting a decision, an intentional exclusion, and an external assumption. Those categories matter for scheduling; the seven `absent` selections need that reading before anyone treats them as seven implementation tasks.

In particular, `m7_of_ledger` proves a conditional route. Its load and decision-preservation premises do not become available because the route theorem is listed as a proved witness. The M7 goals remain distinct from it.

## Next slices, with finish lines

Before a slice is implementation-ready, its affected concept must have a usable semantic contract: definitions, assumptions, observation or judgment, and required laws. An accepting example and a rejecting example help expose a mismatch; they do not replace the laws. Record any new obligation discovered by this analysis for reconciliation with the coordinator, rather than silently changing an existing seat's brief.

### 1. Reconcile evidence and publish a useful first chapter set

**Outcome:** each concept connects the literature to a precise project definition, its applicable obligations, the relevant generated evidence, and the work that implements it. Adopt corrected content through the existing producer; preserve the current evidence API and strict decoder. Do not add a parallel schema, status calculator or environment walker.

**Dependencies and ownership:** Gemini prepares the content in its research drafts under [brief-gemini-next.md](brief-gemini-next.md). Codex owns executable adoption and checks on its branch. Broader evidence preparation waits for the coordinator's typed-state integration; read and record narrower evidence only under explicitly named roots. The coordinator owns promotion of authority links and any changes to decisions, STATE and the system map.

**Done:** ten concept sections with explicit theoretical alignment and a bounded work inventory; each selected witness resolves through the producer before publication as checked evidence; known owed work is linked instead of hidden; literature references retain their verification limits. Generated tables carry statements and evidence states, prose carries meaning and boundaries. Chapters may be published incrementally with draft or unverified sections identified. A slice waits for the definitions and obligations it depends on, not for unrelated chapters, a zero unplaced-declaration count, or an architecture-map redesign.

### 2. Resume the data path at its next unfinished dependency

**Outcome:** advance toward the existing v0 acceptance, p2's handler with host-side decoding. The series already defines the work; this inventory should make its dependencies visible.

**Next boundary:** reconcile W2's handed-back generator work before W4's value and type appends. W4 starts with the signed and binary64 value images; its new type forms precede W5's codecs, W6's terms and the later printed faces. Existing briefs and their amendments determine each implementation's file ownership and controls. Do not launch a duplicate seat from this planning note.

**Done for each dispatch:** the selected form or operation satisfies its documented adapted definition, with its implementation, the laws the existing contract requires, and the relevant accepting and rejecting controls; all consumers changed by that slice are accounted for. An unimplemented face is explicitly refused until its own slice. Record which remaining p2 dependency was removed. Completion of the entire data path is its existing end-to-end handler acceptance, not a total of new type constructors or documentation pages.

### 3. Close one typed-state connection at a time

**Outcome:** make M5/M6 premises available to their consumers, ultimately supporting the declared M7 results on their restricted fragment.

**Next boundary:** reconcile the handed-back D4/D2 work and the owner's Bookkeeping repair before further work on the same modules. Use D2's constructor-group list and the D5 field/command coverage work to choose one next obligation. Row 176 is a layer-context representation decision; row 183 has a lawful `List<A>` to `Option<A>` example whose kernel control remains owed in the register. These are different blockers and should not be folded into one generic “typing repair.”

**Done for each dispatch:** the unchanged or explicitly ruled statement expresses the chapter's intended judgment and is proved and used by its intended caller, with the relevant positive example and rejecting control retained and axiom output recorded. If a statement is refuted, retain the smallest counterexample and request the specific ruling through the coordinator's existing process. The receipt names any remaining assumption and the next dependent obligation. Adding an unused helper does not close the connection.

## Publication and later consumers

Publish the chapters as the semantic contract for the work, with enough explanation to justify each adaptation. Keep their definition and assumption changes alongside the related implementation changes, with coordinator-owned rulings recorded in the existing register. A disagreement between a source, the project definition and a theorem is a design question to resolve, not a wording defect to hide.

Prefer focused explanation over repeating the literature survey. The source audit supplies verified references; the chapter supplies the actual relationship to Effect4. Exact theorem statements and changing counts belong in generated evidence. Necessary mathematical definitions belong in the prose as well as their named code definitions; do not erase them in an effort to avoid duplication.

The architecture view should consume the same report after it contains the information that view needs. Reuse the existing Architecture inventory when the whole declaration-placement question becomes useful. No second taxonomy engine is needed to start the next build slice.

CAS remains set aside. The report is a plain record decoded with Effect Schema; a Schema document describing the report is separate future dogfooding work. In-program decoding follows the data wave; later module families stay in their existing plans. No complete-library proof, general liveness claim or verified backend follows from this inventory.

## Authority and source links

- [First implementation receipt](receipt.md), including exact passed checks and the broader build limit.
- [Coordinator's status and serialization plan](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-landing/status-2026-10-01-evening.md), especially §§3–6. This is a historical checkpoint; current heads and receipts decide integration status.
- [Landing plan](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-landing/plan.md), especially §5's measure of useful proof work.
- [Data-wave series and p2 acceptance](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-data-wave/README.md).
- [Decision register](/Users/pooks/Dev/lean4-effect4/docs/core/decisions.md), the sole owner of rulings and row status.
- [Gemini's current chapter draft](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-semantics/gemini/semantics-v1.md) and [authored registry draft](/Users/pooks/Dev/lean4-effect4/docs/research/2026-10-01-semantics/gemini/registry-content.lean).
