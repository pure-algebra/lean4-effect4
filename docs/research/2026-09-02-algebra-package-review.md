# Standalone effect algebra: plan review and first internal literature pass

The existing nine-module algebra is a credible standalone foundation. The
extraction plan needs corrections before execution, and the wider reification
strategy needs a more precise account of which laws survive interpretation.
The literature inspected here supports keeping the foundation small and
placing execution, stored program identity, and host correspondence above it.

Status: **research and proposed refinements, 2026-09-02**. This document reviews
[ALGEBRA-PACKAGE-PLAN](../ALGEBRA-PACKAGE-PLAN.md) and
[REIFICATION-STRATEGY](../REIFICATION-STRATEGY.md). It changes neither plan and
does not lift the extraction hold. The copied plans identify the streams
repository as their living source; this file is the Effect4 review, not a
replacement authority or a frozen implementation contract.

The reviewed Effect4 commit is `686a93e684fa9ca82026faf25f92622216551521`.
Relevant source bytes, local paper identities, inspected sections, and fresh
verification results are recorded in the
[source receipt](2026-09-02-algebra-package-sources.json). Existing unrelated
working-tree changes are listed there. Findings below separate current source
facts, primary literature findings, historical notes, and proposed design.

## Review findings

### R1 — Major: sharing a signature does not transfer every theorem

RS-5 says a program's theorems hold under either realizer because both are
handlers for the same signature. RS-D6 admits the host by corpus conformance.
These are different claims. `Handler S M` supplies operation clauses; it does
not certify a standard's state invariants, operation equations, scheduling
behavior, or trace relation.

The current `interpret_bind` theorem transfers the algebra's sequencing law
under its target-monad assumptions. A theorem about a particular standard's
handler needs that handler's assumptions too. Agreement on finitely many host
tests establishes those observations, not agreement on every operation and
program. [Dijkstra Monads for All, §§6.1–6.2](#l04) explicitly separates an
operation signature from its equations and requires a handler to satisfy
those equations. [Choice Trees, §5.1](#l02) demonstrates why even preservation
of a chosen behavioral equivalence can impose handler restrictions.

**Proposed repair:** separate three records: an operation implementation, a
proof that it satisfies the selected laws, and host conformance evidence at a
pin. A theorem transfers only through the first two, or under an explicitly
assumed host correspondence. Give host tests their own finite scope. For a
safety claim, specify that every admitted host behavior is allowed by the
model under the stated environment relation; retain separate obligations for
termination, fairness, and eventual response. [L06](#l06) supplies the relevant
preservation-direction distinction.

### R2 — Major: the proposed handler tower leaves state transport unspecified

RS-4 mixes three kinds of object:

- `URL` and stateless `Encoding` are pure functions in RS-2 but signature
  summands in the tower.
- `Handler Jobs Configuration` is incomplete if `Configuration` is a state
  type: a handler target must be a type constructor accepting a result type.
- A handler into `StateT StreamsHeap (Program Jobs)` does not compose with a
  Jobs handler by another direct application of `Handler.through`.

The existing
[composition definition](../../Effect4/Algebra/Handler/Composition.lean)
accepts an upper implementation in **`Program T`**. After state is introduced,
the lower interpretation must also be transported through that state layer.
[ITrees, §3.1](#l01) makes the state-threading equation explicit; the local
[PolyFun implementation](#l07) provides a concrete `StateT.mapHom` comparison.

**Proposed repair:** write a typed example with one upper operation, one
stateful middle layer, and one residual operation before freezing the package
extension. Pure helpers should occur in operation implementations rather than
being inserted into the signature sum by implication. Specify initial and
final state and the final result constructor. Keep the existing `through`
unchanged during extraction; assess a separate transport API afterward.

### R3 — Major: domain equations and observation relations have no named home

RS-3 and the law table suggest that standard-specific laws can all be stated
as equations at the free-program face. The current
[`Signature`](../../Effect4/Algebra/Signature.lean) has operations and answer
types, but no equation field. The current
[`Program`](../../Effect4/Algebra/Program.lean) has structural equality; it is
not quotiented by state, stream, or scheduling equations.

An equation such as eliminating a redundant state read can hold after a
particular interpretation without identifying the original operation trees.
Likewise, scoped operations cannot be classified merely by the presence of a
continuation: every `vis` node has one. The algebraicity test concerns the
operation's behavior under sequencing. See [L04](#l04), equation (8).

RS-4's statement that two atoms always commute also needs narrowing. Pure
functions compose, but arbitrary function composition is not commutative.
Independent calculations can be reordered only with the relevant dependency
and observation conditions. A signature sum supplies disjoint operations; it
does not add cross-operation commutation laws.

**Proposed repair:** let each downstream calculus own its operation laws and
its interpretation or observation relation. Initially express standard laws
over those interpretations. Introduce a reusable theory/model-satisfaction
interface only if real consumers need it; do not silently strengthen
`Signature` or reinterpret the existing initiality theorem as initiality for
every standard's equations. Read the sum/tensor source before freezing an
interaction law. Its primary text was not available in the local material
inspected in this pass.

### R4 — Major: Schema generation does not yet establish atom compilation

RS-2 and §5 infer an early route to compiled pure functions from Schema
generation and say Schema generation is closed. The
[TypeScript target record](../TYPESCRIPT-TARGET-DAG.md), “Schema document
generation subgraph,” closes the target checks and representative census but
keeps document revival and decoded-value simulation **required-open**.
Generating a Schema document also does not translate an arbitrary parser or
normalizer's implementation.

**Proposed repair:** give a pure atom a total model function returning an
explicit success/failure result, an admitted implementation language or named
host boundary, and a separate semantic connection to generated execution.
Keep the parser domain and normalization premises on round-trip laws. The
compiler accepting generated code is one check on that connection, not its
proof. This work belongs above the algebra package.

### R5 — Major: the compatibility proposal names the wrong declaration namespace

AP-1 proposes retaining `Effect4.Algebra` as the old namespace. That is the
module-path prefix; the nine modules declare names in **`Effect4`**:
`Effect4.Signature`, `Effect4.Program`, `Effect4.Handler`, and so on.
Replacing old files with imports preserves import paths but does not preserve
these names after a rename to `EffectAlgebra`.

**Proposed repair:** inventory declaration names, constructors, instances,
notation, and module paths separately. Choose either a package move that
initially retains the declaration namespace, or an explicit downstream alias
layer from the actual old names. The new package must own the sole underlying
carrier. Test both old qualified references and old import paths, as well as
the Schema consumer. Decide the compatibility period with those costs visible.

### R6 — Major: evidence portability is larger than the advertised file list

The plan describes three pinned and five seeded counterexamples. The current
[register](../../test/counterexamples/REGISTER.md) has **five PINNED and three
SEEDED** algebra rows. Five rows point into Foldlab evidence rather than five
self-contained local attacks. The plan's assertion that nothing is vendored
does not settle how those witnesses become reviewable from a clean standalone
checkout. The existing axiom report also imports the whole `Effect4` root.

The proposed `ALGEBRA-DAG.md` is described as a ten-edge graph whose edges can
all be carried over closed. The source extraction contract has an algebra
dependency graph; the design basis has a different ten-row graph, with many
non-algebra obligations open. The proposal needs to identify exactly which
graph and receipts it means. Equal declaration counts are not a comparison of
declaration statements or proof dependencies.

**Proposed repair:** preserve original counterexample IDs as provenance even
if local aliases are introduced. Give each witness an explicit disposition:
ported executable witness, permitted pinned source excerpt, or retained
external evidence with a reproducible acquisition requirement. Preserve
source/license attribution. Restrict the new test imports to the algebra;
derive the package assurance record from the exact source contracts and
named receipts. Compare per-declaration signatures and axiom sets under the
namespace mapping. Do not copy an unrelated graph's closure labels.

### R7 — Major: copied repository-relative instructions are ambiguous here

The plans retain “this repository,” “Windows here,” the streams P3 gate,
`Gates/ + bin/`, R0 references, M1/M2, and the web-target survey. Effect4 uses
`scripts/`, and its native P3 is already complete. The local streams checkout
and those streams-specific documents were not found at the expected path.
Thus this review cannot verify the masks, the queue premise, or streams
dependency acceptance against their own authority.

**Proposed repair:** name the repository on each migration step and attach its
actual gate and document. Retain one living plan with a revision link from
copies. Keep AP-4 and the hold unresolved until the operator's intended
continuation is known. Research can continue independently of that hold.

**Verdict:** rework before extraction or standard-law dispatch. The small
package direction is supported; the findings concern its migration contract
and the claims made by consumers, not a demonstrated failure of the current
algebra proofs.

## What the current source supports

The nine module byte counts still match the extraction plan, and their
explicit imports stay within `Effect4.Algebra`. A diff from `f4f55fa` over the
nine modules, three algebra test files, and two contracts is empty. The sole
direct production consumer outside that tree is
[`Schema/EffectfulField.lean`](../../Effect4/Schema/EffectfulField.lean);
the library root also imports the algebra. This refreshes the move's source
boundary, not the status of every surrounding Effect4 subsystem.

The public proof interface already supplies the important distinctions:

| Existing interface | Scope worth retaining |
| --- | --- |
| `Signature`, `Program`, `Handler` | Independent operation universe; common answer/program-result/handler-input universe; well-founded proof syntax with Lean continuations |
| `interpret` and sharp equation theorems | Target-monad hypotheses are visible; convenience versions use `LawfulMonad` |
| `Signature.sum`, `Program.inl/inr`, `Handler.sum` | Binary disjoint composition with projection, injection, and uniqueness laws |
| `IsMonadMorphism`, `ModelMorphism` | One existing law predicate and its first-class wrapper, with source fixed to `Program S` |
| Freeness, interpreter pin, model initiality | Operation agreement is required alongside pure/bind preservation; initiality is among models equipped with an `S` handler |
| `Handler.through` and category laws | Composition across signatures; a monoid only for endomorphisms |

The [adopted design basis](../DESIGN-BASIS.md), DB-01 through DB-07, already
keeps the proof carrier, checked stored data, relational execution, logic, and
state-preserving failure separate. Extract those boundaries as documentation;
do not extract the upper layers as dependencies.

## Internal source inventory

Foldlab's [paper catalogue](/Users/pooks/Dev/foldlab/.reference/catalog/PAPERS.md)
lists 88 entries. **None of the PDFs is present at its catalogue path on this
Mac.** The catalogue is a discovery aid, not evidence that those papers were
read here. Six relevant PDFs survive in `/private/tmp/lean-reification-research`;
their hashes match the earlier source receipts bundled with the reification
skills. Those six were read at the sections recorded below. Their temporary
location remains a reproducibility limitation.

The local Foldlab corpus contains application and tooling repositories. For
this foundation question, the most useful inspected material was instead the
paper catalogue, existing semantic research, the staged algebra reviews, and
the pinned PolyFun source checkout. No host API census or application sample
was treated as evidence for a general algebra law. No source was fetched.

### L01

**Xia et al., Interaction Trees, arXiv:1906.00046v2**, §§2–4, especially
§§3.1–3.3 and Figures 8–13.
[Local PDF](/private/tmp/lean-reification-research/itrees-v2.pdf).

The paper separates event signatures, event handlers, interpreters, and the
relations used to compare computations. State interpretation carries the
state returned by the first computation into the second. Event inclusion and
handler composition have explicit interfaces. General recursive interpretation
uses an iteration operation and its associated theory.

**Design consequence:** retain Effect4's small free-program algebra and use
the paper to specify composition obligations above it. Do not import the
iteration story into the inductive `Program` merely because both interfaces
have `pure`, `bind`, and operations. Signature embeddings and state transport
are useful extension candidates. This paper's Coq proofs were not rebuilt,
and no ITree-to-Effect4 correspondence is established here.

### L02

**Chappe et al., Choice Trees, arXiv:2211.06863v1**, §5.1, Figure 13 and
Lemma 5.1; §5.2.
[Local PDF](/private/tmp/lean-reification-research/ctrees-v1.pdf).

The paper gives a case where introducing a step in an event implementation
breaks preservation of strong bisimilarity. Its simple-handler condition
restores the stated preservation result. It also separates interpreting an
external event from refining an internal branch, with conditions on the
refinement.

**Design consequence:** masks and equivalences need congruence/transport
obligations. “Both are handlers” is insufficient for a law stated at a
behavioral quotient. This does not contradict Effect4's existing structural
`interpret_bind` theorem: the relations and carriers differ. Keep scheduler
decisions and external replies distinct in the upper semantics; this paper
does not require a branching constructor in the standalone package.

### L03

**Fadaei Ayyam and Sammler, HITrees: Higher-Order Interaction Trees,
arXiv:2510.14558v1**, §§2.1–2.2 and Figure 4.
[Local PDF](/private/tmp/lean-reification-research/hitrees-v1.pdf).

The design uses strictly positive input structure and defunctionalized
identifiers to handle problematic higher-order outputs. It supplies both
monadic execution and state-machine reasoning. Its raw tree still includes a
meta-language continuation; defunctionalizing certain outputs is not a claim
that the entire proof representation is portable stored data.

**Design consequence:** DB-05's block-reference approach has relevant prior
art, but its own adequacy theorem is still needed. A reference alone does not
specify captured values, lookup validity, resumption multiplicity, delimiter
behavior, or cleanup state. Keep those in a downstream checked calculus. Do
not replace `Program` with HITrees or add a second handler carrier during the
move. The paper was read; its Lean implementation was not located and rebuilt
in this pass.

### L04

**Maillard et al., Dijkstra Monads for All, arXiv:1903.01237v1**,
§§3.2–3.3 and §§6.1–6.2.
[Local PDF](/private/tmp/lean-reification-research/dijkstra-v1.pdf).

Computation and specification are separate monads connected by an effect
observation. A computation can have different observations, including
different choices about exceptions, nondeterminism, and prior history.
Section 6 gives the sequencing equation for algebraic operations, relates
them to generic effects, and distinguishes `(Sig, Eq)` from `Sig`. Its
handler rule carries a proof obligation `ok(h)` for the chosen equations.

**Design consequence:** make the law-satisfaction and observation boundary
explicit. Keep logic out of the core carrier. Reuse the existing morphism
notion where its source fits; do not call `ModelMorphism S M` a general
morphism between arbitrary monads. This source provides directly inspected
support for the algebraicity discussion while the original Plotkin/Power
papers remain unread locally.

### L05

**Cohen, Grunfeld, Kirst and Miquey, Syntactic Effectful Realizability in
Higher-Order Logic, arXiv:2506.09458v1**, Figure 5, adjacent modality
discussion, and the soundness/instance discussion.
[Local PDF](/private/tmp/lean-reification-research/effhol-v1.pdf).

EffHOL separates computation from specifications and parameterizes the
realizability construction by the chosen computational and logical instance.
Its discussion explicitly allows a modality with a false postcondition to be
derivable for some computations; termination is not automatic.

**Design consequence:** RS-6's separation is useful. Requirements can be
judgments over implementations while the implementation still has a handler.
An Effect4 `wlp` instance, its execution connection, and any totality theorem
belong downstream. The paper neither supplies a universal program reifier nor
chooses the standalone package's syntax. This review did not rebuild the Rocq
artifact or transfer its soundness result.

### L06

**Leroy, Formal verification of a realistic compiler (2009)**, §§2.1–2.2.
[Local PDF](/private/tmp/lean-reification-research/compcert-cacm.pdf).

The paper states correctness through observable behaviors. It distinguishes
behavior equality from an implementation selecting among permitted source
behaviors, and distinguishes a verified compiler from validation of individual
translations with a verified validator.

**Design consequence:** RS-5 and lowering need a named direction of behavior
transfer, with domain and environment assumptions. A corpus match, compiler
acceptance, and a proved validator are different evidence. These obligations
should appear in downstream realizer records rather than in the core
`Handler` type.

### L07

**PolyFun at `3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9`**, local source
comparison; its files were read, not rebuilt.

| Inspected source | Useful interface |
| --- | --- |
| [Lens/Basic.lean](/private/tmp/polyfun-audit.R4fqzR/PolyFun/PFunctor/Lens/Basic.lean) | Forward operation/position mapping, backward answer/direction mapping, identity and composition |
| [Handler/Stateful.lean](/private/tmp/polyfun-audit.R4fqzR/PolyFun/PFunctor/Handler/Stateful.lean) | A stateful handler is an instance of the existing handler into `StateT`; `run_bind` and `run_reindex` expose state threading and fusion |
| [Control/Monad/Hom.lean](/private/tmp/polyfun-audit.R4fqzR/PolyFun/Control/Monad/Hom.lean) | A chosen general monad map is explicit data; `StateT.mapHom` transports it and has identity/composition laws |
| [lakefile.toml](/private/tmp/polyfun-audit.R4fqzR/lakefile.toml) | Mathlib and cslib dependencies at the recorded release |

**Design consequence:** borrow the interface questions, not the dependency
tree. First try a consumer-local state transport over the existing interpreter.
If two independent consumers need arbitrary monad-map composition, propose
one general abstraction with a conversion from the existing `ModelMorphism`,
not an unrelated second law predicate. A signature-map proposal should keep
answer transport explicit and prove its interaction with `interpret`.

### Existing internal studies: useful, but historically scoped

The [ITree/CTree literature notes](/Users/pooks/Dev/foldlab/docs/entity-store/research/itrees-ctrees-literature-notes.md)
identify Yoon–Zakowski–Zdancewic's layered-interpreter work as the next source
for transformed targets and relational reasoning. That row is a secondary
lead until the primary text is available.

The staged [handler review](/Users/pooks/Dev/foldlab/.staging/algebraic-review/handlers-semantics.md)
and [program-carrier review](/Users/pooks/Dev/foldlab/.staging/algebraic-review/prog-carrier.md)
explain why interpreter uniqueness, operation agreement, and signature
injections matter. Several reported algebra omissions have since been
addressed by Effect4's current source and batteries; do not reopen them from
the historical prose. The synthesis
[THE-ALGEBRA](/Users/pooks/Dev/foldlab/.staging/algebraic-review/THE-ALGEBRA.md)
labels itself pre-grade and is not a superseding design ruling.

Foldlab's [counterexample register](/Users/pooks/Dev/foldlab/.staging/effect-core-v1/COUNTEREXAMPLES.md)
records `EC1-CE041` and `EC1-CE045`: an inadequate target can typecheck while
failing catch or losing the state finalization requires. These are historical
receipts, not newly rerun witnesses here. Their design consequence already
appears in Effect4 DB-07: state produced before failure must remain available
to cleanup. `StateT` alone does not settle failure behavior; the complete
result/transformer order matters.

## Proposed standalone boundary

This is a research recommendation for a later contract, not an expansion of
the extraction fence.

| Layer | Owns | Suggested disposition |
| --- | --- | --- |
| Standalone algebra | Existing signatures, proof programs, handlers, sums, morphism wrapper, interpretation and universal laws | Move the nine modules and their evidence with meaning unchanged |
| Small composition extensions | Explicit signature maps and coherence; transport of an interpreter through state when needed | Separate proposal after a typed consumer example; no speculative hierarchy |
| Standard-specific calculus | Value types, pure functions, operation laws, object identities, state and observations | Downstream library depending on the algebra |
| Stored-program representation and execution | Finite checked syntax, captures and block references, cycles, decisions, traces, failure and finalization | Explicit downstream owners with bridges to the applicable proof fragment |
| Logic and realizers | Partial/total correctness, target lowering, host admission and conformance | Separate connections with their own assumptions and evidence |

“Zero dependencies” should mean no third-party Lake dependencies, with the
Lean toolchain/core/Std boundary stated separately. Test and audit tooling
should be separated from public imports. Web values, Effect Schema, masks,
job queues, and TypeScript code must not become prerequisites of the generic
foundation. A pure value/codec library need not depend on effect syntax merely
because a larger standard later uses both.

Start with structural equality and the existing universal laws. Let consumers
state richer equations after interpretation. This preserves the useful current
foundation while leaving room for a later reusable theory interface if actual
examples justify one.

## Next internal reading and design questions

| Order | Source or local material | Question to resolve | Present evidence |
| --- | --- | --- | --- |
| 1 | Yoon, Zakowski and Zdancewic, *Formal Reasoning about Layered Monadic Interpreters* (2022) | What is the smallest transport and relational API needed once a tower contains state? | Secondary local notes; primary not read |
| 2 | Hyland, Plotkin and Power, *Combining Effects: Sum and Tensor* (2006) | Where do per-signature equations and cross-effect commutation live? | Plan bibliography lead; primary not read |
| 3 | Plotkin and Power (2002/2003); Plotkin and Pretnar (2013) | Which standard operations satisfy the sequencing law, and which handler laws are required? | Direct supporting discussion in L04; originals not read |
| 4 | Wu–Schrijvers–Hinze (2014), Piróg et al. (2018), and the scoped/higher-order papers named by RS | What must a block-reference encoding retain to justify scope laws? | HITrees primary plus existing Effect4/Foldlab records; listed originals not read |
| 5 | The fusion reference named in RS; local frontier survey's separate *Fusion for Free* lead | Which law and observation justify a proposed stream optimization? | Bibliographic identity of the RS Yang/Wu entry still unverified; do not conflate the titles |
| 6 | Streams R0, M1/M2 definitions, job-queue model and web-target survey | Which queue decisions, object identities and observation distinctions are actually promised? | Required local context unavailable at the expected checkout path |

Before designing additional public abstractions, work through three small
examples: a disjoint pair of signatures with explicit embeddings; a stateful
handler over a residual signature; and a scoped body that fails after changing
state needed by cleanup. Each should state exactly what is compared before
and after interpretation. These examples can decide whether a generic
extension is worthwhile without importing a complete runtime into the package.

The remaining compiler/evidence-passing and equational-programming entries in
RS are later reading leads. This first pass does not mark the entire literature
ledger read or verified.

## Verification performed

| Check | Result and scope |
| --- | --- |
| `lake build Effect4Test.Algebra.ExtractionContract Effect4Test.Algebra.RetainedClosureContract Effect4Test.Algebra.AxiomReport` | Exit 0; narrow targets and their dependency closure |
| `lake env lean Effect4Test/Algebra/ExtractionContract.lean` | Fresh invocation, exit 0 |
| `lake env lean Effect4Test/Algebra/RetainedClosureContract.lean` | Fresh invocation, exit 0 |
| `lake env lean Effect4Test/Algebra/AxiomReport.lean` | Fresh invocation, exit 0; 60 distinct named receipts; union of reported axioms is `propext`, `Quot.sound` |
| Source/import refresh and comparison with `f4f55fa` | Nine module sizes unchanged; no explicit external imports; selected algebra source, tests and contracts unchanged |
| Six local paper hashes | All match the earlier local source receipt; no paper downloaded |
| Review-document integrity | All 32 local links/anchors resolve; all 48 recorded source/text hashes match; inspected PolyFun files match its recorded commit |
| `./scripts/check-internal-citations.sh` and `git diff --check` | Exit 0; citation gate is a lexical check, supplemented by the explicit link checks above |

These checks do not establish a whole-repository build, an exhaustive new
declaration audit, a third-party mechanization build, standard conformance, or
consumer compatibility after a move. The extraction remains unexecuted.
