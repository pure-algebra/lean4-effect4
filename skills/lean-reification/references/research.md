# Research and design basis

The skills organize a chain of distinct claims: intended behavior, program
representation, semantic interpretation, Lean proof, transformation, and host
observation. The strongest lesson from the reviewed work is that a correct
result at one link does not establish the next link.

This is a research-based workflow, not a new formalization of EffHOL or an
audit certificate for Effect4. It supplies no new semantic implementation.

## Review scope and source status

The Effect4 review uses commit
`f4f55fae372be373465a9d7049f1c4721073f1ad`, including the trust repair at
`a100daf`, the Scope implementation, and its later runtime-census join. The
Foldlab review uses commit `4005d34f249cda25134ac2bddff514e3a068bc1e` for the
inspected tracked files. [Source records](sources.md) include hashes and the
distinction between available files, published research, and prior reports.

The review followed the architecture and authority records, then inspected
representative source definitions, theorem statements, counterexample records,
and acceptance scripts. It includes the algebra, Schema recursion and exact
views, effectful field generation, state/failure and Scope boundaries, and the
trust-gate repair. It is not a fresh proof check of every declaration. Prior
build receipts retain their stated date and scope; this task's verification
concerns the skill pack and its behavior.

The literature review read the main EffHOL definitions, typing and deduction
rules, soundness statement/proof construction, instance conditions, and stated
limitations, together with the authors' proof sources. It also examined the
relevant semantics and validation sections of the sources below and Foldlab's
existing research notes. No third-party proof development was rebuilt here.

## What EffHOL contributes

[The adaptation record](effhol.md) contains the paper-specific account and
exact limits. The resulting design choice is to place an explicit specification
relation beside an explicit program semantics. The skills do not infer stored
syntax, serialization, host compatibility, or automatic extraction of arbitrary
Lean proofs from that inspiration.

This agrees with Effect4's adopted `docs/DESIGN-BASIS.md`, particularly DB-01
through DB-07. There is no evidence here for replacing its chosen carriers with
a larger foundational framework. The needed work is to state and prove the
connections the existing decomposition already requires.

## Supporting literature and its use

These are short source findings followed by design decisions for this pack.
They are not claims that the cited implementation has been ported into Lean
or related to Effect4.

| Source | Finding used | Consequence for the skills |
| --- | --- | --- |
| [Dijkstra Monads for All](https://arxiv.org/abs/1903.01237v1), Introduction and Sections 2–3 | Computation and specification monads are distinct and connected by an effect observation; different observations can describe the same computation. | Model must choose the specification and connection explicitly, including the treatment of nondeterminism and history. |
| [Interaction Trees](https://arxiv.org/abs/1906.00046v2), Sections 2–4 and 7 | Event-based recursive computations, interpreters, and behavioral equivalences provide a compositional semantic framework. | Reuse the distinction between program structure and observed behavior; require an actual bridge rather than declaring a graph or free program to be an ITree. |
| [Choice Trees](https://arxiv.org/abs/2211.06863v1), Sections 2–4 | Internal branching is represented separately from external events and receives a transition/equivalence theory. | Keep decision sources and quantifiers visible; do not silently replace a nondeterministic contract with one chosen run. |
| [HITrees](https://arxiv.org/abs/2510.14558v1), Sections 2–5 | Inductive higher-order input structure and defunctionalized output make higher-order effects expressible in a Lean development. | Consider defunctionalization and explicit scope structure. The paper is prior art, not a reason to adopt a dependency or claim that all higher-order code has become portable data. |
| [Leroy, compiler verification](https://xavierleroy.org/publi/compcert-CACM.pdf), Section 2 | Correctness is tied to observable behaviors and a precise preservation direction; verified compilers and verified validators are distinct routes. | Target must state the quantifiers and separate universal transformation theorems from acceptance of a particular source/target pair. |
| [Chockler et al., coverage](https://doi.org/10.1007/3-540-44585-4_7), Introduction and coverage definitions | Successful verification can leave parts of a model irrelevant to the specification; controlled changes expose that insensitivity. | Breaker challenges adequacy after success and records which observations or clauses the tests fail to distinguish. This is evidence of sensitivity, not proof that a specification is complete. |
| [Loopy](https://arxiv.org/abs/2311.07948v1), Section 3 | Candidate invariants are combined, filtered by a symbolic checker, and repaired using feedback. | Proof search should validate small ingredients and their usefulness before more generation. The skill imposes no universal attempt count or promised speedup. |
| [LeanDojo](https://arxiv.org/abs/2306.15626v2), retrieval and evaluation sections | Accessible-premise analysis supports retrieval, and evaluation on novel premises tests a different generalization claim. | Use exact local context, preserve independent evaluation inputs, and do not treat remembered or unavailable declarations as usable facts. |
| [Lean's versioned reference](https://lean-lang.org/doc/reference/4.33.0/Axioms/) | Logical assumptions and native evaluation have inspectable dependency consequences. | Proof and Audit inspect actual compiled dependencies at the project's pin and keep logical, compiler, and host trust separate. |

Foldlab's staged model-scout study already connects the last three research
themes to its development loop. This pack reuses the useful process decisions:
small candidates, explicit evidence kinds, counterexample retention, and local
repair. It does not promote that staged system, its budgets, or its empirical
adoption thresholds into general project law.

## Lessons from the actual work

| Reviewed evidence | What it demonstrates | Skill response |
| --- | --- | --- |
| Effect4 `Program.lean`, `Handler.lean`, and `DESIGN-BASIS.md` DB-01/02 | The well-founded continuation tree is a proof carrier. It has no stored-program serialization or finite-node guarantee. | Model separates durable syntax and proof structure and demands an explicit connection. |
| Foldlab `Wp.lean`: `wpAux_append`, `wp_iff_wlp_and_total`; Effect Core `EC1-R31`, `EC1-CE046/047` | The table sequencing specialization needs a valid prefix context and the answer history it produced. A familiar logic rule cannot erase those premises. | Model reuses the existing logic and checks local instantiation obligations; Proof locks the premises. |
| Effect Core `EC1-CE041/045` and their linked witnesses | A handler target can support catch while discarding the state required for cleanup on error. Merely sequencing a finalizer through short-circuiting bind is inadequate. | Model tests the result shape before proving scope laws; Breaker uses information-loss witnesses. |
| Effect Core `EC1-CE042/048`; Effect4 DB-03/04 | Different permitted replies can produce different outcomes. A live approximation is not a stable refusal or a divergence proof. | Model exposes decisions and frontiers, and Audit keeps bounded and all-runs claims separate. |
| Effect4 `E4-SCHEMA-CE-033/043/047/048` | Nested annotation schemas, checks, child records, and stored reference entries all matter to recursive coverage. | Contract inventories semantic children; Breaker uses distinguishable buried witnesses; Target checks an independent census. |
| Effect4 `E4-SCHEMA-CE-025/040/042` | Interface shape, document-codec acceptance, and reference revival have different conditions. | Contract and Target name the exact layer and direction of compatibility. |
| Effect4 `E4-SCHEMA-CE-044/045/046` | Absent focus, present-empty data, duplicate entries, and raw spelling are observable distinctions. One codec inverse does not establish an exact update view. | Model retains raw information; Target chooses exact or normalized reconstruction explicitly. |
| `docs/TYPESCRIPT-TARGET-DAG.md`, Schema document generation subgraph | Finite host checks and generated coverage can exist while revival/decoded-value simulation remains open. | Audit reports each edge independently; passing the host corpus does not close the semantic bridge. |
| `docs/SCOPE-DAG.md`, named boundaries and generated assurance section | A model of finalizer names and results deliberately leaves host key freshness, cross-scope meaning, and full fiber behavior outside its claim. Some authored status rows predate later implementation/census work. | Audit follows the actual artifact and current join; neither an old red label nor a new theorem count determines whole-category closure. |
| Trust repair `a100daf`, `AxiomGate.lean`, and its self-test | Numeric projections broke scanning; derived equality concealed partial machinery; exact string/audit boundaries reached choice; upstream failure could prevent a detector running. | Proof inspects compiled dependencies; Breaker checks accepted, rejected-for-the-right-reason, and restored cases; Audit rejects skipped-input success. |
| `docs/AGENT-ROUTING.md` and the collision history in `COORDINATION.md` | Duplicate ownership and blanket proof graphs cause avoidable work, while unjoined declarations escape assurance. | Contract records one owner and selects graph or leaf receipts from the claim. |

These are evidence-backed examples, not an exhaustive enumeration of all
possible defects. Their generalization is the decision process in the skills.
The live project records remain authoritative for implementation and closure.

## Why seven skills

Each boundary has a different trigger and finish condition. Contract fixes the
question; Model chooses a representation capable of expressing it; Breaker
tests its adequacy independently; Proof establishes frozen judgments; Target
connects artifacts and execution; Audit evaluates the whole requested claim.
The router resumes at the appropriate boundary.

The existing Foldlab Lean suite already handles bootstrap, general invariant
modeling, proof tooling, and assurance review. Repeating that entire suite would
increase ambiguity. These skills specialize it around program reification and
provide self-contained records when another project lacks equivalent ones.

References hold conditional detail, while entry points remain short. Passive
finite leaves and unchanged proof bodies have explicit short routes. The suite
does not prescribe a new algebra, a dependency, a global axiom ceiling, a
universal graph size, or a fixed model-search budget.

## Evaluation standard

Structural validation checks names, frontmatter, links, metadata, and installed
bytes. It does not establish good judgment. The behavioral evaluation therefore
uses realistic raw packets, independent agents, hidden scoring criteria, and
positive controls as well as misleading claims. It checks artifact decisions
and claim boundaries rather than exact wording. The recorded outcomes are in
[the evaluation report](../evaluations/RESULTS.md).
