# Agent routing and continuity

Effect4 uses five authored instruction files. They separate repository-wide
law from source, test, host, and generated-output work without repeating the
same rule in several directories.

## Instruction hierarchy

| File | Applies to | Additional authority |
| --- | --- | --- |
| `AGENTS.md` | the whole repository | global development order, semantic boundaries, compatibility, claims, and handoffs |
| `Effect4/AGENTS.md` | Lean library declarations and proofs | source ownership, declaration admission, and proof-graph obligations |
| `Effect4Test/AGENTS.md` | Lean tests and proof receipts | attacks, counterexample witnesses, and trust evidence |
| `harness/AGENTS.md` | host and TypeScript evidence | exact target profiles, runtime checks, diagnostics, and mutations |
| `generated/AGENTS.md` | deterministic machine projections | regeneration and drift rules for declarations, obligations, and closure snapshots |

The root file applies everywhere. The nearest boundary file adds rules for its
own work but does not restate or weaken the root. A conflict is an ownership
error: stop and repair the routers instead of choosing whichever wording is
more convenient.

These five files are written and reviewed by people. No generator may create,
replace, or edit an `AGENTS.md` file. Effect4 does not place an instruction
file in every category directory because that would fragment shared proof and
representation rules. Add another boundary router only when a directory gains
a distinct owner, trust boundary, or toolchain that the existing five cannot
route accurately.

## Authored facts and generated facts

Instructions and semantic decisions remain authored. Machine projections
make those decisions inspectable and detect drift; they do not decide policy.

| Authored input | Machine projection |
| --- | --- |
| public Lean declarations and theorem statements | declaration and signature snapshot |
| `PORT-MANIFEST.md` source rows and dispositions | existing-type and source-disposition snapshot |
| contracts and declared proof obligations | per-type obligation ledger |
| theorem names, axiom receipts, and counterexample rows | per-type closure snapshot |
| target profile and export census inputs | surface-coverage snapshot |

The projections live under `generated/`. Their generator, canonical inputs,
and exact regeneration command must be recorded before the output becomes a
gate. The gate regenerates into a clean tree and compares bytes. A drift
failure is repaired in the authored input or generator, never by editing the
projection.

`generated/AGENTS.md` is the directory's one authored routing file. It is not
a projection and is excluded from replacement by every generator.

## Existing-type annotation

Every public type has one disposition row before implementation starts. This
includes a type already present in Foldlab, a type retained behind a
compatibility adapter, and a new native Effect4 type. The authored row records:

1. its stable public Lean name and owning module;
2. whether it is the canonical carrier, a view, an adapter, a separate
   calculus, a derived expansion, a foreign boundary, or target-only data;
3. for a port, the source repository pin, path, retained span, and digest;
4. for a native declaration, the contract that first fixes its role;
5. the source disposition from `PORT-MANIFEST.md`;
6. any type it replaces, views, embeds into, or is intentionally separate
   from; and
7. the identifier of its required proof graph.

The generated declaration snapshot must join every exported type to exactly
one such row. An unannotated exported type, two canonical owners for one
semantic role, or two rows claiming the same source declaration is a gate
failure.

An additional representation is permitted only when its role is distinct and
named. Examples are raw versus checked input, syntax versus denotation, and a
downstream compatibility view. Its row names the canonical owner and the
conversion, embedding, erasure, or refusal theorem that relates the two.
Renaming an existing carrier or copying its constructors does not establish a
new role and is rejected as duplication.

## Per-type proof graph

Cutover is decided per public type, not per directory or implementation
milestone. Each annotated type receives a graph whose required edges cover:

| Edge | Required evidence |
| --- | --- |
| identity | unique owner, declaration signature, source disposition, and digest where ported |
| construction | constructors or checked admission, invariants, and rejection behavior |
| semantics | denotation or operational judgment and the observations it exposes |
| laws | the algebraic equations claimed by the public API |
| representation | normalization, erasure, decoding, or round-trip laws that the type claims |
| counterexamples | registered witnesses for rejected stronger statements and their repaired gates |
| bridges | embeddings, interpreter agreement, compatibility, and declared loss where another face exists |
| targets | lowering, typechecking, byte stability, and runtime evidence when the type crosses a host boundary |
| trust | axiom receipt and an explicit split between proved, model-checked, tested, assumed, and unknown facts |
| coverage | public exports and overloads accounted for by the applicable profile |

Each edge is either `required-open`, `required-closed`, or `not-applicable`
with an authored reason. Missing rows are open. A test pass cannot close a
theorem edge, and a theorem about the Lean model cannot close a host-observation
edge. Refusal of a target spelling remains a profile decision with evidence;
it does not erase semantic obligations of the underlying Effect4 type.

The closure snapshot is generated by joining declarations, dispositions,
obligations, theorem and axiom receipts, counterexample registrations, and
target coverage. It may report closure but cannot contain a manual completion
override. A type cuts over only when every required edge is closed. A category
or repository cuts over only when all public types in its mechanically derived
export set are closed and that export census itself is current.

## Counterexample route

`test/counterexamples/REGISTER.md` is the only stable-ID registry for
counterexamples that can change a declaration, theorem, admission rule,
classifier, profile, or cutover decision. IDs are never reused.

- The breaker records the attacked statement, smallest witness, evidence
  command, assumptions, forced repair, and status in the central register.
- An executable Lean witness lives under
  `Effect4Test/Counterexamples/<Area>/` near the attacked library area.
- A host negative or mutation fixture lives under the relevant `harness/`
  area.
- A prose contract lives under `test/contracts/` and links the same ID.
- The register links to each witness. Witnesses are not copied into planning
  prose and remain executable after the repair lands.

A new carrier or bridge cannot close its proof graph until its required
counterexamples have stable IDs and the repaired declaration mechanically
rejects them. Counterexamples that distinguish refusal, typed failure, defect,
interruption, and live frontier remain separate witnesses.

## Long-run work sequence

A fresh source task reads the root router, its nearest boundary router,
`PLAN.md`, the relevant source-disposition row, the frozen contract, and the
central counterexample rows. It then checks the generated closure snapshot and
reproduces the narrow command named by the open edge.

A handoff reports the exact type IDs and proof edges changed. Statements such
as “the category is done” are insufficient unless the generated export census
and closure snapshot have no required-open rows for that category.
