# Agent routing and continuity

Effect4 uses five authored instruction files. They separate repository-wide
law from source, test, host, and generated-output work without repeating the
same rule in several directories.

## Instruction hierarchy

| File | Applies to | Additional authority |
| --- | --- | --- |
| `AGENTS.md` | the whole repository | global development order, semantic boundaries, compatibility, claims, and handoffs |
| `Effect4/AGENTS.md` | Lean library declarations and proofs | source ownership, declaration admission, assurance routes, and proof-graph obligations |
| `Effect4Test/AGENTS.md` | Lean tests and proof receipts | attacks, counterexample witnesses, and trust evidence |
| `harness/AGENTS.md` | host and TypeScript evidence | exact target profiles, runtime checks, diagnostics, and mutations |
| `generated/AGENTS.md` | deterministic machine projections | regeneration and drift rules for declarations, obligations, and assurance snapshots |

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
| contracts and declared proof obligations | graph obligations and leaf-receipt ledger |
| theorem names, axiom receipts, counterexample rows, and leaf receipts | per-declaration assurance snapshot |
| target profile and export census inputs | surface-coverage snapshot |
| vendored pinned Effect runtime source and authored row anchors | runtime mechanism census, joined to test-side witness rows (`docs/RUNTIME-COVERAGE.md`) |

The projections live under `generated/`. Their generator, canonical inputs,
and exact regeneration command must be recorded before the output becomes a
gate. The gate regenerates into a clean tree and compares bytes. A drift
failure is repaired in the authored input or generator, never by editing the
projection.

`generated/AGENTS.md` is the directory's one authored routing file. It is not
a projection and is excluded from replacement by every generator.

## Public declaration records

Every planned public declaration is covered by one lightweight authored record
before implementation. The record names its intended stable Lean name and
module, unique owner and role, ported or native origin and disposition,
relationship to any canonical owner, and assurance route. That relationship
is the duplication check: `canonical`, `view`, `adapter`, `separate-calculus`,
`derived`, or `helper`, with the related public declaration named whenever the
record is not canonical.

Routine constructors, projections, and theorems may inherit from their public
type when the generated declaration snapshot still emits and joins their
individual records. Inheritance deterministically expands the named type or
contract row's owner, disposition, duplicate-prevention relationship, and
assurance route across those declarations. It avoids repeated prose; it does
not permit an exported declaration to disappear from the census. The
pre-implementation type or contract row supplies the inherited coverage, and
the post-elaboration snapshot resolves it to exact declarations.
A source stub with no exported declarations needs neither a declaration record
nor a proof graph.

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
7. its assurance route: either its own proof-graph identifier, or a local
   leaf-receipt identifier marked `standalone` or linked to the shared parent
   graph edge to which those receipts contribute.

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

## Assurance threshold

A public type or declaration does not receive a proof graph merely because it
is public. Use the lightest route that accounts for its actual claims. Attach
one graph to the smallest stable semantic or cutover owner; its public helper
operations and theorems contribute receipts to that graph rather than each
receiving another graph.

A `leaf-receipt` route is allowed only when all of the following hold:

1. the declaration is a nonrecursive finite alphabet or passive value record;
2. construction has no checked invariant beyond the field or constructor
   types;
3. it owns no admission, refusal, diagnostic, judgment, denotation,
   interpreter, handler, reification, refinement, generation, or semantic
   bridge;
4. it states no nontrivial composition law, recursive invariant, protocol
   transition law, or external semantic equivalence; and
5. it does not independently own a source-retirement, profile-admission, or
   cutover claim. Inclusion in an aggregate export census, or contribution
   through a named parent graph, does not make a leaf an independent owner.

Such a leaf closes with local receipts for the public facts it actually
claims: exact declaration and recursor signatures, constructor census and
`Nodup` where finite, encode/decode inverse or injectivity where exposed,
declared separation or embedding lemmas, and axiom output for exported
theorems. A standalone leaf records that it has no parent. A leaf that
contributes evidence to a graph-bearing family must link its receipts to one
named edge of that graph. The leaf does not get an empty ten-edge graph filled
with `not-applicable` rows.

A `graph` route is required as soon as the declaration or its owning type does
any one of the following:

- admits, rejects, refuses, or classifies effectful programs or failures;
- defines a typing or operational judgment, denotation, observation,
  transition system, interpreter, or handler;
- owns a semantic reification, refinement, lowering, or generation relation,
  or claims a relation to generated code;
- carries nontrivial effect composition, recursion, scoped control, resource
  invariants, or protocol-state invariants;
- claims compatibility or semantic equivalence across a Lean, Foldlab, host,
  or external-library boundary; or
- independently owns a source-retirement, profile-admission, or cutover claim
  that is not wholly accounted for by a named parent graph.

Escalation is monotone. Before a leaf acquires the first graph-bearing claim,
change its authored assurance route, name the new obligations and applicable
counterexamples, and freeze the breaker packet for that change. Every former
leaf receipt, counterexample, and evidence link remains required and is mapped
to a named graph edge. A receipt may disappear only through an explicit
supersession ruling that names its replacement and explains the change.
Constructor count, a short proof, or automatic `deriving` never decides the
route.

The current Schema representation split illustrates the threshold:

| Type | Route now | Reason and receipts |
| --- | --- | --- |
| `Effect4.RepresentationTag` | own proof graph | It is the canonical source-facing discriminator for the reification census, and its coverage is a direct cutover condition. Its graph marks identity, construction, representation, counterexample, trust, and coverage as required; at the tag-only stage it marks semantics, laws, bridges, and targets `not-applicable` with authored reasons. No edge may be omitted. |
| `Effect4.UnionMode` | leaf receipt under the `RepresentationTag` graph | The two constructors are passive mode labels. Freeze its signature, census, `Nodup`, and any exposed spelling inverse. |
| `Effect4.CheckTag` | leaf receipt under the `RepresentationTag` graph | It is currently only the two-value lexical tag alphabet, not the Schema checking judgment or admission classifier. Escalate before it controls acceptance, refusal, or diagnostics. |
| `Effect4.LiteralKind` | leaf receipt under the `RepresentationTag` graph | It is a finite kind label. Record its signature, census, `Nodup`, and separation facts. |
| `Effect4.EnumValueKind` | leaf receipt under the `RepresentationTag` graph | Its finite embedding into `LiteralKind` is a local theorem receipt; it needs its own graph only if that mapping later carries denotational or generated-target meaning. |
| `Effect4.PropertyKeyKind` | leaf receipt under the `RepresentationTag` graph | It is a passive three-value key-kind alphabet, closed by its signature, census, `Nodup`, and claimed spelling laws. |

All six still require distinct existing-type rows and duplicate-prevention
relationships. The five leaf rulings describe their present API; a later
semantic use triggers escalation rather than being smuggled through the
parent graph.

## Graph-bearing owner closure

Assurance is decided per public declaration and its owning route, not per
directory or implementation milestone. A graph-bearing owner receives a graph
whose applicable edges cover:

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

The assurance snapshot is generated by joining declarations, dispositions,
graph obligations or leaf receipts, theorem and axiom receipts,
counterexample registrations, and target coverage. It may report closure but
cannot contain a manual completion override. A graph-bearing owner cuts over
only when every required edge is closed. A standalone leaf closes when all
declared local receipts are closed; an attached leaf additionally requires
its named parent-edge link to be closed. A category or repository cuts over
only when every exported declaration in its mechanically derived census joins
exactly one closed owner route, every public type row is closed by its declared
route, and that export census itself is current. Project-wide aggregation does
not promote a leaf to a graph.

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

A new graph-bearing carrier or bridge cannot close its proof graph until its
required counterexamples have stable IDs and the repaired declaration
mechanically rejects them. A leaf counterexample that changes a public
declaration or cutover decision is still registered, and may force escalation.
Counterexamples that distinguish refusal, typed failure, defect, interruption,
and live frontier remain separate witnesses.

## Long-run work sequence

A fresh source task reads the root router, its nearest boundary router,
`PLAN.md`, the relevant source-disposition row, the frozen contract, and the
central counterexample rows. It then checks the generated assurance snapshot
and reproduces the narrow command named by the open graph edge or leaf receipt.

A handoff reports the exact declaration and type IDs, assurance routes, and
graph edges or leaf receipts changed. Statements such as “the category is
done” are insufficient unless the generated export census and assurance
snapshot have no required-open rows for that category.
