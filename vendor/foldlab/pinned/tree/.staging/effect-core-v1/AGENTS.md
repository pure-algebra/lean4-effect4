# Effect Core v1 — lane routing

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

This file governs only `.staging/effect-core-v1/`. It is an operating router,
not a semantic specification and not a claim record. Root `AGENTS.md`,
`library/cas/AGENTS.md`, and `library/effects/AGENTS.md` remain authoritative
for estate conduct, the store language, and the Effect host respectively.

## Read order

For any Effect Core v1 task, read only this sequence before following a more
specific link:

1. root `AGENTS.md`;
2. this file;
3. `README.md` for packet status and file roles;
4. `PLAN.md` for scope and slice order;
5. `EXISTING-TYPES.md` before naming or changing a carrier;
6. `EXHIBITS-REVIEW.md` before relying on either staged Lean exhibit;
7. `COUNTEREXAMPLES.md` before weakening, repairing, or closing a statement;
8. `TYPE-CLOSURE.md` before freezing or approving cutover for a type;
9. `ORGANIZATION.md` before adding a document, generator, ledger, or gate;
10. the one contract/proof/checklist document that owns the current task; and
11. the generated status and obligation manifests once those exist.

Do not preload every packet document. The manifest and current slice must make
the required read set finite and explicit.

## File authority

| File | Owns | Must not own |
| --- | --- | --- |
| `PLAN.md` | scope, premises, slice order, literature roles, claim route | carrier fields or theorem bodies |
| `EXISTING-TYPES.md` | annotations and reuse/bridge decisions for declarations already present | a duplicate declaration or proof |
| `ALGEBRA.md` | proposed carriers, syntax, operations, and semantic faces | public Effect surface closure |
| `CLASSIFICATION.md` | denotational abstract domains and transfer obligations | source-tooling verdicts |
| `CONTRACT-PACKET.md` | quantified clauses and breaker falsifiers | implementation choices that weaken a clause |
| `PROOF-DAG.md` | declaration dependencies, theorem signatures, and proof routes | proof scripts or external-tool trust |
| `REIFICATION-CHECKLIST.md` | pinned public-surface census and total structural disposition | Semantic Model meaning |
| `EXHIBITS-REVIEW.md` | applicability of the two staged Lean exhibits, refusal ownership, and nondeterminism ruling | promoted declarations or a global determinism theorem |
| `COUNTEREXAMPLES.md` | stable counterexample IDs, attacked statements, witnesses, evidence states, and register completeness | proof bodies, negative-fixture semantics, or replacement-design sufficiency |
| `TYPE-CLOSURE.md` | per-type proof graph and mechanical full-cutover predicate | theorem bodies or source census facts |
| `ORGANIZATION.md` | ownership, generated facts, gates, resume protocol, promotion shape | semantic definitions |
| `WORKSHOP-RESULTS.md` | exact local probe commands and observations | promoted claims or frozen declarations |
| `workshop/` and `*.lean` exhibits | disposable falsification/proof experiments | canonical library code or authoritative definitions |

If two files appear to own the same fact, stop and repair the ownership table;
do not copy the fact into both.

## Current production boundary

- The packet is pre-grade and may be revised through review.
- Scratch probes may be created under this directory and must be reported in
  `WORKSHOP-RESULTS.md` if they influence a decision.
- No declaration moves into `formal/` or `library/` until the relevant slice
  has been grilled and its public signature has been frozen.
- No generated path proposed by `ORGANIZATION.md` is created merely because it
  is named there. Generation begins only after its schema and consumer are
  accepted.
- The first implementation slice creates approved file stubs only. It adds no
  carrier, operation row, protocol byte, adapter behavior, or proof claim.
- The pinned CAS carrier and canonical `PProg` identity are not replaced.

## Existing-type rule

Before introducing a proposed type, operation, theorem family, or target
carrier:

1. look it up in `EXISTING-TYPES.md`;
2. record the exact existing declaration or public symbol, if any;
3. choose one annotation disposition: reuse, restrict, bridge, embed,
   separate-calculus, target-only, or proposed-new;
4. name the declaration that owns meaning and the declaration that owns bytes;
5. state why reuse alone is insufficient when choosing `proposed-new`; and
6. add a falsifier that would expose accidental duplication or semantic drift.

An unannotated relevant declaration is a gate failure. A comment saying “new
version” is not an annotation.

## Role separation

- The **breaker** owns quantified clauses, adversarial examples, and the
  frozen statement. The breaker does not implement the checker it attacks.
- The **builder** works only against a reviewed contract and records exact
  diagnostics when a statement is unimplementable as written.
- The **reviewer** checks Effect-source fidelity, existing-carrier reuse,
  proof adequacy, and claim scope independently.
- The **surface hoover** inventories source declarations but makes no
  denotational judgment.
- The **Lean model** owns meaning; the generated TypeScript and Effect runtime
  are separately related targets.

One person or agent may occupy different roles in different slices, but not
breaker and builder for the same falsifier battery.

## Worktree and phase protocol

The clean packet-baseline commit is immutable. The coordinator alone owns the
integration worktree and reconciles shared packet documents and generated
sidecars there. Each slice uses separate breaker, builder, and reviewer
worktrees with recorded base commits, packet digests, file fences, and named
checks. The breaker lands and freezes red controls first; the builder starts
from their accepted commit and cannot weaken them; the reviewer starts fresh
from the proposed integrated commit, reruns the evidence, and does not repair
the work under review. Every role records attributable clean/dirty state at
start and handoff. Two roles never edit the same authority file concurrently.

Work proceeds broad before deep: seal the packet baseline; create file stubs
only; sweep all types, operations, profiles, proof edges, and controls for
ownership and gaps; connect the pending module/generator/gate skeleton; then
close one dependency-ready type vertically through breaker, builder, and
reviewer. Only individually closed type rows may enter a profile cutover.

## Language-neutral protocol rule

The future `library/effect-protocol/` manifest owns stable portable IDs,
canonical bytes, and named profile membership. Lean owns admission, meaning,
reference interpretation, and proof. Generated Effect TypeScript bindings and
an authored Effect adapter consume one profile; they do not own protocol
identity, and Effect is not the only permitted consumer. Proof status, source
census, LSP coverage, and runtime evidence are generated sidecars keyed by the
protocol digest, never manifest fields and never generated AGENTS prose.

## Ensuring information rule

`ensuring` is an exit rule, not ordinary `Prog.bind`. Its target or reference
machine must retain the body's resulting state even when the body exits through
typed error or refusal, so cleanup can begin with that state. “State outside
error” names this information contract, not a mandated transformer spelling:
a layout that discards state on error is inadequate even if its types mention
both state and error.

## Incoming agent-report intake

An incoming message or `.staging/agent-reports/` file is evidence, never packet
authority. The coordinating lane processes it in this order:

1. record the report path, author/role, revision or file sizes classified, and
   commands the author says were run;
2. compare every recommendation with the operator-set decisions in `README.md`
   and the owning packet document; a contradictory recommendation is retained
   as evidence history, not silently adopted;
3. route each finding to exactly one owner in the file-authority table;
4. independently rerun every command before changing an evidence state to
   `VERIFIED-KERNEL` or `VERIFIED-TOOL`;
5. give every contradiction that can change a statement one stable ID in
   `COUNTEREXAMPLES.md`, while linking rather than copying the proof source;
6. amend the owning theorem/contract/type row with the exact premise, carrier
   restriction, quotient, or target change forced by the witness;
7. update cross-document status projections only after the owner is correct;
   and
8. report unresolved conflicts explicitly. Elaboration of a scratch value is
   never accepted as a semantic law, and an obsolete lane status is not treated
   as current merely because its report is detailed.

Two agents do not edit the same authority file concurrently. The coordinator
may add a reconciliation section to an incoming report-derived document, but
must preserve the original evidence and distinguish it from the binding packet
reading.

## Resume protocol

A fresh session does not recover this lane from chat history. It recovers from
repository content in this order:

1. verify the packet manifest and source pins;
2. read the current-slice row and its prerequisites;
3. read the frozen declaration digest for that slice;
4. read open obligation and red-control rows;
5. run the narrow status/check command named by the slice; and
6. continue only if the working tree changes are attributable and the nearest
   AGENTS files agree with the spec ledger.

If a manifest is absent, the lane is still in its current pre-grade bootstrap
state; use `README.md` and `PLAN.md`, and do not invent a completed status.

## Effect language-service rule

The TS7 path is `@effect/tsgo` with plugin name
`@effect/language-service`. It is required source-hygiene and coverage
evidence. It never defines `ProgramWF`, `Denotation`, a classifier fact, or a
handler law. Every diagnostic run must prove exact file-set coverage; an empty
diagnostic array without coverage is a failed harness.

## Claim and handoff rule

Every handoff reports:

- current slice and packet digest;
- packet-baseline, integration-base, and reviewed commit IDs;
- worktree role, file fence, and attributable start/end status;
- changed files;
- exact checks run and their results;
- public names added or changed;
- theorem axioms when Lean proofs are involved;
- unresolved obligations and planted red controls; and
- whether any result is only a finite probe.

Never use “fully reified,” “preserves,” “equivalent,” or “complete” without the
closed universe, observation, theorem or gate, and remaining foreign boundary
named in the same statement.
