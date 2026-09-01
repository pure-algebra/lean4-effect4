/-!
# Protocol.Admission.lean

Owner: Profile admission and refusal classification.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

Generic profile membership and admission policy. `docs/SCHEMA-CUTOVER.md`
section "Canonical wire profile" splits three ways and this module holds the
middle: `Effect4.Protocol.Profile` owns the stable `Effect4Rc112` profile
identity, this module owns membership and policy, and `Effect4.Schema.Check`
owns Schema-specific structural predicates. Unknown-profile behaviour is
this module's.

## Assurance route

This is the one Protocol module whose route is already ruled on rather than
open. `docs/SCHEMA-CUTOVER.md` records that a versioned profile identity is
passive data and takes a leaf receipt, while `Protocol.Admission` **crosses
the graph threshold** when it classifies an unknown profile or an
out-of-profile value. So a leaf receipt is not available here once the first
classifying declaration lands, and the graph must be allocated before it.

`docs/AGENT-ROUTING.md` reaches the same verdict independently: its
graph-trigger list makes "admits, rejects, refuses, or classifies" a trigger
outright, and its `leaf-receipt` conditions exclude a declaration that owns
admission or refusal.

## What must not be precommitted here

`docs/SCHEMA-CUTOVER.md` is explicit that no issue or diagnostic API is
precommitted merely because a predicate can fail, and that a later public
classification boundary needs its own contract. Two consequences:

- A refusal produced here is not automatically an `SC-ISSUE-01` value.
  `SC-ISSUE-01` is currently owned by no module; `docs/SCHEMA-ISSUE-SURVEY.md`
  proposes an owner and the ruling has not been made.
- `PLAN.md` "Non-negotiable semantic boundaries" separates live frontiers from
  typed failure, defects, interruption, and domain-specific refusal. An
  out-of-profile value is a domain refusal. An unanswered choice or exhausted
  fuel is a frontier and may not be spelled with the same constructor.

## Directionality, already established

`E4-SCHEMA-CE-025` fired on exactly this boundary and its result binds this
module. rc.112 accepts documents Effect4 refuses — dangling `$ref`s, alias
cycles, unguarded structural cycles, dead table entries — and the acceptance
is layer-dependent: the document codec admits a dangling `$ref` that revival
then refuses. So an Effect4 admission policy is strictly narrower than the
host's, and every compatibility claim must be stated directionally, naming
the host layer it is about. No Effect4 refusal may be reported as an rc.112
refusal.

## Gated by

`Effect4/Protocol/Profile.lean` for the identity being admitted against, and
`Effect4/Protocol/Bytes.lean` for anything decided below the tag vocabulary —
`docs/WIRE-DAG.md` records that duplicate keys must be decided before any
`_tag` is read, so a policy phrased over representations has already passed
the point where that obligation is statable.
-/
