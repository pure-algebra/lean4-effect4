/-!
# Protocol.Profile.lean

Owner: Closed target profiles and dispositions.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The versioned identity of a target profile, and the disposition each profile
assigns. A profile says *which* closed target a document is being read
against; it does not classify the document.

## What this module does not own

`SC-PROFILE-01` total classifier on all tags, `SC-PROFILE-02` Boolean
classifier iff propositional admission, and `SC-PROFILE-03` source-census
exhaustiveness belong to `Protocol.Admission`. `Schema.Check` supplies Schema
input to that classifier; it does not own the tag alphabet or generic profile
admission. Naming the classifier here as well would duplicate ownership.

The residue that is genuinely this module's is the profile's own identity:
which profile and at which version. It is passive finite data and will receive
an attached leaf receipt when declared. What happens when a document names a
profile this build does not have is an admission decision owned by
`Protocol.Admission`, not part of identity.

## Relation to the target profile in `PLAN.md`

`PLAN.md` fixes that "Effect TypeScript is one target profile, not the
identity or semantic owner." This module is where that sentence becomes a
declaration: rc.112 has to be *a* profile value, not the privileged one, or
the P10 target lane and the P12 Foldlab compatibility lane cannot both be
expressed. The `SC-CAS-01` through `SC-CAS-06` compatibility edges
(the `SC-CAS-*` block of that document's proof graph) are likewise
assigned to no module today;
they are the second profile consumer and are noted here only so the eventual
ruling has both consumers in view.

## Gated by

Nothing: a versioned profile identity can be declared and closed locally
without byte or payload semantics. The admission classifier that consumes it
is separately gated on its input carriers and graph.
-/
