/-!
# Protocol.Identity.lean

Owner: Portable effect, type, and operation identities.

This breadth stub intentionally declares no semantic object. Its public
surface is frozen only after the owning contract and counterexample packet.

The annotations below are navigation and scope, not declarations. Obligation
names are those of the graph in `docs/SCHEMA-CUTOVER.md`; counterexample rows
are those of `test/counterexamples/REGISTER.md`.

## Ownership

The stable names by which an effect, a type, or an operation is referred to
across a wire — as distinct from the values so named. `PLAN.md` phase P5 lists
"portable protocol identities" alongside rows and cause/exit.

## The distinction this module exists to hold

An identity is a name, not a meaning. Two facts already established elsewhere
show why the separation has to be a declaration rather than a convention.

- **A registry is open; an alphabet is closed.** `Effect4/Schema/Registry.lean`
  records that rc.112 resolves declaration and check revivers by a `string`
  `id` against a per-call map, installing none implicitly, and rejects a
  duplicate `id` eagerly at map construction. So identity uniqueness is a real
  obligation with a host witness, and it is separate from any closed tag
  census.
- **A code is not a faithful name for a type.** The closed
  `Effect4/Context/Key.lean` proves `ServiceUniverse.exists_carrier_collision`:
  distinct `ServiceTypeCode`s may read as the same Lean type, so type identity
  never recovers code identity and no inverse interpretation exists. Any
  identity scheme here inherits that asymmetry rather than escaping it.

## Assigned future obligations

None are allocated to this module by name in the current graph. That is a gap
rather than a decision: `SC-CAS-01` through `SC-CAS-06`, the Foldlab
compatibility edges, are the natural consumers of a portable identity and are
presently assigned to no module at all. `Effect4/Protocol/Profile.lean`
records the same gap from the profile side. Allocating them is a ruling for
`docs/SCHEMA-CUTOVER.md`, not something this stub may assume.

## Gated by

`Effect4/Protocol/Profile.lean`, since an identity is only portable relative
to a profile that fixes its spelling, and the payload carrier for any identity
that appears inside persisted data.
-/
