# Context payload order and membership

The type-order migration keeps exact payload equality in `Ty.sameHead`.
`Ty.contextOf` adds an order on its canonical key-row payload.
An available row is below a promised row when the promised keys are included in the available keys.

Concept: subtyping-algebra.
Required property: canonical subtype antisymmetry and membership weakening.
Registry claims: `sub-antisymm-canonical` and the existing typed membership preservation claims.
Proof role: the generated payload laws are helpers used by `TypeAlgebra`, `Admits` and `Typed.Membership`.
Requirement: R14, with semantic membership serving R4.

`payload-orders.json` names the payload relation and its checked companion laws.
The existing View producer emits the payload rule and its helpers.
It refuses an absent head, a recursive payload shape or an absent companion law.
The relation remains outside the finite leaf-edge table.

The incomplete decomposition helpers gain a payload-rule-false premise:
`sub_eq_false_of_not_sameHead`, `sub_eq_args` and `sub_eq_leafRule_of_not_sameHead`.
Their callers handle the declared payload rule before the ordinary child comparison.
The outward subtype, order and membership statements retain their claims.
A search finds no frozen contract that pins these helper statements.

`Typed.Fits` requires key coverage, matching world service declarations and service-value membership.
The executable `Val.hasTy` check alone supplies none of the latter world premises.
`ValueBoundary.lean` retains that distinction.
The source reader and provider must consume these exact premises during their semantic migration.

Reach: canonical native context rows in the source/type slice.
The proof is not execution progress or a target equivalence.
The signature-dependent target projection and outside behaviour gates remain separate obligations.
