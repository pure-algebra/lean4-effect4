# Generic algebra attacks

Packet: `test/contracts/algebra-extraction.contract.md`

These attacks are durable regression inputs, not scratch alternatives. The
Foldlab witnesses are cited at commit
`feb29321fd50204aa338209d313e84a3f8b71c66`; Effect4 does not import them.

## Sum branch erasure or swap — `E4-ALG-CE-001`

Candidate mutation:

```text
badSum(h,g).handle(inl op) = g.handle mappedOp
badSum(h,g).handle(inr op) = h.handle mappedOp
```

Exhibit an equal-answer signature pair for which either result differs from
the required arm. The concrete `swappedSum` in the Lean battery supplies both
witnesses. Passing only a left-arm sample is inadequate; the categorical
repair is the pair of projections plus uniqueness.

## Missing half of interpreter adequacy — `E4-ALG-CE-002/003`

Two independent mutations kill the two tempting weakened statements:

```text
I_ignores(h,p) = interpret fixedHandler p
I_drifts(h,perform op) = h.handle op
I_drifts(h,twoOperations) != interpret h twoOperations
```

The first can preserve pure and bind while ignoring the supplied handler. The
second agrees on every single operation while failing sequencing. Therefore
the only admitted pin is the conjunction:

```text
IsMonadMorphism (I h)
and
forall op, I h (perform op) = h.handle op
```

Its conclusion is pointwise equality with `interpret h`. An axiom or `sorry`
would defeat the role of the attack, so exported pin/free/initiality theorems
also require `#print axioms` receipts.

## Category versus monoid — `E4-ALG-CE-004`

For

```text
t : Handler S (Program T)
u : Handler T (Program U)
```

`t.through u : Handler S (Program U)`. This is typed composition, but not a
binary operation on one carrier unless `S = T = U`. A theorem advertising a
global monoid is refuted by any three distinct signatures because the alleged
operation cannot be applied twice at one type. Keep category-shaped laws
general and state the monoid corollary only for `Handler S (Program S)`.

## Universe mismatch — `E4-ALG-CE-005`

The rejected old shape is:

```text
S       : Signature.{0,0}
A       : Type 1
p       : Program S A
M       : Type 0 -> Type v
handler : Handler S M
```

If `p` can be constructed, no generic `interpret handler p : M A` can be
typed. The battery asks Lean to reject `Program SmallSignature Type`. A future
explicit lift is acceptable only if its source/target signature, program, and
handler translations carry both round trips.

## Fixed-fuel false composition — `E4-ALG-CE-006`

The Foldlab witness gives two programs with equal runs at fuel three whose
bound composites have different runs. In exhibit form:

```text
run 3 p = run 3 q
and
run 3 (bind p f) != run 3 (bind q f)
```

That refutes every binary operator proposed as fixed-fuel bind, not merely one
candidate implementation. Effect4's generic composition theorem is therefore
about `interpret`; bounded execution belongs to a later observation face.

## First-order identity overclaim — `E4-ALG-CE-007`

`Program.vis` stores a Lean continuation. Exhibit two extensionally equal
continuations with no decidable structural equality or canonical bytes. No
hash, `DecidableEq`, or serializer may be derived for `Program`; the later
first-order flow is a separate representation related by named embedding and
adequacy theorems.
