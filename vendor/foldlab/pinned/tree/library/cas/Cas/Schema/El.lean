import Cas.Schema.Discriminated

/-!
# The denotation — a code is a type

`El` interprets each code as the Lean type of its values: the
universe's decoding function. Structs denote right-nested products
(one component per field, optional fields under `Option`), references
denote addresses, literals denote the singleton. Every described tree
type in the estate is meant to arrive as `El` of a code — never as a
new hand-written inductive (the three-trees discipline).
-/

namespace Cas.Schema

/-- A typed store reference that RETAINS the kind it expects — the
Lean face of the runtime's branded roots. Erasing the tag would make
every reference code denote one type and lose the refinement. -/
structure StoreRef (tag : UInt8) where
  addr : Addr32

/-! ## The general declaration's denotation — a named obligation

`El (.decl id p ps) = Empty`: a general declaration denotes NO Lean
values yet, and that is a statement, not a placeholder. The three
admitted general rows (`Date`, `URL`, `Option`) are admitted AS
CONTENT — the store can hold, address, re-emit, and hand back such a
schema — but Lean has no carrier for their instances, so claiming one
would be a lie and `Empty` is the truth. Every value-plane law about
the code then holds vacuously rather than falsely: `encode` on this arm
is `Empty.elim`, and the codec's own arms never fire.

The design call this parks, stated so the next slice does not
rediscover it: the obvious shape — a typeclass associating an admitted
id with its carrier, the way `Described` associates a code with a type
— does NOT fit. `El` is a function on first-order DATA and consumes a
runtime `DeclarationId.General`; typeclass resolution runs at
elaboration and cannot see a value. The denotation therefore wants a
CARRIER TABLE, `DeclarationId.General → DeclPayload → List Ast → Type`,
defined by cases on the closed registry — a small function, but one
that puts inhabited types under the arm and so drags the value-plane
codec (`Cas/Schema/Codec/`) and its mutual law block
(`Codec/Laws/Mutual.lean`) in with it. That is its own increment. Named
obligation:

    declEl : the carrier table for the admitted general rows, with
             `El (.decl id p ps) = declEl id p ps` and the codec arms
             that follow from it.

## The union's denotation — discriminated first (stage 2)

`El (.union ms m) = cond (discriminatedB ms) (ElMembers ms) Empty`: the
denotation is REAL exactly where decoding is deterministic, and `Empty`
everywhere else.

This is the staged answer `UNION-DESIGN.md` ratified, and the split is
not a convenience — it is what keeps every unconditional law of stage 1
TRUE over the grown carrier. A general union's denotation is a
dependent sum with TRY-ORDER semantics: for overlapping members two
members can both accept a value, and which one the sum records is a
function of the member order, not of the value, so the round trip is
false. Under DISCRIMINATION — every member a struct whose first field
is a required string-literal `_tag`, all tags distinct
(`Cas/Schema/Discriminated.lean`) — the tags are pairwise disjoint
evidence and the round trip is a theorem
(`decodeMembers_encodeMembers`). A non-discriminated union keeps
carriage without denotation: it is store content — mintable,
addressable, re-emittable, materializable into a live Effect validator
through `fromRepresentation` — while Lean holds no values of it, so its
value-plane laws hold vacuously rather than falsely, exactly as in
stage 1.

Discrimination stays OUT of `Ast.WF` on purpose: `WF` is the store's
admission discipline and stage 1 already admits every union. `El`'s
guard is a denotation precondition, and moving it into `WF` would
retire content the store already carries.

The general union's denotation therefore remains a named obligation:

    generalUnionEl : the try-order denotation for undiscriminated
                     unions, with whatever weaker-than-exactness law
                     its consumer can live with. Owed only when a
                     consumer demands it.

## The enum's denotation — a named obligation

`El (.enum ms) = Empty`: an enum denotes NO Lean values yet, and that is
a statement rather than a placeholder — the same shape of answer the
general declaration gets, and for a sharper reason than cost.

An enum's values are its members' values, so the obvious denotation is
the index `Fin ms.length` with `encode` sending index `i` to the `i`-th
member's value. That is a bijection exactly when the VALUES are
pairwise distinct — and `Ast.WF` deliberately does not ask that, because
TypeScript admits alias members (`enum E { A = 1, B = 1 }`) and Effect
persists both rows. Under aliasing the decode side is not extensional:
two indices carry one value, so which index the wire records is a
function of the member ORDER, not of the value, and the round trip is
false. That is the general union's pathology exactly, and it takes the
same staged answer: a distinctness guard in `El` (`cond` on a boolean
twin, the way `discriminatedB` guards the union) with `Fin`-indexed
carriage under it. Until a consumer wants enum VALUES rather than enum
CARRIAGE, `Empty` is the truth and every value-plane law holds over the
grown carrier vacuously rather than falsely. Named obligation:

    enumEl : the distinctness-guarded denotation for enums —
             `El (.enum ms) = cond (valuesDistinctB ms) (Fin ms.length)
             Empty` or its equivalent — with the codec arms and the
             round trip that follow from it.

## The tuple's denotation — a named obligation, and why the product
   alone is not enough

`El (.tuple e es r) = Empty` for now. The PRODUCT is the obvious shape
and it is within reach — `ElElements` mirroring `ElFields`, the rest as
a `List` — but the product alone is not a denotation, because a tuple's
positions live in an ARRAY and a struct's live under NAMES.

Concretely: an absent optional element does not leave a hole in a JSON
array, it SHORTENS it. So `readonly [a?, b]` cannot be encoded at all —
dropping the first element moves `b` into position 0, and the decoder
reading position 0 gets `b` where the code says `a`. Exactness and the
round trip are both false on such a code. TypeScript's own type system
forbids it, so Effect can never CONSTRUCT one; but the representation
can spell one, and `Ast.WF` admits it, because `WF` is the store's
admission discipline and the store should carry what the wire carries.

That is the general union's situation exactly, and it takes the ratified
answer: a boolean guard in `El`, not a new clause in `WF`. Named
obligation:

    tupleEl : `El (.tuple e es r) = cond (trailingOptionalB (e :: es))
              (ElElements (e :: es) × ElRest r) Empty`, with the
              positional codec arms and the round trip that follow —
              the encoder emitting elements then rest, the decoder
              splitting the array at the element count, and the
              trailing-optional guard doing for the split what
              discrimination does for tag dispatch.

Until then a tuple is carried and not inhabited: mintable, addressable,
re-emittable, materializable into a live Effect validator, with every
value-plane law holding vacuously rather than falsely.

## The C6 codes' denotation — REFUSED for v1, not parked

`El (.reference _) = Empty` and `El (.susp _) = Empty`, and these two
arms are different in kind from the four above. The others are parked:
the carrier exists, the shape is known, and a later increment writes it.
These two are REFUSED, and the refusal is the ticket's own claim scope
(PDD-3, plan HARD PARTS 2): v1 states no denotational adequacy for
recursive codes AT ALL.

The reason is not effort. `El` is a CLOSED STRUCTURAL function — it
reads a code and nothing else — and a reference's target does not live
in the code. It lives in the document's references table, one level up.
Denoting `.reference n` therefore needs either fuel-indexed semantics or
an `El` relativised to a table, and both are real theory that no
consumer has asked for. Writing `Empty` here is the honest answer and
not a placeholder for an obvious one: the value-plane laws hold over the
grown carrier vacuously rather than falsely, exactly as they do for the
four parked arms, and the recursive schemas the estate admits are
CARRIED — mintable, addressable, re-emittable, and materializable into a
live Effect validator, which handles `Schema.suspend` natively.

What v1 does claim about these codes is decode, encode, and guardedness,
and it claims them in `Cas/Schema/Guarded.lean` and the ingestion door.
The value-plane verdict gap for recursive codes is a KNOWN, RECORDED
hole, named in `contracts/PDD-3.contract.md`. Named obligation:

    recursiveEl : a denotation for `.reference` and `.susp` — fuel
                  indexed, or relative to a references table — with the
                  codec arms and the round trip that follow from it.
-/

mutual

/-- The type a code denotes. -/
def El : Ast → Type
  | .null => Unit
  | .bool => Bool
  | .int => SafeInt
  | .str => String
  | .lit _ => Unit
  | .arr a => List (El a)
  | .struct fs => ElFields fs
  | .ref t => StoreRef t
  | .decl _ _ _ => Empty
  | .union ms _ => cond (discriminatedB ms) (ElMembers ms) Empty
  | .enum _ => Empty
  | .tuple _ _ _ => Empty
  | .reference _ => Empty
  | .susp _ => Empty

/-- Field components, right-nested: `(first, rest)`. -/
def ElFields : List (String × Bool × Ast) → Type
  | [] => Unit
  | (_, opt, a) :: fs => (cond opt (Option (El a)) (El a)) × ElFields fs

/-- Member components, right-nested: the iterated sum, with the LAST
member carried bare rather than wrapped against a dead `Empty`
summand. The empty list is unreachable under `Ast.WF` — the type
function is total anyway, and answers `Empty`, which is the same thing
the guard answers. -/
def ElMembers : List Ast → Type
  | [] => Empty
  | [a] => El a
  | a :: b :: rest => El a ⊕ ElMembers (b :: rest)

end

/-- The undiscriminated union denotes nothing — stage 1's statement,
kept as a theorem so the vacuity every unconditional law leans on is
citable rather than incidental. -/
theorem El_union_undiscriminated {ms : List Ast} {m : UnionMode}
    (h : discriminatedB ms = false) : El (.union ms m) = Empty := by
  simp only [El, h, cond_false]

/-- The discriminated union denotes the member sum. -/
theorem El_union_discriminated {ms : List Ast} {m : UnionMode}
    (h : discriminatedB ms = true) : El (.union ms m) = ElMembers ms := by
  simp only [El, h, cond_true]

/-- A union VALUE is itself the evidence that its code is discriminated
— the undiscriminated arm is `Empty`, so holding one is impossible.
This is what lets the value-plane laws take discrimination as a
hypothesis without carrying it in `Ast.WF`. -/
theorem discriminatedB_of_el {ms : List Ast} {m : UnionMode}
    (x : El (.union ms m)) : discriminatedB ms = true := by
  cases hb : discriminatedB ms with
  | true => rfl
  | false => exact Empty.elim (El_union_undiscriminated (m := m) hb ▸ x)

end Cas.Schema
