import Effect4.Program.Typing.Rules

/-!
# Program.Typing.Blame — the vocabulary of the located refusal (DI-86)

`TypeReason` names why a node refuses in its rule's own terms (a term with no type, a request
outside the row's request, a predicate that is not `bool`, a bare layer reference, a `return`
that is not last, …), and `TypeRefusal` is a reason at a path — `Node.child` indices, the same
addressing the authoring refusals and the layer references use. The refusal itself is the
checker's: `Program/Checker.lean`'s `check` answers the type or the refusal in one
`Except`-valued fold, `explain` is its refusal at the root and `blame` the refusal's path, and
`explain = none ↔ effTy.isSome` (`Typing/Agreement.lean`) is the shape of `Except`. The hand
walk that once lived here beside `effTy`, and the mutual induction that tied the two, were
deleted on 2026-09-18 once the fold carried both.
-/

set_option autoImplicit false

namespace Effect4.Program

open Effect4 (ServiceKey)

/-- Why the checker refused at a node, in the node's own rule's terms. -/
inductive TypeReason
  /-- A term with no type in this environment: an unbound level, an atom the signature
  refuses at these argument types, a literal outside the value alphabet. -/
  | term (t : Term)
  | cause (c : CauseTerm)
  /-- `fail` at a type the error alphabet does not admit. -/
  | errorNotAdmitted (error : Ty)
  /-- The row is outside the signature's domain (DI-54). -/
  | outsideDomain (row : String)
  /-- The request is not a subtype of the row's request (DI-15). -/
  | requestNotSubtype (row : String) (request expected : Ty)
  | predicateNotBool (t : Ty)
  /-- A `select` whose decision cannot select on the scrutinee's type (`Decision.arms`
  answers `none`): a non-option under `.option`, a column that is not tagged or carries no
  member of the tag under `.tag`. Under `.bool` the refusal is `predicateNotBool`, the
  conditional's own reason (`selectRefusal`). -/
  | notSelectable (decision : Decision) (scrutinee : Ty)
  /-- A loop's step does not have the cursor's type. -/
  | stepNotCursor (step cursor : Ty)
  /-- An `iterate`'s initial cursor is not under the cursor's annotation. -/
  | initialNotCursor (initial cursor : Ty)
  /-- A release whose error column is not `never` (rc.112 `Effect<unknown, never, R2>`,
  `Effect.ts:12930`; decisions row 47, DI-94): a release cannot fail, a failing one is a defect. -/
  | releaseFails (error : Ty)
  | notFiber (t : Ty)
  | scopeExpected (t : Ty)
  | natExpected (t : Ty)
  | listOfFibersExpected (t : Ty)
  | contextExpected (t : Ty)
  | snapshotExpected (t : Ty)
  | exitExpected (t : Ty)
  /-- The signature types no service under this key. -/
  | serviceUnknown (key : ServiceKey)
  /-- The provided value is not a subtype of the key's carrier (DI-15). -/
  | valueNotSubtype (key : ServiceKey) (value carrier : Ty)
  /-- A bare reference is typed by the whole program after expansion, never structurally. -/
  | layerReference (target : List Nat)
  /-- A reference of the whole program is ill formed (`Eff.layerRefsWF`): its target is not a
  preceding non-reference layer. Reported at the root by the facade. -/
  | referencesIllFormed
  | mergeAllEmpty
  | returnNotLast
  | breakOutsideLoop
  | literalOutsideAlphabet (value : Lit)
deriving DecidableEq

/-- The constructor's name: the reason as one word, for tables and reports. -/
def TypeReason.head : TypeReason → String
  | .term _ => "term"
  | .cause _ => "cause"
  | .errorNotAdmitted _ => "errorNotAdmitted"
  | .outsideDomain _ => "outsideDomain"
  | .requestNotSubtype _ _ _ => "requestNotSubtype"
  | .predicateNotBool _ => "predicateNotBool"
  | .notSelectable _ _ => "notSelectable"
  | .stepNotCursor _ _ => "stepNotCursor"
  | .initialNotCursor _ _ => "initialNotCursor"
  | .releaseFails _ => "releaseFails"
  | .notFiber _ => "notFiber"
  | .scopeExpected _ => "scopeExpected"
  | .natExpected _ => "natExpected"
  | .listOfFibersExpected _ => "listOfFibersExpected"
  | .contextExpected _ => "contextExpected"
  | .snapshotExpected _ => "snapshotExpected"
  | .exitExpected _ => "exitExpected"
  | .serviceUnknown _ => "serviceUnknown"
  | .valueNotSubtype _ _ _ => "valueNotSubtype"
  | .layerReference _ => "layerReference"
  | .referencesIllFormed => "referencesIllFormed"
  | .mergeAllEmpty => "mergeAllEmpty"
  | .returnNotLast => "returnNotLast"
  | .breakOutsideLoop => "breakOutsideLoop"
  | .literalOutsideAlphabet _ => "literalOutsideAlphabet"

/-- A refusal at a path of the tree. -/
structure TypeRefusal where
  path : List Nat
  reason : TypeReason
deriving DecidableEq

/-- Why a `select` refuses its scrutinee's type: under `.bool` it is the conditional on a
non-Boolean, which TypeScript accepts (no diagnostic); under the other two decisions the
argument is not assignable. -/
def selectRefusal : Decision → Ty → TypeReason
  | .bool, t => .predicateNotBool t
  | .option, t => .notSelectable .option t
  | .tag name, t => .notSelectable (.tag name) t

/-- The generator answer join never refuses (part 4: the least upper bound). -/
@[simp] theorem GenTy.joinAnswer_isSome (a b : Option Ty) : (GenTy.joinAnswer a b).isSome = true := by
  unfold GenTy.joinAnswer
  split <;> simp [EffTy.joinAnswer]

@[simp] theorem GenTy.merge_isSome (a b : GenTy) : (GenTy.merge a b).isSome = true := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (GenTy.joinAnswer_isSome a.answer b.answer)
  simp [GenTy.merge, hx]

end Effect4.Program
