/-!
# GenFix.LeafOne.Ty — today's `Ty` with its one cross-head rule as the leaf-order table (a fixture)

Today's twenty constructors (`src/Effect4/Program/Ty.lean`, base `74dae8d2`), and `sub` with its
literal arm `.lit _, .string` replaced by the leaf-order table of decisions row 177 (probe P,
`P/probes/P2Ty.lean:666-739`) holding today's one edge, `lit < string`: `LeafHead`, `leafHead`,
`leafEdges`, `leafReach`, `leafLe`, `leafRule`, consulted by `sub` before its rows. On this family
the view generator (`tools/Effect4Gen/View.lean`) reads the table from the environment and emits
the table's laws; the order is today's (the table's rule is today's literal rule).

No `normalize` here, so the view's `normalize` facts are not emitted (the branch the wave fixture
takes the other way). Read by `scripts/test-generators.py`; not a battery module.
-/

set_option autoImplicit false

namespace GenFix.LeafOne

inductive Ty
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | except (error value : Ty)
  | exitOf (value error : Ty)
  | causeOf (error : Ty)
  | fiberOf (value error : Ty)
  | union (left right : Ty)
  | lit (value : String)
  | refOf (value : Ty)
  | deferredOf (value error : Ty)
  | var (index : Nat)
  | unknown
deriving DecidableEq, Repr

namespace Ty

/-- A union member has neither an empty nor a union head. -/
def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown => true

/-! ## The leaf-order table, at today's one edge -/

/-- The heads the leaf order relates: today, the literal and its base. -/
inductive LeafHead where
  | lit
  | string
deriving DecidableEq, Repr

/-- Every leaf head: the finite domain the closure's checks range over. -/
def LeafHead.all : List LeafHead := [.lit, .string]

/-- A type's leaf head, when its head is one. -/
def leafHead : Ty → Option LeafHead
  | .lit _ => some .lit
  | .string => some .string
  | _ => none

/-- **The declared edges**: today's one, a literal below its base. -/
def leafEdges : List (LeafHead × LeafHead) :=
  [ (.lit, .string) ]

/-- Reachability in a table of edges, with fuel. -/
def leafReach (edges : List (LeafHead × LeafHead)) : Nat → LeafHead → LeafHead → Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y => decide (x = y) || edges.any fun e => decide (e.1 = x) && leafReach edges n e.2 y

/-- The leaf order: the table's reflexive-transitive closure. -/
def leafLe (x y : LeafHead) : Bool := leafReach leafEdges leafEdges.length x y

/-- The rule `sub` consults before its rows: two types whose leaf heads differ and are related. -/
def leafRule (a b : Ty) : Bool :=
  match leafHead a, leafHead b with
  | some x, some y => !decide (x = y) && leafLe x y
  | _, _ => false

/-- The subtype relation of `Ty.lean:437` with its literal arm read from the table. -/
def sub (a b : Ty) : Bool :=
  if a = b then true
  else if leafRule a b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  | _, .unknown => true
  | .option a, .option b => sub a b
  | .list a, .list b => sub a b
  | .prod a1 a2, .prod b1 b2 => sub a1 b1 && sub a2 b2
  | .except e1 a1, .except e2 a2 => sub e1 e2 && sub a1 a2
  | .exitOf a1 e1, .exitOf a2 e2 => sub a1 a2 && sub e1 e2
  | .causeOf e1, .causeOf e2 => sub e1 e2
  | .fiberOf a1 e1, .fiberOf a2 e2 => sub a1 a2 && sub e1 e2
  | .refOf a1, .refOf a2 => sub a1 a2 && sub a2 a1
  | .deferredOf a1 e1, .deferredOf a2 e2 => sub a1 a2 && sub a2 a1 && sub e1 e2 && sub e2 e1
  | _, _ => false
termination_by sizeOf a + sizeOf b

/-! ## The four `sub` lemmas the table's laws read (probe P, `P2Ty.lean:1140-1160`) -/

/-- The table is silent when the left side has no leaf head. -/
theorem leafRule_of_left_none (a b : Ty) (h : leafHead a = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]

/-- The table is silent when the right side has no leaf head. -/
theorem leafRule_of_right_none (a b : Ty) (h : leafHead b = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]
  cases leafHead a <;> rfl

/-- The table's line of `sub`, when the table is silent. -/
theorem ite_leafRule_false {a b : Ty} {r : Bool} (h : leafRule a b = false) :
    (if leafRule a b = true then true else r) = r := by
  rw [h]
  rfl

/-- Each rule of the table is in the order. -/
theorem sub_of_leafRule {a b : Ty} (h : leafRule a b = true) : sub a b = true := by
  unfold sub
  by_cases hab : a = b
  · rw [if_pos hab]
  · rw [if_neg hab, if_pos h]

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  rw [if_pos rfl]

/-- Today's literal rule, now the table's one element. -/
theorem sub_lit_string (s : String) : sub (lit s) string = true :=
  sub_of_leafRule rfl

#guard sub (.lit "a") .string && !sub .string (.lit "a") && !sub (.lit "a") (.lit "b")
#guard sub (.option (.lit "a")) (.option .string) && !sub .nat .int

end Ty
end GenFix.LeafOne
