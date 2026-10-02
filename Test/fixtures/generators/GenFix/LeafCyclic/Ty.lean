/-!
# GenFix.LeafCyclic.Ty — a leaf-order table whose closure is cyclic (a red fixture)

Probe P's red control (`P/probes/P2Ty.lean:1285`) as a family: the table relates `nat` below `int`
and `int` below `nat`, so its closure is not antisymmetric and the order it would give `sub` has
two different heads each below the other. The core compiles (the table is data); the view
generator (`tools/Effect4Gen/View.lean`) must refuse it by name before writing a line, since
`leafLe_antisymm` (and `sub`'s antisymmetry through `leafRule_asymm`) would be false. Everything
else the generator reads is present, so the cycle is the one reason. Read by
`scripts/test-generators.py`; not a battery module.
-/

set_option autoImplicit false

namespace GenFix.LeafCyclic

inductive Ty
  | never
  | nat
  | int
  | string
  | lit (value : String)
  | union (left right : Ty)
  | unknown
deriving DecidableEq, Repr

namespace Ty

def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .nat | .int | .string | .lit _ | .unknown => true

inductive LeafHead where
  | lit
  | string
  | nat
  | int
deriving DecidableEq, Repr

def LeafHead.all : List LeafHead := [.lit, .string, .nat, .int]

def leafHead : Ty → Option LeafHead
  | .lit _ => some .lit
  | .string => some .string
  | .nat => some .nat
  | .int => some .int
  | _ => none

/-- The cyclic table: `nat < int` and `int < nat`. -/
def leafEdges : List (LeafHead × LeafHead) :=
  [ (.lit, .string), (.nat, .int), (.int, .nat) ]

def leafReach (edges : List (LeafHead × LeafHead)) : Nat → LeafHead → LeafHead → Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y => decide (x = y) || edges.any fun e => decide (e.1 = x) && leafReach edges n e.2 y

def leafLe (x y : LeafHead) : Bool := leafReach leafEdges leafEdges.length x y

def leafRule (a b : Ty) : Bool :=
  match leafHead a, leafHead b with
  | some x, some y => !decide (x = y) && leafLe x y
  | _, _ => false

def sub (a b : Ty) : Bool :=
  if a = b then true
  else if leafRule a b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  | _, .unknown => true
  | _, _ => false
termination_by sizeOf a + sizeOf b

theorem leafRule_of_left_none (a b : Ty) (h : leafHead a = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]

theorem leafRule_of_right_none (a b : Ty) (h : leafHead b = none) : leafRule a b = false := by
  unfold leafRule
  rw [h]
  cases leafHead a <;> rfl

theorem ite_leafRule_false {a b : Ty} {r : Bool} (h : leafRule a b = false) :
    (if leafRule a b = true then true else r) = r := by
  rw [h]
  rfl

theorem sub_of_leafRule {a b : Ty} (h : leafRule a b = true) : sub a b = true := by
  unfold sub
  by_cases hab : a = b
  · rw [if_pos hab]
  · rw [if_neg hab, if_pos h]

-- the cycle, computed: `nat` and `int` are each below the other
#guard sub .nat .int && sub .int .nat

end Ty
end GenFix.LeafCyclic
