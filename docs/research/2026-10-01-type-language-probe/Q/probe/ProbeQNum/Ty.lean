/-!
# ProbeQNum.Ty — today's `Ty` plus a `number` leaf and one rule of a number tower

Seat Q probe (2026-10-01). The red control for the view generator's hard-coded rules: seat T's
census puts a number tower in `sub` (`nat` and `int` below `number`, P's to rule) and `undefined`
below `unit`. Each is a rule beside the congruences, like the literal rule; the generated view
names exactly two such rules (`litRule`, `topRule`) and six rule cases, so a third rule makes
`sub_eq_args` false at the pair it relates. `sub` is copied from `Ty.lean:437-457` with one rule
added, `nat` below `number`.
-/

namespace ProbeQNum

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
  | number
deriving DecidableEq, Repr

namespace Ty

def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown | .number => true

def sub (a b : Ty) : Bool :=
  if a = b then true
  else match a, b with
  | .never, _ => true
  | .union a1 a2, b => sub a1 b && sub a2 b
  | a, .union b1 b2 => sub a b1 || sub a b2
  | _, .unknown => true
  | .lit _, .string => true
  | .option a, .option b => sub a b
  | .list a, .list b => sub a b
  | .prod a1 a2, .prod b1 b2 => sub a1 b1 && sub a2 b2
  | .except e1 a1, .except e2 a2 => sub e1 e2 && sub a1 a2
  | .exitOf a1 e1, .exitOf a2 e2 => sub a1 a2 && sub e1 e2
  | .causeOf e1, .causeOf e2 => sub e1 e2
  | .fiberOf a1 e1, .fiberOf a2 e2 => sub a1 a2 && sub e1 e2
  | .refOf a1, .refOf a2 => sub a1 a2 && sub a2 a1
  | .deferredOf a1 e1, .deferredOf a2 e2 => sub a1 a2 && sub a2 a1 && sub e1 e2 && sub e2 e1
  | .nat, .number => true
  | _, _ => false
termination_by sizeOf a + sizeOf b

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  simp

end Ty
end ProbeQNum
