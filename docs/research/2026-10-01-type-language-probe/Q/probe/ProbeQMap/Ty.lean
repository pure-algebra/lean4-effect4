/-!
# ProbeQMap.Ty — today's `Ty` plus a fixed-arity `map (key value : Ty)` only

Seat Q probe (2026-10-01). The red control for the view generator's hard-coded case numbering:
an append with no variable arity at all (row 125's map, a plain two-child head) still adds an arm
to `sub`, which moves `sub`'s catch-all from `fun_cases` case 16 to case 17. `sub` is copied from
`src/Effect4/Program/Ty.lean:437-457` with one arm added: the key exact (invariant), the value
covariant, as seat P's brief states row 125.
-/

namespace ProbeQMap

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
  | map (key value : Ty)
deriving DecidableEq, Repr

namespace Ty

def isMember : Ty → Bool
  | .never | .union _ _ => false
  | .unit | .nat | .int | .string | .bool
  | .handle _ | .option _ | .list _ | .prod _ _
  | .except _ _ | .exitOf _ _ | .causeOf _ | .fiberOf _ _
  | .lit _ | .refOf _ | .deferredOf _ _ | .var _ | .unknown | .map _ _ => true

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
  | .map k1 v1, .map k2 v2 => sub k1 k2 && sub k2 k1 && sub v1 v2
  | _, _ => false
termination_by sizeOf a + sizeOf b

theorem sub_refl (t : Ty) : sub t t = true := by
  unfold sub
  simp

end Ty
end ProbeQMap
