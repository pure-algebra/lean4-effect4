import Lean
/-! Seat TREE exploration E1 (2026-10-01): which Lean 4.33.1 instruments accept a `Ty` with a
nested record field `List (String × Ty)` (option C) and a mutual spine `Fields` (option B).
Core Lean only. Messages are the measurement; this file is expected to report errors. -/

namespace E1.C

inductive Ty
  | never | unit | nat | int | string | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | union (left right : Ty)
  | lit (value : String)
  | unknown
  | record (fields : List (String × Ty))

-- C1: derived decidable equality on the nested block
deriving instance DecidableEq for Ty

-- C2: the induction tactic on the nested block
example (t : Ty) : t = t := by
  induction t with
  | never => rfl
  | _ => rfl

-- C3: structural recursion through an inline pair pattern, no `Prod` companion
mutual
def size : Ty → Nat
  | .option t | .list t => size t + 1
  | .prod a b | .union a b => size a + size b + 1
  | .record fs => sizeFields fs + 1
  | _ => 1
def sizeFields : List (String × Ty) → Nat
  | [] => 0
  | (_, t) :: rest => size t + sizeFields rest
end

#eval size (.record [("a", .nat), ("b", .list .string)])

-- C4: structural, stated explicitly
mutual
def size2 : Ty → Nat
  | .option t | .list t => size2 t + 1
  | .prod a b | .union a b => size2 a + size2 b + 1
  | .record fs => size2Fields fs + 1
  | _ => 1
termination_by structural t => t
def size2Fields : List (String × Ty) → Nat
  | [] => 0
  | (_, t) :: rest => size2 t + size2Fields rest
termination_by structural fs => fs
end

example : size2 (.record [("a", .nat)]) = 2 := rfl
example : size (.record [("a", .nat)]) = 2 := rfl

-- C5: derived Repr on the nested block
deriving instance Repr for Ty

end E1.C

namespace E1.B

mutual
inductive Ty
  | never | unit | nat | int | string | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | union (left right : Ty)
  | lit (value : String)
  | unknown
  | record (fields : Fields)
inductive Fields
  | nil
  | cons (name : String) (type : Ty) (rest : Fields)
end

-- B1: derived decidable equality on the mutual block
deriving instance DecidableEq for Ty, Fields

-- B2: the induction tactic on the mutual block
example (t : Ty) : t = t := by
  induction t with
  | never => rfl
  | _ => rfl

-- B3: structural mutual recursion
mutual
def size : Ty → Nat
  | .option t | .list t => size t + 1
  | .prod a b | .union a b => size a + size b + 1
  | .record fs => sizeFields fs + 1
  | _ => 1
termination_by structural t => t
def sizeFields : Fields → Nat
  | .nil => 0
  | .cons _ t rest => size t + sizeFields rest
termination_by structural fs => fs
end

example : size (.record (.cons "a" .nat .nil)) = 2 := rfl

-- B5: derived Repr on the mutual block
deriving instance Repr for Ty, Fields

end E1.B

open Lean in
/-- Which constants of the two namespaces are `opaque` (what `partial def` elaborates to). -/
elab "#opaques" : command => do
  let env ← Lean.getEnv
  for (n, info) in env.constants.map₂.toList ++ env.constants.map₁.toList do
    if (`E1).isPrefixOf n || ((Lean.privateToUserName? n).map (`E1).isPrefixOf).getD false then
      if let .opaqueInfo _ := info then
        Lean.logInfo m!"opaque: {n}"

#opaques
