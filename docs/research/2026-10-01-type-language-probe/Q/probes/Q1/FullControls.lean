import ProbeQFull.TyEq

/-!
# Q1 controls on the variant family `ProbeQFull.Ty`

`record (fields : List (String × Ty × Bool))` and `map (key value : Ty)`: the generated
structural `Repr` prints what the `partial` derived one prints (a field's triple is flattened
as core's `ReprTuple` does), and the generated equality decides equality.
-/

namespace Q1Full

open ProbeQFull

def generated (t : Ty) : String := Std.Format.pretty (Ty.repr t 0)

def samples : List Ty :=
  [ .record [], .record [("a", .nat, false), ("b", .map .string .nat, true)],
    .map (.lit "k") (.record [("x", .option .nat, true)]),
    .union (.record [("z", .unknown, false)]) (.map .string (.list .bool)) ]

deriving instance Repr for ProbeQFull.Ty

def derived (t : Ty) : String := Std.Format.pretty (repr t)

#guard samples.all fun t => generated t == derived t
#guard samples.all fun t => samples.all fun u => Ty.beq t u == decide (t = u)
#guard Ty.beq (.record [("a", .nat, false)]) (.record [("a", .nat, true)]) = false

/-- The generated eliminator reaches a field's type inside the triple. -/
example (P : Ty → Prop) (fs : List (String × Ty × Bool)) (h : ∀ x ∈ fs, P x.2.1)
    (hr : ∀ fs, (∀ x ∈ fs, P (Prod.fst (Prod.snd x))) → P (.record fs)) : P (.record fs) := hr fs h

end Q1Full
