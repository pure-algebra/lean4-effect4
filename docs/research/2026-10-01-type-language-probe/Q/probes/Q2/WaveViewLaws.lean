import ProbeQW.TyView

/-!
# Q2 on the whole wave: the generated view of `ProbeQW.Ty`

Seat Q probe (2026-10-01). `ProbeQW.TyView` is written by the copy `Q/tools/Effect4Gen/View.lean`
from `ProbeQW.Ty` (record with optional flags, map, tuple, app, four leaves) and
`Q/generated/variances-wave.json` (`record` and `tuple` at `"arity": "each"`, `app` at
`"arity": "byName"`, `map` `[inv, co]`, and the order's rule table: five structural cases and five
leaf edges). `Variance` and `edgeRule` are the core module's (`ProbeQW.TyVariance`, generated from
the same table), which `sub`'s `app` arm and catch-all read.
-/

open ProbeQW ProbeQW.Ty

#check @Ty.sub_eq_args
#check @Ty.sub_eq_edgeRule_of_not_sameHead
#check @Ty.edgeRule_trans
#check @Ty.edgeRule_eq_true
#check @Ty.args
#check @Ty.sub_args_record
#check @Ty.sub_args_tuple
#check @Ty.sub_args_app
#check @Ty.eq_of_sameHead

-- the children each head of variable arity yields, with their variances
#guard Ty.args (.record [("b", .nat, true), ("a", .bool, false)]) = [(.co, .bool), (.co, .nat)]
#guard Ty.args (.tuple [.nat, .bool]) = [(.co, .nat), (.co, .bool)]
#guard Ty.args (.app "Layer.Layer" [.nat, .bool, .unit]) = [(.contra, .nat), (.co, .bool), (.co, .unit)]
#guard Ty.args (.app "Undeclared.Name" [.nat]) = [(.inv, .nat)]
#guard Ty.args (.map .string .nat) = [(.inv, .string), (.co, .nat)]

-- the head: payloads in canonical order (record), the arity (tuple), the name and the arity (app)
#guard Ty.sameHead (.record [("b", .nat, true), ("a", .bool, false)]) (.record [("a", .unit, false), ("b", .unit, true)])
#guard !Ty.sameHead (.record [("a", .nat, true)]) (.record [("a", .nat, false)])
#guard Ty.sameHead (.tuple [.nat, .bool]) (.tuple [.unit, .unit])
#guard !Ty.sameHead (.tuple [.nat]) (.tuple [.nat, .nat])
#guard !Ty.sameHead (.app "Fiber.Fiber" [.nat, .nat]) (.app "Exit.Exit" [.nat, .nat])

-- the law, computed at one pair per new head
#guard Ty.sub (.app "Layer.Layer" [.string, .nat, .nat]) (.app "Layer.Layer" [.lit "a", .nat, .nat]) =
  (Ty.sameHead (.app "Layer.Layer" [.string, .nat, .nat]) (.app "Layer.Layer" [.lit "a", .nat, .nat]) &&
   Ty.argsBelow Ty.sub (.app "Layer.Layer" [.string, .nat, .nat]) (.app "Layer.Layer" [.lit "a", .nat, .nat]))
#guard Ty.sub (.tuple [.lit "a", .nat]) (.tuple [.string, .nat]) =
  (Ty.sameHead (.tuple [.lit "a", .nat]) (.tuple [.string, .nat]) &&
   Ty.argsBelow Ty.sub (.tuple [.lit "a", .nat]) (.tuple [.string, .nat]))

-- The two controls of a cross-head edge: accepted, and its converse refused, through the law
#guard Ty.sub .nat .number = ((Ty.sameHead .nat .number && Ty.argsBelow Ty.sub .nat .number) || Ty.edgeRule .nat .number)
#guard Ty.sub .nat .number && Ty.edgeRule .nat .number && !Ty.sameHead .nat .number
#guard !Ty.sub .number .nat && !Ty.edgeRule .number .nat
-- heads with no declared edge: the different-head theorem's `false`
#guard !Ty.sub .number .string && !Ty.edgeRule .number .string
#guard !Ty.sub .bytes .string

/-- Transitivity through a leaf edge, from the generated closure certificate. -/
example : Ty.edgeRule .nat .number = true := Ty.edgeRule_trans (b := .int) rfl rfl

/-- The accepted cross-head case, as a theorem through the restated law. -/
theorem nat_sub_number : Ty.sub .nat .number = true := by
  rw [Ty.sub_eq_args .nat .number rfl rfl rfl]
  rfl

/-- Its converse, refused through the different-head theorem: no edge goes down the tower. -/
theorem number_not_sub_nat : Ty.sub .number .nat = false := by
  rw [Ty.sub_eq_edgeRule_of_not_sameHead .number .nat rfl rfl rfl rfl]
  rfl

/-- At a tuple or a reference the node law needs no canonicity: position is the order. -/
example (xs ys : List Ty) (h : Ty.sameHead (.tuple xs) (.tuple ys) = true)
    (hx : (Ty.tuple xs).args.map Prod.snd = (Ty.tuple ys).args.map Prod.snd) : Ty.tuple xs = Ty.tuple ys :=
  Ty.eq_of_sameHead h hx rfl rfl

/-- Red control (proved): at a record the unpremised node law is false. -/
theorem wave_eq_of_sameHead_needs_canon :
    ¬ ∀ a b : Ty, Ty.sameHead a b = true → a.args.map Prod.snd = b.args.map Prod.snd → a = b := by
  intro h
  have := h (.record [("b", .nat, false), ("a", .bool, false)]) (.record [("a", .bool, false), ("b", .nat, false)])
    (by decide) (by decide)
  exact absurd this (by decide)

#print axioms Ty.sub_eq_args
#print axioms Ty.sub_eq_edgeRule_of_not_sameHead
#print axioms Ty.edgeRule_eq_false_of_sameHead
#print axioms Ty.edgeRule_eq_true
#print axioms Ty.edgeRule_trans
#print axioms nat_sub_number
#print axioms number_not_sub_nat
#print axioms Ty.sub_eq_argsBelow_of_sameHead
#print axioms Ty.sub_args_record
#print axioms Ty.sub_args_tuple
#print axioms Ty.sub_args_app
#print axioms Ty.sub_args_map
#print axioms Ty.eq_of_sameHead
#print axioms Ty.eq_of_sameHead_nil
#print axioms Ty.argsBelow_antisymm
#print axioms Ty.argsBelow_trans
#print axioms Ty.argsBelow_refl
#print axioms Ty.args_congr
#print axioms Ty.sameHead_refl
#print axioms Ty.sameHead_symm
#print axioms Ty.sameHead_trans
#print axioms Ty.sizeOf_args
#print axioms wave_eq_of_sameHead_needs_canon
