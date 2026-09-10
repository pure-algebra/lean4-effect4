import Effect4.Store.Canonical
import Std.Tactic.Do

/-! Specifications for the existing Option-valued list decoder. Runtime decoding stays in
Canonical; its monadic proof interface belongs only to Laws. -/
namespace Effect4.Store
open Std.Do

@[spec] theorem ofVal_spec {α : Type} [Canonical α] (v : Val) :
    ⦃⌜True⌝⦄ ofVal (α := α) v
      ⦃(fun a => ⌜v = toVal a⌝, fun _ => ⌜True⌝, ())⦄ := by
  cases h : ofVal (α := α) v with
  | none => simp [Triple.iff, wp, Option.instWP._aux_1, OptionT.run, Id.run]
  | some a => simpa [Triple.iff, wp, Option.instWP._aux_1, OptionT.run, Id.run] using (ofVal_exact h)

/-- Compose the actual list traversal through standard List equations and Std.Do's
Option/bind specifications. A successful decode reconstructs the whole input, in order. -/
@[spec] theorem mapM_ofVal_spec {α : Type} [Canonical α] (vs : List Val) :
    ⦃⌜True⌝⦄ vs.mapM (ofVal (α := α))
      ⦃(fun xs => ⌜vs = xs.map toVal⌝, fun _ => ⌜True⌝, ())⦄ := by
  induction vs with
  | nil => simp only [List.mapM_nil]; mvcgen
  | cons v vs ih =>
    simp only [List.mapM_cons]
    mvcgen [ofVal_spec, ih]
    all_goals simp_all

#print axioms ofVal_spec
#print axioms mapM_ofVal_spec
end Effect4.Store
