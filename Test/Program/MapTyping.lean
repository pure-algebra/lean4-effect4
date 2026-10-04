import Effect4.Laws.Program.Typed.Denotation
import Effect4.Laws.Program.MeaningSound

/-! Finite typing controls and universal theorem applications for the six map atoms.
The world fixtures test declaration-sensitive payload membership, not validity of a whole machine.
Target execution and JSON codecs remain outside these checks. -/

namespace Effect4.Test.MapTyping
open Program Machine

#guard NativeAtom.typeOf .mapEmpty [] = some (.map .string .never)
#guard NativeAtom.typeOf .mapGet [.map .string .nat, .string] = some (.option .nat)
#guard NativeAtom.typeOf .mapSet [.map .string .nat, .string, .string] =
  some (.map .string (.union .nat .string))
#guard NativeAtom.typeOf .mapSet [.map .string .never, .string, .nat] =
  some (.map .string (.union .never .nat))
#guard NativeAtom.typeOf .mapKeys [.map .string (.option (.refOf .nat))] = some (.list .string)
#guard NativeAtom.typeOf .mapEntries [.map .string .nat] = some (.list (.prod .string .nat))
#guard NativeAtom.typeOf .mapFromEntries [.list (.prod .string .nat)] = some (.map .string .nat)
#guard NativeAtom.typeOf .mapFromEntries [.list .never] = some (.map .string .never)
#guard NativeAtom.typeOf .mapGet [.map .nat .nat, .string] = none
#guard NativeAtom.typeOf .mapFromEntries [.list (.prod .nat .nat)] = none
#guard NativeAtom.typeOf .mapSet [.map .string .nat, .nat, .string] = none

-- The empty snapshot was the concrete progress counterexample to a plain-list-only reader.
#guard Val.hasTy (Val.fibers []) (.list (.prod .string .nat))
#guard NativeAtom.eval .mapFromEntries [Val.fibers []] = some Map.empty
#guard !Val.hasTy (Val.fibers [⟨0⟩]) (.list (.prod .string .nat))

example : ∃ out, Map.fromEntries (Val.fibers []) = some out ∧
    Val.hasTy out (.map .string .nat) = true :=
  MapChecks.fromEntries (by decide)

-- Typed lookup keeps present undefined and present Option.none distinct from absence.
example (w : Typed.World) : ∃ out,
    Map.get (Map.write [("x", .unit)]) "x" = some out ∧ Typed.Fits w out (.option .undefined) := by
  apply Typed.MapFits.get
  exact ⟨rfl, fun _ he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨True.intro, True.intro⟩
    · exact nomatch he⟩

example (w : Typed.World) : ∃ out,
    Map.get (Map.write [("x", Store.Val.none)]) "x" = some out ∧
      Typed.Fits w out (.option (.option .nat)) := by
  apply Typed.MapFits.get
  exact ⟨rfl, fun _ he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨True.intro, True.intro⟩
    · exact nomatch he⟩

-- This declaration table supplies a concrete positive witness for the handle premises below.
def declaredWorld : Typed.World :=
  { Typed.initialWorld ⟨.unit, .never, Env.Requirement.empty⟩ with
    Ρ := Typed.tableInsert (fun _ => none) ⟨9⟩ .nat }

example : Typed.RefDeclared declaredWorld ⟨9⟩ .nat := ⟨.nat, rfl, Ty.subN_refl _, Ty.subN_refl _⟩

-- A declared nested reference survives lookup and mixed-type update.
example (w : Typed.World) (key : RefKey) (h : Typed.RefDeclared w key .nat) :
    ∃ out, Map.get (Map.write [("cell", Store.Val.some (Val.cell key))]) "cell" = some out ∧
      Typed.Fits w out (.option (.option (.refOf .nat))) := by
  apply Typed.MapFits.get
  exact ⟨rfl, fun _ he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨True.intro, h⟩
    · exact nomatch he⟩

example (w : Typed.World) (key : RefKey) (h : Typed.RefDeclared w key .nat) :
    ∃ out, Map.set (Map.write [("cell", Store.Val.some (Val.cell key))]) "label" (.str "new") = some out ∧
      Typed.Fits w out (.map .string (.union (.option (.refOf .nat)) .string)) := by
  apply Typed.MapFits.set (w := w) (replacement := .str "new")
    (key := "label") (b := .string) (hr := True.intro)
  exact ⟨rfl, fun _ he => by
    rcases List.mem_cons.mp he with rfl | he
    · exact ⟨True.intro, h⟩
    · exact nomatch he⟩

example (w : Typed.World) (key : RefKey) (h : ¬ Typed.RefDeclared w key .nat) :
    ¬ Typed.Fits w (Map.write [("cell", Store.Val.some (Val.cell key))])
      (.map .string (.option (.refOf .nat))) := by
  intro hf
  exact h ((hf.2 _ List.mem_cons_self).2)

#print axioms Typed.MapValues.encoded_of_all
#print axioms Typed.MapValues.sorted_pairs
#print axioms MapChecks.get
#print axioms MapChecks.set
#print axioms MapChecks.fromEntries
#print axioms NativeAtom.sound
#print axioms Typed.MapFits.get
#print axioms Typed.MapFits.set
#print axioms Typed.MapFits.fromEntries
#print axioms Typed.atomFits
#print axioms Typed.atom_progress
#print axioms Typed.evalTerm_progress
#print axioms Denote.NativeAtom.eval_validIn
#print axioms Denote.evalTerm_validIn
#print axioms Denote.sound

end Effect4.Test.MapTyping
