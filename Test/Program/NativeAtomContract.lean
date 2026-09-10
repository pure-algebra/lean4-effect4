import Effect4.Program.Native

/-!
# Native atom inventory contract (DI-40)

The universal inventory/lookup statements and explicit omissions below prevent checking
only a supplied partial table. These are alphabet controls, not a host-equivalence claim.
The generator's target scheme tests live in its own driver; prelude coverage is tested on
the actual generated profile and actual self-test cases in the truth harness.
-/

namespace Test.Program.NativeAtomContract

open Effect4.Program

#check (NativeAtom.all_complete : ∀ atom : NativeAtom, atom ∈ NativeAtom.all)
#check (NativeAtom.covers_iff : ∀ names : List String,
  NativeAtom.covers names = true ↔ ∀ atom : NativeAtom, atom.name ∈ names)
#check (NativeAtom.ofName?_name : ∀ atom : NativeAtom,
  NativeAtom.ofName? atom.name = some atom)

#guard NativeAtom.names =
  ["succ", "pred", "isZero", "not", "add", "lt", "eq", "pair", "fst", "snd", "strings",
   "causeIsFail", "causeError", "causeIsDie", "causeIsInterrupt", "or", "and"]
#guard NativeAtom.names.eraseDups.length = NativeAtom.names.length
#guard NativeAtom.covers NativeAtom.names
#guard !NativeAtom.covers (NativeAtom.names.filter (· != "strings"))
#guard !NativeAtom.covers (NativeAtom.names.filter (· != "succ"))
#guard !NativeAtom.covers []
#guard NativeAtom.ofName? "unknown" = none
#guard NativeAtom.ofName? "Succ" = none
#guard NativeAtom.arity .strings = none
#guard NativeAtom.arity .pair = some 2
#guard nativeAtomTy "unknown" [.nat] = none
#guard nativeAtomTy "succ" [] = none
#guard nativeAtomTy "pair" [.nat, .bool] = some (.prod .nat .bool)
#guard nativeAtomTy "strings" [] = some (.list .string)

/-- Every successful native typing names an inventoried atom, for arbitrary input types. -/
theorem typed_name_known (name : String) (args : List Ty) (answer : Ty)
    (h : nativeAtomTy name args = some answer) : name ∈ NativeAtom.names := by
  obtain ⟨atom, hname, _⟩ := Option.bind_eq_some_iff.mp h
  rw [← NativeAtom.ofName?_sound hname]
  exact List.mem_map.mpr ⟨atom, NativeAtom.all_complete atom, rfl⟩

/-- Every successful native evaluation names an inventoried atom, even without typing. -/
theorem evaluated_name_known (name : String) (args : List Effect4.Machine.Val)
    (answer : Effect4.Machine.Val) (h : nativeAtom name args = some answer) :
    name ∈ NativeAtom.names := by
  obtain ⟨atom, hname, _⟩ := Option.bind_eq_some_iff.mp h
  rw [← NativeAtom.ofName?_sound hname]
  exact List.mem_map.mpr ⟨atom, NativeAtom.all_complete atom, rfl⟩

#print axioms Effect4.Program.NativeAtom.all_complete
#print axioms Effect4.Program.NativeAtom.ofName?_name
#print axioms Effect4.Program.NativeAtom.ofName?_sound
#print axioms Effect4.Program.NativeAtom.name_injective
#print axioms Effect4.Program.NativeAtom.covers_iff
#print axioms typed_name_known
#print axioms evaluated_name_known

end Test.Program.NativeAtomContract
