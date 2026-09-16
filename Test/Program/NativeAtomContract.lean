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

#guard NativeAtom.names =
  ["succ", "pred", "isZero", "not", "add", "lt", "eq", "pair", "fst", "snd", "strings",
   "causeIsFail", "causeError", "causeIsDie", "causeIsInterrupt", "or", "and", "tagIs",
   "isSome", "getOrElse"]
-- the tag test (DI-39, part 4 commit 3): a string or literal tag, any tested value; total on
-- values — true exactly on a pair whose first component is the tag
#guard NativeAtom.arity .tagIs = some 2
#guard NativeAtom.mono .tagIs = none
#guard !NativeAtom.constGeneric .tagIs
#guard nativeAtomTy "tagIs" [.string, .nat] = some .bool
#guard nativeAtomTy "tagIs" [.lit "A", .union (.prod (.lit "A") .string) .string] = some .bool
#guard nativeAtomTy "tagIs" [.nat, .string] = none
#guard nativeAtomTy "tagIs" [.string] = none
#guard nativeAtom "tagIs" [.str "A", .list [.str "A", .str "m"]] = some (.bool true)
#guard nativeAtom "tagIs" [.str "A", .list [.str "B", .str "m"]] = some (.bool false)
#guard nativeAtom "tagIs" [.str "A", .str "A"] = some (.bool false)
#guard nativeAtom "tagIs" [.str "A", .nat 7] = some (.bool false)
#guard nativeAtom "tagIs" [.str "A", .list [.str "A"]] = some (.bool false)
#guard nativeAtom "tagIs" [.nat 1, .str "A"] = none
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
-- subsumption at a fixed-signature atom (part 4, DI-15): a subtype of the parameter is
-- accepted, a literal is a string, `never` is anything; the const-generic flag names `pair`
#guard nativeAtomTy "succ" [.never] = some .nat
#guard nativeAtomTy "eq" [.lit "a", .lit "b"] = some .bool
#guard nativeAtomTy "eq" [.lit "a", .string] = some .bool
#guard nativeAtomTy "eq" [.lit "a", .nat] = none
#guard nativeAtomTy "strings" [.lit "x", .string] = some (.list .string)
#guard nativeConstAtom "pair"
#guard !nativeConstAtom "eq"
#guard NativeAtom.constGeneric .pair
#guard !NativeAtom.constGeneric .fst

-- Option elimination uses ordinary eager terms. The default must fit the existing
-- payload type; it cannot widen that type, even when the option is empty.
#guard NativeAtom.arity .isSome = some 1
#guard NativeAtom.arity .getOrElse = some 2
#guard NativeAtom.mono .isSome = none
#guard NativeAtom.mono .getOrElse = none
#guard !NativeAtom.constGeneric .isSome
#guard !NativeAtom.constGeneric .getOrElse
#guard nativeAtomTy "isSome" [.option .never] = some .bool
#guard nativeAtomTy "isSome" [.nat] = none
#guard nativeAtomTy "isSome" [] = none
#guard nativeAtomTy "isSome" [.option .nat, .nat] = none
#guard nativeAtomTy "getOrElse" [.option .nat, .nat] = some .nat
#guard nativeAtomTy "getOrElse" [.option .string, .lit "fallback"] = some .string
#guard nativeAtomTy "getOrElse" [.option (.union .nat .never), .nat] =
  some (.union .nat .never)
#guard nativeAtomTy "getOrElse" [.option .nat, .string] = none
#guard nativeAtomTy "getOrElse" [.option .never, .nat] = none
#guard nativeAtomTy "getOrElse" [.nat, .nat] = none
#guard nativeAtomTy "getOrElse" [.option .nat] = none
#guard nativeAtomTy "getOrElse" [.option .nat, .nat, .nat] = none
#guard nativeAtom "isSome" [.none] = some (.bool false)
#guard nativeAtom "isSome" [.some .none] = some (.bool true)
#guard nativeAtom "isSome" [.nat 0] = none
#guard nativeAtom "isSome" [.none, .nat 0] = none
#guard nativeAtom "getOrElse" [.none, .nat 9] = some (.nat 9)
#guard nativeAtom "getOrElse" [.some (.nat 3), .nat 9] = some (.nat 3)
#guard nativeAtom "getOrElse" [.nat 3, .nat 9] = none
#guard nativeAtom "getOrElse" [.some (.nat 3)] = none
#guard nativeAtom "getOrElse" [.none, .nat 9, .nat 10] = none
#guard !NativeAtom.covers (NativeAtom.names.filter (· != "isSome"))
#guard !NativeAtom.covers (NativeAtom.names.filter (· != "getOrElse"))

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
