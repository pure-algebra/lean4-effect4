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
   "isSome", "getOrElse", "ite", "some", "none", "mul",
   "nil", "cons", "get", "length", "append", "sub", "div", "mod", "concat"]
-- the tag test (DI-39, part 4 commit 3): a string or literal tag, any tested value; total on
-- values — true exactly on a pair whose first component is the tag
#guard NativeAtom.arity .tagIs = some 2
-- The tag test *is* monomorphic now that the language has a top (decisions row 46): its second
-- parameter is `unknown`, which every type is below, so the arm that used to ignore its second
-- argument is the signature the prelude's own `(tag: string, e: unknown)` spells. `typeOf`
-- answers exactly what it answered before; what changed is that the metadata says so, and
-- `typeOf_mono` now covers this row (tooling plan 2.5).
#guard NativeAtom.mono .tagIs = some ([.string, .unknown], .bool)
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
-- the literal rule through the template calculus (DI-55): two distinct parameters bind
-- positionally, so a literal argument keeps its type
#guard NativeAtom.typeOf .pair [.lit "A", .string] = some (.prod (.lit "A") .string)
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
#guard NativeAtom.mono .isSome = some ([.option .unknown], .bool)
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

-- The L4-blocking atoms (DI-40, DI-78). `ite` selects between two evaluated arguments, and at
-- its repeated parameter it infers the candidates' common supertype, never a union: tsgo 7
-- refuses `ite(b, n, s)` at `n: number`, `s: string` (TS2345) and types `ite(b, nv, n)` at
-- `nv: never` as `number`. `getOrElse`'s fallback is `NoInfer`, so its first binding stays:
-- tsgo refuses `getOrElse(o, n)` at `o: Option<never>` (TS2345), and so does the guard above.
#guard nativeAtomTy "ite" [.bool, .nat, .nat] = some .nat
#guard nativeAtomTy "ite" [.bool, .never, .nat] = some .nat
#guard nativeAtomTy "ite" [.bool, .nat, .never] = some .nat
#guard nativeAtomTy "ite" [.bool, .option .never, .option .nat] = some (.option .nat)
#guard nativeAtomTy "ite" [.bool, .nat, .string] = none
#guard nativeAtomTy "ite" [.nat, .nat, .nat] = none
#guard nativeAtomTy "some" [.nat] = some (.option .nat)
#guard nativeAtomTy "none" [] = some (.option .never)
#guard nativeAtomTy "mul" [.nat, .nat] = some .nat
#guard nativeAtom "ite" [.bool true, .nat 1, .nat 2] = some (.nat 1)
#guard nativeAtom "ite" [.bool false, .nat 1, .nat 2] = some (.nat 2)
#guard nativeAtom "some" [.nat 4] = some (.some (.nat 4))
#guard nativeAtom "none" [] = some .none
#guard nativeAtom "mul" [.nat 6, .nat 7] = some (.nat 42)
#guard !NativeAtom.constGeneric .ite
#guard !NativeAtom.constGeneric .optSome

-- Red controls: fiber snapshots unwrap to lists of handles; products are not lists
#guard (Effect4.Machine.Val.asList? (Effect4.Machine.Val.fibers [⟨0⟩])).map List.length = some 1
#guard Ty.sub (.prod .nat .nat) (.list .nat) = false
#guard nativeAtomTy "length" [.prod .nat .nat] = none
#guard nativeAtom "length" [Effect4.Machine.Val.fibers [⟨0⟩]] = some (.nat 1)

-- The L3 atoms (plan §2.6). `length` is `mono` at `list unknown` (decisions row 69's rule: a
-- parameter no answer mentions is the top). `cons` and `append` infer the common supertype of
-- their element types as tsgo does: `cons(n, nil())` and `append(nil(), ns)` type at `number`,
-- and `cons(n, ss)` and `append(ns, ss)` are refused (TS2345). `get` answers `some unit` on a
-- list of units, which the prelude must not read as a missing element.
#guard NativeAtom.mono .listLength = some ([.list .unknown], .nat)
#guard !NativeAtom.constGeneric .listCons
#guard nativeAtomTy "nil" [] = some (.list .never)
#guard nativeAtomTy "cons" [.nat, .list .nat] = some (.list .nat)
#guard nativeAtomTy "cons" [.nat, .list .never] = some (.list .nat)
#guard nativeAtomTy "cons" [.never, .list .nat] = some (.list .nat)
#guard nativeAtomTy "cons" [.nat, .list .string] = none
#guard nativeAtomTy "append" [.list .never, .list .nat] = some (.list .nat)
#guard nativeAtomTy "append" [.list .nat, .list .string] = none
#guard nativeAtomTy "get" [.list .string, .nat] = some (.option .string)
#guard nativeAtomTy "get" [.prod .nat .nat, .nat] = none
#guard nativeAtomTy "length" [.list .nat] = some .nat
#guard nativeAtomTy "concat" [.lit "a", .string] = some .string
#guard nativeAtomTy "div" [.nat, .never] = some .nat
#guard nativeAtom "nil" [] = some (.list [])
#guard nativeAtom "cons" [.nat 1, .list [.nat 2]] = some (.list [.nat 1, .nat 2])
#guard nativeAtom "cons" [.nat 1, Effect4.Machine.Val.fibers [⟨0⟩]] =
  some (.list [.nat 1, Effect4.Machine.Val.fiber ⟨0⟩])
#guard nativeAtom "get" [.list [.nat 10, .nat 20], .nat 1] = some (.some (.nat 20))
#guard nativeAtom "get" [.list [.nat 10, .nat 20], .nat 5] = some .none
#guard nativeAtom "get" [.list [.unit], .nat 0] = some (.some .unit)
#guard nativeAtom "append" [.list [.nat 1], .list [.nat 2]] = some (.list [.nat 1, .nat 2])
#guard nativeAtom "length" [.nat 3] = none
#guard nativeAtom "sub" [.nat 5, .nat 2] = some (.nat 3)
#guard nativeAtom "sub" [.nat 2, .nat 5] = some (.nat 0)
#guard nativeAtom "div" [.nat 10, .nat 3] = some (.nat 3)
#guard nativeAtom "div" [.nat 10, .nat 0] = some (.nat 0)
#guard nativeAtom "mod" [.nat 10, .nat 3] = some (.nat 1)
#guard nativeAtom "mod" [.nat 10, .nat 0] = some (.nat 10)
#guard nativeAtom "concat" [.str "a", .str "b"] = some (.str "ab")


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
