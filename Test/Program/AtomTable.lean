import Effect4.Program.NativeAtom

/-!
# The atom table's structural well-formedness, and the control that it has teeth

The tooling plan 2.1 and 2.5. `NativeAtom.atom_table_wf` (`src/Effect4/Program/NativeAtom.lean`)
decides four structural obligations over the whole inventory at once, in the kernel. A decided
fact is only worth what its predicate refuses, so this battery builds table rows by hand that
are wrong in five separate ways and shows each one refused on its own.

The predicate is not copied here. `NativeAtom.specWellFormed` takes an inventory of names, an
`AtomRow` and a `Spec`, and `atomWellFormed` is that predicate at the real table's columns — so
the fixture rows below are judged by exactly the code the core ships, not by a second text that
could drift from it.

The inventory `all` itself is guarded differently and better, by `all_complete`: it is
generated from the constructor list, so a missing atom is not expressible.
-/

namespace Test.Program.AtomTable

open Effect4.Program
open Effect4.Program.NativeAtom (AtomRow Spec specWellFormed)

/-! ## The fact -/

#guard NativeAtom.all.all NativeAtom.atomWellFormed

/-- The decided fact, named here so the battery fails with it. -/
example : NativeAtom.all.all NativeAtom.atomWellFormed = true := NativeAtom.atom_table_wf

/-! ## Rows built by hand, judged by the shipped predicate

`prelude` and `cite` play no part in well-formedness, so they are empty here; every other
column is the one the clause reads. -/

/-- A row and a spec under one name, the pair `specWellFormed` judges. -/
private def mk (name : String) (arity : Option Nat) (constGeneric : Bool)
    (scheme : NativeAtom.Scheme) : AtomRow × Spec :=
  ({ name, arity, constGeneric, prelude := "" }, { scheme, cite := "" })

/-- A fixed signature, arity agreeing. -/
private def good1 : AtomRow × Spec := mk "good1" (some 1) false (.mono [.nat] .nat)
/-- Two alternatives of one arity. -/
private def good2 : AtomRow × Spec :=
  mk "good2" (some 2) false (.alts [([.nat, .nat], .bool), ([.string, .string], .bool)])
/-- A variadic row declares no arity. -/
private def goodVariadic : AtomRow × Spec :=
  mk "goodVariadic" none false (.variadic .string (.list .string))
/-- A template whose answer names only parameters the arguments bind. -/
private def goodPoly : AtomRow × Spec :=
  mk "goodPoly" (some 2) true (.poly [.var 0, .var 1] (.prod (.var 0) (.var 1)))
/-- A named rule declares its own arity. -/
private def goodCustom : AtomRow × Spec :=
  mk "goodCustom" (some 1) false (.custom (.project false))

/-- Defect: arity 1 against a two-parameter signature. -/
private def badArity : AtomRow × Spec := mk "badArity" (some 1) false (.mono [.nat, .nat] .nat)
/-- Defect: a template whose answer names a parameter nothing binds, so instantiating its own
parameters does not give its own answer back (it gives `never`). -/
private def badAnswer : AtomRow × Spec := mk "badAnswer" (some 1) false (.poly [.var 0] (.var 1))
/-- Defect: const-generic (DI-55) *and* monomorphic. -/
private def badConst : AtomRow × Spec := mk "badConst" (some 1) true (.mono [.nat] .nat)
/-- Defect: two alternatives of different arity under one declared arity. -/
private def badAlts : AtomRow × Spec :=
  mk "badAlts" (some 2) false (.alts [([.nat, .nat], .bool), ([.nat], .bool)])
/-- Defect: the name of `good1`. -/
private def dupName : AtomRow × Spec := mk "good1" (some 1) false (.mono [.nat] .nat)

private def table : List (AtomRow × Spec) :=
  [good1, good2, goodVariadic, goodPoly, goodCustom, badArity, badAnswer, badConst, badAlts,
   dupName]

private def names : List String := table.map (·.1.name)

/-- One row judged in an inventory holding only itself: every clause but uniqueness. -/
private def alone (r : AtomRow × Spec) : Bool := specWellFormed [r.1.name] r.1 r.2

/-! The whole fixture table is refused, so `decide` could not close `table.all wellFormed =
true` for it — which is the shape `atom_table_wf` asserts for the real inventory. -/
#guard !table.all (fun r => specWellFormed names r.1 r.2)

/-! The five good rows pass on their own. Without this the control could be passing for a
reason that has nothing to do with the five defects — and between them they exercise every
constructor of `Scheme`. -/
#guard alone good1
#guard alone good2
#guard alone goodVariadic
#guard alone goodPoly
#guard alone goodCustom

/-! Each defect is refused on its own. `dupName` is the one whose refusal is the uniqueness
clause, so it is judged in the full inventory and passes alone. -/
#guard !alone badArity
#guard !alone badAnswer
#guard !alone badConst
#guard !alone badAlts
#guard !specWellFormed names dupName.1 dupName.2
#guard alone dupName

/-! And the real table's own rows pass the same predicate, row by row, so `atom_table_wf` is
not carrying a vacuous inventory. -/
#guard NativeAtom.all.all fun a => specWellFormed NativeAtom.names (NativeAtom.row a) (NativeAtom.spec a)

#print axioms NativeAtom.atom_table_wf

end Test.Program.AtomTable
