import Effect4.Program.NativeAtom

/-!
# The atom table's structural well-formedness, and the control that it has teeth

The tooling plan 2.1. `NativeAtom.atom_table_wf` (`src/Effect4/Program/NativeAtom.lean`) decides
four structural obligations over the whole inventory at once, in the kernel. A decided fact is
only worth what its predicate refuses, so this battery carries a fixture alphabet whose columns
are wrong in four separate ways and shows each one refused on its own.

The predicate's clauses are repeated here over the fixture's own columns rather than applied to
it: `atomWellFormed` reads `NativeAtom`'s projections, and a fixture cannot be a `NativeAtom`
without being an atom. What the control therefore establishes is that these four clauses, as
written, refuse each defect — not that the two texts are the same text. The inventory `all`
itself is guarded differently and better, by `all_complete`: it is generated from the
constructor list, so a missing atom is not expressible.
-/

namespace Test.Program.AtomTable

open Effect4.Program

/-! ## The fact -/

#guard NativeAtom.all.all NativeAtom.atomWellFormed

/-- The decided fact, named here so the battery fails with it. -/
example : NativeAtom.all.all NativeAtom.atomWellFormed = true := NativeAtom.atom_table_wf

/-! ## The red control

Six fixture rows. `good1` and `good2` satisfy every clause; `badArity` declares arity 1 against
a two-parameter monomorphic signature; `badAnswer`'s `typeOf` answers a type its own `mono`
column does not; `badConst` is const-generic *and* monomorphic (DI-55 says a const-generic
atom's parameters are polymorphic); `dupName` repeats `good1`'s name. -/

inductive Fixture
  | good1 | good2 | badArity | badAnswer | badConst | dupName
  deriving DecidableEq

namespace Fixture

def all : List Fixture := [.good1, .good2, .badArity, .badAnswer, .badConst, .dupName]

def name : Fixture → String
  | .good1 => "good1"
  | .good2 => "good2"
  | .badArity => "badArity"
  | .badAnswer => "badAnswer"
  | .badConst => "badConst"
  -- the defect: two rows of one inventory carry one name
  | .dupName => "good1"

def arity : Fixture → Option Nat
  | .good1 => some 1
  | .good2 => some 2
  -- the defect: the monomorphic signature below declares two parameters
  | .badArity => some 1
  | .badAnswer => some 1
  | .badConst => some 1
  | .dupName => some 1

def mono : Fixture → Option (List Ty × Ty)
  | .good1 => some ([.nat], .nat)
  | .good2 => some ([.nat, .nat], .nat)
  | .badArity => some ([.nat, .nat], .nat)
  -- the defect: `typeOf` answers `.nat` at `[.nat]`, not `.bool`
  | .badAnswer => some ([.nat], .bool)
  -- the defect: const-generic below, with a monomorphic signature here
  | .badConst => some ([.nat], .nat)
  | .dupName => some ([.nat], .nat)

def typeOf : Fixture → List Ty → Option Ty
  | f, tys =>
    match f.mono with
    | some (args, answer) =>
      if tys.length = args.length ∧ (tys.zip args).all (fun (a, e) => a.sub e) then
        -- every row but `badAnswer` answers what it declares
        some (match f with
              | .badAnswer => .nat
              | .good1 | .good2 | .badArity | .badConst | .dupName => answer)
      else none
    | none => none

def constGeneric : Fixture → Bool
  | .badConst => true
  | .good1 | .good2 | .badArity | .badAnswer | .dupName => false

/-- The four clauses of `NativeAtom.atomWellFormed`, over the fixture's columns, with the
inventory of names supplied so a single row can be judged against an inventory of its own. -/
def wellFormedIn (inventory : List String) (a : Fixture) : Bool :=
  (inventory.count a.name == 1)
    && (match a.mono, a.arity with
        | some (args, _), some n => args.length == n
        | some _, none => false
        | none, _ => true)
    && (match a.mono with
        | some (args, answer) => a.typeOf args == some answer
        | none => true)
    && (!a.constGeneric || a.mono.isNone)

def names : List String := all.map name

/-- One row judged against an inventory holding only itself: every clause but uniqueness. -/
def alone (a : Fixture) : Bool := wellFormedIn [a.name] a

end Fixture

/-! The whole fixture table is refused, so `decide` could not close `all.all wellFormed = true`
for it — which is the shape `atom_table_wf` asserts for the real inventory. -/
#guard !Fixture.all.all (Fixture.wellFormedIn Fixture.names)

/-! The two good rows pass on their own. Without this the control could be passing for a
reason that has nothing to do with the four defects. -/
#guard Fixture.alone .good1
#guard Fixture.alone .good2

/-! Each defect is detected independently, judged in an inventory where it is the only row (so
`dupName` is the one row whose refusal is the uniqueness clause, and it needs the full
inventory). -/
#guard !Fixture.alone .badArity
#guard !Fixture.alone .badAnswer
#guard !Fixture.alone .badConst
#guard !Fixture.wellFormedIn Fixture.names .dupName
#guard Fixture.alone .dupName

#print axioms NativeAtom.atom_table_wf

end Test.Program.AtomTable
