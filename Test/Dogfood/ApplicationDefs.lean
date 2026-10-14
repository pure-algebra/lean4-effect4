import Test.Dogfood.Bank

/-!
# An application whose entries invoke its definitions, a banked block among them

Decisions row 378 (4) and (8), at the application (`src/Effect4/Program/Authoring/Application.lean`).
An entry's open program now reads the application's definitions, and is checked at the
application's table extended by them (`Application.signature`). A banked block joins the
definitions by reference (`DefSrc.ofBlock`, `src/Effect4/Program/Authoring/Defs.lean`), each
declaration and body kept as the bank holds it.

The example is the to-do's rows with the banked Ref cache's three definitions
(`Test/Dogfood/Bank.lean`) and one entry, `cachedList`: it makes a cell, then reads through the
cache with the to-do's `all` as the loader. Each line is a finite evaluation or a control
(decisions row 301). A run is a finite probe on the Lean machine, driven by the to-do's reference
model `repository` from one stored to-do.

* **The definitions are the bank's.** The kept declarations are the block's, and the built entry
  holds the block's bytes: its first three definitions, as a block, have the bank's recorded digest.
  So the built application pins the digest (row 378 (4)); an edit of the block fails this guard
  and the bank's.
* **The open program invokes them.** It elaborates with the definitions in scope and is typed at
  the application's signature. Without the definitions it is refused at the invocation, by name,
  and at the table's own signature the checker refuses it outside the domain.
* **It runs.** The built entry asks the repository once and answers the stored list.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.ApplicationDefs

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Machine
open Effect4.Program.Denote (blockOf?)
open Test.Dogfood.Scenario.Todo (application)
open Test.Dogfood.Bank (refCache refusedAt milk observe)

/-- `cachedList`: a cell made by the cache, then a read through it, the to-do's `all` the loader. -/
def cachedList : Src NativeOp :=
  bindWith (Def.invoke "listCacheMake" []) fun cell =>
    Def.invokeWith "listCacheGet" [cell]
      [fun _ => Test.Dogfood.Scenario.Todo.TodoRepo.all unit]

/-- The entry `cachedList`, with no parameter. -/
def entry : Application.Entry NativeOp := { name := "cachedList", body := cachedList }

/-- The to-do's rows, the banked cache's definitions kept, and the one entry. -/
def cached : Application NativeOp :=
  { application with defs := DefSrc.ofBlock refCache.block, entries := [entry] }

/-- The first `n` definitions of a program's block as a block of their own, with a main that
answers `unit` and no layer: the form in which the bank records a block. -/
def prefixBlock (n : Nat) (p : NativeEff) : Option NativeEff :=
  (blockOf? p).map fun b =>
    .defs (b.1.take n) (effsOfList (b.2.1.take n)) (.succeed (.lit .unit)) .nil

/-- The entry's built module. -/
def built : Option Api.Built := (Api.Author.build (cached.moduleOf entry [])).toOption

/-! ## The definitions are the bank's -/

-- finite evaluation: the kept declarations are the block's, in order
#guard cached.defs.map (·.decl) = refCache.block.defsOf
-- finite evaluation (row 378 (4)): the built entry holds the bank's block, byte for byte, so it pins
-- the bank's recorded digest
#guard (built.bind fun b => prefixBlock 3 b.program).map (fun p => (Store.Canonical.digest p).hex) =
  some refCache.digest

/-! ## The open program invokes them -/

/-- The entry's open program: `make`, then `get` at the cell with the loader `all()`. -/
def opened : NativeEff :=
  .bind (.perform (.call 0) (.lit .unit))
    (.invoke 1 (.var 0) (.cons (.perform (.external 1) (.lit .unit)) .nil))

-- finite evaluation: the open program elaborates with the definitions in scope
#guard cached.openProgram entry = .ok opened
-- finite evaluation: at the application's signature it answers the to-dos, and only the repository
-- fails
#guard (Checker.check cached.signature [] [] opened).toOption.map (fun t => (t.answer, t.error)) =
  some ((Ty.list Test.Dogfood.Scenario.Todo.Todo.ty).normalize, Test.Dogfood.Scenario.Todo.SqlError.ty)
-- control: without the definitions, the scope reader refuses the first invocation, by name
#guard ({ cached with defs := [] } : Application NativeOp).openProgram entry =
  .error ⟨[0], .unboundDef "listCacheMake"⟩
-- control: at the table's own signature the checker refuses the invocation outside the domain
#guard refusedAt (Checker.check (nativeSignature cached.table) [] [] opened) =
  some ([0], "outsideDomain")

/-! ## It runs -/

-- tested: under the reference model, from one stored to-do, the built entry asks the repository
-- once and answers the stored list
#guard (built.map (·.program)).bind observe == some (some (Exit.success milk), 1)

end Test.Dogfood.ApplicationDefs
