import Effect4.Author
import Effect4.Program.Authoring.Application

/-!
# A vending machine whose host rows are its events: a coin comes in, an item goes out, change returns

The machine moves through three states: it collects coins until the credit covers the price,
then it vends the item, then it returns the change. Each move is one host row. The coin row
declares its protocol: a coin is worth 5, 10 or 25. The vend row declares that it vends the item
it was asked for.
-/

set_option autoImplicit false

namespace Examples.VendingMachine

open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (add sub lt)

/-! ## The events -/

eff_failure Jammed message

/-- The machine's service key. -/
def machineKey : ServiceKey := ⟨⟨34⟩, ⟨6⟩⟩

eff_rows Machine key machineKey error Jammed.ty cite "the vending machine" where
  coin(.unit) : .nat,
  vend(.string) : .string,
  change(.nat) : .unit

/-! ## The protocols

A protocol reads the request at level 0 and the answer at level 1. -/

/-- `coin()`: the coin is worth 5, 10 or 25. -/
def coinProtocol : RowProtocol :=
  { post := .app "or" (termsOfList
      [.app "eq" (termsOfList [.var 1, .lit (.nat 5)]),
       .app "or" (termsOfList
        [.app "eq" (termsOfList [.var 1, .lit (.nat 10)]),
         .app "eq" (termsOfList [.var 1, .lit (.nat 25)])])]) }

/-- `vend(item)`: the item that comes out is the item asked for. -/
def vendProtocol : RowProtocol :=
  { post := .app "eq" (termsOfList [.var 1, .var 0]) }

/-! ## The machine -/

/-- Collecting: take coins until the credit reaches the price, and answer the credit. -/
def collect (price : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun credit => lt credit price
      body := fun _ => Machine.coin unit
      step := fun credit coin => add credit coin }

/-- `sell(item, price)`: collect, vend, then return the change; answer the change. -/
def sell (item price : TermSrc) : Src NativeOp := eff do
  let credit ← collect price
  let _ ← Machine.vend item
  let change := sub credit price
  let _ ← Machine.change change
  return change

/-! ## The application -/

/-- The vending machine: its three event rows, their protocols, and one entry. -/
def application : Application NativeOp :=
  { name := "vendingMachine"
    rows := Machine.rows
    protocols := [("Machine.coin", coinProtocol), ("Machine.vend", vendProtocol)]
    entries :=
      [ { name := "sell", params := [("item", .string), ("price", .nat)]
          body := sell (var "item") (var "price") } ] }

end Examples.VendingMachine
