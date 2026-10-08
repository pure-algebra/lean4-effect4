import Effect4.Laws.Codegen.PrintTyped
import Effect4.Program.Native
import TypeScript.Render

/-!
# The typed print at a join: the battery of slice P2a

`printTypedAt` (`Codegen/PrintTyped.lean`) is the table-driven print with the node's address.
While the guards stand no call has a join, so the typed print of every program is its print
(`printTyped_eq_print`, `Laws/Codegen/PrintTyped.lean`). These lines run the print at a hand
annotation, the one that UNGUARD's match by bounds answers at a join. Each line is a finite
evaluation or a control (decisions row 301).
-/

namespace Test.Codegen.PrintTyped

open Effect4.Program Effect4.Codegen.Templates
open TypeScript (house0)
open TypeScript.Render (expr)

/-- `Ref.modify` whose term answers the pair `["s", a]`, called on the cell `a0`. -/
def modify : Eff NativeOp :=
  .perform (.refModifyWith (.app "pair" (.cons (.lit (.str "s")) (.cons (.var 1) .nil)))) (.var 0)

/-- The call after a first program: it stands at the address `[1]`. -/
def after : Eff NativeOp := .bind (.succeed (.var 0)) modify

/-- An annotation that answers the join `number, number | string` at one address. -/
def joinAt (path : List Nat) : List Nat → Option (List Ty) :=
  fun p => if p = path then some [.nat, .union .nat .string] else none

-- finite evaluation: the call at a join carries the row's bindings on its head, `A` then `B`
#guard (printTypedAt nativeSignature (joinAt []) 1 modify).map (expr house0 0) =
  .ok "Ref.modify<number, number | string>(a0, (a1) => pair(\"s\", a1))"
-- finite evaluation: a child's address is its parent's and its index among the node arguments
#guard (printTypedAt nativeSignature (joinAt [1]) 1 after).map (expr house0 0) =
  .ok "Effect.flatMap(Effect.succeed(a0), (a1) => Ref.modify<number, number | string>(a0, (a2) => pair(\"s\", a1)))"
-- control: an annotation at another address leaves the call as the print prints it
#guard (printTypedAt nativeSignature (joinAt [0]) 1 after).map (expr house0 0) =
  (print nativeSignature 1 after).map (expr house0 0)

end Test.Codegen.PrintTyped
