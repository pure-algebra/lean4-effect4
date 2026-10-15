import Lean
import OCaml5.Ml.Syntax

/-! Local lowering for Effect4's exact clock: its two constructors. It depends only on Lean
names and OCaml syntax. The clock's type is a row of the type table (`OCaml5.Lcnf.typeRows`),
and its operations are rows of the builtin table (`OCaml5.Lcnf.Builtins`), each with its
contract. Properties: the nominal carrier alone receives arbitrary precision arithmetic;
number-valued observation calls an explicit profile check; all other Nat lowering is untouched
[by construction]. Host boundary controls live in ocaml/clock/test_clock.ml. -/

namespace OCaml5.Lcnf.Clock
open Lean

def owns (name : Name) : Bool := name == `Effect4.ClockMillis

def constructor? (name : Name) (args : List Ml.Expr) : Option Ml.Expr :=
  match name, args with
  | `Effect4.ClockMillis.zero, [] => some (.var "E4_clock.zero")
  | `Effect4.ClockMillis.positive, [n] => some (Ml.Expr.call "E4_clock.positive" [n])
  | _, _ => none

end OCaml5.Lcnf.Clock
