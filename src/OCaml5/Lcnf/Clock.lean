import Lean
import OCaml5.Ml.Syntax

/-! Local lowering for Effect4's exact clock. It depends only on Lean names and OCaml
syntax. Properties: the nominal carrier alone receives arbitrary precision arithmetic;
number-valued observation calls an explicit profile check; all other Nat lowering is
untouched [by construction]. Host boundary controls live in ocaml/clock/test_clock.ml. -/

namespace OCaml5.Lcnf.Clock
open Lean

def owns (name : Name) : Bool := name == `Effect4.ClockMillis

def type? (name : Name) (args : List Ml.Ty) : Option Ml.Ty :=
  if owns name && args.isEmpty then some (.con "E4_clock.t" []) else none

def constructor? (name : Name) (args : List Ml.Expr) : Option Ml.Expr :=
  match name, args with
  | `Effect4.ClockMillis.zero, [] => some (.var "E4_clock.zero")
  | `Effect4.ClockMillis.positive, [n] => some (Ml.Expr.call "E4_clock.positive" [n])
  | _, _ => none

private def unary (name : String) : Nat × (List Ml.Expr → Ml.Expr) :=
  (1, fun | [a] => Ml.Expr.call name [a] | _ => .unit)

private def binary (name : String) : Nat × (List Ml.Expr → Ml.Expr) :=
  (2, fun | [a, b] => Ml.Expr.call name [a, b] | _ => .unit)

def builtin? (name : Name) : Option (Nat × (List Ml.Expr → Ml.Expr)) :=
  match name with
  | `Effect4.ClockMillis.ofNat => some (unary "E4_clock.of_nat")
  | `Effect4.ClockMillis.toNat => some (unary "E4_clock.to_profile_nat")
  | `Effect4.ClockMillis.add => some (binary "E4_clock.add")
  | `Effect4.ClockMillis.decLe => some (binary "E4_clock.le")
  | `Effect4.ClockMillis.decLt => some (binary "E4_clock.lt")
  | `Effect4.ClockMillis.beq | `Effect4.instDecidableEqClockMillis =>
    some (binary "E4_clock.equal")
  | `Effect4.ClockMillis.toDecimal => some (unary "E4_clock.to_decimal")
  | `Effect4.ClockMillis.ofDecimal => some (unary "E4_clock.of_decimal")
  | _ => none

end OCaml5.Lcnf.Clock
