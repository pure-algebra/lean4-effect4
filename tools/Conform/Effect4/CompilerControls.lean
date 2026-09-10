import Conform.Effect4.LcnfMl
import Conform.Effect4.NormalizationInputs

/-! Focused regressions for the compiler adoption. All expressions below come from the
production builtin table; the evaluator is a separate consumer of that emitted syntax. -/
namespace Conform.Effect4.CompilerControls
open Lean Conform.Lcnf OCaml5

private def decl (name : String) (deps : Array String := #[]) : Lcnf.Translated :=
  { (default : Lcnf.Translated) with
    ocamlName := name
    externDeps := deps
    bind := { name, body := .unit } }

#guard Lcnf.emissionGroups #[decl "a" #["b"], decl "b", decl "c" #["d"], decl "d" #["c"]] =
  .ok [[1], [0], [2, 3]]
#guard Lcnf.emissionGroups #[decl "a", decl "a"] = .error "duplicate emitted name: a"

private def evaluate (name : Name) (args : List Ml.Expr) : Target.TOutcome :=
  match Lcnf.builtin? name with
  | none => .stuck "missing builtin"
  | some rule => match Conform.Effect4.LcnfMl.ofExpr (Lcnf.applyBuiltin rule args) with
    | .error why => .stuck why
    | .ok e => Target.evalT { binds := {} } 2000 [("max_int", .int 4611686018427387903)] e

private def equals (actual : Target.TOutcome) (expected : Target.TValue) : Bool :=
  match actual with | .value v => v.beq expected | _ => false

#guard equals (evaluate `Nat.div [.int 5, .int 0]) (.int 0)
#guard equals (evaluate `Nat.mod [.int 5, .int 0]) (.int 5)
#guard equals (evaluate `UInt8.ofNatTruncate [.int 256]) (.int 255)
#guard equals (evaluate `String.length [.str "é🙂"]) (.int 2)
#guard equals (evaluate `String.toUTF8 [.str "é"]) (Target.TValue.ofList [.int 195, .int 169])
#guard equals (evaluate `Array.get! [.int 77, .listLit [.int 3], .int 2]) (.int 77)
#guard equals (evaluate `Nat.shiftLeft [.int 3, .int 62]) (.int 4611686018427387903)

-- The binder policy recognizes types and the explicitly admitted Row order instance.
#guard (Lcnf.typeParameterIndices `Indexed 1
  (.forallE `n (.const ``Nat []) (.sort .zero) .default)).toOption.isNone

/-- Host checks include the asymmetric comparator that a symmetric equality fixture misses. -/
def hostChecks : List (String × Ml.Expr × Ml.Expr) := [
  ("contains-order", Lcnf.applyBuiltin (Lcnf.builtin? `List.contains).get!
    [.fn ["a", "b"] (.binop "<" (.var "a") (.var "b")), .listLit [.int 3], .int 2], .bool false),
  ("shift-saturation", Lcnf.applyBuiltin (Lcnf.builtin? `Nat.shiftLeft).get! [.int 3, .int 62], .var "max_int"),
  ("array-default", Lcnf.applyBuiltin (Lcnf.builtin? `Array.get!).get! [.int 77, .listLit [.int 3], .int 2], .int 77),
  ("utf8-length", Lcnf.applyBuiltin (Lcnf.builtin? `String.length).get! [.str "é🙂"], .int 2),
  ("utf8-literal-bytes", Lcnf.applyBuiltin (Lcnf.builtin? `String.toUTF8).get! [.str "é🙂\n"],
    .listLit [.int 195, .int 169, .int 240, .int 159, .int 153, .int 130, .int 10]),
  ("u8-clamp", Lcnf.applyBuiltin (Lcnf.builtin? `UInt8.ofNatTruncate).get! [.int 256], .int 255),
  ("div-zero", Lcnf.applyBuiltin (Lcnf.builtin? `Nat.div).get! [.int 5, .int 0], .int 0),
  ("mod-zero", Lcnf.applyBuiltin (Lcnf.builtin? `Nat.mod).get! [.int 5, .int 0], .int 5)]

end Conform.Effect4.CompilerControls
