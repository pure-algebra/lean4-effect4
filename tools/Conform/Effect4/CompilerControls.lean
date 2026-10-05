import Conform.Effect4.LcnfMl
import Conform.Effect4.NormalizationInputs
import Conform.Effect4.LoweringNames

/-! Focused regressions for the compiler adoption. All expressions below come from the
production builtin table (`OCaml5.Lcnf.builtins`); the evaluator is a separate consumer of that
emitted syntax. A control here is finite evidence: it runs a row at chosen points. The value
rows name their controls (`Builtin.controls`), and `hostChecks` is where those names resolve. -/
namespace Conform.Effect4.CompilerControls
open Lean Elab Command Conform.Lcnf OCaml5

private def decl (name : String) (deps : Array String := #[]) : Lcnf.Translated :=
  { (default : Lcnf.Translated) with
    ocamlName := name
    externDeps := deps
    bind := { name, body := .unit } }

#guard Lcnf.emissionGroups #[decl "a" #["b"], decl "b", decl "c" #["d"], decl "d" #["c"]] =
  .ok [[1], [0], [2, 3]]
#guard Lcnf.emissionGroups #[decl "a", decl "a"] = .error "duplicate emitted name: a"

/-- The program a builtin's form is evaluated in: the support functions, read from the
definitions the prelude prints, and `max_int`. -/
private def programOf (support : List Lcnf.Support) : Except String Target.Program :=
  (Conform.Effect4.LcnfMl.supportBinds { bits := 63 } support).map fun binds =>
    { binds, pe := { word := { bits := 63 } } }

/-- A row applied to `given`, and the result applied to `rest`: `rest` is empty for a saturated
row, and holds the later arguments of a partial application. -/
private def evaluateIn (support : List Lcnf.Support) (name : Name) (given : List Ml.Expr)
    (rest : List Ml.Expr := []) : Target.TOutcome :=
  match Lcnf.builtin? name, programOf support with
  | none, _ => .stuck "missing builtin"
  | _, .error why => .stuck why
  | some rule, .ok program =>
    let applied := if rest.isEmpty then rule.apply given else .app (rule.apply given) rest
    match Conform.Effect4.LcnfMl.ofExpr applied with
    | .error why => .stuck why
    | .ok e => Target.evalT program 2000 [] e

private def evaluate (name : Name) (given : List Ml.Expr) (rest : List Ml.Expr := []) :
    Target.TOutcome :=
  evaluateIn Lcnf.support name given rest

private def equals (actual : Target.TOutcome) (expected : Target.TValue) : Bool :=
  match actual with | .value v => v.beq expected | _ => false

private def refused (actual : Target.TOutcome) (reason : String) : Bool :=
  match actual with | .stuck why => (why.splitOn reason).length > 1 | _ => false

private def maxInt : Target.TValue := .int 4611686018427387903

#guard equals (evaluate `Nat.div [.int 5, .int 0]) (.int 0)
#guard equals (evaluate `Nat.mod [.int 5, .int 0]) (.int 5)
#guard equals (evaluate `UInt8.ofNatTruncate [.int 256]) (.int 255)
#guard equals (evaluate `String.length [.str "é🙂"]) (.int 2)
#guard equals (evaluate `String.toUTF8 [.str "é"]) (Target.TValue.ofList [.int 195, .int 169])
#guard equals (evaluate `Array.get! [.int 77, .listLit [.int 3], .int 2]) (.int 77)

/-! ### The support functions run from their own definitions

The evaluator reads each support body from `OCaml5.Lcnf.support`, the list the prelude prints.
The saturating rows answer as before, and now through `lcnf_nat_mul`, `lcnf_nat_pow` and
`lcnf_nat_shift_left`. -/

#guard equals (evaluate `Nat.shiftLeft [.int 3, .int 62]) maxInt
#guard equals (evaluate `Nat.shiftLeft [.int 3, .int 2]) (.int 12)
#guard equals (evaluate `Nat.mul [.int 3, .int 5]) (.int 15)
#guard equals (evaluate `Nat.mul [.int 0, .int 5]) (.int 0)
#guard equals (evaluate `Nat.mul [.var "max_int", .int 2]) maxInt
#guard equals (evaluate `Nat.pow [.int 2, .int 10]) (.int 1024)
#guard equals (evaluate `Nat.pow [.int 2, .int 64]) maxInt
#guard equals (evaluate `Nat.pow [.int 0, .int 0]) (.int 1)

-- A wrong body is what runs: the altered definition changes the answer.
private def squaring : List Lcnf.Support := Lcnf.support.map fun s =>
  if s.name == "lcnf_nat_mul" then { s with body := .binop "*" (.var "a") (.var "a") } else s
#guard equals (evaluateIn squaring `Nat.mul [.int 3, .int 5]) (.int 9)
-- A missing definition, a body outside the reader's fragment and a primitive's name are
-- refusals with their reason, never a silent default.
#guard refused (evaluateIn (Lcnf.support.filter (·.name != "lcnf_nat_mul")) `Nat.mul [.int 3, .int 5])
  "unbound name `lcnf_nat_mul`"
#guard refused (evaluateIn [{ name := "lcnf_x", params := ["a"], body := .raw "a" }] `Nat.add [.int 1, .int 2])
  "support `lcnf_x`: Ml.Expr.raw"
#guard refused (evaluateIn [{ name := "max", params := ["a"], body := .var "a" }] `Nat.add [.int 1, .int 2])
  "support `max`: the evaluator has a primitive of this name"

/-! ### Application: partial, exact and surplus

A row applied to fewer arguments is a function of the rest. A row applied to more hands the
surplus to its result. Lean's compiled definitions give the expected answers of the persisted
fixtures below; these are the same shapes built by hand. -/

#guard equals (evaluate `Nat.add [.int 3] [.int 5]) (.int 8)
#guard equals (evaluate `Nat.sub [.int 3] [.int 5]) (.int 0)
#guard equals (evaluate `Nat.sub [.int 5] [.int 3]) (.int 2)
#guard equals (evaluate `Nat.mul [.int 3] [.int 5]) (.int 15)
#guard equals (evaluate `Nat.decEq [] [.int 3, .int 3]) (.bool true)
#guard equals (evaluate `Nat.decLt [] [.int 3, .int 3]) (.bool false)
-- the pair's first component is a function, and the surplus argument goes to it
#guard equals
  (evaluate `Prod.fst [.tuple [.fn ["y"] (.binop "+" (.var "y") (.int 1)), .int 0], .int 5])
  (.int 6)
-- the operands keep their order: 5 - 3 is 2, and 3 - 5 stops at 0
#guard equals (evaluate `Nat.sub [.int 5, .int 3]) (.int 2)
#guard equals (evaluate `Nat.sub [.int 3, .int 5]) (.int 0)

-- The binder policy recognizes types and the explicitly admitted Row order instance.
#guard (Lcnf.typeParameterIndices `Indexed 1
  (.forallE `n (.const ``Nat []) (.sort .zero) .default)).toOption.isNone

private def host (name : Name) (args : List Ml.Expr) : Ml.Expr :=
  ((Lcnf.builtin? name).map (·.apply args)).getD (.hole s!"no row for {name}" .unit)

/-- Host checks include the asymmetric comparator that a symmetric equality fixture misses.
`List.contains as a` is `elem a as`, and `elem a (b :: bs)` tests `a == b` — the target
first — so `[3].contains 2` under `a == b := a < b` is `2 < 3 = true` (Lean 4.33.1,
`Init/Data/List/Basic.lean`, `elem` and `contains`). The control was first executed on
2026-09-13, once the checkpoint's primitive table gained the array rows; it had expected
`false`, the element-first order, and the emitted row (`OCaml5.Lcnf.builtins`,
`List.contains`) was right. -/
def hostChecks : List (String × Ml.Expr × Ml.Expr) := [
  ("contains-order", host `List.contains
    [.fn ["a", "b"] (.binop "<" (.var "a") (.var "b")), .listLit [.int 3], .int 2], .bool true),
  ("shift-saturation", host `Nat.shiftLeft [.int 3, .int 62], .var "max_int"),
  ("mul-saturation", host `Nat.mul [.var "max_int", .int 2], .var "max_int"),
  ("pow-saturation", host `Nat.pow [.int 2, .int 64], .var "max_int"),
  ("array-default", host `Array.get! [.int 77, .listLit [.int 3], .int 2], .int 77),
  ("utf8-length", host `String.length [.str "é🙂"], .int 2),
  ("utf8-literal-bytes", host `String.toUTF8 [.str "é🙂\n"],
    .listLit [.int 195, .int 169, .int 240, .int 159, .int 153, .int 130, .int 10]),
  ("u8-clamp", host `UInt8.ofNatTruncate [.int 256], .int 255),
  ("div-zero", host `Nat.div [.int 5, .int 0], .int 0),
  ("mod-zero", host `Nat.mod [.int 5, .int 0], .int 5)]

-- Every control that a row names is a host check, and a host check has one name.
#guard Lcnf.builtins.all fun b => b.controls.all fun c => hostChecks.any (·.1 == c)
#guard (hostChecks.map (·.1)).eraseDups.length == hostChecks.length

/-! ### Names: the persisted fixtures

`Conform.Effect4.LoweringNames` holds definitions whose binders take the route's own names. The
translator reads their persisted mono LCNF, as it reads the machine's. Three checks follow:
the translated declarations pass the hygiene check, the target evaluator answers each entry as
the compiled Lean definition does, and the hygiene check itself refuses the shapes that
captured. The compiled OCaml of the same entries runs in `Conform.Effect4.Normalization`. -/

/-- The roots of the name fixtures. -/
def nameRoots : Array Name := (LoweringNames.entries.map (·.1)).toArray

/-- The stable name of a name fixture, in every lane that runs it. -/
def nameId (name : Name) : String := s!"names/{name.getString!}"

/-- One entry as the emitted OCaml calls it, with Lean's own answer. -/
def nameChecks : List (String × String × Nat) :=
  LoweringNames.entries.filterMap fun (name, args) =>
    (LoweringNames.leanAnswer name args).map fun answer =>
      (nameId name, String.intercalate " " (Lcnf.globalName name :: args.map toString), answer)

#guard nameChecks.length == LoweringNames.entries.length

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure nameRoots
  unless translated.todos.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
    throwError "name fixtures refused: {translated.todos}; {translated.missing}; {translated.frontier}"
  let captures := Lcnf.hygieneProblems translated.decls
  unless captures.isEmpty do
    throwError "name fixtures: the hygiene check refuses the translation: {captures}"
  let program ← match Conform.Effect4.LcnfMl.assemble translated.decls with
    | .ok program => pure program
    | .error why => throwError "name fixtures: {why}"
  for (name, args) in LoweringNames.entries do
    let some expected := LoweringNames.leanAnswer name args
      | throwError "name fixtures: no Lean answer for {name}"
    let values := args.toArray.map fun a => Target.TValue.int (Int.ofNat a)
    match Target.runT program 4000 (Lcnf.globalName name) values with
    | .value v =>
      unless v.beq (.int (Int.ofNat expected)) do
        throwError "name fixtures: {name} {args}: Lean answers {expected}, the target {v.render}"
    | other => throwError "name fixtures: {name} {args}: {other.render}"
  -- the binders that took a reserved name were named again, and the forms kept their names
  let body (root : Name) : String :=
    ((translated.decls.find? (·.leanName == root)).map fun d => Ml.renderExpr 0 d.bind.body).getD ""
  let params (root : Name) : List String :=
    ((translated.decls.find? (·.leanName == root)).map fun d => d.bind.params.map (·.1)).getD []
  let mulBody := body ``LoweringNames.mulCap
  unless mulBody == "lcnf_nat_mul x _mula" do
    throwError "name fixtures: mulCap is {mulBody}"
  for (root, expected) in [
      (``LoweringNames.etaCap, ["_b1_1", "y"]),
      (``LoweringNames.freeCap, ["max_1", "a", "b"]),
      (``LoweringNames.helperCap, ["lcnf_nat_mul_1", "a", "b"]),
      (``LoweringNames.globalCap, ["conform_effect4_lowering_names_apply_to_1", "y"])] do
    let found := params root
    unless found == expected do
      throwError "name fixtures: {root} binds {found}, expected {expected}"

/-! ### Names: the check refuses what captured

Three bindings as the route wrote them before the table was data, and one that hides a name its
body means as free. `Ml.shadowDiags` refuses each for its own binder, and passes the forms the
route writes now. -/

private def captured (guarded : List String) (params : List String) (body : Ml.Expr) :
    List String :=
  (Ml.shadowDiags guarded { name := "f", params := params.map fun p => (p, none), body }).map
    (·.detail)

-- `let _mula = x in let _mulb = _mula in …` under a parameter `_mula`
#guard captured [] ["x", "_mula"]
  (.letIn "_mula" (.var "x") (.letIn "_mulb" (.var "_mula")
    (.binop "*" (.var "_mula") (.var "_mulb")))) == ["`_mula`"]
-- `fun _b1 -> _b1 + _b1` under a parameter `_b1`
#guard captured [] ["_b1"] (.fn ["_b1"] (.binop "+" (.var "_b1") (.var "_b1"))) == ["`_b1`"]
-- a parameter `max` in a body that means the library's `max`
#guard captured ["max"] ["max", "a"] (Ml.Expr.call "max" [.int 0, .var "a"]) == ["`max`"]
-- a pattern variable that hides a parameter
#guard captured [] ["x"]
  (.matchE (.var "x") [.mk (.ctor "Some" [.var "x"]) none (.var "x")]) == ["`x`"]
-- the same eta binder in two sibling scopes hides nothing
#guard captured [] ["x"]
  (.letIn "p" (.fn ["_b1"] (.var "_b1")) (.letIn "q" (.fn ["_b1"] (.var "_b1")) (.var "x")))
    == []
-- a parameter that repeats an earlier one of its own batch, at the top and in a function
#guard captured [] ["x", "x"] (.var "x") == ["`x`"]
#guard captured [] ["x"] (.fn ["y", "y"] (.var "y")) == ["`y`"]
-- `_` and `()` bind nothing, however often they stand
#guard captured [] ["_", "_"] (.fn ["()"] (.fn ["()"] .unit)) == []

/-! ### Names: a generated declaration does not take a hand function's name

The hand prelude comes first in the engine's module. A generated declaration with the name of a
hand function would answer every later call of the extern row that names it. -/

private def calling (name : String) (head : String) : Lcnf.Translated :=
  { (default : Lcnf.Translated) with
    ocamlName := name
    leanName := Name.mkSimple name
    externHeads := #[head]
    bind := { name, body := Ml.Expr.call head [.unit] } }

#guard (Lcnf.hygieneProblems #[decl "sh_machine_finished", calling "caller" "sh_machine_finished"]).length == 1
#guard (Lcnf.hygieneProblems #[decl "machine_finished", calling "caller" "sh_machine_finished"]).isEmpty

/-! ### A row without a contract does not elaborate

The contract's fields have no default, so the omission is an error of the elaborator and not a
row that reads as exact. -/

run_cmd liftTermElabM do
  let elaborates (row : Term) : TermElabM Bool :=
    try
      discard <| Term.withoutErrToSorry (Term.elabTermAndSynthesize row none)
      pure true
    catch _ => pure false
  let complete ← `(({ lean := `Nat.add, form := Lcnf.Form.op "+", fidelity := Lcnf.Fidelity.exact,
                      domain := "", controls := [], note := "", cost := "" } : Lcnf.Builtin))
  let bare ← `(({ lean := `Nat.add, form := Lcnf.Form.op "+" } : Lcnf.Builtin))
  unless ← elaborates complete do throwError "the complete row did not elaborate"
  if ← elaborates bare then throwError "a row without a contract elaborated"

end Conform.Effect4.CompilerControls
