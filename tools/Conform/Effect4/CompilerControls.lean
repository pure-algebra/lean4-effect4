import Conform.Effect4.LcnfMl
import Conform.Effect4.NormalizationInputs
import Conform.Effect4.LoweringNames
import OCaml5.Lcnf.Gen
import Effect4.Program.Native

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

/-- The program a builtin's form is evaluated in: the runtime library's functions, read from
their reference definitions (`OCaml5.Lcnf.support`), and the evaluator's primitives computed from
the table. -/
private def programOf (support : List Lcnf.Support) : Except String Target.Program :=
  (Conform.Effect4.LcnfMl.supportBinds support).map fun binds =>
    { binds, pe := Conform.Effect4.LcnfMl.primEnv }

/-- A program with no binding: the evaluator's primitives alone. -/
private def bare : Target.Program := { binds := {}, pe := Conform.Effect4.LcnfMl.primEnv }

/-- An expression of the emitted syntax, read and evaluated in a program. A reader's refusal
is the evaluator's. -/
private def run (program : Target.Program) (fuel : Nat) (e : Ml.Expr) : Target.TOutcome :=
  match Conform.Effect4.LcnfMl.ofExpr e with
  | .error why => .stuck why
  | .ok t => Target.evalT program fuel [] t

/-- A row applied to `given`, and the result applied to `rest`: `rest` is empty for a saturated
row, and holds the later arguments of a partial application. -/
private def evaluateIn (support : List Lcnf.Support) (name : Name) (given : List Ml.Expr)
    (rest : List Ml.Expr := []) : Target.TOutcome :=
  match Lcnf.builtin? name, programOf support with
  | none, _ => .stuck "missing builtin"
  | _, .error why => .stuck why
  | some rule, .ok program =>
    run program 2000 (if rest.isEmpty then rule.apply given else .app (rule.apply given) rest)

private def evaluate (name : Name) (given : List Ml.Expr) (rest : List Ml.Expr := []) :
    Target.TOutcome :=
  evaluateIn Lcnf.support name given rest

private def equals (actual : Target.TOutcome) (expected : Target.TValue) : Bool :=
  match actual with | .value v => v.beq expected | _ => false

private def refused (actual : Target.TOutcome) (reason : String) : Bool :=
  match actual with | .stuck why => (why.splitOn reason).length > 1 | _ => false

private def raises (actual : Target.TOutcome) (exn : String) : Bool :=
  match actual with | .exn m => m == exn | _ => false

private def frontier (actual : Target.TOutcome) : Bool :=
  match actual with | .outOfFuel => true | _ => false

/-- A natural as the `Nat` row spells it (`OCaml5.Lcnf.natLiteral`): `Z.of_int n`, or its digits
past the target's `int`. -/
private def nat (n : Nat) : Ml.Expr := Lcnf.natLiteral n

#guard equals (evaluate `Nat.div [.int 5, .int 0]) (.int 0)
#guard equals (evaluate `Nat.mod [.int 5, .int 0]) (.int 5)
#guard equals (evaluate `UInt8.ofNatTruncate [.int 256]) (.int 255)
#guard equals (evaluate `String.length [.str "é🙂"]) (.int 2)
#guard equals (evaluate `String.toUTF8 [.str "é"]) (Target.TValue.ofList [.int 195, .int 169])

/-! ### The runtime library's functions run from their reference definitions

The evaluator reads each body from `OCaml5.Lcnf.support`, the reference definition of the
runtime library's function of that name (`ocaml/lcnf`). A natural is exact, Zarith's `Z.t`
(M4): the product, the power and the shift answer past the target's `int`, and an exponent or a
shift past it is refused at the arithmetic crossing, the target's exception. -/

#guard equals (evaluate `Nat.shiftLeft [.int 3, .int 62]) (.int (3 * 2 ^ 62))
#guard equals (evaluate `Nat.shiftLeft [.int 3, .int 2]) (.int 12)
#guard equals (evaluate `Nat.mul [.int 3, .int 5]) (.int 15)
#guard equals (evaluate `Nat.mul [.int 0, .int 5]) (.int 0)
#guard equals (evaluate `Nat.mul [nat (2 ^ 62 - 1), .int 2]) (.int (2 * (2 ^ 62 - 1)))
#guard equals (evaluate `Nat.pow [.int 2, .int 10]) (.int 1024)
#guard equals (evaluate `Nat.pow [.int 2, .int 64]) (.int (2 ^ 64))
#guard equals (evaluate `Nat.pow [.int 0, .int 0]) (.int 1)
-- an exponent past the target's `int` is refused at the arithmetic crossing
#guard raises (evaluate `Nat.pow [.int 2, nat (2 ^ 62)])
  "Lcnf_crossing.Refused(Lcnf_crossing.Arithmetic, an exponent or a shift past the target's capacity)"
#guard raises (evaluate `Nat.shiftLeft [.int 1, nat (2 ^ 62)])
  "Lcnf_crossing.Refused(Lcnf_crossing.Arithmetic, an exponent or a shift past the target's capacity)"
-- the red control: the target's own `int` product wraps where `Z.mul` is exact
#guard equals (run bare 100 (.binop "*" (.int (2 ^ 62 - 1)) (.int 2))) (.int (-2))

-- A wrong body is what runs: the altered definition changes the answer. Its parameters are
-- swapped, so it subtracts the first operand from the second.
private def swapped : List Lcnf.Support := Lcnf.support.map fun s =>
  if s.name == "Lcnf_nat.sub" then { s with params := ["b", "a"] } else s
#guard equals (evaluateIn swapped `Nat.sub [.int 5, .int 3]) (.int 0)
-- A missing definition, a body outside the reader's fragment and a primitive's name are
-- refusals with their reason, never a silent default.
#guard refused (evaluateIn (Lcnf.support.filter (·.name != "Lcnf_nat.sub")) `Nat.sub [.int 3, .int 5])
  "unbound name `Lcnf_nat.sub`"
#guard refused (evaluateIn [{ name := "lcnf_x", params := ["a"], body := .seq (.var "a") (.var "a") }]
    `Nat.add [.int 1, .int 2])
  "support `lcnf_x`: Ml.Expr.seq"
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

/-! ### Callback functions: the callback goes through `applyT`

`List.exists` and `List.for_all` are the two library functions with a rule that take a function.
Four rows of the table reach them: `List.contains` through the runtime library's
`Lcnf_list.contains`, `List.elem`, `List.any` and `List.all`. -/

/-- An asymmetric instance: `a == b` is `a < b`. -/
private def lessThan : Ml.Expr := .fn ["a", "b"] (.binop "<" (.var "a") (.var "b"))

/-- An instance that divides its first argument by its second. It raises on a zero element. -/
private def dividing : Ml.Expr :=
  .fn ["a", "b"] (.binop "=" (.binop "/" (.var "a") (.var "b")) (.int 1))

/-- `fun e -> 6 / e <op> k`: a predicate that raises when it reaches a zero. -/
private def sixOver (op : String) (k : Nat) : Ml.Expr :=
  .fn ["e"] (.binop op (.binop "/" (.int 6) (.var "e")) (.int k))

private def ints (xs : List Nat) : Ml.Expr := .listLit (xs.map Ml.Expr.int)

-- `contains as a` is `elem a as`: the target is the instance's first argument, so `2 < 3`.
#guard equals (evaluate `List.contains [lessThan, ints [3], .int 2]) (.bool true)
#guard equals (evaluate `List.contains [lessThan, ints [2], .int 3]) (.bool false)
-- The red control of that order: a support body that hands the element first answers the
-- opposite, so the control tells the two orders apart.
private def elementFirst : List Lcnf.Support := Lcnf.support.map fun s =>
  if s.name == "Lcnf_list.contains" then
    { s with body := (Ml.Expr.call "List.exists"
        [.fn ["e"] (.app (.var "inst") [.var "e", .var "a"]), .var "l"]) }
  else s
#guard equals (evaluateIn elementFirst `List.contains [lessThan, ints [3], .int 2]) (.bool false)
-- `List.elem`: the instance takes its first argument by a partial application, and the
-- element through `List.exists`.
#guard equals (evaluate `List.elem [lessThan, .int 2, ints [3]]) (.bool true)
#guard equals (evaluate `List.elem [lessThan, .int 3, ints [2]]) (.bool false)
-- A callback's exception passes through: out of the instance, the closure of the support
-- body, the scan and the support call.
#guard raises (evaluate `List.contains [dividing, ints [0], .int 2]) "Division_by_zero"
#guard raises (evaluate `List.any [ints [1, 0], sixOver "=" 7]) "Division_by_zero"
-- A scan goes on past an element that does not decide, and stops at the one that does. The
-- zero after it is never reached. At the end of the list the answer is the other one.
#guard equals (evaluate `List.any [ints [1, 3, 0], sixOver "=" 2]) (.bool true)
#guard equals (evaluate `List.any [ints [1, 3], sixOver "=" 7]) (.bool false)
#guard equals (evaluate `List.any [ints [], sixOver "=" 7]) (.bool false)
#guard equals (evaluate `List.all [ints [1, 3, 0], sixOver ">" 2]) (.bool false)
#guard equals (evaluate `List.all [ints [1, 3], sixOver ">" 1]) (.bool true)
#guard equals (evaluate `List.all [ints [], sixOver ">" 1]) (.bool true)
-- Under-applied, the row is a function of the rest: the callback arrives later.
#guard equals (evaluate `List.any [ints [1, 3]] [sixOver "=" 2]) (.bool true)
-- The library function itself, applied to its callback first and to its list later.
#guard equals (run bare 200
  (.app (Ml.Expr.call "List.for_all" [sixOver ">" 1]) [ints [1, 3]])) (.bool true)
-- A callback that answers no boolean and a second argument that is no list are refusals.
#guard refused (evaluate `List.any [ints [1], .fn ["e"] (.var "e")])
  "List.exists: the callback did not answer a boolean"
#guard refused (evaluate `List.any [.int 5, sixOver "=" 2]) "List.exists: not a list"
-- The library entries with no rule on the evaluator (the other callback functions and two string
-- functions) are refusals there: a call of one is never a value.
#guard (Lcnf.targetLibrary.filter (·.target matches .unruled)).all fun f =>
  refused (run bare 200 (Ml.Expr.call f.name [sixOver "=" 2, ints [1]])) s!"unbound name `{f.name}`"

/-- A list of `n` ones, as a value: a scan of it costs fuel, and reading it costs none. -/
private def ones (n : Nat) : Target.TValue :=
  Target.TValue.ofList ((List.range n).map fun _ => .int 1)

private def scanOnes (fuel n : Nat) : Target.TOutcome :=
  Target.evalT bare fuel [("l", ones n)]
    (.prim "List.exists" [.fn ["e"] (.prim "=" [.var "e", .int 0]), .var "l"])

-- Exhaustion stays the frontier. With too little fuel a scan is out of fuel, never `false`;
-- with enough it answers.
#guard frontier (scanOnes 30 60)
#guard equals (scanOnes 200 60) (.bool false)
#guard frontier (scanOnes 0 0) && frontier (scanOnes 1 0) && frontier (scanOnes 3 0)
-- At the least fuel that reads both arguments, the empty list answers and one element does not.
#guard equals (scanOnes 4 0) (.bool false)
#guard frontier (scanOnes 4 1)

/-! ### The one labelled call: `Option.value o ~default:d`

The row `Option.getD` writes it. The reader admits that exact shape and refuses every other
labelled application. Both arguments are evaluated, as the call evaluates them. -/

private def someOf (n : Nat) : Ml.Expr := .ctor "Some" [.int n]
private def noneOf : Ml.Expr := .ctor "None" []

#guard equals (evaluate `Option.getD [someOf 3, .int 7]) (.int 3)
#guard equals (evaluate `Option.getD [noneOf, .int 7]) (.int 7)
-- The default is evaluated for `Some` too: its exception is the call's.
#guard raises (evaluate `Option.getD [someOf 1, .binop "/" (.int 1) (.int 0)]) "Division_by_zero"
-- under-applied: `fun _b1 -> Option.value None ~default:_b1`
#guard equals (evaluate `Option.getD [noneOf] [.int 9]) (.int 9)
#guard refused (evaluate `Option.getD [.int 5, .int 7]) "Option.value: not an option and a default"

private def unread (e : Ml.Expr) : Bool :=
  match Conform.Effect4.LcnfMl.ofExpr e with
  | .error why => (why.splitOn "Ml.Expr.appL (a labelled application other than").length > 1
  | .ok _ => false

private def labelled (f : String) (args : List (Ml.ArgLabel × Ml.Expr)) : Ml.Expr :=
  .appL (.var f) args

-- the row's own form is read
#guard !unread (labelled "Option.value" [(.nolabel, someOf 3), (.lbl "default", .int 7)])
-- another label, another order, another function, a missing or a surplus argument, and a head
-- that is not a name: each is refused (an optional label is no form of the syntax)
#guard unread (labelled "Option.value" [(.nolabel, someOf 3), (.lbl "other", .int 7)])
#guard unread (labelled "Option.value" [(.lbl "default", .int 7), (.nolabel, someOf 3)])
#guard unread (labelled "Option.get" [(.nolabel, someOf 3), (.lbl "default", .int 7)])
#guard unread (labelled "Option.value" [(.nolabel, someOf 3)])
#guard unread (labelled "Option.value" [(.lbl "default", .int 7)])
#guard unread (labelled "Option.value"
  [(.nolabel, someOf 3), (.lbl "default", .int 7), (.nolabel, .int 1)])
#guard unread (.appL (.fn ["o"] (.var "o")) [(.nolabel, someOf 3), (.lbl "default", .int 7)])
-- Without its label the call is not the primitive: the name is unbound, a refusal.
#guard refused (run bare 200 (Ml.Expr.call "Option.value" [someOf 3, .int 7]))
  "unbound name `Option.value`"

-- The parameter rule by binder kind: a type parameter is kept, and an instance parameter and
-- a value parameter are dropped. A telescope shorter than its count is the one refusal.
#guard (Lcnf.typeParameterSlots (fun _ => none) `Indexed 3
  (.forallE `α (.sort (.succ .zero))
    (.forallE `inst (.app (.const ``Inhabited [.succ .zero]) (.bvar 0))
      (.forallE `n (.const ``Nat []) (.sort .zero) .default) .instImplicit) .default)).toOption
  == some #[.type 0]
#guard (Lcnf.typeParameterSlots (fun _ => none) `Indexed 2
  (.forallE `n (.const ``Nat []) (.sort .zero) .default)).toOption.isNone

/-- A type with one parameter, a family `R : index → codomain`. -/
private def familyOver (index : Name) (codomain : Level) : Lean.Expr :=
  .forallE `R (.forallE `i (.const index []) (.sort codomain) .default) (.sort (.succ .zero)) .default

/-- A finite index of two constructors, `Fam`; every other name is none. -/
private def twoCtors : Name → Option (List Name)
  | `Fam => some [`Fam.a, `Fam.b]
  | _ => none

-- F3: a family over a finite index is one slot of one OCaml parameter per constructor of the
-- index. The red controls: a family over a type that is no finite index, and a family into
-- `Prop`, are dropped as a value parameter is.
#guard (Lcnf.typeParameterSlots twoCtors `Alg 1 (familyOver `Fam (.succ .zero))).toOption
  == some #[.family 0 [] [`Fam.a, `Fam.b]]
#guard (Lcnf.typeParameterSlots twoCtors `Alg 1 (familyOver ``Nat (.succ .zero))).toOption
  == some #[]
#guard (Lcnf.typeParameterSlots twoCtors `Alg 1 (familyOver `Fam .zero)).toOption == some #[]

-- F3 on the environment. `EffFam` is a finite index of seven constructors, and `Nat` and `Option`
-- are none. `EffAlgebra` declares its family as seven parameters after `Op`, and an instance reads
-- each by reducing the family at a constructor. The red control is `ArgF`: its field
-- `r : R fam` is the family at a variable, which no parameter spells, so it stays unknown.
run_cmd liftTermElabM do
  let env ← getEnv
  unless (Lcnf.finiteIndexIn env ``Effect4.Program.EffFam).map List.length == some 7 do
    throwError "F3: EffFam is not read as a finite index of seven constructors"
  unless (Lcnf.finiteIndexIn env ``Nat).isNone && (Lcnf.finiteIndexIn env ``Option).isNone do
    throwError "F3: Nat or Option is read as a finite index"
  let some alg ← Lcnf.typeInfo? {} {} ``Effect4.Program.EffAlgebra
    | throwError "F3: no declaration for EffAlgebra"
  unless alg.params == ["op", "r_eff", "r_stmt", "r_stmts", "r_effs", "r_action", "r_layer",
      "r_layers"] && alg.unknown.isEmpty do
    throwError "F3: EffAlgebra declares {alg.params}, with unknown fields {alg.unknown}"
  let text := Ml.renderDecl (.types [alg.decl])
  unless (text.splitOn "eff_gen : 'r_stmts -> 'r_eff;").length == 2 do
    throwError "F3: EffAlgebra's field eff_gen is not 'r_stmts -> 'r_eff:\n{text}"
  let op := mkConst ``Effect4.Program.NativeOp
  let self := mkApp2 (mkConst ``Effect4.Program.EffAlgebra [Level.zero]) op
    (mkApp (mkConst ``Effect4.Program.EffSelfCarrier) op)
  let (spelled, _) ← Lcnf.kernelTy {} {} {} self
  unless (spelled.map Ml.renderTy) == some ("(native_op, native_op eff, native_op stmt, " ++
      "native_op stmts, native_op effs, native_op action_term, native_op layer_term, " ++
      "native_op layer_terms) eff_algebra") do
    throwError "F3: EffAlgebra at the identity carrier spells {spelled.map Ml.renderTy}"
  let some argF ← Lcnf.typeInfo? {} {} ``Effect4.Program.ArgF
    | throwError "F3: no declaration for ArgF"
  unless argF.unknown.size == 1 && (argF.unknown[0]!.splitOn "ArgF.r :").length == 2 do
    throwError "F3: ArgF's dependent field is not the one unknown field: {argF.unknown}"

private def host (name : Name) (args : List Ml.Expr) : Ml.Expr :=
  ((Lcnf.builtin? name).map (·.apply args)).getD (.hole s!"no row for {name}" .unit)

/-- What a host check expects of its expression: a value, written as an expression, or an
exception of the target by its name. The name is the OCaml constructor of a constant exception
and the evaluator's message for it: one spelling for both. -/
inductive Expect where
  | value (e : Ml.Expr)
  | raises (exn : String)

/-- The host checks: one expression each, built from a row of the table, with what it expects.
Each runs in compiled OCaml (`Conform.Effect4.Normalization`) and on the target evaluator
(`onTarget`).

They include the asymmetric comparator that a symmetric equality fixture misses.
`List.contains as a` is `elem a as`, and `elem a (b :: bs)` tests `a == b` — the target
first — so `[3].contains 2` under `a == b := a < b` is `2 < 3 = true` (Lean 4.33.1,
`Init/Data/List/Basic.lean`, `elem` and `contains`). The control was first executed on
2026-09-13, once the checkpoint's primitive table gained the array rows; it had expected
`false`, the element-first order, and the emitted row (`OCaml5.Lcnf.builtins`,
`List.contains`) was right. -/
def hostChecks : List (String × Ml.Expr × Expect) := [
  ("contains-order", host `List.contains [lessThan, ints [3], .int 2], .value (.bool true)),
  -- a natural is exact past the target's `int`: each is Zarith's `Z.t`, written by its row
  ("shift-exact", host `Nat.shiftLeft [nat 3, nat 62], .value (nat (3 * 2 ^ 62))),
  ("mul-exact", host `Nat.mul [nat (2 ^ 62 - 1), nat 2], .value (nat (2 * (2 ^ 62 - 1)))),
  ("pow-exact", host `Nat.pow [nat 2, nat 64], .value (nat (2 ^ 64))),
  ("utf8-length", host `String.length [.str "é🙂"], .value (nat 2)),
  -- a byte array is a vector (`Lcnf_array`), so the check reads its bytes as Lean's
  -- `s.toUTF8.data.toList` does
  ("utf8-literal-bytes",
    host `Array.toList [host `ByteArray.data [host `String.toUTF8 [.str "é🙂\n"]]],
    .value (ints [195, 169, 240, 159, 153, 130, 10])),
  ("u8-clamp", host `UInt8.ofNatTruncate [nat 256], .value (.int 255)),
  ("div-zero", host `Nat.div [nat 5, nat 0], .value (nat 0)),
  ("mod-zero", host `Nat.mod [nat 5, nat 0], .value (nat 5)),
  -- the instance's first argument by a partial application, the element through the scan
  ("elem-order", host `List.elem [lessThan, .int 2, ints [3]], .value (.bool true)),
  -- a callback's exception passes through the support function
  ("callback-exception", host `List.contains [dividing, ints [0], .int 2],
    .raises "Division_by_zero"),
  -- a scan stops at the element that decides, before the zero; without one it reaches the end
  ("any-scan", .tuple [host `List.any [ints [1, 3, 0], sixOver "=" 2],
      host `List.any [ints [1, 3], sixOver "=" 7]], .value (.tuple [.bool true, .bool false])),
  ("all-scan", .tuple [host `List.all [ints [1, 3, 0], sixOver ">" 2],
      host `List.all [ints [1, 3], sixOver ">" 1]], .value (.tuple [.bool false, .bool true])),
  -- the labelled call: the option's value or the default, and the default evaluated either way
  ("option-default", .tuple [host `Option.getD [someOf 3, .int 7], host `Option.getD [noneOf, .int 7]],
    .value (.tuple [.int 3, .int 7])),
  ("option-default-eager", host `Option.getD [someOf 1, .binop "/" (.int 1) (.int 0)],
    .raises "Division_by_zero")]

-- Every control that a row names is a host check, and a host check has one name.
#guard Lcnf.builtins.all fun b => b.controls.all fun c => hostChecks.any (·.1 == c)
#guard (hostChecks.map (·.1)).eraseDups.length == hostChecks.length
-- A named exception is spelled as an OCaml constructor: the compiled check matches on it.
#guard hostChecks.all fun (_, _, expected) =>
  match expected with
  | .value _ => true
  | .raises exn => exn.front.isUpper && exn.all fun c => c.isAlphanum || c == '_'

/-- A host check on the target evaluator: the outcome of its expression in `program`, and what
it expects there. An expected value is the outcome of the expected expression. `none` says
that the expected expression itself gave no value. -/
def onTarget (program : Target.Program) (fuel : Nat) (expression : Ml.Expr) (expected : Expect) :
    Target.TOutcome × Option Target.TExpect :=
  (run program fuel expression,
    match expected with
    | .raises exn => some (.raises exn)
    | .value e => match run program fuel e with | .value v => some (.value v) | _ => none)

/-- The host checks that the evaluator answers as the check expects, with the given support
definitions. -/
private def agreeing (support : List Lcnf.Support) : List String :=
  match programOf support with
  | .error _ => []
  | .ok program => hostChecks.filterMap fun (id, expression, expected) =>
    match onTarget program 2000 expression expected with
    | (.value v, some (.value w)) => if v.beq w then some id else none
    | (.exn m, some (.raises n)) => if m == n then some id else none
    | _ => none

-- The evaluator answers every host check as the check expects: the asymmetric
-- `contains-order` among them, through `Lcnf_list.contains` and `List.exists`.
#guard agreeing Lcnf.support == hostChecks.map (·.1)
-- The red control: with the element-first support body, the two checks of the row
-- `List.contains` no longer agree, and every other check does. The order check answers
-- `3 < 2`, and the zero is divided, not divided by.
#guard (hostChecks.map (·.1)).filter (!(agreeing elementFirst).contains ·) ==
  ["contains-order", "callback-exception"]

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

/-- One entry as the emitted OCaml calls it, with Lean's own answer. Each argument and the answer
is a natural, written as the `Nat` row spells one (`Z.of_int n`). -/
def nameChecks : List (String × String × Nat) :=
  LoweringNames.entries.filterMap fun (name, args) =>
    (LoweringNames.leanAnswer name args).map fun answer =>
      (nameId name, String.intercalate " " (Lcnf.globalName name ::
        args.map fun a => "(" ++ Ml.renderExpr 0 (nat a) ++ ")"), answer)

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
  -- the binders that took a reserved name were named again, and the forms kept their names;
  -- helperCap's `lcnf_nat_mul` keeps its own, since every function of the runtime library and of
  -- Zarith is qualified (`Lcnf_nat.sub`, `Z.mul`), which no binder can take
  let body (root : Name) : String :=
    ((translated.decls.find? (·.leanName == root)).map fun d => Ml.renderExpr 0 d.bind.body).getD ""
  let params (root : Name) : List String :=
    ((translated.decls.find? (·.leanName == root)).map fun d => d.bind.params.map (·.1)).getD []
  let mulBody := body ``LoweringNames.mulCap
  unless mulBody == "Z.mul x _mula" do
    throwError "name fixtures: mulCap is {mulBody}"
  for (root, expected) in [
      (``LoweringNames.etaCap, ["_b1_1", "y"]),
      (``LoweringNames.freeCap, ["max_1", "a", "b"]),
      (``LoweringNames.helperCap, ["lcnf_nat_mul", "a", "b"]),
      (``LoweringNames.globalCap, ["conform_effect4_lowering_names_apply_to_1", "y"])] do
    let found := params root
    unless found == expected do
      throwError "name fixtures: {root} binds {found}, expected {expected}"

/-! ### Linkage: a declaration another artifact lowers (4b)

`OCaml5.Lcnf.Gen`'s `--use` hands the translator the declarations another artifact lowers
(`TCtx.links`). The walk stops at one and records it, and its caller writes that artifact's
binding by its module. A qualified name is no free reference, so the binder of `globalCap` that
takes the generated name of `applyTo` keeps that name. The red control is the same walk with no
link: `applyTo` is lowered here, and the binder is named again. -/

run_cmd liftTermElabM do
  let applyTo := ``LoweringNames.applyTo
  let target := Lcnf.globalName applyTo
  let links : Std.HashMap Name OCaml5.Lcnf.Link :=
    ({} : Std.HashMap Name OCaml5.Lcnf.Link).insert applyTo { unit := "Used", name := target }
  let roots := #[``LoweringNames.etaOk, ``LoweringNames.globalCap]
  let linked ← Lcnf.translateClosure roots 60 {} {} #[] links
  let alone ← Lcnf.translateClosure roots
  let lowered (c : OCaml5.Lcnf.Closure) : List Name := c.decls.toList.map (·.leanName)
  let body (c : OCaml5.Lcnf.Closure) (root : Name) : String :=
    ((c.decls.find? (·.leanName == root)).map fun d => Ml.renderExpr 0 d.bind.body).getD ""
  let params (c : OCaml5.Lcnf.Closure) (root : Name) : List String :=
    ((c.decls.find? (·.leanName == root)).map fun d => d.bind.params.map (·.1)).getD []
  let names (s : String) (n : String) : Bool := (s.splitOn n).length > 1
  unless lowered linked == roots.toList && linked.linked == #[applyTo] do
    throwError "linkage: the walk lowered {lowered linked} and linked {linked.linked}"
  unless names (body linked ``LoweringNames.etaOk) ("Used." ++ target)
      && names (body linked ``LoweringNames.globalCap) ("Used." ++ target) do
    throwError "linkage: the callers do not write Used.{target}"
  unless params linked ``LoweringNames.globalCap == [target, "y"] do
    throwError "linkage: globalCap binds {params linked ``LoweringNames.globalCap}"
  unless (Lcnf.hygieneProblems linked.decls).isEmpty do
    throwError "linkage: the hygiene check refuses {Lcnf.hygieneProblems linked.decls}"
  -- red: no link, so the callee is lowered here and the binder that took its name is renamed
  unless (lowered alone).contains applyTo && alone.linked.isEmpty
      && !names (body alone ``LoweringNames.etaOk) "Used."
      && params alone ``LoweringNames.globalCap == [target ++ "_1", "y"] do
    throwError "linkage, red: without the link the walk lowered {lowered alone}"

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
  (.matchE (.var "x") [(.ctor "Some" [.var "x"], .var "x")]) == ["`x`"]
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

/-! ### The runtime column is Lean's

A row's runtime column, read against the environment: the row names a constant of the
environment or a persisted mono declaration (a specialization the compiler made), and its C
symbol is the one that Lean's extern attribute names, or none where Lean names none. The source
evaluator's primitive stands only beside a symbol, by the column's type (`Lcnf.LeanRuntime`). -/

/-- Everything wrong with the runtime column of `rows` in `env`. -/
private def runtimeProblems (env : Environment) (rows : List Lcnf.Builtin) : List String :=
  let mono := OCaml5.Lcnf.persistedMonoIndex env
  rows.flatMap fun b =>
    let named := if env.contains b.lean || mono.contains b.lean then []
      else [s!"builtin {b.lean}: no constant and no mono declaration of this name"]
    let symbol := getExternNameFor env `c b.lean
    let column := if b.runtime.symbol? == symbol then []
      else [s!"builtin {b.lean}: the runtime column names {b.runtime.symbol?}, and Lean {symbol}"]
    named ++ column

run_cmd liftTermElabM do
  let env ← getEnv
  let found := runtimeProblems env Lcnf.builtins
  unless found.isEmpty do throwError "the runtime column: {found}"
  -- the red controls: a row that says `body` for an extern, one with another symbol, and a
  -- constant that the environment does not hold are each refused for their own reason
  let change (lean : Name) (runtime : Lcnf.LeanRuntime) : List Lcnf.Builtin :=
    Lcnf.builtins.map fun b => if b.lean == lean then { b with runtime } else b
  let refused (rows : List Lcnf.Builtin) (reason : String) : Bool :=
    (runtimeProblems env rows).any fun p => (p.splitOn reason).length > 1
  unless refused (change ``Nat.add .body) "builtin Nat.add: the runtime column names none" do
    throwError "the runtime column: an extern written as a body passes"
  unless refused (change ``String.append (.extern "lean_string_push" none))
      "the runtime column names (some lean_string_push), and Lean (some lean_string_append)" do
    throwError "the runtime column: a wrong symbol passes"
  let ghost := { (Lcnf.builtins.headD default) with lean := `Nat.notAConstant }
  unless refused (ghost :: Lcnf.builtins) "builtin Nat.notAConstant: no constant" do
    throwError "the runtime column: a row for no constant passes"

/-! ### A row without a contract does not elaborate

The contract's fields and the runtime column have no default, so an omission is an error of the
elaborator and not a row that reads as exact or as a body. Since M4 a row has one contract: the
receipt under a second spelling went with the `int` spelling of `Nat`. -/

run_cmd liftTermElabM do
  let elaborates (row : Term) : TermElabM Bool :=
    try
      discard <| Term.withoutErrToSorry (Term.elabTermAndSynthesize row none)
      pure true
    catch _ => pure false
  let complete ← `(({ lean := `Nat.add, runtime := .extern "lean_nat_add" (some .natAdd),
                      form := Lcnf.Form.op "+", fidelity := Lcnf.Fidelity.exact,
                      domain := "", crossing := none, controls := [], note := "",
                      cost := "" } : Lcnf.Builtin))
  let contractless ← `(({ lean := `Nat.add, runtime := .body, form := Lcnf.Form.op "+" } : Lcnf.Builtin))
  let noRuntime ← `(({ lean := `Nat.add, form := Lcnf.Form.op "+",
                        fidelity := Lcnf.Fidelity.exact, domain := "", crossing := none,
                        controls := [], note := "", cost := "" } : Lcnf.Builtin))
  -- the crossing has no default either: a row cannot leave out where it refuses
  let noCrossing ← `(({ lean := `Nat.add, runtime := .extern "lean_nat_add" (some .natAdd),
                        form := Lcnf.Form.op "+", fidelity := Lcnf.Fidelity.exact,
                        domain := "", controls := [], note := "", cost := "" } : Lcnf.Builtin))
  unless ← elaborates complete do throwError "the complete row did not elaborate"
  if ← elaborates contractless then throwError "a row without a contract elaborated"
  if ← elaborates noRuntime then throwError "a row without its runtime column elaborated"
  if ← elaborates noCrossing then throwError "a row without its crossing elaborated"

-- The ordinary recipe reader resolves the project's type owner and returns only its artifact.
-- A library without that owner refuses the same project, before the generator writes any file.
#guard
  let library := Lean.Json.parse "{\"format\":\"effect4-lcnf-roots-v3\",\"facade\":{\"module\":\"Effect4\"},\"artifacts\":[{\"out\":\"ocaml/eff/eff_types.ml\",\"import\":[\"Effect4\"],\"cap\":0,\"modules\":true,\"types\":[\"Effect4.Store.Val\"]}]}"
  let absent := Lean.Json.parse "{\"format\":\"effect4-lcnf-roots-v3\",\"facade\":{\"module\":\"Effect4\"},\"artifacts\":[]}"
  let project := Lean.Json.parse "{\"format\":\"effect4-lcnf-roots-v3\",\"facade\":{\"module\":\"Project\"},\"artifacts\":[{\"out\":\"todo_gen.ml\",\"import\":[\"Todo\"],\"cap\":4000,\"linkage\":[\"Todo.repository\"],\"open\":{\"module\":\"Eff_types\",\"artifact\":\"ocaml/eff/eff_types.ml\"}}]}"
  match library, absent, project with
  | .ok owner, .ok missing, .ok recipe =>
    match OCaml5.Lcnf.Gen.projectArgvs owner recipe, OCaml5.Lcnf.Gen.projectArgvs missing recipe with
    | .ok runs, .error _ => runs.size == 1 &&
        (runs[0]!.dropWhile (· != "--open-types")).take 2 == ["--open-types", "Effect4.Store.Val"] &&
        runs[0]!.take 2 == ["--out", "todo_gen.ml"]
    | _, _ => false
  | _, _, _ => false

end Conform.Effect4.CompilerControls
