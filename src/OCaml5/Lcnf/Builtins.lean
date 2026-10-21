import Lean
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Check
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.TypeRows
import OCaml5.Lcnf.Prim

/-!
# OCaml5.Lcnf.Builtins

**What it is.** The one primitive table of the LCNF route: one row for each Lean constant that
the route does not translate from its own body. A row is data: the constant, how Lean itself
realizes it (its body, or a C function of Lean's runtime and the source evaluator's primitive),
its OCaml form and its contract. Beside the rows stands the target's library, one entry for each
function and operator a form names, with the target evaluator's rule for it, and the runtime
library's functions that a form names (`support`, `ocaml/lcnf`), each with the definition the
target evaluator runs. The lookup, the reserved names, the fidelity inventory and both evaluators'
primitive tables (`sourcePrims`, `targetArities`, `targetScans`) are computed from the rows.

**Depends on.** `OCaml5.Ml.Syntax` (a form is OCaml syntax), `OCaml5.Ml.Render` (a form's
spelling in a report), `OCaml5.Lcnf.Externs` (`stripRedArg`), `OCaml5.Lcnf.TypeRows` (the
contract's class, `Fidelity`, and the crossing a refusing row names, `Crossing`, which the type
rows share; a natural's literal, `natLiteral`), `Conform.Lcnf.Semantics` (the source evaluator's
primitives, `Prim`).

**Properties.**
* **One owner.** A constant has a row in `builtins` or the route translates it. `builtin?`,
  `runtimeModules`, `reservedNames`, `Form.spelling` and the evaluators' tables are computed from
  `builtins`, `support` and `targetLibrary`. No second list names a row: *by construction*.
* **The runtime column is Lean's.** A row's `runtime` names the C symbol of Lean's runtime
  exactly when Lean's extern attribute names one. A row holds the source evaluator's primitive
  only beside such a symbol, since that evaluator reads every other constant's body: *checked*
  against the environment (`Conform.Effect4.CompilerControls`).
* **A form binds nothing at a call site.** An inline body is binder-free. A support function is
  a closed function of the runtime library, named by its path. An application adds a binder only
  by eta-expansion, and the eta binders are in `reservedNames`: *checked* (`problemsOf`, the
  `#guard`s at the foot).
* **A form states what it needs.** Every free name of a row is a function of `targetLibrary`
  or of `support`, and every operator is an operator of `targetLibrary`. A body outside its
  fragment is refused: *checked* (`problemsOf`).
* **Arguments are values.** `Builtin.apply` substitutes its arguments into an inline body, which
  is exact for an atom. `Form.strict` holds when a body evaluates each parameter exactly once;
  `Translate.applyBuiltin` binds every other argument that is not an atom before the form.
* **Every row has one contract.** `fidelity`, `domain`, `crossing`, `controls` and `note` have no
  default. The class is a reading of the row against the Lean definition; no theorem proves a
  row. An exact row states no domain and no crossing, and a row exact under a domain states its
  domain and the crossing at which it refuses outside it (`contractProblems`): *checked*.
* **Numbers are exact (M4, decisions row 417 (1)).** A natural, an integer, a bit vector and a
  64-bit word are Zarith's `Z.t` (`OCaml5.Lcnf.typeRows`), and their rows are Zarith's exact
  operations, or the runtime library's exact helpers (`Lcnf_nat`). Nothing saturates and nothing
  wraps. The only refusals are crossings: an exponent or a shift past the target's `int`
  (arithmetic), a natural taken as an index past the target's `int` (index), and the program's
  own `panic`: *checked* (the census `#guard`s).

**What it does not own.** The type rows (`OCaml5.Lcnf.TypeRows`), the native constructors
(`OCaml5.Lcnf.Native`), and the extern table of a run (`OCaml5.Lcnf.Externs`).
-/

namespace OCaml5.Lcnf

open Lean

/-! ## 1. Forms -/

/-- The OCaml realization of a row. Each form denotes one closed function of the target. -/
inductive Form where
  /-- `fun params -> body`, written in place at a call site. `body` is binder-free. -/
  | inline (params : List String) (body : Ml.Expr)
  /-- A function of the runtime library that `support` defines for the target evaluator. -/
  | support (name : String)
  /-- A function of the target's own library, named in `targetLibrary`: a trusted leaf. -/
  | library (name : String)
  deriving Inhabited

/-- How Lean itself realizes a row's constant. -/
inductive LeanRuntime where
  /-- The constant has a Lean body: Lean's compiler compiles it, and the source evaluator reads
  it. The route short-circuits it with the row's form. -/
  | body
  /-- An `@[extern]` of Lean's runtime: the C function that implements it, and the source
  evaluator's primitive for it (`Conform.Lcnf.Prim`), or `none` where that evaluator has none. -/
  | extern (symbol : String) (source : Option Prim)
  deriving Inhabited

/-- The C symbol of a realization, when it is one of Lean's runtime. -/
def LeanRuntime.symbol? : LeanRuntime → Option String
  | .body => none
  | .extern symbol _ => some symbol

/-- One row of the table. No field of the contract or of a column has a default. -/
structure Builtin where
  /-- The Lean constant, as `stripRedArg` leaves it. -/
  lean : Name
  /-- How Lean realizes the constant: the source evaluator's column and the C column. -/
  runtime : LeanRuntime
  form : Form
  fidelity : Fidelity
  /-- The domain on which the row is exact (`""` when the class is `exact`). -/
  domain : String
  /-- The crossing at which the row refuses outside its domain (`none` when it is exact). -/
  crossing : Option Crossing
  /-- The identifiers of the finite controls that run this row
  (`Conform.Effect4.CompilerControls`). Empty when no control runs it. -/
  controls : List String
  /-- Why: the difference, or the argument that there is none. -/
  note : String
  /-- The cost where it differs from Lean's. A cost is not a difference of meaning. -/
  cost : String
  deriving Inhabited

/-- A function of the runtime library (`ocaml/lcnf`), with the definition the target evaluator
runs: its qualified name, its parameters and its body. -/
structure Support where
  name : String
  params : List String
  body : Ml.Expr
  /-- Whether the body calls the function itself. -/
  recursive : Bool := false
  deriving Inhabited

/-- The definition as an OCaml binding. -/
def Support.bind (s : Support) : Ml.Bind :=
  { name := s.name, params := s.params.map fun p => (p, none), body := s.body }

/-! ## 2. What a body uses

Two fragments of `Ml.Expr`. An inline body is built from variables, literals, constructors,
applications, labelled applications, infix operators, conditionals and list literals. A support
body may also bind, by `let` and by `fun`. Everything else is outside both. -/

/-- The operators whose right operand is evaluated only when the left one does not decide. -/
def lazyOperators : List String := ["&&", "||"]

/-- The facts one traversal reads off a body. -/
structure Uses where
  /-- The free variable occurrences, in order and with repetition. -/
  free : List String := []
  /-- The free occurrences that every evaluation of the body evaluates. -/
  always : List String := []
  /-- The infix operators. -/
  ops : List String := []
  /-- The names the body binds. -/
  binders : List String := []
  deriving Repr, Inhabited

instance : Append Uses where
  append a b := { free := a.free ++ b.free, always := a.always ++ b.always,
                  ops := a.ops ++ b.ops, binders := a.binders ++ b.binders }

/-- A part of a body that is not always evaluated: an arm, a lazy operand, a function body. -/
def Uses.deferred (u : Uses) : Uses := { u with always := [] }

/-- The uses of a list of parts, in order: `none` when one part leaves its fragment. -/
private def usesAll : List (Option Uses) → Option Uses
  | [] => some {}
  | u :: rest => do
    let a ← u
    let b ← usesAll rest
    return a ++ b

/-- What a body uses under the names it is handed, or `none` when it leaves its fragment, as an
algebra of the expression fold (`OCaml5.Ml.Fold`). `binding` admits `let` and `fun`: a support
body may bind and an inline body may not. -/
def usesAlg (binding : Bool) : Ml.ExprAlgebra (fun _ => List String → Option Uses) where
  expr_var n := fun bound => some (if bound.contains n then {} else { free := [n], always := [n] })
  expr_int _ := fun _ => some {}
  expr_str _ := fun _ => some {}
  expr_bool _ := fun _ => some {}
  expr_unit := fun _ => some {}
  expr_ctor _ args := fun bound => usesAll (args.map (· bound))
  expr_app f args := fun bound => do
    let a ← f bound
    let b ← usesAll (args.map (· bound))
    return a ++ b
  expr_appL f args := fun bound => do
    let a ← f bound
    let b ← usesAll (args.map (·.2 bound))
    return a ++ b
  expr_binop op l r := fun bound => do
    let a ← l bound
    let b ← r bound
    let b := if lazyOperators.contains op then b.deferred else b
    return { free := a.free ++ b.free, always := a.always ++ b.always,
             ops := op :: (a.ops ++ b.ops), binders := a.binders ++ b.binders }
  expr_ifThen c t e := fun bound => do
    let a ← c bound
    let b ← t bound
    let d ← e bound
    return a ++ b.deferred ++ d.deferred
  expr_listLit items := fun bound => usesAll (items.map (· bound))
  expr_letIn n v b := fun bound =>
    if binding then do
      let a ← v bound
      let c ← b (n :: bound)
      return { free := a.free ++ c.free, always := a.always ++ c.always,
               ops := a.ops ++ c.ops, binders := n :: (a.binders ++ c.binders) }
    else none
  expr_fn ps b := fun bound =>
    if binding then do
      let c ← b (ps ++ bound)
      return { c.deferred with binders := ps ++ c.binders }
    else none
  -- outside both fragments
  expr_letAttr _ _ _ _ := fun _ => none
  expr_letRec _ _ _ _ := fun _ => none
  expr_matchE _ _ := fun _ => none
  expr_record _ := fun _ => none
  expr_field _ _ := fun _ => none
  expr_tuple _ := fun _ => none
  expr_annot _ _ := fun _ => none
  expr_hole _ _ := fun _ => none
  expr_assertE _ := fun _ => none
  expr_fnMatch _ := fun _ => none
  expr_seq _ _ := fun _ => none
  expr_letPat _ _ _ := fun _ => none
  expr_ifUnit _ _ := fun _ => none
  expr_commented _ _ := fun _ => none
  expr_pack _ _ := fun _ => none

/-- What a body uses under the names `bound`, or `none` when it leaves its fragment. -/
def usesExpr (binding : Bool) (bound : List String) (e : Ml.Expr) : Option Uses :=
  Ml.cata_expr (usesAlg binding) e bound

/-- Put values in the place of an inline body's parameters: the fold's identity algebra with
the variables replaced. The body binds nothing, so no name of a value can be captured;
`problemsOf` refuses a table whose inline body leaves the fragment. -/
def substAlg (σ : List (String × Ml.Expr)) : Ml.ExprAlgebra Ml.ExprSelfCarrier :=
  { Ml.ExprAlgebra.id with expr_var := fun n => (σ.lookup n).getD (.var n) }

/-- An inline body with its parameters replaced. -/
def substExpr (σ : List (String × Ml.Expr)) (e : Ml.Expr) : Ml.Expr := Ml.cata_expr (substAlg σ) e

/-! ## 3. The target's library and the runtime library -/

/-- How the target evaluator (`Conform.Lcnf.Target`, `tools/Conform/Lcnf/SemanticsTarget.lean`)
answers a function or an operator of the target's library. -/
inductive TargetRule where
  /-- `Target.applyPrim` answers it from its argument values, under this spelling. -/
  | prim (spelling : String)
  /-- `Target.scanT` applies the callback along the list, and stops at the answer `stop`. -/
  | scan (stop : Bool)
  /-- No rule: a call of it is a refusal on the evaluator, and only compiled OCaml runs it. -/
  | unruled
  deriving Inhabited

/-- One function, value or infix operator of the target's own library. It is a trusted leaf: the
route does not define it. -/
structure LibFn where
  name : String
  /-- The number of arguments it takes; an infix operator takes two. -/
  arity : Nat
  /-- An infix operator rather than a function or a value. -/
  isInfix : Bool
  target : TargetRule
  deriving Inhabited

private def infixOp (symbol : String) : LibFn :=
  { name := symbol, arity := 2, isInfix := true, target := .prim symbol }
private def prim (name : String) (arity : Nat) : LibFn :=
  { name, arity, isInfix := false, target := .prim name }
private def scan (name : String) (stop : Bool) : LibFn :=
  { name, arity := 2, isInfix := false, target := .scan stop }
private def unruled (name : String) (arity : Nat) : LibFn :=
  { name, arity, isInfix := false, target := .unruled }

/-- The target's library: every function, value and operator that a form or a support body may
name, with the number of arguments it takes and the target evaluator's rule for it. The `Z`
functions are Zarith's, the spelling of every natural and integer (`OCaml5.Lcnf.typeRows`); the
target evaluator answers each over unbounded integers. `Lcnf_crossing.refuse` is the runtime
library's refusal at a named crossing. The four `Lcnf_string` functions are the string primitives
of the runtime library (`ocaml/lcnf`, library `effect4_lcnf`); the target evaluator answers two of
them by name and has no rule for the other two. The `Lcnf_array` functions are the runtime
library's vector, which the target evaluator models by its element list. The labelled call
`Option.value o ~default:d` is the evaluator's primitive `Option.value~default`
(`Conform.Effect4.LcnfMl.ofExpr`). -/
def targetLibrary : List LibFn := [
  infixOp "=", infixOp "<", infixOp "<=", infixOp ">", infixOp ">=", infixOp "+", infixOp "-",
  infixOp "*", infixOp "/", infixOp "mod", infixOp "land", infixOp "lor", infixOp "lxor",
  infixOp "lsr", infixOp "&&", infixOp "||", infixOp "^", infixOp "@",
  prim "max" 2, prim "min" 2, prim "not" 1, prim "fst" 1, prim "snd" 1, prim "failwith" 1,
  prim "Z.of_int" 1, prim "Z.to_int" 1, prim "Z.fits_int" 1, prim "Z.of_string" 1,
  prim "Z.add" 2, prim "Z.sub" 2, prim "Z.mul" 2, prim "Z.div" 2, prim "Z.rem" 2,
  prim "Z.succ" 1, prim "Z.pred" 1, prim "Z.neg" 1, prim "Z.abs" 1,
  prim "Z.equal" 2, prim "Z.lt" 2, prim "Z.leq" 2,
  prim "Z.logand" 2, prim "Z.logor" 2, prim "Z.logxor" 2,
  prim "Z.shift_left" 2, prim "Z.shift_right" 2, prim "Z.pow" 2, prim "Z.extract" 3,
  prim "Lcnf_crossing.refuse" 2,
  prim "Lcnf_string.utf8_bytes" 1, prim "Lcnf_string.utf8_length" 1,
  unruled "Lcnf_string.of_code_points" 1, unruled "Lcnf_string.of_utf8_bytes" 1,
  prim "Lcnf_array.with_capacity" 1, prim "Lcnf_array.push" 2, prim "Lcnf_array.length" 1,
  prim "Lcnf_array.get_exn" 2, prim "Lcnf_array.set_exn" 3, prim "Lcnf_array.to_list" 1,
  prim "Lcnf_array.of_list" 1, prim "Lcnf_array.append_list" 2, prim "Lcnf_array.replicate" 2,
  unruled "string_of_int" 1,
  prim "List.rev" 1, prim "List.rev_append" 2, prim "List.length" 1, prim "List.nth" 2,
  scan "List.exists" true, scan "List.for_all" false, unruled "List.map" 2,
  unruled "List.filter" 2, unruled "List.fold_left" 3, unruled "List.find_opt" 2,
  prim "List.concat" 1, unruled "List.filter_map" 2,
  prim "Option.is_some" 1, prim "Option.is_none" 1,
  { name := "Option.value", arity := 2, isInfix := false, target := .prim "Option.value~default" },
  unruled "Option.map" 2, unruled "Option.bind" 2]

/-- The arity of a function or value of the library. -/
def libraryArity? (lib : List LibFn) (name : String) : Option Nat :=
  (lib.find? fun f => !f.isInfix && f.name == name).map (·.arity)

/-- Whether a symbol is an infix operator of the library. -/
def isOperator (lib : List LibFn) (symbol : String) : Bool :=
  lib.any fun f => f.isInfix && f.name == symbol

private def va : Ml.Expr := .var "a"
private def vb : Ml.Expr := .var "b"

/-- A Zarith function applied. -/
private def z (f : String) (args : List Ml.Expr) : Ml.Expr := Ml.Expr.call ("Z." ++ f) args

/-- The natural zero, as the `Nat` row spells it. -/
private def zero : Ml.Expr := natLiteral 0

/-- A refusal at a named crossing of the runtime library (`Lcnf_crossing`). -/
private def refuseAt (crossing : String) (reason : String) : Ml.Expr :=
  Ml.Expr.call "Lcnf_crossing.refuse" [.ctor ("Lcnf_crossing." ++ crossing) [], .str reason]

/-- The functions of the runtime library (`ocaml/lcnf`, library `effect4_lcnf`) that a form names
and the target evaluator runs from a definition, in dependency order. A form that binds a name, or
that calls itself, is one of these and not inline, so that no call site carries its binders.
Each body here is the one definition of the library function of its name: the library's modules
that hold them are rendered from these bodies (`supportModule`, `ocaml/lcnf/lcnf_nat.ml` and
`lcnf_list.ml`), and the target evaluator binds the same bodies
(`Conform.Effect4.LcnfMl.supportBinds`). The host checks run them once on the evaluator and once
in compiled OCaml that carries the library's own modules (`Conform.Effect4.Normalization`), and
the library's tests are `ocaml/lcnf/test_lcnf.ml`.

The natural helpers are exact over Zarith's `Z.t` (M4): Lean's total division and remainder at a
zero divisor, subtraction and predecessor that stop at zero, and the two narrowings of a natural
to the target's `int`, each refusing past it at its named crossing (`to_index_exn`, `to_shift_exn`). The
index helpers check the target's `int` arithmetic of `USize`. Until M4 the product, the power and
the left shift stopped at `max_int`, since `Nat` was `int`. -/
def support : List Support := [
  { name := "Lcnf_nat.sub", params := ["a", "b"],
    body := .ifThen (z "lt" [va, vb]) zero (z "sub" [va, vb]) },
  { name := "Lcnf_nat.pred", params := ["a"],
    body := .ifThen (z "equal" [va, zero]) zero (z "pred" [va]) },
  { name := "Lcnf_nat.div", params := ["a", "b"],
    body := .ifThen (z "equal" [vb, zero]) zero (z "div" [va, vb]) },
  { name := "Lcnf_nat.rem", params := ["a", "b"],
    body := .ifThen (z "equal" [vb, zero]) va (z "rem" [va, vb]) },
  -- the natural as the target's index type: refused past it, at the index crossing
  { name := "Lcnf_nat.to_index_exn", params := ["a"],
    body := .ifThen (z "fits_int" [va]) (z "to_int" [va])
      (refuseAt "Index" "a natural past the target's index capacity") },
  -- an exponent or a shift as the target's `int`: refused past it, at the arithmetic crossing
  { name := "Lcnf_nat.to_shift_exn", params := ["a"],
    body := .ifThen (z "fits_int" [va]) (z "to_int" [va])
      (refuseAt "Arithmetic" "an exponent or a shift past the target's capacity") },
  { name := "Lcnf_nat.pow", params := ["a", "b"],
    body := z "pow" [va, Ml.Expr.call "Lcnf_nat.to_shift_exn" [vb]] },
  { name := "Lcnf_nat.shift_left", params := ["a", "b"],
    body := z "shift_left" [va, Ml.Expr.call "Lcnf_nat.to_shift_exn" [vb]] },
  { name := "Lcnf_nat.shift_right", params := ["a", "b"],
    body := z "shift_right" [va, Ml.Expr.call "Lcnf_nat.to_shift_exn" [vb]] },
  -- `USize`, the target's `int`: Lean's word arithmetic is exact where the index fits
  { name := "Lcnf_nat.index_add", params := ["a", "b"],
    body := .letIn "s" (.binop "+" va vb)
      (.ifThen (.binop "<" (.var "s") va) (refuseAt "Index" "an index sum past the target's capacity")
        (.var "s")) },
  { name := "Lcnf_nat.index_sub", params := ["a", "b"],
    body := .ifThen (.binop "<=" vb va) (.binop "-" va vb)
      (refuseAt "Index" "an index difference below zero, where Lean wraps") },
  -- `contains as a` is `elem a as`: the target is the first argument of the instance.
  { name := "Lcnf_list.contains", params := ["inst", "l", "a"],
    body := Ml.Expr.call "List.exists"
      [.fn ["e"] (.app (.var "inst") [va, .var "e"]), .var "l"] }]

/-! ### The runtime library's rowed modules

`ocaml/lcnf/lcnf_nat.ml` and `ocaml/lcnf/lcnf_list.ml` are rendered from `support`, so the body a
row's form calls in every generated file and the body the target evaluator runs are one
definition. Each module holds the support functions named under it, in `support`'s order, and a
call of a function of its own module is written unqualified, as OCaml requires inside the module.
`lake exe lcnfgen --support <dir>` writes them (`make gen-lcnf`); their interfaces stay
hand-written, with their property lists (`lcnf_nat.mli`, `lcnf_list.mli`). -/

/-- The modules of the runtime library that `support` defines functions of, each once, in
`support`'s order. -/
def supportModules : List String :=
  (support.filterMap fun s => match s.name.splitOn "." with
    | [m, _] => some m
    | _ => none).eraseDups

/-- One module of the runtime library as OCaml syntax: its support functions, each a `let`, and
a `let rec` when it calls itself. -/
def supportModule (m : String) : Ml.Module :=
  let own := support.filter fun s => s.name.startsWith (m ++ ".")
  let short (s : Support) : String := (s.name.drop (m.length + 1)).toString
  let unqualified : List (String × Ml.Expr) := own.map fun s => (s.name, .var (short s))
  let bind (s : Support) : Ml.Bind :=
    { name := short s, params := s.params.map (·, none), body := substExpr unqualified s.body }
  { name := m.decapitalize, items := own.map fun s => .letD s.recursive [bind s] }

/-- The modules of the runtime library that the table names, each once and sorted: the module part
of every qualified name of `support` and of `targetLibrary` that starts with `Lcnf_`. A program
that carries the library's modules itself, as the compiler checkpoint's module does, reads this
list. -/
def runtimeModules : List String :=
  let names := support.map (·.name) ++ targetLibrary.map (·.name)
  let modules := names.filterMap fun n =>
    match n.splitOn "." with
    | [m, _] => if m.startsWith "Lcnf_" then some m else none
    | _ => none
  (modules.eraseDups.toArray.qsort (· < ·)).toList

/-! ## 4. The table -/

namespace Form

/-- `a op b`. -/
def op (symbol : String) : Form := .inline ["a", "b"] (.binop symbol va vb)

/-- The argument itself: the two types share one representation. -/
def same : Form := .inline ["a"] va

end Form

-- `Int.negSucc n` is `-(n + 1)`.
private def intNegSucc : Form := .inline ["a"] (z "neg" [z "succ" [va]])
-- A byte of a natural: `n % 256`, the low eight bits, as the `int` they fit.
private def u8OfNat : Form := .inline ["a"] (z "to_int" [z "logand" [va, natLiteral 255]])
-- The natural clamped at 255, as an `int`.
private def u8Clamp : Form :=
  .inline ["a"] (.ifThen (z "leq" [va, natLiteral 255]) (z "to_int" [va]) (.int 255))
-- A word of a natural: `n % 2^64`, the low 64 bits.
private def u64OfNat : Form := .inline ["a"] (z "extract" [va, .int 0, .int 64])
-- A count of the target's, as a natural.
private def countOf (f : String) (p : String) : Form :=
  .inline [p] (z "of_int" [Ml.Expr.call f [.var p]])
private def listIsEmpty : Form := .inline ["l"] (.binop "=" (.var "l") Ml.Expr.nil)
-- `[BEq α]` is a one-field structure: mono passes the `beq` function itself as a relevant
-- argument, so `elem` and `contains` both take three.
private def listElem : Form :=
  .inline ["inst", "a", "l"] (Ml.Expr.call "List.exists" [.app (.var "inst") [va], .var "l"])
-- Lean takes the list first, OCaml the predicate first.
private def listAll : Form :=
  .inline ["l", "p"] (Ml.Expr.call "List.for_all" [.var "p", .var "l"])
private def listAny : Form :=
  .inline ["l", "p"] (Ml.Expr.call "List.exists" [.var "p", .var "l"])
private def optionGetD : Form :=
  .inline ["o", "d"]
    (.appL (.var "Option.value") [(.nolabel, .var "o"), (.lbl "default", .var "d")])
-- The capacity is a hint: the vector is empty whatever it is.
private def emptyWithHint : Form := .inline ["c"] (Ml.Expr.call "Lcnf_array.with_capacity" [.int 0])
-- An element at a natural index, which the proof puts in range.
private def getAtNat : Form :=
  .inline ["a", "i"] (Ml.Expr.call "Lcnf_array.get_exn" [va, Ml.Expr.call "Lcnf_nat.to_index_exn" [.var "i"]])
-- `n` copies of `v`: the count as the target's index.
private def replicateNat : Form :=
  .inline ["n", "v"]
    (Ml.Expr.call "Lcnf_array.replicate" [Ml.Expr.call "Lcnf_nat.to_index_exn" [.var "n"], .var "v"])
-- The program's own `panic`: Lean logs and answers a default; the target refuses.
private def panicForm : Form := .library "failwith"

private def row (lean : Name) (runtime : LeanRuntime) (form : Form) (fidelity : Fidelity)
    (domain : String) (crossing : Option Crossing) (controls : List String) (note : String)
    (cost : String := "") : Builtin :=
  { lean, runtime, form, fidelity, domain, crossing, controls, note, cost }

open Form in
/-- The Lean constants with a native OCaml spelling, one row per constant. Names are unchecked
literals: several are specialisations that exist only in the target's environment. A row is
matched after `stripRedArg`, so one row stands for a constant and its `_redArg` twin. -/
def builtins : List Builtin := [
  -- Nat comparisons and arithmetic: `Nat` is Zarith's `Z.t` (M4), and every operation is exact.
  row `Nat.decEq (.extern "lean_nat_dec_eq" (some .natDecEq)) (.library "Z.equal") .exact "" none []
    "`Z.equal` is equality of integers, and one natural has one `Z.t`.",
  row `Nat.beq (.extern "lean_nat_dec_eq" (some .natDecEq)) (.library "Z.equal") .exact "" none []
    "as `Nat.decEq`.",
  row `instDecidableEqNat .body (.library "Z.equal") .exact "" none []
    "as `Nat.decEq`; `Decidable` is `Bool` at mono.",
  row `Nat.decLt (.extern "lean_nat_dec_lt" (some .natDecLt)) (.library "Z.lt") .exact "" none []
    "`Z.lt` is the order of integers.",
  row `Nat.blt .body (.library "Z.lt") .exact "" none []
    "as `Nat.decLt`.",
  row `Nat.decLe (.extern "lean_nat_dec_le" (some .natDecLe)) (.library "Z.leq") .exact "" none []
    "as `Nat.decLt`.",
  row `Nat.ble (.extern "lean_nat_dec_le" (some .natDecLe)) (.library "Z.leq") .exact "" none []
    "as `Nat.decLt`.",
  row `Nat.add (.extern "lean_nat_add" (some .natAdd)) (.library "Z.add") .exact "" none []
    "`Z.add` is exact: no sum wraps.",
  row `Nat.mul (.extern "lean_nat_mul" (some .natMul)) (.library "Z.mul") .exact "" none ["mul-exact"]
    "`Z.mul` is exact: no product saturates or wraps.",
  row `Nat.div (.extern "lean_nat_div" (some .natDiv)) (.support "Lcnf_nat.div") .exact "" none ["div-zero"]
    "Lean answers 0 at a zero divisor (`Lcnf_nat.div`); `Z.div` truncates, which is the floor of two naturals.",
  row `Nat.mod (.extern "lean_nat_mod" (some .natMod)) (.support "Lcnf_nat.rem") .exact "" none ["mod-zero"]
    "Lean's remainder by zero is the dividend (`Lcnf_nat.rem`).",
  row `Nat.sub (.extern "lean_nat_sub" (some .natSub)) (.support "Lcnf_nat.sub") .exact "" none []
    "truncated subtraction: zero where the difference would be negative (`Lcnf_nat.sub`).",
  -- Int: `Int` is `Z.t` too. Lean's compiler reads an integer's two constructors through these
  -- two (`Store.Image.int`).
  row `Int.ofNat (.extern "lean_nat_to_int" none) same .exact "" none []
    "`Nat` and `Int` share `Z.t`, so the injection is the value itself.",
  row `Int.negSucc (.extern "lean_int_neg_succ_of_nat" none) intNegSucc .exact "" none []
    "`-(n + 1)` on `Z.t`.",
  row `Int.decLt (.extern "lean_int_dec_lt" none) (.library "Z.lt") .exact "" none []
    "`Z.lt` is `Int`'s order.",
  row `Int.natAbs (.extern "lean_nat_abs" none) (.library "Z.abs") .exact "" none []
    "the absolute value, a natural.",
  row `Int.neg (.extern "lean_int_neg" none) (.library "Z.neg") .exact "" none []
    "`Z.neg`; a negative literal compiles to it (`-3` is `Int.neg 3`).",
  row `Nat.pred (.extern "lean_nat_pred" (some .natPred)) (.support "Lcnf_nat.pred") .exact "" none []
    "truncated predecessor (`Lcnf_nat.pred`).",
  row `Nat.pow (.extern "lean_nat_pow" (some .natPow)) (.support "Lcnf_nat.pow")
    .domain "the exponent fits the target's int" (some .arithmetic) ["pow-exact"]
    "`Z.pow` is exact and takes an `int` exponent: an exponent past it is refused at the arithmetic crossing (`Lcnf_nat.to_shift_exn`), where Lean computes a number no memory holds.",
  row `Nat.shiftLeft (.extern "lean_nat_shiftl" (some .natShiftLeft)) (.support "Lcnf_nat.shift_left")
    .domain "the shift fits the target's int" (some .arithmetic) ["shift-exact"]
    "`Z.shift_left` is exact; a shift past the target's `int` is refused at the arithmetic crossing.",
  row `Nat.shiftRight (.extern "lean_nat_shiftr" (some .natShiftRight)) (.support "Lcnf_nat.shift_right")
    .domain "the shift fits the target's int" (some .arithmetic) []
    "`Z.shift_right` is exact; a shift past the target's `int` is refused at the arithmetic crossing.",
  row `Nat.land (.extern "lean_nat_land" (some .natLand)) (.library "Z.logand") .exact "" none []
    "bitwise and of two naturals.",
  row `Nat.lor (.extern "lean_nat_lor" (some .natLor)) (.library "Z.logor") .exact "" none []
    "bitwise or of two naturals.",
  row `Nat.xor (.extern "lean_nat_lxor" (some .natXor)) (.library "Z.logxor") .exact "" none []
    "bitwise xor of two naturals.",
  -- UInt8: `int`, reduced on the way in from a natural.
  row `UInt8.decEq (.extern "lean_uint8_dec_eq" (some .natDecEq)) (op "=") .exact "" none []
    "`UInt8` is `int`; both sides are already reduced mod 256.",
  row `instDecidableEqUInt8 .body (op "=") .exact "" none []
    "as `UInt8.decEq`.",
  row `UInt8.ofNat (.extern "lean_uint8_of_nat" (some (.uintOfNat 8))) u8OfNat .exact "" none []
    "`UInt8.ofNat` is `n % 256`: the low eight bits of the natural (`Z.logand`), as the `int` they fit.",
  row `UInt8.ofNatLT (.extern "lean_uint8_of_nat" (some (.uintOfNat 8))) (.library "Z.to_int") .exact "" none []
    "the argument is below 256, so it fits `int`.",
  row `UInt8.ofNatTruncate .body u8Clamp .exact "" none ["u8-clamp"]
    "Clamps at 255, matching Lean; the 256 counterexample is a permanent control.",
  row `UInt8.ofNatClamp .body u8Clamp .exact "" none []
    "The current spelling of the same clamping operation.",
  row `UInt8.toNat (.extern "lean_uint8_to_nat" (some .identity)) (.library "Z.of_int") .exact "" none []
    "the byte as a natural.",
  row `UInt8.toUInt64 (.extern "lean_uint8_to_uint64" (some .identity)) (.library "Z.of_int") .exact "" none []
    "`UInt64` is `Z.t`, a word's natural.",
  row `UInt8.toUInt32 (.extern "lean_uint8_to_uint32" (some .identity)) same .exact "" none []
    "both are `int`.",
  -- UInt64: `Z.t`, the word's natural below 2^64, the float frame's bits (`Store.Val.float`).
  row `UInt64.decEq (.extern "lean_uint64_dec_eq" (some .natDecEq)) (.library "Z.equal") .exact "" none []
    "a word is its natural below 2^64, and one `Z.t` stands for one word.",
  row `instDecidableEqUInt64 .body (.library "Z.equal") .exact "" none []
    "as `UInt64.decEq`.",
  row `UInt64.toNat (.extern "lean_uint64_to_nat" (some .identity)) same .exact "" none []
    "the word is its natural.",
  row `UInt64.ofNat (.extern "lean_uint64_of_nat" (some (.uintOfNat 64))) u64OfNat .exact "" none []
    "`UInt64.ofNat n` is `n` mod 2^64: the low 64 bits of the natural (`Z.extract`).",
  -- A word's constructor and projection: a word is its bit vector, and a bit vector its natural
  -- (`Z.t`). `UInt8` to `UInt32` and `USize` are `int`, so theirs convert; `UInt64`'s is the
  -- value itself. Lean implements them outside their bodies, so they are rows (the constructor
  -- census, `Test/Audit/ConstructorOwners.lean`).
  row `UInt8.ofBitVec (.extern "lean_uint8_of_nat_mk" (some .identity)) (.library "Z.to_int") .exact "" none []
    "the bit vector's natural, below 256, as the `int` it fits.",
  row `UInt8.toBitVec (.extern "lean_uint8_to_nat" (some .identity)) (.library "Z.of_int") .exact "" none []
    "the byte as its bit vector's natural.",
  row `UInt16.ofBitVec (.extern "lean_uint16_of_nat_mk" (some .identity)) (.library "Z.to_int") .exact "" none []
    "as `UInt8.ofBitVec`, below 2^16.",
  row `UInt16.toBitVec (.extern "lean_uint16_to_nat" (some .identity)) (.library "Z.of_int") .exact "" none []
    "as `UInt8.toBitVec`.",
  row `UInt32.ofBitVec (.extern "lean_uint32_of_nat_mk" (some .identity)) (.library "Z.to_int") .exact "" none []
    "as `UInt8.ofBitVec`, below 2^32.",
  row `UInt32.toBitVec (.extern "lean_uint32_to_nat" (some .identity)) (.library "Z.of_int") .exact "" none []
    "as `UInt8.toBitVec`.",
  row `UInt64.ofBitVec (.extern "lean_uint64_of_nat_mk" (some .identity)) same .exact "" none []
    "a word and its bit vector are one natural, `Z.t`.",
  row `UInt64.toBitVec (.extern "lean_uint64_to_nat" (some .identity)) same .exact "" none []
    "as `UInt64.ofBitVec`.",
  row `USize.ofBitVec (.extern "lean_usize_of_nat_mk" (some .identity)) (.support "Lcnf_nat.to_index_exn")
    .domain "the word is at most the target's index capacity" (some .index) []
    "the bit vector's natural as the target's `int`, refused past it (`Lcnf_nat.to_index_exn`).",
  row `USize.toBitVec (.extern "lean_usize_to_nat" (some .identity)) (.library "Z.of_int") .exact "" none []
    "the index as its bit vector's natural.",
  -- Bool
  row `Bool.decEq .body (op "=") .exact "" none []
    "OCaml `bool` is Lean `Bool`.",
  row `instDecidableEqBool .body (op "=") .exact "" none []
    "as `Bool.decEq`.",
  row `Bool.not .body (.library "not") .exact "" none []
    "",
  row `Bool.and .body (op "&&") .exact "" none []
    "OCaml's `&&` is short-circuiting and Lean's `Bool.and` is a strict function of two already-evaluated arguments. At mono LCNF both arguments are already `let`-bound values, so the two agree here; an emitter that inlined the arguments would change evaluation order.",
  row `Bool.or .body (op "||") .exact "" none []
    "as `Bool.and`.",
  -- String: UTF-8 bytes on both sides.
  row `String.decEq (.extern "lean_string_dec_eq" (some .strDecEq)) (op "=") .exact "" none []
    "OCaml's structural `=` on `string` is byte equality; two Lean strings are equal iff their UTF-8 encodings are equal, and the route's strings *are* their UTF-8 bytes.",
  row `instDecidableEqString .body (op "=") .exact "" none []
    "as `String.decEq`.",
  row `String.append (.extern "lean_string_append" (some .strAppend)) (op "^") .exact "" none []
    "concatenation of UTF-8 byte sequences is the encoding of the concatenation.",
  row `String.length (.extern "lean_string_length" (some .strLength)) (countOf "Lcnf_string.utf8_length" "s")
    .exact "" none ["utf8-length"]
    "Counts the scalar values of a valid UTF-8 string (`Lcnf_string.utf8_length`), as a natural.",
  row `String.toUTF8 (.extern "lean_string_to_utf8" (some .strToUTF8)) (.library "Lcnf_string.utf8_bytes") .exact "" none ["utf8-literal-bytes"]
    "Emitted helper returns the actual encoded bytes, including non-ASCII keys.",
  row `ByteArray.data (.extern "lean_byte_array_data" (some .identity)) same .exact "" none []
    "a byte array and its data array are one `int Lcnf_array.t`.",
  row `ByteArray.mk (.extern "lean_byte_array_mk" (some .identity)) same .exact "" none []
    "a byte array is its data array, an `int Lcnf_array.t`. Before this row the constructor built a record of no declared type, which `ocamlopt` refused.",
  -- The session's closure (LC-6, LC-7): strings from code points, bytes, and the platform.
  row `String.ofList (.extern "lean_string_mk" none) (.library "Lcnf_string.of_code_points") .exact "" none []
    "A `Char` is its code point, and every one is a Unicode scalar value, so the UTF-8 encoding is the string Lean's `String.ofList` builds.",
  row `String.toByteArray (.extern "lean_string_to_utf8" (some .strToUTF8)) (.library "Lcnf_string.utf8_bytes") .exact "" none []
    "as `String.toUTF8`, whose bytes it is.",
  row `String.ofByteArray (.extern "lean_string_from_utf8_unchecked" none) (.library "Lcnf_string.of_utf8_bytes") .exact "" none []
    "the string whose UTF-8 encoding is the bytes; the constructor's proof is that they are valid.",
  row `ByteArray.emptyWithCapacity (.extern "lean_mk_empty_byte_array" (some .arrayMkEmpty)) emptyWithHint .exact "" none []
    "the capacity is a hint; the byte vector is empty.",
  row `ByteArray.push (.extern "lean_byte_array_push" (some .arrayPush)) (.library "Lcnf_array.push") .exact "" none []
    "the byte vector with the byte appended, as `Array.push`.",
  row `Char.ofNatAux (.extern "lean_uint32_of_nat" (some .identity)) (.library "Z.to_int") .exact "" none []
    "the proof that the natural is a scalar value is erased; the code point is the natural, which fits `int`.",
  row `USize.repr (.extern "lean_string_of_usize" none) (.library "string_of_int") .exact "" none []
    "`string_of_int` writes the decimal digits with no leading zero, as `Nat.repr` does.",
  row `System.Platform.getNumBits (.extern "lean_system_platform_nbits" none) (.inline ["u"] (natLiteral 64)) .exact "" none []
    "the engine requires a 63-bit integer host (`E4_engine.Make`), which is a 64-bit platform.",
  -- List
  row `List.appendTR .body (op "@") .exact "" none []
    "`appendTR` is `append` (the tail-recursive spelling the mono phase leaves behind).",
  row `List.append .body (op "@") .exact "" none []
    "",
  row `List.reverse .body (.library "List.rev") .exact "" none []
    "",
  row `List.reverseAux .body (.library "List.rev_append") .exact "" none []
    "`List.reverseAux as bs = List.rev_append as bs`.",
  row `List.length .body (countOf "List.length" "l") .exact "" none []
    "the length as a natural; a list a memory holds is shorter than `int`'s bound.",
  row `List.lengthTR .body (countOf "List.length" "l") .exact "" none []
    "as `List.length`.",
  row `List.instDecidableEqNil .body (listIsEmpty) .exact "" none []
    "the structural comparison of a list against the empty list is `isEmpty`.",
  row `List.isEmpty .body (listIsEmpty) .exact "" none []
    "",
  row `List.elem .body (listElem) .exact "" none ["elem-order"]
    "`[BEq α]` is a one-field structure at mono, so the instance is a relevant argument. Lean's `List.elem a (b :: l)` tests `a == b`, i.e. `inst a b`; `List.exists (inst a) l` tests the same, in the same order.",
  row `List.contains .body (.support "Lcnf_list.contains") .exact "" none ["contains-order", "callback-exception"]
    "`contains as a` is `elem a as`, so the target is the first BEq argument, as in the `elem` row; an asymmetric instance sees the same order on both sides (the `contains-order` control).",
  row `List.map .body (.library "List.map") .exact "" none []
    "",
  row `List.mapTR .body (.library "List.map") .exact "" none []
    "",
  row `List.filter .body (.library "List.filter") .exact "" none []
    "",
  row `List.filterTR .body (.library "List.filter") .exact "" none []
    "",
  row `List.foldl .body (.library "List.fold_left") .exact "" none []
    "same argument order (`f`, `init`, `l`) and same associativity.",
  row `List.all .body (listAll) .exact "" none ["all-scan"]
    "Lean takes the list first, OCaml the predicate first; the row swaps.",
  row `List.any .body (listAny) .exact "" none ["any-scan"]
    "as `List.all`.",
  row `List.find? .body (.library "List.find_opt") .exact "" none []
    "",
  row `List.flatten .body (.library "List.concat") .exact "" none []
    "OCaml's `List.concat` is `flatten`.",
  row `List.flattenTR .body (.library "List.concat") .exact "" none []
    "",
  row `List.filterMap .body (.library "List.filter_map") .exact "" none []
    "",
  row `List.filterMapTR .body (.library "List.filter_map") .exact "" none []
    "",
  -- Array: the persistent chunked vector of the runtime library (`Lcnf_array`, decision D-3).
  -- `USize` is its index type, and a natural index or count is narrowed to it.
  row `Array.mkEmpty (.extern "lean_mk_empty_array_with_capacity" (some .arrayMkEmpty)) emptyWithHint .exact "" none []
    "the capacity is a hint; the vector is empty.",
  row `Array.emptyWithCapacity (.extern "lean_mk_empty_array_with_capacity" (some .arrayMkEmpty)) emptyWithHint .exact "" none []
    "as `Array.mkEmpty`.",
  row `Array.toList (.extern "lean_array_to_list" (some .arrayToList)) (.library "Lcnf_array.to_list") .exact "" none []
    "the elements in index order.",
  row `Array.mk (.extern "lean_array_mk" (some .listToArray)) (.library "Lcnf_array.of_list") .exact "" none []
    "the vector of the list's elements in order, as `List.toArray`.",
  row `List.toArray .body (.library "Lcnf_array.of_list") .exact "" none []
    "as `Array.mk`.",
  row `Array.push (.extern "lean_array_push" (some .arrayPush)) (.library "Lcnf_array.push") .exact "" none []
    "the vector with `x` appended."
    (cost := "amortised O(1), as Lean's; every 256th push fills one chunk and inserts it in the chunk map."),
  row `Array.size (.extern "lean_array_get_size" (some .arraySize)) (countOf "Lcnf_array.length" "a") .exact "" none []
    "the vector's length, kept in the value, as a natural.",
  row `Array.appendList .body (.library "Lcnf_array.append_list") .exact "" none []
    "the vector with the list's elements appended in order.",
  row `List.foldl._at_.Array.appendList.spec_0 .body (.library "Lcnf_array.append_list") .exact "" none []
    "the specialisation of the fold that `Array.appendList` compiles to.",
  row `USize.ofNat (.extern "lean_usize_of_nat" (some (.uintOfNat 64))) (.support "Lcnf_nat.to_index_exn")
    .domain "n is at most the target's index capacity; Lean reduces it mod 2^64" (some .index) []
    "`USize` is the index type of `Array` (`Lcnf_array`), the target's `int`.",
  row `USize.toNat (.extern "lean_usize_to_nat" (some .identity)) (.library "Z.of_int") .exact "" none []
    "the index as a natural.",
  row `USize.ofNatLT (.extern "lean_usize_of_nat" (some (.uintOfNat 64))) (.support "Lcnf_nat.to_index_exn")
    .domain "n is at most the target's index capacity" (some .index) []
    "",
  row `USize.decEq (.extern "lean_usize_dec_eq" (some .natDecEq)) (op "=") .exact "" none []
    "two indexes, two `int`s.",
  row `USize.sub (.extern "lean_usize_sub" (some (.uintSub 64))) (.support "Lcnf_nat.index_sub")
    .domain "b ≤ a; Lean wraps below zero, past the index capacity" (some .index) []
    "`USize.sub` in Lean wraps (it is `Fin (2^64)` subtraction: `0 - 1 = 2^64 - 1`); the row refuses where it would wrap (`Lcnf_nat.index_sub`). Every use in this closure is a bounded index decrement where `a ≥ b`.",
  row `USize.add (.extern "lean_usize_add" none) (.support "Lcnf_nat.index_add")
    .domain "a + b is at most the target's index capacity; Lean wraps at 2^64" (some .index) []
    "`USize.add` wraps at 2^64 in Lean; the row refuses past the target's `int` (`Lcnf_nat.index_add`).",
  row `Array.uget (.extern "lean_array_uget" (some .arrayGet)) (.library "Lcnf_array.get_exn") .exact "" none []
    "Lean's `Array.uget a i h` is total because `h` proves `i` in range; `Lcnf_array.get_exn` answers in range, and raises `Invalid_argument` only outside it, which `h` excludes."
    (cost := "O(log (i / 256)) where Lean's is O(1)."),
  -- Option, Prod, panic
  row `Array.getInternal (.extern "lean_array_fget" (some .arrayGet)) getAtNat .exact "" none []
    "the proof that the index is in range is erased; the natural index fits the target's index (`Lcnf_nat.to_index_exn`), and `Lcnf_array.get_exn` answers in range."
    (cost := "O(log (i / 256)) where Lean's is O(1)."),
  row `Array.uset (.extern "lean_array_uset" (some .arraySet)) (.library "Lcnf_array.set_exn") .exact "" none []
    "Lean's `Array.uset a i v h` replaces the element at `i`, which `h` proves in range. `Lcnf_array.set_exn` answers a new vector and copies the one chunk it changes, so the argument and every version that shares that chunk keep their elements, as Lean's values do."
    (cost := "O(log (n / 256) + 256) per update, where Lean's is O(1) on an array no other reference holds."),
  row `Array.replicate (.extern "lean_mk_array" (some .arrayReplicate)) replicateNat
    .domain "n is at most the target's index capacity" (some .index) []
    "`n` copies of `v`; the full chunks share one array that nothing writes.",
  row `Option.isSome .body (.library "Option.is_some") .exact "" none []
    "",
  row `Option.isNone .body (.library "Option.is_none") .exact "" none []
    "",
  row `Option.getD .body (optionGetD) .exact "" none ["option-default", "option-default-eager"]
    "",
  row `Option.map .body (.library "Option.map") .exact "" none []
    "",
  row `Option.bind .body (.library "Option.bind") .exact "" none []
    "",
  row `Prod.fst .body (.library "fst") .exact "" none []
    "",
  row `Prod.snd .body (.library "snd") .exact "" none []
    "",
  row `panic .body panicForm .domain "a run that does not reach `panic`" (some .panic) []
    "Lean's `panic` logs and **returns `default`**: the caller continues with a junk value. OCaml's `failwith` raises `Failure`, a refusal at the program's own panic, never a junk value. A Lean theorem about a program that panics says nothing about an OCaml run that aborts.",
  row `panicCore (.extern "lean_panic_fn_borrowed" none) panicForm .domain "a run that does not reach `panic`" (some .panic) []
    "as `panic`."
]

/-! ## 5. What the table computes -/

/-- The support function of a name. -/
def supportOf? (name : String) : Option Support := support.find? (·.name == name)

/-- The number of relevant (non-erased) arguments a form takes. -/
def Form.arity : Form → Nat
  | .inline ps _ => ps.length
  | .support n => ((supportOf? n).map (·.params.length)).getD 0
  | .library n => (libraryArity? targetLibrary n).getD 0

def Builtin.arity (b : Builtin) : Nat := b.form.arity

/-- The unqualified names that an application of the form leaves free at its call site. -/
def Form.freeNames : Form → List String
  | .inline ps body =>
    ((((usesExpr false ps body).map (·.free)).getD []).filter (!isQualified ·)).eraseDups
  | .support n => if isQualified n then [] else [n]
  | .library n => if isQualified n then [] else [n]

/-- Whether the form evaluates each of its parameters exactly once, whenever it is evaluated.
An expression may then stand in a parameter's place, as in any application. -/
def Form.strict : Form → Bool
  | .inline ps body =>
    match usesExpr false [] body with
    | some u => ps.all fun p => (u.free.filter (· == p)).length == 1 && u.always.contains p
    | none => false
  | .support _ => true
  | .library _ => true

/-- The form as a report spells it. -/
def Form.spelling : Form → String
  | .inline _ body => Ml.renderExpr 0 body
  | .support n => n
  | .library n => n

/-- The form applied to exactly its arity's worth of relevant arguments. -/
def Form.saturated (f : Form) (args : List Ml.Expr) : Ml.Expr :=
  match f with
  | .inline ps body => substExpr (ps.zip args) body
  | .support n => Ml.Expr.call n args
  | .library n => Ml.Expr.call n args

/-- The largest arity of a row. -/
def maxArity : Nat := builtins.foldl (fun k b => max k b.arity) 0

/-- The binders of an eta-expansion, `_b1`, `_b2`, …: one per missing argument, so the table's
largest arity bounds them. `reservedNames` holds them, so no source binder has one of these
names, and no argument of an application can mention one. -/
def etaBinders : List String := (List.range maxArity).map fun i => s!"_b{i + 1}"

/-- Apply a row to its relevant arguments: saturated, eta-expanded when under-applied, applied
to the rest when over-applied. An argument is a value, or the form is `strict`
(`Translate.applyBuiltin` sees to it). -/
def Builtin.apply (b : Builtin) (args : List Ml.Expr) : Ml.Expr :=
  let k := b.arity
  if args.length == k then b.form.saturated args
  else if args.length < k then
    let extra := etaBinders.take (k - args.length)
    .fn extra (b.form.saturated (args ++ extra.map Ml.Expr.var))
  else .app (b.form.saturated (args.take k)) (args.drop k)

/-- The names a call site must reach: every unqualified name a row leaves free at a call site,
and every unqualified function of the target's library, which a reader of the emitted code
resolves as the library's (`Conform.Effect4.LcnfMl.ofExpr`). A binder that took one would capture
a reference. A qualified name, such as a function of the runtime library or of Zarith, is no
binder's. Until M4 the row `Nat.sub` left `max` free; the library's own names keep it reserved. -/
def protectedNames : List String :=
  (builtins.flatMap (·.form.freeNames) ++
    (targetLibrary.filter fun f => !f.isInfix && !f.name.contains '.').map (·.name)).eraseDups

/-- The names no source binder of a declaration may take: the eta binders and the protected
names. -/
def reservedNames : List String := etaBinders ++ protectedNames

/-- The table by constant. -/
def builtinIndex : Std.HashMap Name Builtin :=
  builtins.foldl (fun m b => m.insert b.lean b) {}

/-- The row of a Lean constant, if it has one. A `_redArg` twin has its wrapper's row. -/
def builtin? (n : Name) : Option Builtin := builtinIndex[stripRedArg n]?

/-- The source evaluator's primitive table (`Conform.Lcnf.Semantics`): each row's Lean constant
with the primitive of its runtime column. -/
def sourcePrims : PrimTable :=
  builtins.filterMap fun b =>
    match b.runtime with
    | .extern _ (some p) => some (b.lean, p)
    | _ => none

/-- The target evaluator's arity of each primitive spelling (`Conform.Lcnf.Target.PrimEnv`):
every entry of the library that it answers, by `applyPrim` or by a scan. -/
def targetArities : Std.HashMap String Nat :=
  targetLibrary.foldl (init := {}) fun m f =>
    match f.target with
    | .prim spelling => m.insert spelling f.arity
    | .scan _ => m.insert f.name f.arity
    | _ => m

/-- The library functions that the target evaluator scans a list with, each with the callback's
answer that ends the scan. -/
def targetScans : Std.HashMap String Bool :=
  targetLibrary.foldl (init := {}) fun m f =>
    match f.target with
    | .scan stop => m.insert f.name stop
    | _ => m

/-! ## 6. The table's own check -/

/-- The names of a list that occur more than once, each reported once. -/
private def repeated [BEq α] (xs : List α) : List α :=
  (xs.filter fun x => (xs.filter (· == x)).length > 1).eraseDups

/-- Everything wrong with a table, a support list and a library. It is empty for the three of
this module, and it refuses each altered copy below. -/
def problemsOf (rows : List Builtin) (sup : List Support) (lib : List LibFn) :
    List String := Id.run do
  let libNames := (lib.filter (!·.isInfix)).map (·.name)
  let supNames := sup.map (·.name)
  let mut out : List String := []
  -- the keys
  for r in rows do
    if stripRedArg r.lean != r.lean then
      out := out ++ [s!"row {r.lean}: the key is not normalized"]
  for n in repeated (rows.map (·.lean)) do
    out := out ++ [s!"row {n}: the key has two rows"]
  -- the contracts
  for r in rows do
    for p in contractProblems r.fidelity r.domain r.crossing do
      out := out ++ [s!"row {r.lean}: {p}"]
  -- the forms
  for r in rows do
    match r.form with
    | .inline ps body =>
      unless (repeated ps).isEmpty do
        out := out ++ [s!"row {r.lean}: a parameter is named twice"]
      match usesExpr false ps body with
      | none => out := out ++ [s!"row {r.lean}: the inline body leaves its fragment"]
      | some u =>
        for f in u.free.eraseDups do
          unless libNames.contains f || supNames.contains f do
            out := out ++ [s!"row {r.lean}: `{f}` is not declared"]
        for o in u.ops.eraseDups do
          unless isOperator lib o do
            out := out ++ [s!"row {r.lean}: the operator `{o}` is not declared"]
    | .support n =>
      unless supNames.contains n do
        out := out ++ [s!"row {r.lean}: the support function `{n}` is not defined"]
    | .library n =>
      match libraryArity? lib n with
      | none => out := out ++ [s!"row {r.lean}: the library function `{n}` is not declared"]
      | some 0 => out := out ++ [s!"row {r.lean}: `{n}` is not a function"]
      | some _ => pure ()
  -- the library and the runtime library's definitions
  for n in repeated (lib.map (·.name)) do
    out := out ++ [s!"library `{n}`: declared twice"]
  for f in lib do
    if f.isInfix && f.arity != 2 then
      out := out ++ [s!"library `{f.name}`: an operator takes two arguments"]
    match f.target with
    | .scan _ =>
      unless f.arity == 2 do
        out := out ++ [s!"library `{f.name}`: a scan takes a callback and a list"]
    | _ => pure ()
  let spellings := lib.filterMap fun f => match f.target with
    | .prim spelling => some spelling
    | .scan _ => some f.name
    | _ => none
  for n in repeated spellings do
    out := out ++ [s!"library: the evaluator's primitive `{n}` answers two entries"]
  for n in repeated supNames do
    out := out ++ [s!"support `{n}`: defined twice"]
  let mut earlier : List String := []
  for s in sup do
    if libNames.contains s.name || isOperator lib s.name then
      out := out ++ [s!"support `{s.name}`: the name is the library's"]
    match usesExpr true s.params s.body with
    | none => out := out ++ [s!"support `{s.name}`: the body leaves its fragment"]
    | some u =>
      unless (repeated (s.params ++ u.binders)).isEmpty do
        out := out ++ [s!"support `{s.name}`: a name is bound twice"]
      let self := if s.recursive then [s.name] else []
      for f in u.free.eraseDups do
        unless libNames.contains f || earlier.contains f || self.contains f do
          out := out ++ [s!"support `{s.name}`: `{f}` is not declared before it"]
      for o in u.ops.eraseDups do
        unless isOperator lib o do
          out := out ++ [s!"support `{s.name}`: the operator `{o}` is not declared"]
      if s.recursive && !u.free.contains s.name then
        out := out ++ [s!"support `{s.name}`: marked recursive, and it does not call itself"]
    earlier := earlier ++ [s.name]
  return out

/-- The problems of this module's table. -/
def problems : List String := problemsOf builtins support targetLibrary

#guard problems.isEmpty

-- No reserved name is another's: an eta binder is not a name a call site must reach.
#guard etaBinders.all fun b => !protectedNames.contains b && !(targetLibrary.map (·.name)).contains b
#guard maxArity == 3
#guard builtins.length == 117
-- The runtime library's modules that the table names: the five of `ocaml/lcnf`. Sorted, they are
-- also in dependency order (`Lcnf_string` reads `Lcnf_array`, `Lcnf_nat` reads `Lcnf_crossing`),
-- which a program that carries them in one file needs.
#guard runtimeModules == ["Lcnf_array", "Lcnf_crossing", "Lcnf_list", "Lcnf_nat", "Lcnf_string"]
-- No name of the runtime library is one a binder must avoid: each is qualified.
#guard (support.map (·.name) ++ ["Lcnf_string.utf8_bytes"]).all (!protectedNames.contains ·)
-- The rowed modules: one per module `support` names, each passing the module checker, each body
-- the support function's own, with a call into its own module unqualified.
#guard supportModules == ["Lcnf_nat", "Lcnf_list"]
#guard supportModules.all fun m => (Ml.checkModule (supportModule m)).isEmpty
#guard ((supportModule "Lcnf_nat").items.map Ml.renderDecl).take 2 ==
  ["let sub a b =\n  if Z.lt a b then Z.of_int 0 else Z.sub a b",
   "let pred a =\n  if Z.equal a (Z.of_int 0) then Z.of_int 0 else Z.pred a"]
#guard ((supportModule "Lcnf_nat").items.map Ml.renderDecl).contains
  "let pow a b =\n  Z.pow a (to_shift_exn b)"
#guard (supportModule "Lcnf_list").items.map Ml.renderDecl ==
  ["let contains inst l a =\n  List.exists (fun e -> inst a e) l"]
-- The two evaluators' tables, computed: the source evaluator has the primitive of every extern
-- row but eleven (`Int`'s five, which `Store.Image.int` and a negative literal need; three the
-- session's closure needs; `String.ofByteArray`, the inverse of the bytes it has no primitive
-- for; `USize.add`; `panicCore`), and the target evaluator scans with two functions.
#guard sourcePrims.length == 61
#guard (builtins.filter fun b => b.runtime matches .extern _ none).map (·.lean) ==
  [`Int.ofNat, `Int.negSucc, `Int.decLt, `Int.natAbs, `Int.neg, `String.ofList, `String.ofByteArray,
    `USize.repr, `System.Platform.getNumBits, `USize.add, `panicCore]
#guard targetScans.toList.length == 2 && targetScans["List.exists"]? == some true
#guard targetArities["Option.value~default"]? == some 2 && (targetArities["List.map"]?).isNone
#guard targetArities["Z.add"]? == some 2 && targetArities["Z.extract"]? == some 3

/-! ### Controls: each altered copy is refused, for its own reason -/

private def refuses (ps : List String) (reason : String) : Bool :=
  ps.any fun p => (p.splitOn reason).length > 1

-- a support definition left out: its row has no function, and its dependent no declaration
#guard refuses (problemsOf builtins (support.filter (·.name != "Lcnf_nat.to_shift_exn")) targetLibrary)
  "support `Lcnf_nat.pow`: `Lcnf_nat.to_shift_exn` is not declared before it"
#guard refuses (problemsOf builtins (support.filter (·.name != "Lcnf_nat.pow")) targetLibrary)
  "the support function `Lcnf_nat.pow` is not defined"
-- the definitions out of order
#guard refuses (problemsOf builtins support.reverse targetLibrary)
  "support `Lcnf_nat.pow`: `Lcnf_nat.to_shift_exn` is not declared before it"
-- a library dependency left out
#guard refuses (problemsOf builtins support (targetLibrary.filter (·.name != "Z.fits_int")))
  "support `Lcnf_nat.to_index_exn`: `Z.fits_int` is not declared before it"
#guard refuses (problemsOf builtins support (targetLibrary.filter (·.name != "Z.equal")))
  "row Nat.decEq: the library function `Z.equal` is not declared"
-- a contract whose domain or crossing disagrees with its class
#guard refuses (problemsOf [row `Nat.add .body (.library "Z.add") .exact "a + b < 2^62" none [] ""]
    support targetLibrary)
  "row Nat.add: an exact row states a domain"
#guard refuses (problemsOf [row `Nat.pow .body (.support "Lcnf_nat.pow") .domain "a domain" none [] ""]
    support targetLibrary)
  "row Nat.pow: a row exact under a domain names no crossing"
#guard refuses (problemsOf [row `Nat.add .body (.library "Z.add") .exact "" (some .arithmetic) [] ""]
    support targetLibrary)
  "row Nat.add: an exact row names the crossing arithmetic"
-- a library whose evaluator spelling answers two entries, and an operator of one argument
private def secondRev : LibFn :=
  { name := "List.rev2", arity := 1, isInfix := false, target := .prim "List.rev" }
private def unaryOp : LibFn := { name := "~~", arity := 1, isInfix := true, target := .unruled }
#guard refuses (problemsOf builtins support (targetLibrary ++ [secondRev]))
  "the evaluator's primitive `List.rev` answers two entries"
#guard refuses (problemsOf builtins support (targetLibrary ++ [unaryOp]))
  "library `~~`: an operator takes two arguments"
-- two rows for one key, and a key that `stripRedArg` would change
#guard refuses (problemsOf (builtins ++ builtins.take 1) support targetLibrary)
  "row Nat.decEq: the key has two rows"
#guard refuses
  (problemsOf
    (row (`Nat.add ++ `_redArg) .body (.library "Z.add") .exact "" none [] "" :: builtins)
    support targetLibrary)
  "the key is not normalized"
-- an inline body that binds, and a support body outside its fragment (a `match`)
#guard refuses
  (problemsOf
    [row `Nat.mul .body (.inline ["a"] (.letIn "t" va (.var "t"))) .exact "" none [] ""]
    support targetLibrary)
  "row Nat.mul: the inline body leaves its fragment"
#guard refuses
  (problemsOf builtins [{ name := "lcnf_x", params := ["a"], body := .matchE va [(.wild, va)] }]
    targetLibrary)
  "support `lcnf_x`: the body leaves its fragment"
-- a support body whose own binder hides a parameter
#guard refuses
  (problemsOf [] [{ name := "lcnf_x", params := ["a"], body := .letIn "a" va va }] targetLibrary)
  "support `lcnf_x`: a name is bound twice"

/-! ### The census: where a row refuses

Each row is exact, or exact on a domain and refusing outside it at a named crossing. `Nat`,
`Int` and the 64-bit word are exact, so no arithmetic row refuses but the two that narrow an
exponent or a shift to the target's `int`. A program's literals and a host's answer are no row's
crossing: Lean's profile support judges them at ingress (`Effect4.Program.ProfileData`, lowered;
M2). The clock is an ordinary natural and has no row (M4). -/

private def refusingAt (c : Crossing) : List Name :=
  (builtins.filter (·.crossing == some c)).map (·.lean)
#guard refusingAt .arithmetic == [`Nat.pow, `Nat.shiftLeft, `Nat.shiftRight]
#guard refusingAt .index ==
  [`USize.ofBitVec, `USize.ofNat, `USize.ofNatLT, `USize.sub, `USize.add, `Array.replicate]
#guard refusingAt .panic == [`panic, `panicCore]
#guard (builtins.filter (·.fidelity == .exact)).length == 106
-- no row names the clock or the profile's arithmetic: both are translated from their bodies
#guard builtins.all fun b => !(`Effect4.ClockMillis).isPrefixOf b.lean && b.lean != `Effect4.Program.Profile.grow

/-! ### Controls: the forms the route has

Each inline form is the expression the table builds, and each support call replaces an
expansion that would bind names at its call site. -/

private def spelled (name : Name) (args : List Ml.Expr) : String :=
  match builtin? name with
  | some b => Ml.renderExpr 0 (b.apply args)
  | none => "no row"

#guard spelled `Nat.add [.var "x", .var "y"] == "Z.add x y"
#guard spelled `Nat.sub [.var "x", .var "y"] == "Lcnf_nat.sub x y"
#guard spelled `Nat.div [.var "x", .var "y"] == "Lcnf_nat.div x y"
#guard spelled `Nat.mod [.var "x", .var "y"] == "Lcnf_nat.rem x y"
#guard spelled `Nat.mul [.var "x", .var "y"] == "Z.mul x y"
#guard spelled `Nat.shiftLeft [.var "x", .var "y"] == "Lcnf_nat.shift_left x y"
#guard spelled `UInt8.ofNat [.var "n"] == "Z.to_int (Z.logand n (Z.of_int 255))"
#guard spelled `UInt64.ofNat [.var "n"] == "Z.extract n 0 64"
#guard spelled `String.length [.var "s"] == "Z.of_int (Lcnf_string.utf8_length s)"
#guard spelled `Array.getInternal [.var "xs", .var "i"] == "Lcnf_array.get_exn xs (Lcnf_nat.to_index_exn i)"
#guard spelled `List.all [.var "l", .var "p"] == "List.for_all p l"
#guard spelled `List.elem [.var "inst", .var "x", .var "l"] == "List.exists (inst x) l"
#guard spelled `List.contains [.var "inst", .var "l", .var "_elem"] == "Lcnf_list.contains inst l _elem"
#guard spelled `Array.mkEmpty [.var "n"] == "Lcnf_array.with_capacity 0"
#guard spelled `Array.push [.var "xs", .var "x"] == "Lcnf_array.push xs x"
#guard spelled `Array.uset [.var "xs", .var "i", .var "v"] == "Lcnf_array.set_exn xs i v"
#guard spelled `Option.getD [.var "o", .var "d"] == "Option.value o ~default:d"
-- under-applied: eta binders; over-applied: the rest is applied to the result, which the
-- renderer prints with its parentheses (`OCaml5.Ml.renderExprAlg`, an application's head)
#guard spelled `Nat.decEq [] == "fun _b1 _b2 -> Z.equal _b1 _b2"
#guard spelled `Nat.add [.var "x"] == "fun _b1 -> Z.add x _b1"
#guard spelled `Prod.fst [.var "p", .var "x"] == "(fst p) x"
-- a twin has its wrapper's row
#guard (builtin? (`List.map ++ `_redArg)).isSome
-- which forms may take an expression in a parameter's place
#guard (builtin? `Nat.sub).any (·.form.strict)
#guard (builtin? `List.all).any (·.form.strict)
#guard (builtin? `UInt8.ofNatTruncate).any (!·.form.strict)  -- `a` twice
#guard (builtin? `Option.getD).any (·.form.strict)    -- each argument once, always
#guard (builtin? `Bool.and).any (!·.form.strict)      -- the right operand is lazy
#guard (builtin? `Array.mkEmpty).any (!·.form.strict)  -- the capacity is a hint, never read

end OCaml5.Lcnf
