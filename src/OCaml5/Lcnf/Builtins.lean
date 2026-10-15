import Lean
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.TypeRows
import OCaml5.Lcnf.Prim

/-!
# OCaml5.Lcnf.Builtins

**What it is.** The one primitive table of the LCNF route: one row for each Lean constant that
the route does not translate from its own body. A row is data: the constant, how Lean itself
realizes it (its body, or a C function of Lean's runtime and the source evaluator's primitive),
its OCaml form and its contract. Beside the rows stands the target's library, one entry for each
function and operator a form names, with the target evaluator's rule for it. The lookup, the
prelude, the reserved names, the fidelity inventory and both evaluators' primitive tables
(`sourcePrims`, `targetArities`, `targetScans`) are computed from the rows.

**Depends on.** `OCaml5.Ml.Syntax` (a form is OCaml syntax), `OCaml5.Ml.Render` (a form's
spelling in a report), `OCaml5.Lcnf.Externs` (`stripRedArg`), `OCaml5.Lcnf.TypeRows` (the
contract's class, `Fidelity`, which the type rows share), `Conform.Lcnf.Semantics` (the source
evaluator's primitives, `Prim`).

**Properties.**
* **One owner.** A constant has a row in `builtins` or the route translates it. `builtin?`,
  `prelude`, `reservedNames`, `Form.spelling` and the evaluators' tables are computed from
  `builtins`, `support` and `targetLibrary`. No second list names a row: *by construction*.
* **The runtime column is Lean's.** A row's `runtime` names the C symbol of Lean's runtime
  exactly when Lean's extern attribute names one. A row holds the source evaluator's primitive
  only beside such a symbol, since that evaluator reads every other constant's body: *checked*
  against the environment (`Conform.Effect4.CompilerControls`).
* **A form binds nothing at a call site.** An inline body is binder-free. A support function is
  a closed definition of the prelude. An application adds a binder only by eta-expansion, and
  the eta binders are in `reservedNames`: *checked* (`problemsOf`, the `#guard`s at the foot).
* **A form states what it needs.** Every free name of a row is a function of `targetLibrary`
  or of `support`, and every operator is an operator of `targetLibrary`. A body outside its
  fragment is refused, and `Expr.raw` is outside both fragments: *checked* (`problemsOf`).
* **Arguments are values.** `Builtin.apply` substitutes its arguments into an inline body, which
  is exact for an atom. `Form.strict` holds when a body evaluates each parameter exactly once;
  `Translate.applyBuiltin` binds every other argument that is not an atom before the form.
* **Every row has a contract.** `fidelity`, `domain`, `controls` and `note` have no default.
  The class is a reading of the row against the Lean definition. No theorem proves a row. An
  exact row states no domain, and a row exact under a domain states its domain: *checked*.
* **The raw natural rows retain their numeric limits.** Addition and successor use 63-bit `+`.
  Raw multiplication, powers and left shifts saturate at `max_int`; subtraction stops at zero.
  `Profile.grow` and `Profile.scale` instead compute exactly and refuse outside their declared domain.
  Decisions row 108 remains open for the raw rows.

**What it does not own.** The type rows (`OCaml5.Lcnf.TypeRows`), the native constructors
(`OCaml5.Lcnf.Native`), the exact clock's constructors (`OCaml5.Lcnf.Clock`), and the extern
table of a run (`OCaml5.Lcnf.Externs`).
-/

namespace OCaml5.Lcnf

open Lean

/-! ## 1. Forms -/

/-- The OCaml realization of a row. Each form denotes one closed function of the target. -/
inductive Form where
  /-- `fun params -> body`, written in place at a call site. `body` is binder-free. -/
  | inline (params : List String) (body : Ml.Expr)
  /-- A function that `support` defines in the prelude. -/
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
  /-- The identifiers of the finite controls that run this row
  (`Conform.Effect4.CompilerControls`). Empty when no control runs it. -/
  controls : List String
  /-- Why: the difference, or the argument that there is none. -/
  note : String
  /-- The cost where it differs from Lean's. A cost is not a difference of meaning. -/
  cost : String
  deriving Inhabited

/-- A function of the prelude that the route itself defines. -/
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
body may also bind, by `let` and by `fun`. Everything else is outside both, `Expr.raw` first. -/

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
  -- outside both fragments, `Expr.raw` first
  expr_letRec _ _ _ _ := fun _ => none
  expr_matchE _ _ := fun _ => none
  expr_record _ := fun _ => none
  expr_field _ _ := fun _ => none
  expr_tuple _ := fun _ => none
  expr_annot _ _ := fun _ => none
  expr_hole _ _ := fun _ => none
  expr_raw _ := fun _ => none
  expr_assertE _ := fun _ => none

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

/-! ## 3. The target's library and the prelude -/

/-- How the target evaluator (`Conform.Lcnf.Target`, `tools/Conform/Lcnf/SemanticsTarget.lean`)
answers a function or an operator of the target's library. -/
inductive TargetRule where
  /-- `Target.applyPrim` answers it from its argument values, under this spelling. -/
  | prim (spelling : String)
  /-- `Target.scanT` applies the callback along the list, and stops at the answer `stop`. -/
  | scan (stop : Bool)
  /-- The evaluator's program binds it from the target's word (`supportBinds`). -/
  | bound
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
name, with the number of arguments it takes and the target evaluator's rule for it.
`lcnf_utf8_bytes` and `lcnf_utf8_length` are the two the prelude carries as verbatim OCaml
(`rawPrimitives`). The labelled call `Option.value o ~default:d` is the evaluator's primitive
`Option.value~default` (`Conform.Effect4.LcnfMl.ofExpr`). -/
def targetLibrary : List LibFn := [
  infixOp "=", infixOp "<", infixOp "<=", infixOp ">", infixOp ">=", infixOp "+", infixOp "-",
  infixOp "*", infixOp "/", infixOp "mod", infixOp "land", infixOp "lor", infixOp "lxor",
  infixOp "lsr", infixOp "&&", infixOp "||", infixOp "^", infixOp "@",
  { name := "max_int", arity := 0, isInfix := false, target := .bound },
  prim "max" 2, prim "min" 2, prim "not" 1, prim "fst" 1, prim "snd" 1, prim "failwith" 1,
  prim "lcnf_utf8_bytes" 1, prim "lcnf_utf8_length" 1,
  prim "List.rev" 1, prim "List.rev_append" 2, prim "List.length" 1, prim "List.nth" 2,
  scan "List.exists" true, scan "List.for_all" false, unruled "List.map" 2,
  unruled "List.filter" 2, unruled "List.fold_left" 3, unruled "List.find_opt" 2,
  prim "List.concat" 1, unruled "List.filter_map" 2,
  prim "Option.is_some" 1, prim "Option.is_none" 1,
  { name := "Option.value", arity := 2, isInfix := false, target := .prim "Option.value~default" },
  unruled "Option.map" 2, unruled "Option.bind" 2,
  unruled "E4_clock.of_nat" 1, unruled "E4_clock.to_profile_nat" 1, unruled "E4_clock.add" 2,
  unruled "E4_clock.mul" 2, unruled "E4_clock.le" 2, unruled "E4_clock.lt" 2,
  unruled "E4_clock.equal" 2, unruled "E4_clock.to_decimal" 1, unruled "E4_clock.of_decimal" 1]

/-- The arity of a function or value of the library. -/
def libraryArity? (lib : List LibFn) (name : String) : Option Nat :=
  (lib.find? fun f => !f.isInfix && f.name == name).map (·.arity)

/-- Whether a symbol is an infix operator of the library. -/
def isOperator (lib : List LibFn) (symbol : String) : Bool :=
  lib.any fun f => f.isInfix && f.name == symbol

/-- The two primitives the prelude carries as verbatim OCaml. Strings admitted by this profile
are valid UTF-8; `ByteArray` and `Array UInt8` both use a byte list. -/
-- Declarations, not `rawD`: a top-level `rawD` is text `Ml.Check` cannot see into, so a module
-- holding one has to be checked with its value scope open and `unbound-value` stops deciding
-- anything there (tooling plan 4.3). The binder and its parameter are structure the checker
-- reads; only the body stays verbatim, which is all these two need.
def rawPrimitives : List Ml.Bind := [
  { name := "lcnf_utf8_bytes", params := [("s", none)],
    body := .raw "List.init (String.length s) (fun i -> Char.code (String.get s i))" },
  { name := "lcnf_utf8_length", params := [("s", none)],
    body := .raw "String.fold_left (fun n c -> if Char.code c land 192 = 128 then n else n + 1) 0 s" }]

private def va : Ml.Expr := .var "a"
private def vb : Ml.Expr := .var "b"

/-- `if x = 0 then 0 else if y > max_int / x then max_int else product`: the product of `x` and
`y`, stopped at `max_int`. The test divides, so no intermediate overflows. -/
private def saturating (x y product : Ml.Expr) : Ml.Expr :=
  .ifThen (.binop "=" x (.int 0)) (.int 0)
    (.ifThen (.binop ">" y (.binop "/" (.var "max_int") x)) (.var "max_int") product)

/-- The functions the prelude defines, in dependency order. A form that binds a name, or that
calls itself, is here and not inline, so that no call site carries its binders.

The 63-bit rule. `Nat` is unbounded and OCaml's `int` is 63-bit, so a faithful `a * b` or
`a ^ b` does not exist; a wrapping one is worse than a saturating one, because
`Effect4.Store.Val.wf`'s `… < 2 ^ 64` would then read as `… < 0` and answer `false` for every
value: a silently wrong `Api.ofBytes`, not a compile error. Saturating makes `2 ^ 64` read as
`max_int`, and every list OCaml can hold is shorter than `max_int`, so the guard keeps its
meaning. Recorded in `ocaml/gen/NOTES.md` §5. -/
def support : List Support := [
  { name := "lcnf_nat_mul", params := ["a", "b"],
    body := saturating va vb (.binop "*" va vb) },
  { name := "lcnf_nat_pow", params := ["a", "b"], recursive := true,
    body := .ifThen (.binop "=" vb (.int 0)) (.int 1)
      (.letIn "h" (Ml.Expr.call "lcnf_nat_pow" [va, .binop "-" vb (.int 1)])
        (saturating va (.var "h") (.binop "*" (.var "h") va))) },
  -- The scale and the final product are both stopped: stopping only the power still wrapped.
  { name := "lcnf_nat_shift_left", params := ["a", "b"],
    body := .letIn "s" (Ml.Expr.call "lcnf_nat_pow" [.int 2, vb])
      (saturating va (.var "s") (.binop "*" va (.var "s"))) },
  -- `contains as a` is `elem a as`: the target is the first argument of the instance.
  { name := "lcnf_list_contains", params := ["inst", "l", "a"],
    body := Ml.Expr.call "List.exists"
      [.fn ["e"] (.app (.var "inst") [va, .var "e"]), .var "l"] }]

/-- The prelude of an emitted module: the two verbatim primitives, then the support functions.
The production backend emits it, and it is part of the manifest, never patched into a
generated file. -/
def prelude : List Ml.Decl :=
  rawPrimitives.map (fun b => Ml.Decl.letD false [b])
    ++ support.map (fun s => Ml.Decl.letD s.recursive [s.bind])
    ++ [.blank]

/-! ## 4. The table -/

namespace Form

/-- `a op b`. -/
def op (symbol : String) : Form := .inline ["a", "b"] (.binop symbol va vb)

/-- The argument itself: the two types share one representation. -/
def same : Form := .inline ["a"] va

end Form

-- Lean answers `0` for a division by zero and `a` for a remainder by zero.
private def natDiv : Form :=
  .inline ["a", "b"] (.ifThen (.binop "=" vb (.int 0)) (.int 0) (.binop "/" va vb))
private def natMod : Form :=
  .inline ["a", "b"] (.ifThen (.binop "=" vb (.int 0)) va (.binop "mod" va vb))
private def natSub : Form := .inline ["a", "b"] (Ml.Expr.call "max" [.int 0, .binop "-" va vb])
private def natPred : Form := .inline ["a"] (Ml.Expr.call "max" [.int 0, .binop "-" va (.int 1)])
-- OCaml's shifts are undefined at 63 and above, so the form answers `0` there.
private def natShiftRight : Form :=
  .inline ["a", "b"] (.ifThen (.binop ">=" vb (.int 63)) (.int 0) (.binop "lsr" va vb))
private def u8Mask : Form := .inline ["a"] (.binop "land" va (.int 255))
private def u8Clamp : Form := .inline ["a"] (Ml.Expr.call "min" [va, .int 255])
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
-- The capacity is a hint, and the list has none.
private def arrayEmpty : Form := .inline ["n"] Ml.Expr.nil
private def arrayPush : Form := .inline ["a", "x"] (.binop "@" va (.listLit [.var "x"]))
private def optionGetD : Form :=
  .inline ["o", "d"]
    (.appL (.var "Option.value") [(.nolabel, .var "o"), (.lbl "default", .var "d")])

private def row (lean : Name) (runtime : LeanRuntime) (form : Form) (fidelity : Fidelity)
    (domain : String) (controls : List String) (note : String) (cost : String := "") : Builtin :=
  { lean, runtime, form, fidelity, domain, controls, note, cost }

open Form in
/-- The Lean constants with a native OCaml spelling, one row per constant. Names are unchecked
literals: several are specialisations that exist only in the target's environment. A row is
matched after `stripRedArg`, so one row stands for a constant and its `_redArg` twin. -/
def builtins : List Builtin := [
  -- Nat comparisons and arithmetic: `Nat` is `int`. A comparison is exact wherever both operands
  -- are representable.
  row `Nat.decEq (.extern "lean_nat_dec_eq" (some .natDecEq)) (op "=") .domain "0 ≤ a, b < 2^62" []
    "Lean `Nat` is unbounded; OCaml `int` is 63-bit. `=` on `int` is structural equality of the machine word, which agrees with `Nat` equality on the representable range.",
  row `Nat.beq (.extern "lean_nat_dec_eq" (some .natDecEq)) (op "=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decEq`.",
  row `instDecidableEqNat .body (op "=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decEq`; `Decidable` is `Bool` at mono.",
  row `Nat.decLt (.extern "lean_nat_dec_lt" (some .natDecLt)) (op "<") .domain "0 ≤ a, b < 2^62" []
    "OCaml's `<` on `int` is signed; a saturated or wrapped operand can compare wrongly, which is why literals and `pow` saturate rather than wrap.",
  row `Nat.blt .body (op "<") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decLt`.",
  row `Nat.decLe (.extern "lean_nat_dec_le" (some .natDecLe)) (op "<=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decLt`.",
  row `Nat.ble (.extern "lean_nat_dec_le" (some .natDecLe)) (op "<=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decLt`.",
  row `Nat.add (.extern "lean_nat_add" (some .natAdd)) (op "+") .domain "a + b < 2^62" []
    "OCaml `+` wraps at 2^62 without a trap; Lean's `Nat.add` does not.",
  row `Nat.mul (.extern "lean_nat_mul" (some .natMul)) (.support "lcnf_nat_mul") .domain "a * b < 2^62" ["mul-saturation"]
    "saturating: a product above `max_int` reads as `max_int`, where OCaml's raw `*` would wrap. The check is `b > max_int / a`, so no intermediate overflows.",
  row `Nat.div (.extern "lean_nat_div" (some .natDiv)) (natDiv) .domain "0 ≤ a, b < 2^62" ["div-zero"]
    "Includes Lean's total value at zero; unbounded input representation remains outside this target profile.",
  row `Nat.mod (.extern "lean_nat_mod" (some .natMod)) (natMod) .domain "0 ≤ a, b < 2^62" ["mod-zero"]
    "Includes Lean's remainder value at zero.",
  row `Nat.sub (.extern "lean_nat_sub" (some .natSub)) (natSub) .domain "0 ≤ a, b < 2^62" []
    "truncated subtraction, spelled out; exact on the representable range.",
  row `Nat.pred (.extern "lean_nat_pred" (some .natPred)) (natPred) .domain "a < 2^62" []
    "truncated predecessor.",
  row `Nat.pow (.extern "lean_nat_pow" (some .natPow)) (.support "lcnf_nat_pow") .approximate "a ^ b < max_int" ["pow-saturation"]
    "saturating: `2 ^ 64` reads as `max_int` rather than wrapping to 0. The host profile of `ocaml/gen/NOTES.md` §5. Note the helper's own multiplications are checked against `max_int / a`, so the saturation is monotone.",
  row `Nat.shiftLeft (.extern "lean_nat_shiftl" (some .natShiftLeft)) (.support "lcnf_nat_shift_left") .approximate "a * 2^b ≤ max_int" ["shift-saturation"]
    "Checks both the power and final multiplication; larger results saturate at max_int.",
  row `Nat.shiftRight (.extern "lean_nat_shiftr" (some .natShiftRight)) (natShiftRight) .domain "a < 2^62" []
    "OCaml's `lsr` is undefined at shift ≥ 63, so the row guards it; `lsr` on a non-negative `int` is Lean's `shiftRight` below 2^62.",
  row `Nat.land (.extern "lean_nat_land" (some .natLand)) (op "land") .domain "a, b < 2^62" []
    "bitwise and on the 63-bit word.",
  row `Nat.lor (.extern "lean_nat_lor" (some .natLor)) (op "lor") .domain "a, b < 2^62" []
    "bitwise or on the 63-bit word.",
  row `Nat.xor (.extern "lean_nat_lxor" (some .natXor)) (op "lxor") .domain "a, b < 2^62" []
    "bitwise xor on the 63-bit word.",
  -- UInt8: `int` with an explicit truncation on the way in.
  row `UInt8.decEq (.extern "lean_uint8_dec_eq" (some .natDecEq)) (op "=") .exact "" []
    "`UInt8` is `int`; both sides are already reduced mod 256 by `ofNat`.",
  row `instDecidableEqUInt8 .body (op "=") .exact "" []
    "as `UInt8.decEq`.",
  row `UInt8.ofNat (.extern "lean_uint8_of_nat" (some (.uintOfNat 8))) (u8Mask) .exact "" []
    "`UInt8.ofNat` is `n % 256`, and `land 255` is `% 256` on a non-negative `int`.",
  row `UInt8.ofNatLT (.extern "lean_uint8_of_nat" (some (.uintOfNat 8))) (u8Mask) .exact "" []
    "the argument is already < 256; the mask is a no-op.",
  row `UInt8.ofNatTruncate .body (u8Clamp) .domain "a is a representable non-negative int" ["u8-clamp"]
    "Clamps at 255, matching Lean; the 256 counterexample is a permanent control.",
  row `UInt8.ofNatClamp .body (u8Clamp) .domain "a is a representable non-negative int" []
    "The current spelling of the same clamping operation.",
  row `UInt8.toNat (.extern "lean_uint8_to_nat" (some .identity)) (same) .exact "" []
    "identity on the representation.",
  row `UInt8.toUInt64 (.extern "lean_uint8_to_uint64" (some .identity)) (same) .exact "" []
    "identity on the representation; `UInt64` is `int` too.",
  row `UInt8.toUInt32 (.extern "lean_uint8_to_uint32" (some .identity)) (same) .exact "" []
    "identity on the representation.",
  -- UInt64: `int` too, the float frame's bits (`Store.Val.float`). Not exact above 2^62.
  row `UInt64.decEq (.extern "lean_uint64_dec_eq" (some .natDecEq)) (op "=") .domain "both bit patterns < 2^62" []
    "`UInt64` is `int` here, the float frame's bits. A pattern at 2^62 or above has no carrier, and nothing detects it. The type row is `unsound` for the same reason. Open, not supported, until an exact 64-bit carrier exists.",
  row `instDecidableEqUInt64 .body (op "=") .domain "both bit patterns < 2^62" []
    "as `UInt64.decEq`.",
  row `UInt64.toNat (.extern "lean_uint64_to_nat" (some .identity)) (same) .domain "the bit pattern < 2^62" []
    "identity on the representation; as `UInt64.decEq` outside the domain.",
  -- Bool
  row `Bool.decEq .body (op "=") .exact "" []
    "OCaml `bool` is Lean `Bool`.",
  row `instDecidableEqBool .body (op "=") .exact "" []
    "as `Bool.decEq`.",
  row `Bool.not .body (.library "not") .exact "" []
    "",
  row `Bool.and .body (op "&&") .approximate "" []
    "OCaml's `&&` is short-circuiting and Lean's `Bool.and` is a strict function of two already-evaluated arguments. At mono LCNF both arguments are already `let`-bound values, so the difference is unobservable *here* — but the row is not exact as a function-level claim, and an emitter that inlined the arguments would change evaluation order.",
  row `Bool.or .body (op "||") .approximate "" []
    "as `Bool.and`.",
  -- String: UTF-8 bytes on both sides.
  row `String.decEq (.extern "lean_string_dec_eq" (some .strDecEq)) (op "=") .exact "" []
    "OCaml's structural `=` on `string` is byte equality; two Lean strings are equal iff their UTF-8 encodings are equal, and the route's strings *are* their UTF-8 bytes.",
  row `instDecidableEqString .body (op "=") .exact "" []
    "as `String.decEq`.",
  row `String.append (.extern "lean_string_append" (some .strAppend)) (op "^") .exact "" []
    "concatenation of UTF-8 byte sequences is the encoding of the concatenation.",
  row `String.length (.extern "lean_string_length" (some .strLength)) (.library "lcnf_utf8_length") .domain "valid UTF-8; scalar count fits int" ["utf8-length"]
    "Counts leading UTF-8 bytes, hence Unicode scalar values for represented Lean strings.",
  row `String.toUTF8 (.extern "lean_string_to_utf8" (some .strToUTF8)) (.library "lcnf_utf8_bytes") .domain "valid UTF-8" ["utf8-literal-bytes"]
    "Emitted helper returns the actual encoded bytes, including non-ASCII keys.",
  row `ByteArray.data (.extern "lean_byte_array_data" (some .identity)) (same) .exact "" []
    "Byte arrays use the same list-of-byte representation as their data array.",
  -- List
  row `List.appendTR .body (op "@") .exact "" []
    "`appendTR` is `append` (the tail-recursive spelling the mono phase leaves behind).",
  row `List.append .body (op "@") .exact "" []
    "",
  row `List.reverse .body (.library "List.rev") .exact "" []
    "",
  row `List.reverseAux .body (.library "List.rev_append") .exact "" []
    "`List.reverseAux as bs = List.rev_append as bs`.",
  row `List.length .body (.library "List.length") .domain "length < 2^62" []
    "the result is a `Nat` spelled as `int`.",
  row `List.lengthTR .body (.library "List.length") .domain "length < 2^62" []
    "as `List.length`.",
  row `List.instDecidableEqNil .body (listIsEmpty) .exact "" []
    "the structural comparison of a list against the empty list is `isEmpty`.",
  row `List.isEmpty .body (listIsEmpty) .exact "" []
    "",
  row `List.elem .body (listElem) .exact "" ["elem-order"]
    "`[BEq α]` is a one-field structure at mono, so the instance is a relevant argument. Lean's `List.elem a (b :: l)` tests `a == b`, i.e. `inst a b`; `List.exists (inst a) l` tests the same, in the same order.",
  row `List.contains .body (.support "lcnf_list_contains") .exact "" ["contains-order", "callback-exception"]
    "`contains as a` is `elem a as`, so the target is the first BEq argument, as in the `elem` row; an asymmetric instance sees the same order on both sides (the `contains-order` control).",
  row `List.map .body (.library "List.map") .exact "" []
    "",
  row `List.mapTR .body (.library "List.map") .exact "" []
    "",
  row `List.filter .body (.library "List.filter") .exact "" []
    "",
  row `List.filterTR .body (.library "List.filter") .exact "" []
    "",
  row `List.foldl .body (.library "List.fold_left") .exact "" []
    "same argument order (`f`, `init`, `l`) and same associativity.",
  row `List.all .body (listAll) .exact "" ["all-scan"]
    "Lean takes the list first, OCaml the predicate first; the row swaps.",
  row `List.any .body (listAny) .exact "" ["any-scan"]
    "as `List.all`.",
  row `List.find? .body (.library "List.find_opt") .exact "" []
    "",
  row `List.flatten .body (.library "List.concat") .exact "" []
    "OCaml's `List.concat` is `flatten`.",
  row `List.flattenTR .body (.library "List.concat") .exact "" []
    "",
  row `List.filterMap .body (.library "List.filter_map") .exact "" []
    "",
  row `List.filterMapTR .body (.library "List.filter_map") .exact "" []
    "",
  -- Array as list: the shim. `USize` is the shim's index type.
  row `Array.mkEmpty (.extern "lean_mk_empty_array_with_capacity" (some .arrayMkEmpty)) (arrayEmpty) .exact "" []
    "`Array` is `list`; the capacity hint is dropped.",
  row `Array.emptyWithCapacity (.extern "lean_mk_empty_array_with_capacity" (some .arrayMkEmpty)) (arrayEmpty) .exact "" []
    "",
  row `Array.toList (.extern "lean_array_to_list" (some .arrayToList)) (same) .exact "" []
    "identity under the shim.",
  row `List.toArray .body (same) .exact "" []
    "identity under the shim.",
  row `Array.push (.extern "lean_array_push" (some .arrayPush)) (arrayPush) .exact "" []
    "`a @ [x]` is the sequence with `x` appended."
    (cost := "O(n) per push where Lean's `Array.push` is amortised O(1); a `push` in a loop is quadratic."),
  row `Array.size (.extern "lean_array_get_size" (some .arraySize)) (.library "List.length") .exact "" []
    "the length of the list that stands for the array."
    (cost := "O(n) where Lean's is O(1)."),
  row `Array.appendList .body (op "@") .exact "" []
    "",
  row `List.foldl._at_.Array.appendList.spec_0 .body (op "@") .exact "" []
    "the specialisation of the fold that `Array.appendList` compiles to.",
  row `USize.ofNat (.extern "lean_usize_of_nat" (some (.uintOfNat 64))) (same) .domain "a < 2^62" []
    "`USize` is the shim's index type and is `int`.",
  row `USize.toNat (.extern "lean_usize_to_nat" (some .identity)) (same) .exact "" []
    "",
  row `USize.ofNatLT (.extern "lean_usize_of_nat" (some (.uintOfNat 64))) (same) .exact "" []
    "",
  row `USize.decEq (.extern "lean_usize_dec_eq" (some .natDecEq)) (op "=") .domain "a, b < 2^62" []
    "",
  row `USize.sub (.extern "lean_usize_sub" (some (.uintSub 64))) (natSub) .unsound "a ≥ b" []
    "`USize.sub` in Lean **wraps** (it is `Fin (2^64)` subtraction: `0 - 1 = 2^64 - 1`); the row **truncates** to 0. Every use in this closure is a bounded index decrement where `a ≥ b`, so the difference is not reached, but the row is not the Lean function.",
  row `USize.add (.extern "lean_usize_add" none) (op "+") .unsound "a + b < 2^62" []
    "`USize.add` wraps at 2^64 in Lean; OCaml's `+` wraps at 2^62. Two different wrapping points.",
  row `Array.uget (.extern "lean_array_uget" (some .arrayGet)) (.library "List.nth") .unsound "i < length" []
    "Lean's `Array.uget a i h` is total (`h` proves `i` in range) and the row is `List.nth`, which **raises** `Failure \"nth\"` out of range and `Invalid_argument` on a negative index."
    (cost := "O(i) under the shim where Lean's is O(1)."),
  -- Option, Prod, panic
  row `Option.isSome .body (.library "Option.is_some") .exact "" []
    "",
  row `Option.isNone .body (.library "Option.is_none") .exact "" []
    "",
  row `Option.getD .body (optionGetD) .exact "" ["option-default", "option-default-eager"]
    "",
  row `Option.map .body (.library "Option.map") .exact "" []
    "",
  row `Option.bind .body (.library "Option.bind") .exact "" []
    "",
  row `Prod.fst .body (.library "fst") .exact "" []
    "",
  row `Prod.snd .body (.library "snd") .exact "" []
    "",
  row `panic .body (.library "failwith") .approximate "" []
    "Lean's `panic` logs and **returns `default`**: the caller continues with a junk value. OCaml's `failwith` raises `Failure`. The OCaml behaviour is arguably the better one, but it is not the Lean one, and a Lean theorem about a program that panics says nothing about an OCaml run that aborts.",
  row `panicCore (.extern "lean_panic_fn_borrowed" none) (.library "failwith") .approximate "" []
    "as `panic`.",
  -- The exact clock: `Effect4.ClockMillis` is `E4_clock.t`, a Zarith integer.
  row `Effect4.ClockMillis.ofNat .body (.library "E4_clock.of_nat") .domain "n < 2^62, the natural as the `int` that carries it" []
    "`E4_clock.of_nat` is `Z.of_int` on a non-negative `int`, and raises `Profile_refusal` on a negative one. A literal reaches the clock by `clockNatIngress?` as exact decimal text, and a natural that the literal rule narrowed is refused at generation. Read against `ocaml/clock/e4_clock.ml`; its own tests are `ocaml/clock/test_clock.ml`.",
  row `Effect4.ClockMillis.toNat .body (.library "E4_clock.to_profile_nat") .domain "millis ≤ 2^53 - 1 and the value fits `int`" []
    "`E4_clock.to_profile_nat` raises `Profile_refusal` outside the domain: a refusal outside the program's result, never a wrapped value (DI-56).",
  -- The one addition that can leave the profile (decisions row 321): `succ`, `add`, `plus` and
  -- `minus` grow through it, and its form refuses outside the bound.
  row `Effect4.Program.Profile.grow .body
    (.inline ["a", "b"] (.call "E4_clock.to_profile_nat"
      [.call "E4_clock.add" [.call "E4_clock.of_nat" [.var "a"], .call "E4_clock.of_nat" [.var "b"]]]))
    .domain "a + b ≤ 2^53 - 1, and each of a and b fits `int`" []
    "Exact addition on `E4_clock.t`, then `E4_clock.to_profile_nat`, which raises `Profile_refusal` outside the domain: a refusal outside the program's result, never a wrapped value (DI-56, decisions row 108). The engine answers it as `Outside_profile` with the input machine retained (`ocaml/engine/e4_engine.mli`)."
    "two conversions and one Zarith addition for one machine addition",
  row `Effect4.Program.Profile.scale .body
    (.inline ["a", "b"] (.call "E4_clock.to_profile_nat"
      [.call "E4_clock.mul" [.call "E4_clock.of_nat" [.var "a"], .call "E4_clock.of_nat" [.var "b"]]]))
    .domain "a * b ≤ 2^53 - 1, and nonnegative a and b fit `int`" []
    "Exact Zarith multiplication followed by checked natural observation. Outside the domain, Profile_refusal remains outside the program result (DI-56)."
    "two conversions and one Zarith multiplication",
  row `Effect4.ClockMillis.add .body (.library "E4_clock.add") .exact "" []
    "`E4_clock.add` is `Z.add`, exact on naturals of any size; Lean's `add` is `ofNat (a.toNat + b.toNat)` (`ClockMillis.toNat_add`).",
  row `Effect4.ClockMillis.decLe .body (.library "E4_clock.le") .exact "" []
    "`E4_clock.le` is `Z.leq`; Lean compares the two `toNat`.",
  row `Effect4.ClockMillis.decLt .body (.library "E4_clock.lt") .exact "" []
    "`E4_clock.lt` is `Z.lt`; as `decLe`.",
  row `Effect4.ClockMillis.beq .body (.library "E4_clock.equal") .exact "" []
    "`E4_clock.equal` is `Z.equal`. One `Z.t` stands for one natural, and `ofNat` and `toNat` are inverse (`ofNat_toNat`, `toNat_ofNat`), so equality of the carriers is equality of the clocks.",
  row `Effect4.instDecidableEqClockMillis .body (.library "E4_clock.equal") .exact "" []
    "as `ClockMillis.beq`; `Decidable` is `Bool` at mono.",
  row `Effect4.ClockMillis.toDecimal .body (.library "E4_clock.to_decimal") .exact "" []
    "`E4_clock.to_decimal` is `Z.to_string`: the decimal digits with no leading zero, as `Nat.repr` writes them.",
  row `Effect4.ClockMillis.ofDecimal .body (.library "E4_clock.of_decimal") .exact "" []
    "Both read exactly the spelling `toDecimal` writes: a non-empty digit string with no leading zero, or `0`. Lean's side is `ofDecimal_exact` and `ofDecimal_toDecimal`; the OCaml side is read against `e4_clock.ml`. No theorem joins the two."
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
  | .support n => [n]
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

/-- The names a call site must reach: the names the prelude defines, and every unqualified
name a row leaves free at a call site. A binder that took one would capture a reference. -/
def protectedNames : List String :=
  (rawPrimitives.map (·.name) ++ support.map (·.name)
    ++ builtins.flatMap (·.form.freeNames)).eraseDups

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
    for p in Fidelity.problems r.fidelity r.domain do
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
  -- the library and the prelude
  for n in repeated (lib.map (·.name)) do
    out := out ++ [s!"library `{n}`: declared twice"]
  for f in lib do
    if f.isInfix && f.arity != 2 then
      out := out ++ [s!"library `{f.name}`: an operator takes two arguments"]
    match f.target with
    | .scan _ =>
      unless f.arity == 2 do
        out := out ++ [s!"library `{f.name}`: a scan takes a callback and a list"]
    | .bound =>
      unless f.arity == 0 do
        out := out ++ [s!"library `{f.name}`: a bound name is a value"]
    | _ => pure ()
  let spellings := lib.filterMap fun f => match f.target with
    | .prim spelling => some spelling
    | .scan _ => some f.name
    | _ => none
  for n in repeated spellings do
    out := out ++ [s!"library: the evaluator's primitive `{n}` answers two entries"]
  for b in rawPrimitives do
    unless libraryArity? lib b.name == some b.params.length do
      out := out ++ [s!"primitive `{b.name}`: not declared with its arity"]
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
#guard builtins.length == 99
-- The two evaluators' tables, computed: the source evaluator has the primitive of every extern
-- row but two (`USize.add`, `panicCore`), and the target evaluator scans with two functions.
#guard sourcePrims.length == 41
#guard (builtins.filter fun b => b.runtime matches .extern _ none).map (·.lean) == [`USize.add, `panicCore]
#guard targetScans.toList.length == 2 && targetScans["List.exists"]? == some true
#guard targetArities["Option.value~default"]? == some 2 && (targetArities["List.map"]?).isNone

/-! ### Controls: each altered copy is refused, for its own reason -/

private def refuses (ps : List String) (reason : String) : Bool :=
  ps.any fun p => (p.splitOn reason).length > 1

-- a support definition left out: its row has no function, and its dependent no declaration
#guard refuses (problemsOf builtins (support.filter (·.name != "lcnf_nat_pow")) targetLibrary)
  "the support function `lcnf_nat_pow` is not defined"
#guard refuses (problemsOf builtins (support.filter (·.name != "lcnf_nat_pow")) targetLibrary)
  "support `lcnf_nat_shift_left`: `lcnf_nat_pow` is not declared before it"
-- the definitions out of order
#guard refuses (problemsOf builtins support.reverse targetLibrary)
  "support `lcnf_nat_shift_left`: `lcnf_nat_pow` is not declared before it"
-- a library dependency left out
#guard refuses (problemsOf builtins support (targetLibrary.filter (·.name != "max_int")))
  "support `lcnf_nat_mul`: `max_int` is not declared before it"
#guard refuses (problemsOf builtins support (targetLibrary.filter (·.name != "max")))
  "row Nat.sub: `max` is not declared"
-- a contract whose domain disagrees with its class
#guard refuses (problemsOf [row `Nat.add .body (Form.op "+") .exact "a + b < 2^62" [] ""] support targetLibrary)
  "row Nat.add: an exact row states a domain"
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
  (problemsOf (row (`Nat.add ++ `_redArg) .body (Form.op "+") .exact "" [] "" :: builtins) support
    targetLibrary)
  "the key is not normalized"
-- an inline body that binds, and a support body of verbatim text
#guard refuses
  (problemsOf [row `Nat.mul .body (.inline ["a"] (.letIn "t" va (.var "t"))) .exact "" [] ""] support
    targetLibrary)
  "row Nat.mul: the inline body leaves its fragment"
#guard refuses
  (problemsOf builtins [{ name := "lcnf_x", params := ["a"], body := .raw "a" }] targetLibrary)
  "support `lcnf_x`: the body leaves its fragment"
-- a support body whose own binder hides a parameter
#guard refuses
  (problemsOf [] [{ name := "lcnf_x", params := ["a"], body := .letIn "a" va va }] targetLibrary)
  "support `lcnf_x`: a name is bound twice"

/-! ### Controls: the forms the route had

Each inline form is the expression the earlier table built, and each support call replaces an
expansion that bound names at its call site. -/

private def spelled (name : Name) (args : List Ml.Expr) : String :=
  match builtin? name with
  | some b => Ml.renderExpr 0 (b.apply args)
  | none => "no row"

#guard spelled `Nat.add [.var "x", .var "y"] == "x + y"
#guard spelled `Nat.sub [.var "x", .var "y"] == "max 0 (x - y)"
#guard spelled `Nat.div [.var "x", .var "y"] == "if y = 0 then 0 else x / y"
#guard spelled `Nat.mod [.var "x", .var "y"] == "if y = 0 then x else x mod y"
#guard spelled `Nat.mul [.var "x", .var "_mula"] == "lcnf_nat_mul x _mula"
#guard spelled `Nat.shiftLeft [.var "_shift_scale", .var "y"] == "lcnf_nat_shift_left _shift_scale y"
#guard spelled `List.all [.var "l", .var "p"] == "List.for_all p l"
#guard spelled `List.elem [.var "inst", .var "x", .var "l"] == "List.exists (inst x) l"
#guard spelled `List.contains [.var "inst", .var "l", .var "_elem"] == "lcnf_list_contains inst l _elem"
#guard spelled `Array.mkEmpty [.var "n"] == "[]"
#guard spelled `Array.push [.var "xs", .var "x"] == "xs @ [x]"
#guard spelled `Option.getD [.var "o", .var "d"] == "Option.value o ~default:d"
-- under-applied: eta binders; over-applied: the rest is applied to the result
#guard spelled `Nat.decEq [] == "fun _b1 _b2 -> _b1 = _b2"
#guard spelled `Nat.add [.var "x"] == "fun _b1 -> x + _b1"
#guard spelled `Effect4.ClockMillis.beq [] == "fun _b1 _b2 -> E4_clock.equal _b1 _b2"
#guard spelled `Prod.fst [.var "p", .var "x"] == "fst p x"
-- a twin has its wrapper's row
#guard (builtin? (`List.map ++ `_redArg)).isSome
-- which forms may take an expression in a parameter's place
#guard (builtin? `Nat.sub).any (·.form.strict)
#guard (builtin? `List.all).any (·.form.strict)
#guard (builtin? `Nat.div).any (!·.form.strict)       -- `b` twice
#guard (builtin? `Option.getD).any (·.form.strict)    -- each argument once, always
#guard (builtin? `Bool.and).any (!·.form.strict)      -- the right operand is lazy
#guard (builtin? `Array.mkEmpty).any (!·.form.strict) -- the capacity is dropped

end OCaml5.Lcnf
