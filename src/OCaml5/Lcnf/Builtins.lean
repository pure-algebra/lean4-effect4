import Lean
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Lcnf.Externs

/-!
# OCaml5.Lcnf.Builtins

**What it is.** The table of the Lean constants that the LCNF route does not translate from
their own bodies. One row is data: the constant, its OCaml form and its contract. The lookup,
the prelude, the reserved names and the fidelity inventory are computed from the rows.

**Depends on.** `OCaml5.Ml.Syntax` (a form is OCaml syntax), `OCaml5.Ml.Render` (a form's
spelling in a report), `OCaml5.Lcnf.Externs` (`stripRedArg`).

**Properties.**
* **One owner.** A constant has a row in `builtins` or the route translates it. `builtin?`,
  `prelude`, `reservedNames` and `Form.spelling` are computed from `builtins`, `support` and
  `libraries`. No second list names a row: *by construction*.
* **A form binds nothing at a call site.** An inline body is binder-free. A support function is
  a closed definition of the prelude. An application adds a binder only by eta-expansion, and
  the eta binders are in `reservedNames`: *checked* (`problemsOf`, the `#guard`s at the foot).
* **A form states what it needs.** Every free name of a row is an entry of `libraries` or a
  function of `support`, and every operator is in `operators`. A body outside its fragment is
  refused, and `Expr.raw` is outside both fragments: *checked* (`problemsOf`).
* **Arguments are values.** `Builtin.apply` substitutes its arguments into an inline body, which
  is exact for an atom. `Form.strict` holds when a body evaluates each parameter exactly once;
  `Translate.applyBuiltin` binds every other argument that is not an atom before the form.
* **Every row has a contract.** `fidelity`, `domain`, `controls` and `note` have no default.
  The class is a reading of the row against the Lean definition. No theorem proves a row.
* **The numbers are the ones the route had.** Addition and successor are the raw 63-bit `+`.
  Multiplication, powers and the left shift saturate at `max_int`. Subtraction stops at zero.
  Decisions row 108 is open, and this module does not move it.

**What it does not own.** The native constructors (`OCaml5.Lcnf.Native`), the exact clock's
constructors and type (`OCaml5.Lcnf.Clock`), and the extern table of a run
(`OCaml5.Lcnf.Externs`).
-/

namespace OCaml5.Lcnf

open Lean

/-! ## 1. The contract of a row -/

/-- How faithfully an OCaml form reproduces the Lean constant it stands for. The class is a
claim about the row, read against the Lean definition. -/
inductive Fidelity
  /-- The OCaml form denotes the same function on the whole Lean domain. -/
  | exact
  /-- The OCaml form denotes the same function on a stated sub-domain, and something else
  outside it. The domain is the row's `domain` field. -/
  | domain
  /-- The OCaml form denotes a different function that agrees on the values this tree
  produces, or differs in a way the row states. -/
  | approximate
  /-- The OCaml form denotes a different function and the difference can be reached. -/
  | unsound
  deriving DecidableEq, Repr, Inhabited

namespace Fidelity
protected def toString : Fidelity → String
  | .exact => "exact"
  | .domain => "exact-under-domain"
  | .approximate => "approximate"
  | .unsound => "unsound"
instance : ToString Fidelity := ⟨Fidelity.toString⟩
end Fidelity

/-! ## 2. Forms -/

/-- The OCaml realization of a row. Each form denotes one closed function of the target. -/
inductive Form where
  /-- `fun params -> body`, written in place at a call site. `body` is binder-free. -/
  | inline (params : List String) (body : Ml.Expr)
  /-- A function that `support` defines in the prelude. -/
  | support (name : String)
  /-- A function of the target's own library, named in `libraries`: a trusted leaf. -/
  | library (name : String)
  deriving Inhabited

/-- One row of the table. No field of the contract has a default. -/
structure Builtin where
  /-- The Lean constant, as `stripRedArg` leaves it. -/
  lean : Name
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

/-! ## 3. What a body uses

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

mutual

/-- What a body uses under the names `bound`, or `none` when it leaves its fragment. `binding`
admits `let` and `fun`: a support body may bind and an inline body may not. -/
def usesExpr (binding : Bool) (bound : List String) : Ml.Expr → Option Uses
  | .var n => some (if bound.contains n then {} else { free := [n], always := [n] })
  | .int _ => some {}
  | .str _ => some {}
  | .bool _ => some {}
  | .unit => some {}
  | .ctor _ args => usesExprs binding bound args
  | .app f args => do
    let a ← usesExpr binding bound f
    let b ← usesExprs binding bound args
    return a ++ b
  | .appL f args => do
    let a ← usesExpr binding bound f
    let b ← usesLabelled binding bound args
    return a ++ b
  | .binop op l r => do
    let a ← usesExpr binding bound l
    let b ← usesExpr binding bound r
    let b := if lazyOperators.contains op then b.deferred else b
    return { free := a.free ++ b.free, always := a.always ++ b.always,
             ops := op :: (a.ops ++ b.ops), binders := a.binders ++ b.binders }
  | .ifThen c t e => do
    let a ← usesExpr binding bound c
    let b ← usesExpr binding bound t
    let d ← usesExpr binding bound e
    return a ++ b.deferred ++ d.deferred
  | .listLit items => usesExprs binding bound items
  | .letIn n v b =>
    if binding then do
      let a ← usesExpr binding bound v
      let c ← usesExpr binding (n :: bound) b
      return { free := a.free ++ c.free, always := a.always ++ c.always,
               ops := a.ops ++ c.ops, binders := n :: (a.binders ++ c.binders) }
    else none
  | .fn ps b =>
    if binding then do
      let c ← usesExpr binding (ps ++ bound) b
      return { c.deferred with binders := ps ++ c.binders }
    else none
  | _ => none

def usesExprs (binding : Bool) (bound : List String) : List Ml.Expr → Option Uses
  | [] => some {}
  | e :: rest => do
    let a ← usesExpr binding bound e
    let b ← usesExprs binding bound rest
    return a ++ b

def usesLabelled (binding : Bool) (bound : List String) :
    List (Ml.ArgLabel × Ml.Expr) → Option Uses
  | [] => some {}
  | (_, e) :: rest => do
    let a ← usesExpr binding bound e
    let b ← usesLabelled binding bound rest
    return a ++ b

end

mutual

/-- Put values in the place of an inline body's parameters. The body binds nothing, so no name
of a value can be captured. A constructor outside the inline fragment is returned as it is;
`problemsOf` refuses a table that holds one. -/
def substExpr (σ : List (String × Ml.Expr)) : Ml.Expr → Ml.Expr
  | .var n => (σ.lookup n).getD (.var n)
  | .ctor c args => .ctor c (substExprs σ args)
  | .app f args => .app (substExpr σ f) (substExprs σ args)
  | .appL f args => .appL (substExpr σ f) (substLabelled σ args)
  | .binop op l r => .binop op (substExpr σ l) (substExpr σ r)
  | .ifThen c t e => .ifThen (substExpr σ c) (substExpr σ t) (substExpr σ e)
  | .listLit items => .listLit (substExprs σ items)
  | e => e

def substExprs (σ : List (String × Ml.Expr)) : List Ml.Expr → List Ml.Expr
  | [] => []
  | e :: rest => substExpr σ e :: substExprs σ rest

def substLabelled (σ : List (String × Ml.Expr)) :
    List (Ml.ArgLabel × Ml.Expr) → List (Ml.ArgLabel × Ml.Expr)
  | [] => []
  | (l, e) :: rest => (l, substExpr σ e) :: substLabelled σ rest

end

/-! ## 4. The target's library and the prelude -/

/-- The functions and values of the target's own library that a form or a support body may
name, each with the number of arguments it takes. They are trusted leaves: the route does not
define them. `lcnf_utf8_bytes` and `lcnf_utf8_length` are the two the prelude carries as
verbatim OCaml (`rawPrimitives`). -/
def libraries : List (String × Nat) := [
  ("max_int", 0), ("max", 2), ("min", 2), ("not", 1), ("fst", 1), ("snd", 1), ("failwith", 1),
  ("lcnf_utf8_bytes", 1), ("lcnf_utf8_length", 1),
  ("List.rev", 1), ("List.rev_append", 2), ("List.length", 1), ("List.nth", 2),
  ("List.exists", 2), ("List.for_all", 2), ("List.map", 2), ("List.filter", 2),
  ("List.fold_left", 3), ("List.find_opt", 2), ("List.concat", 1), ("List.filter_map", 2),
  ("Option.is_some", 1), ("Option.is_none", 1), ("Option.value", 2), ("Option.map", 2),
  ("Option.bind", 2),
  ("E4_clock.of_nat", 1), ("E4_clock.to_profile_nat", 1), ("E4_clock.add", 2),
  ("E4_clock.le", 2), ("E4_clock.lt", 2), ("E4_clock.equal", 2), ("E4_clock.to_decimal", 1),
  ("E4_clock.of_decimal", 1)]

/-- The infix operators a form or a support body may use. -/
def operators : List String :=
  ["=", "<", "<=", ">", ">=", "+", "-", "*", "/", "mod", "land", "lor", "lxor", "lsr", "&&",
   "||", "^", "@"]

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

/-! ## 5. The table -/

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
private def natSucc : Form := .inline ["a"] (.binop "+" va (.int 1))
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
private def arrayGetBang : Form :=
  .inline ["d", "a", "i"]
    (.ifThen (.binop "<" (.var "i") (Ml.Expr.call "List.length" [va]))
      (Ml.Expr.call "List.nth" [va, .var "i"]) (.var "d"))
private def optionGetD : Form :=
  .inline ["o", "d"]
    (.appL (.var "Option.value") [(.nolabel, .var "o"), (.lbl "default", .var "d")])

private def row (lean : Name) (form : Form) (fidelity : Fidelity) (domain : String)
    (controls : List String) (note : String) (cost : String := "") : Builtin :=
  { lean, form, fidelity, domain, controls, note, cost }

open Form in
/-- The Lean constants with a native OCaml spelling, one row per constant. Names are unchecked
literals: several are specialisations that exist only in the target's environment. A row is
matched after `stripRedArg`, so one row stands for a constant and its `_redArg` twin. -/
def builtins : List Builtin := [
  -- Nat comparisons and arithmetic: `Nat` is `int`. A comparison is exact wherever both operands
  -- are representable.
  row `Nat.decEq (op "=") .domain "0 ≤ a, b < 2^62" []
    "Lean `Nat` is unbounded; OCaml `int` is 63-bit. `=` on `int` is structural equality of the machine word, which agrees with `Nat` equality on the representable range.",
  row `Nat.beq (op "=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decEq`.",
  row `instDecidableEqNat (op "=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decEq`; `Decidable` is `Bool` at mono.",
  row `Nat.decLt (op "<") .domain "0 ≤ a, b < 2^62" []
    "OCaml's `<` on `int` is signed; a saturated or wrapped operand can compare wrongly, which is why literals and `pow` saturate rather than wrap.",
  row `Nat.blt (op "<") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decLt`.",
  row `Nat.decLe (op "<=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decLt`.",
  row `Nat.ble (op "<=") .domain "0 ≤ a, b < 2^62" []
    "as `Nat.decLt`.",
  row `Nat.add (op "+") .domain "a + b < 2^62" []
    "OCaml `+` wraps at 2^62 without a trap; Lean's `Nat.add` does not.",
  row `Nat.mul (.support "lcnf_nat_mul") .domain "a * b < 2^62" ["mul-saturation"]
    "saturating: a product above `max_int` reads as `max_int`, where OCaml's raw `*` would wrap. The check is `b > max_int / a`, so no intermediate overflows.",
  row `Nat.div (natDiv) .domain "0 ≤ a, b < 2^62" ["div-zero"]
    "Includes Lean's total value at zero; unbounded input representation remains outside this target profile.",
  row `Nat.mod (natMod) .domain "0 ≤ a, b < 2^62" ["mod-zero"]
    "Includes Lean's remainder value at zero.",
  row `Nat.sub (natSub) .domain "0 ≤ a, b < 2^62" []
    "truncated subtraction, spelled out; exact on the representable range.",
  row `Nat.succ (natSucc) .domain "a + 1 < 2^62" []
    "as `Nat.add`.",
  row `Nat.pred (natPred) .domain "a < 2^62" []
    "truncated predecessor.",
  row `Nat.pow (.support "lcnf_nat_pow") .approximate "a ^ b < max_int" ["pow-saturation"]
    "saturating: `2 ^ 64` reads as `max_int` rather than wrapping to 0. The host profile of `ocaml/gen/NOTES.md` §5. Note the helper's own multiplications are checked against `max_int / a`, so the saturation is monotone.",
  row `Nat.shiftLeft (.support "lcnf_nat_shift_left") .approximate "a * 2^b ≤ max_int" ["shift-saturation"]
    "Checks both the power and final multiplication; larger results saturate at max_int.",
  row `Nat.shiftRight (natShiftRight) .domain "a < 2^62" []
    "OCaml's `lsr` is undefined at shift ≥ 63, so the row guards it; `lsr` on a non-negative `int` is Lean's `shiftRight` below 2^62.",
  row `Nat.land (op "land") .domain "a, b < 2^62" []
    "bitwise and on the 63-bit word.",
  row `Nat.lor (op "lor") .domain "a, b < 2^62" []
    "bitwise or on the 63-bit word.",
  row `Nat.xor (op "lxor") .domain "a, b < 2^62" []
    "bitwise xor on the 63-bit word.",
  -- UInt8: `int` with an explicit truncation on the way in.
  row `UInt8.decEq (op "=") .exact "" []
    "`UInt8` is `int`; both sides are already reduced mod 256 by `ofNat`.",
  row `instDecidableEqUInt8 (op "=") .exact "" []
    "as `UInt8.decEq`.",
  row `UInt8.beq (op "=") .exact "" []
    "as `UInt8.decEq`.",
  row `UInt8.ofNat (u8Mask) .exact "" []
    "`UInt8.ofNat` is `n % 256`, and `land 255` is `% 256` on a non-negative `int`.",
  row `UInt8.ofNatLT (u8Mask) .exact "" []
    "the argument is already < 256; the mask is a no-op.",
  row `UInt8.ofNatTruncate (u8Clamp) .domain "a is a representable non-negative int" ["u8-clamp"]
    "Clamps at 255, matching Lean; the 256 counterexample is a permanent control.",
  row `UInt8.ofNatClamp (u8Clamp) .domain "a is a representable non-negative int" []
    "The current spelling of the same clamping operation.",
  row `UInt8.toNat (same) .exact "" []
    "identity on the representation.",
  row `UInt8.toUInt64 (same) .exact "" []
    "identity on the representation; `UInt64` is `int` too.",
  row `UInt8.toUInt32 (same) .exact "" []
    "identity on the representation.",
  -- UInt64: `int` too, the float frame's bits (`Store.Val.float`). Not exact above 2^62.
  row `UInt64.decEq (op "=") .domain "both bit patterns < 2^62" []
    "`UInt64` is `int` here, the float frame's bits. A pattern at 2^62 or above has no carrier, and nothing detects it. The type row is `unsound` for the same reason. Open, not supported, until an exact 64-bit carrier exists.",
  row `instDecidableEqUInt64 (op "=") .domain "both bit patterns < 2^62" []
    "as `UInt64.decEq`.",
  row `UInt64.beq (op "=") .domain "both bit patterns < 2^62" []
    "as `UInt64.decEq`.",
  row `UInt64.toNat (same) .domain "the bit pattern < 2^62" []
    "identity on the representation; as `UInt64.decEq` outside the domain.",
  -- Bool
  row `Bool.decEq (op "=") .exact "" []
    "OCaml `bool` is Lean `Bool`.",
  row `instDecidableEqBool (op "=") .exact "" []
    "as `Bool.decEq`.",
  row `Bool.not (.library "not") .exact "" []
    "",
  row `not (.library "not") .exact "" []
    "",
  row `Bool.and (op "&&") .approximate "" []
    "OCaml's `&&` is short-circuiting and Lean's `Bool.and` is a strict function of two already-evaluated arguments. At mono LCNF both arguments are already `let`-bound values, so the difference is unobservable *here* — but the row is not exact as a function-level claim, and an emitter that inlined the arguments would change evaluation order.",
  row `and (op "&&") .approximate "" []
    "as `Bool.and`.",
  row `Bool.or (op "||") .approximate "" []
    "as `Bool.and`.",
  row `or (op "||") .approximate "" []
    "as `Bool.and`.",
  -- String: UTF-8 bytes on both sides.
  row `String.decEq (op "=") .exact "" []
    "OCaml's structural `=` on `string` is byte equality; two Lean strings are equal iff their UTF-8 encodings are equal, and the route's strings *are* their UTF-8 bytes.",
  row `instDecidableEqString (op "=") .exact "" []
    "as `String.decEq`.",
  row `String.append (op "^") .exact "" []
    "concatenation of UTF-8 byte sequences is the encoding of the concatenation.",
  row `String.length (.library "lcnf_utf8_length") .domain "valid UTF-8; scalar count fits int" ["utf8-length"]
    "Counts leading UTF-8 bytes, hence Unicode scalar values for represented Lean strings.",
  row `String.toUTF8 (.library "lcnf_utf8_bytes") .domain "valid UTF-8" ["utf8-literal-bytes"]
    "Emitted helper returns the actual encoded bytes, including non-ASCII keys.",
  row `ByteArray.data (same) .exact "" []
    "Byte arrays use the same list-of-byte representation as their data array.",
  -- List
  row `List.appendTR (op "@") .exact "" []
    "`appendTR` is `append` (the tail-recursive spelling the mono phase leaves behind).",
  row `List.append (op "@") .exact "" []
    "",
  row `List.reverse (.library "List.rev") .exact "" []
    "",
  row `List.reverseAux (.library "List.rev_append") .exact "" []
    "`List.reverseAux as bs = List.rev_append as bs`.",
  row `List.length (.library "List.length") .domain "length < 2^62" []
    "the result is a `Nat` spelled as `int`.",
  row `List.lengthTR (.library "List.length") .domain "length < 2^62" []
    "as `List.length`.",
  row `List.instDecidableEqNil (listIsEmpty) .exact "" []
    "the structural comparison of a list against the empty list is `isEmpty`.",
  row `List.isEmpty (listIsEmpty) .exact "" []
    "",
  row `List.elem (listElem) .exact "" ["elem-order"]
    "`[BEq α]` is a one-field structure at mono, so the instance is a relevant argument. Lean's `List.elem a (b :: l)` tests `a == b`, i.e. `inst a b`; `List.exists (inst a) l` tests the same, in the same order.",
  row `List.contains (.support "lcnf_list_contains") .exact "" ["contains-order", "callback-exception"]
    "`contains as a` is `elem a as`, so the target is the first BEq argument, as in the `elem` row; an asymmetric instance sees the same order on both sides (the `contains-order` control).",
  row `List.map (.library "List.map") .exact "" []
    "",
  row `List.mapTR (.library "List.map") .exact "" []
    "",
  row `List.filter (.library "List.filter") .exact "" []
    "",
  row `List.filterTR (.library "List.filter") .exact "" []
    "",
  row `List.foldl (.library "List.fold_left") .exact "" []
    "same argument order (`f`, `init`, `l`) and same associativity.",
  row `List.all (listAll) .exact "" ["all-scan"]
    "Lean takes the list first, OCaml the predicate first; the row swaps.",
  row `List.any (listAny) .exact "" ["any-scan"]
    "as `List.all`.",
  row `List.find? (.library "List.find_opt") .exact "" []
    "",
  row `List.flatten (.library "List.concat") .exact "" []
    "OCaml's `List.concat` is `flatten`.",
  row `List.flattenTR (.library "List.concat") .exact "" []
    "",
  row `List.filterMap (.library "List.filter_map") .exact "" []
    "",
  row `List.filterMapTR (.library "List.filter_map") .exact "" []
    "",
  -- Array as list: the shim. `USize` is the shim's index type.
  row `Array.mkEmpty (arrayEmpty) .exact "" []
    "`Array` is `list`; the capacity hint is dropped.",
  row `Array.emptyWithCapacity (arrayEmpty) .exact "" []
    "",
  row `Array.toList (same) .exact "" []
    "identity under the shim.",
  row `List.toArray (same) .exact "" []
    "identity under the shim.",
  row `Array.push (arrayPush) .exact "" []
    "`a @ [x]` is the sequence with `x` appended."
    (cost := "O(n) per push where Lean's `Array.push` is amortised O(1); a `push` in a loop is quadratic."),
  row `Array.size (.library "List.length") .exact "" []
    "the length of the list that stands for the array."
    (cost := "O(n) where Lean's is O(1)."),
  row `Array.appendList (op "@") .exact "" []
    "",
  row `List.foldl._at_.Array.appendList.spec_0 (op "@") .exact "" []
    "the specialisation of the fold that `Array.appendList` compiles to.",
  row `USize.ofNat (same) .domain "a < 2^62" []
    "`USize` is the shim's index type and is `int`.",
  row `USize.toNat (same) .exact "" []
    "",
  row `USize.ofNatLT (same) .exact "" []
    "",
  row `USize.decEq (op "=") .domain "a, b < 2^62" []
    "",
  row `USize.beq (op "=") .domain "a, b < 2^62" []
    "",
  row `USize.sub (natSub) .unsound "a ≥ b" []
    "`USize.sub` in Lean **wraps** (it is `Fin (2^64)` subtraction: `0 - 1 = 2^64 - 1`); the row **truncates** to 0. Every use in this closure is a bounded index decrement where `a ≥ b`, so the difference is not reached, but the row is not the Lean function.",
  row `USize.add (op "+") .unsound "a + b < 2^62" []
    "`USize.add` wraps at 2^64 in Lean; OCaml's `+` wraps at 2^62. Two different wrapping points.",
  row `Array.uget (.library "List.nth") .unsound "i < length" []
    "Lean's `Array.uget a i h` is total (`h` proves `i` in range) and the row is `List.nth`, which **raises** `Failure \"nth\"` out of range and `Invalid_argument` on a negative index."
    (cost := "O(i) under the shim where Lean's is O(1)."),
  row `Array.get! (arrayGetBang) .domain "represented non-negative index; returned-value observation" ["array-default"]
    "Out-of-range lookup returns the supplied default. Lean panic diagnostics are not reproduced."
    (cost := "linear in the index."),
  row `Array.fget (.library "List.nth") .domain "i < length" []
    "The source carries a bounded index; list lookup agrees on that domain."
    (cost := "linear in the index."),
  -- Option, Prod, panic
  row `Option.isSome (.library "Option.is_some") .exact "" []
    "",
  row `Option.isNone (.library "Option.is_none") .exact "" []
    "",
  row `Option.getD (optionGetD) .exact "" ["option-default", "option-default-eager"]
    "",
  row `Option.map (.library "Option.map") .exact "" []
    "",
  row `Option.bind (.library "Option.bind") .exact "" []
    "",
  row `Prod.fst (.library "fst") .exact "" []
    "",
  row `Prod.snd (.library "snd") .exact "" []
    "",
  row `panic (.library "failwith") .approximate "" []
    "Lean's `panic` logs and **returns `default`**: the caller continues with a junk value. OCaml's `failwith` raises `Failure`. The OCaml behaviour is arguably the better one, but it is not the Lean one, and a Lean theorem about a program that panics says nothing about an OCaml run that aborts.",
  row `panicCore (.library "failwith") .approximate "" []
    "as `panic`.",
  -- The exact clock: `Effect4.ClockMillis` is `E4_clock.t`, a Zarith integer.
  row `Effect4.ClockMillis.ofNat (.library "E4_clock.of_nat") .domain "n < 2^62, the natural as the `int` that carries it" []
    "`E4_clock.of_nat` is `Z.of_int` on a non-negative `int`, and raises `Profile_refusal` on a negative one. A literal reaches the clock by `clockNatIngress?` as exact decimal text, and a natural that the literal rule narrowed is refused at generation. Read against `ocaml/clock/e4_clock.ml`; its own tests are `ocaml/clock/test_clock.ml`.",
  row `Effect4.ClockMillis.toNat (.library "E4_clock.to_profile_nat") .domain "millis ≤ 2^53 - 1 and the value fits `int`" []
    "`E4_clock.to_profile_nat` raises `Profile_refusal` outside the domain: a refusal outside the program's result, never a wrapped value (DI-56).",
  -- The one addition that can leave the profile (decisions row 321): `succ`, `add`, `plus` and
  -- `minus` grow through it, and its form refuses outside the bound.
  row `Effect4.Program.Profile.grow
    (.inline ["a", "b"] (.call "E4_clock.to_profile_nat"
      [.call "E4_clock.add" [.call "E4_clock.of_nat" [.var "a"], .call "E4_clock.of_nat" [.var "b"]]]))
    .domain "a + b ≤ 2^53 - 1, and each of a and b fits `int`" []
    "Exact addition on `E4_clock.t`, then `E4_clock.to_profile_nat`, which raises `Profile_refusal` outside the domain: a refusal outside the program's result, never a wrapped value (DI-56, decisions row 108). The engine answers it as `Outside_profile` with the input machine retained (`ocaml/engine/e4_engine.mli`)."
    "two conversions and one Zarith addition for one machine addition",
  row `Effect4.ClockMillis.add (.library "E4_clock.add") .exact "" []
    "`E4_clock.add` is `Z.add`, exact on naturals of any size; Lean's `add` is `ofNat (a.toNat + b.toNat)` (`ClockMillis.toNat_add`).",
  row `Effect4.ClockMillis.decLe (.library "E4_clock.le") .exact "" []
    "`E4_clock.le` is `Z.leq`; Lean compares the two `toNat`.",
  row `Effect4.ClockMillis.decLt (.library "E4_clock.lt") .exact "" []
    "`E4_clock.lt` is `Z.lt`; as `decLe`.",
  row `Effect4.ClockMillis.beq (.library "E4_clock.equal") .exact "" []
    "`E4_clock.equal` is `Z.equal`. One `Z.t` stands for one natural, and `ofNat` and `toNat` are inverse (`ofNat_toNat`, `toNat_ofNat`), so equality of the carriers is equality of the clocks.",
  row `Effect4.instDecidableEqClockMillis (.library "E4_clock.equal") .exact "" []
    "as `ClockMillis.beq`; `Decidable` is `Bool` at mono.",
  row `Effect4.ClockMillis.toDecimal (.library "E4_clock.to_decimal") .exact "" []
    "`E4_clock.to_decimal` is `Z.to_string`: the decimal digits with no leading zero, as `Nat.repr` writes them.",
  row `Effect4.ClockMillis.ofDecimal (.library "E4_clock.of_decimal") .exact "" []
    "Both read exactly the spelling `toDecimal` writes: a non-empty digit string with no leading zero, or `0`. Lean's side is `ofDecimal_exact` and `ofDecimal_toDecimal`; the OCaml side is read against `e4_clock.ml`. No theorem joins the two."
]

/-! ## 6. What the table computes -/

/-- The support function of a name. -/
def supportOf? (name : String) : Option Support := support.find? (·.name == name)

/-- The number of relevant (non-erased) arguments a form takes. -/
def Form.arity : Form → Nat
  | .inline ps _ => ps.length
  | .support n => ((supportOf? n).map (·.params.length)).getD 0
  | .library n => (libraries.lookup n).getD 0

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

/-! ## 7. The table's own check -/

/-- The names of a list that occur more than once, each reported once. -/
private def repeated [BEq α] (xs : List α) : List α :=
  (xs.filter fun x => (xs.filter (· == x)).length > 1).eraseDups

/-- Everything wrong with a table, a support list and a library list. It is empty for the
three of this module, and it refuses each altered copy below. -/
def problemsOf (rows : List Builtin) (sup : List Support) (lib : List (String × Nat)) :
    List String := Id.run do
  let libNames := lib.map (·.1)
  let supNames := sup.map (·.name)
  let mut out : List String := []
  -- the keys
  for r in rows do
    if stripRedArg r.lean != r.lean then
      out := out ++ [s!"row {r.lean}: the key is not normalized"]
  for n in repeated (rows.map (·.lean)) do
    out := out ++ [s!"row {n}: the key has two rows"]
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
          unless operators.contains o do
            out := out ++ [s!"row {r.lean}: the operator `{o}` is not declared"]
    | .support n =>
      unless supNames.contains n do
        out := out ++ [s!"row {r.lean}: the support function `{n}` is not defined"]
    | .library n =>
      match lib.lookup n with
      | none => out := out ++ [s!"row {r.lean}: the library function `{n}` is not declared"]
      | some 0 => out := out ++ [s!"row {r.lean}: `{n}` is not a function"]
      | some _ => pure ()
  -- the library and the prelude
  for n in repeated libNames do
    out := out ++ [s!"library `{n}`: declared twice"]
  for b in rawPrimitives do
    unless lib.lookup b.name == some b.params.length do
      out := out ++ [s!"primitive `{b.name}`: not declared with its arity"]
  for n in repeated supNames do
    out := out ++ [s!"support `{n}`: defined twice"]
  let mut earlier : List String := []
  for s in sup do
    if libNames.contains s.name || operators.contains s.name then
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
        unless operators.contains o do
          out := out ++ [s!"support `{s.name}`: the operator `{o}` is not declared"]
      if s.recursive && !u.free.contains s.name then
        out := out ++ [s!"support `{s.name}`: marked recursive, and it does not call itself"]
    earlier := earlier ++ [s.name]
  return out

/-- The problems of this module's table. -/
def problems : List String := problemsOf builtins support libraries

#guard problems.isEmpty

-- No reserved name is another's: an eta binder is not a name a call site must reach.
#guard etaBinders.all fun b => !protectedNames.contains b && !(libraries.map (·.1)).contains b
#guard maxArity == 3
#guard builtins.length == 107

/-! ### Controls: each altered copy is refused, for its own reason -/

private def refuses (ps : List String) (reason : String) : Bool :=
  ps.any fun p => (p.splitOn reason).length > 1

-- a support definition left out: its row has no function, and its dependent no declaration
#guard refuses (problemsOf builtins (support.filter (·.name != "lcnf_nat_pow")) libraries)
  "the support function `lcnf_nat_pow` is not defined"
#guard refuses (problemsOf builtins (support.filter (·.name != "lcnf_nat_pow")) libraries)
  "support `lcnf_nat_shift_left`: `lcnf_nat_pow` is not declared before it"
-- the definitions out of order
#guard refuses (problemsOf builtins support.reverse libraries)
  "support `lcnf_nat_shift_left`: `lcnf_nat_pow` is not declared before it"
-- a library dependency left out
#guard refuses (problemsOf builtins support (libraries.filter (·.1 != "max_int")))
  "support `lcnf_nat_mul`: `max_int` is not declared before it"
#guard refuses (problemsOf builtins support (libraries.filter (·.1 != "max")))
  "row Nat.sub: `max` is not declared"
-- two rows for one key, and a key that `stripRedArg` would change
#guard refuses (problemsOf (builtins ++ builtins.take 1) support libraries)
  "row Nat.decEq: the key has two rows"
#guard refuses
  (problemsOf (row (`Nat.add ++ `_redArg) (Form.op "+") .exact "" [] "" :: builtins) support
    libraries)
  "the key is not normalized"
-- an inline body that binds, and a support body of verbatim text
#guard refuses
  (problemsOf [row `Nat.mul (.inline ["a"] (.letIn "t" va (.var "t"))) .exact "" [] ""] support
    libraries)
  "row Nat.mul: the inline body leaves its fragment"
#guard refuses
  (problemsOf builtins [{ name := "lcnf_x", params := ["a"], body := .raw "a" }] libraries)
  "support `lcnf_x`: the body leaves its fragment"
-- a support body whose own binder hides a parameter
#guard refuses
  (problemsOf [] [{ name := "lcnf_x", params := ["a"], body := .letIn "a" va va }] libraries)
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
#guard (builtin? `Array.get!).any (!·.form.strict)    -- `a` and `i` twice, `d` in one arm
#guard (builtin? `Bool.and).any (!·.form.strict)      -- the right operand is lazy
#guard (builtin? `Array.mkEmpty).any (!·.form.strict) -- the capacity is dropped

end OCaml5.Lcnf
