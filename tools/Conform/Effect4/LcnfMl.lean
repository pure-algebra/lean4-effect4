import Conform.Lcnf.SemanticsTarget
import Conform.Lcnf.Validity
import OCaml5.Lcnf.Translate
import OCaml5.Lcnf.Types
import OCaml5.Ml.Render
import Effect4.Program.Ty
import Effect4.Machine.Key

/-!
# Conform.Effect4.LcnfMl — rung 3: the emitted OCaml, read into the target semantics

**What it is.** A reader from `OCaml5.Ml.Syntax` into `Conform.Lcnf.Target`, the assembly of an
emitted module into a target program, and the marshalling of `Ty` into the target's values. The
compiler checkpoint (`Conform.Effect4.Normalization`, `make check-compiler`) runs its target lane
through them: the input is exactly the syntax tree `OCaml5.Ml.Render` renders. The vector lane
that ran this reader on 20,387 vectors went on 2026-10-15: no gate ran it
(`git:fef45fb5a:tools/Conform/Effect4/LcnfMl.lean`, decisions row 391).

**The reader refuses by name.** The reader reads every form the route builds. The syntax also
holds the `eff/` emitter's forms and the module language (`OCaml5.Ml.Syntax`): a trailing comment
reads as its expression, an integer pattern as the target's, and `function`, a sequence, a
pattern `let`, an `if` without `else` and a packed module are refused by name, each an `Except`
error naming it. One labelled application is read, by its exact shape:
`Option.value o ~default:d`, the form of the row `Option.getD`. Every other labelled application
is refused. The refusals a run reports are listed in its output.

The production backend emits its UTF-8 helper and byte-array identity. This reader uses
those same emitted declarations, with named primitive assumptions in the target evaluator.
No generated binding is replaced by this driver.
-/

open Lean Compiler LCNF
open Conform Conform.Lcnf
open Effect4.Program

namespace Conform.Effect4.LcnfMl

/-! ## 1. The reader

The reader is two algebras of the OCaml syntax's fold (`OCaml5.Ml.Fold`): every pattern reads,
and an expression reads unless it is a form the route never emits or a labelled application other
than the one the builtin table writes. -/

/-- Constructor names an OCaml target spells as a literal rather than as a constructor. -/
def litCtor? : String → Option Target.Pat
  | "true" => some (.bool true)
  | "false" => some (.bool false)
  | "()" => some .unit
  | _ => none

/-- A pattern, read. -/
def ofPatAlg : OCaml5.Ml.PatAlgebra (fun _ => Target.Pat) where
  pat_wild := .wild
  pat_var n := .var n
  pat_ctor n args :=
    match litCtor? n, args with
    | some p, [] => p
    | _, _ => .ctor n args
  pat_record fs := .record fs false
  pat_recordOpen fs := .record fs true
  pat_tuple ps := .tuple ps
  pat_cons h t := .ctor "::" [h, t]
  pat_int n := .int n

def ofPat (p : OCaml5.Ml.Pat) : Target.Pat := OCaml5.Ml.cata_pat ofPatAlg p

/-- The target evaluator's primitives: the route's library entries that it answers, with their
arities and scans (`OCaml5.Lcnf.targetArities`, `OCaml5.Lcnf.targetScans`), at a word. -/
def primEnv (word : Target.Word := { bits := 63 }) : Target.PrimEnv :=
  { word, arity := OCaml5.Lcnf.targetArities, scans := OCaml5.Lcnf.targetScans }

/-- Operators and function names the target evaluates as primitives; `::` is a constructor,
not a primitive, and is handled before this. -/
def isPrimName (n : String) : Bool := OCaml5.Lcnf.targetArities.contains n

private def all (xs : List (Except String Target.Expr)) : Except String (List Target.Expr) :=
  xs.mapM id

/-- An expression, read. An application of a primitive's name is the primitive; the one labelled
call it reads is `Option.value o ~default:d`, the form of the row `Option.getD`, by its exact
shape, and the target primitive takes both as values, as the call evaluates both. -/
def ofExprAlg : OCaml5.Ml.ExprAlgebra (fun _ => Except String Target.Expr) where
  expr_var n := .ok (.var n)
  expr_int n := .ok (.int n)
  expr_str s := .ok (.str s)
  expr_bool b := .ok (.bool b)
  expr_unit := .ok .unit
  expr_ctor n args := do
    match n, args with
    | "true", [] => return .bool true
    | "false", [] => return .bool false
    | "()", [] => return .unit
    | _, _ => return .ctor n (← all args)
  expr_app f args := do
    let as ← all args
    match ← f with
    | .var n => if isPrimName n then return .prim n as else return .app (.var n) as
    | f' => return .app f' as
  expr_appL f args := do
    match ← f, args with
    | .var "Option.value", [(.nolabel, o), (.lbl "default", d)] =>
      return .prim "Option.value~default" [← o, ← d]
    | _, _ => .error "Ml.Expr.appL (a labelled application other than `Option.value o ~default:d`)"
  expr_binop op l r := do
    if op == "::" then return .ctor "::" [← l, ← r]
    else if isPrimName op then return .prim op [← l, ← r]
    else .error s!"Ml.Expr.binop `{op}`"
  expr_fn params body := do return .fn params (← body)
  expr_letIn n v b := do return .letIn n (← v) (← b)
  expr_letRec f ps v b := do return .letRec [(f, ps, ← v)] (← b)
  expr_ifThen c t e := do return .ifThen (← c) (← t) (← e)
  expr_matchE scrut arms := do
    return .matchE (← scrut) (← arms.mapM fun (p, body) => do return (ofPat p, ← body))
  expr_record fs := do return .record (← fs.mapM fun (k, e) => do return (k, ← e))
  expr_field e n := do return .field (← e) n
  expr_tuple parts := do return .tuple (← all parts)
  expr_listLit items := do
    let es ← all items
    return es.foldr (fun h t => .ctor "::" [h, t]) (.ctor "[]" [])
  expr_annot e _ := e
  expr_hole note _ := .ok (.fail s!"HOLE: {note}")
  expr_assertE _ := .ok (.fail "assert false")
  -- a trailing comment is whitespace; the forms the route never emits are refused by name
  expr_commented e _ := e
  expr_fnMatch _ := .error "Ml.Expr.fnMatch"
  expr_seq _ _ := .error "Ml.Expr.seq"
  expr_letPat _ _ _ := .error "Ml.Expr.letPat"
  expr_ifUnit _ _ := .error "Ml.Expr.ifUnit"
  expr_pack _ _ := .error "Ml.Expr.pack"

def ofExpr (e : OCaml5.Ml.Expr) : Except String Target.Expr := OCaml5.Ml.cata_expr ofExprAlg e

/-- One `Ml.Bind` as a top-level target binding. -/
def ofBind (b : OCaml5.Ml.Bind) : Except String (String × List String × Target.Expr) := do
  return (b.name, b.params.map (·.1), ← ofExpr b.body)

/-! ## 1b. The program an emitted module is

An emitted module is its declarations, which call the route's runtime library (`ocaml/lcnf`,
library `effect4_lcnf`). The target program is the same declarations, beside a binding for each
library function that `OCaml5.Lcnf.support` defines, read from that reference definition. The
library holds the OCaml of the same functions; the host checks hold the two to the same answers,
on this evaluator and in compiled OCaml (`Conform.Effect4.Normalization`). The library's string
primitives and the target's own library are not read: they are the evaluator's primitives
(`Target.applyPrim`), named assumptions. -/

/-- The bindings every target program starts from: `max_int` for the profile's word, and the
runtime library's functions that `OCaml5.Lcnf.support` defines, each under its library path. A
support function called from another binding starts from its parameters
alone (`Target.applyNamed`), so `max_int` is a binding of the program and not of a caller's
environment. A body the reader refuses, a name bound twice and a name the evaluator already
answers as a primitive are errors here, never missing bindings. -/
def supportBinds (word : Target.Word := { bits := 63 })
    (support : List OCaml5.Lcnf.Support := OCaml5.Lcnf.support) :
    Except String (Std.HashMap String (List String × Target.Expr)) := do
  let mut binds : Std.HashMap String (List String × Target.Expr) := {}
  binds := binds.insert "max_int" ([], .int word.maxInt)
  for s in support do
    if isPrimName s.name then throw s!"support `{s.name}`: the evaluator has a primitive of this name"
    let (name, ps, body) ← (ofBind s.bind).mapError fun why => s!"support `{s.name}`: {why}"
    if binds.contains name then throw s!"support `{name}`: bound twice"
    binds := binds.insert name (ps, body)
  return binds

/-- The target program of a translated closure: the support bindings, then the closure's own
declarations. A declaration that takes a name already bound is refused. -/
def assemble (decls : Array OCaml5.Lcnf.Translated) (word : Target.Word := { bits := 63 })
    (support : List OCaml5.Lcnf.Support := OCaml5.Lcnf.support) :
    Except String Target.Program := do
  let mut binds ← supportBinds word support
  for d in decls do
    let (name, ps, body) ← (ofBind d.bind).mapError fun why => s!"{d.leanName}: {why}"
    if binds.contains name then throw s!"{d.leanName}: `{name}` is already bound"
    binds := binds.insert name (ps, body)
  return { binds, pe := primEnv word }

/-! ## 2. Marshalling `Ty` into the OCaml value domain

The OCaml constructor names come from `OCaml5.Lcnf.ctorName` — the same function the
translator uses — so a rename in `Naming` breaks this differential rather than silently
comparing two different representations. -/

def tyCtor (c : String) : String := OCaml5.Lcnf.ctorName ``Ty c

mutual
def tyT : Ty → Target.TValue
  | .never => .ctorV (tyCtor "never") #[]
  | .unit => .ctorV (tyCtor "unit") #[]
  | .nat => .ctorV (tyCtor "nat") #[]
  | .int => .ctorV (tyCtor "int") #[]
  | .string => .ctorV (tyCtor "string") #[]
  | .bool => .ctorV (tyCtor "bool") #[]
  | .handle t => .ctorV (tyCtor "handle") #[.str t]
  | .option i => .ctorV (tyCtor "option") #[tyT i]
  | .list i => .ctorV (tyCtor "list") #[tyT i]
  | .prod l r => .ctorV (tyCtor "prod") #[tyT l, tyT r]
  | .except e v => .ctorV (tyCtor "except") #[tyT e, tyT v]
  | .exitOf v e => .ctorV (tyCtor "exitOf") #[tyT v, tyT e]
  | .causeOf e => .ctorV (tyCtor "causeOf") #[tyT e]
  | .fiberOf v e => .ctorV (tyCtor "fiberOf") #[tyT v, tyT e]
  | .union l r => .ctorV (tyCtor "union") #[tyT l, tyT r]
  | .lit s => .ctorV (tyCtor "lit") #[.str s]
  | .refOf v => .ctorV (tyCtor "refOf") #[tyT v]
  | .deferredOf v e => .ctorV (tyCtor "deferredOf") #[tyT v, tyT e]
  | .var i => .ctorV (tyCtor "var") #[.int i]
  | .unknown => .ctorV (tyCtor "unknown") #[]
  | .record fs => .ctorV (tyCtor "record") #[Target.TValue.ofList (fieldTs fs)]
  | .map k v => .ctorV (tyCtor "map") #[tyT k, tyT v]
  | .tuple ts => .ctorV (tyCtor "tuple") #[Target.TValue.ofList (itemTs ts)]
  | .app n ts => .ctorV (tyCtor "app") #[.str n, Target.TValue.ofList (itemTs ts)]
  | .null => .ctorV (tyCtor "null") #[]
  | .undefined => .ctorV (tyCtor "undefined") #[]
  | .number => .ctorV (tyCtor "number") #[]
  | .bytes => .ctorV (tyCtor "bytes") #[]
  -- the row is the engine's `service_key effect4_row`, a list of key records; not in the vectors
  | .contextOf keys => .ctorV (tyCtor "contextOf") #[Target.TValue.ofList (keys.elems.map fun k =>
      .recordV #[("name", .int k.name.value), ("service", .int k.service.value)])]
/-- A record's fields, each the OCaml tuple `(name, (optional, type))`. -/
def fieldTs : List (String × Bool × Ty) → List Target.TValue
  | [] => []
  | (n, o, t) :: rest => .tupleV #[.str n, .tupleV #[.bool o, tyT t]] :: fieldTs rest
/-- A tuple's or a reference's items. -/
def itemTs : List Ty → List Target.TValue
  | [] => []
  | t :: rest => tyT t :: itemTs rest
end

def natListT (ns : List Nat) : Target.TValue :=
  Target.TValue.ofList (ns.map fun n => Target.TValue.int (Int.ofNat n))

end Conform.Effect4.LcnfMl
