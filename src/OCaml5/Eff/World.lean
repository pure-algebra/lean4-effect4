import Lean
import Effect4.Program.Native

/-!
# OCaml5.Eff.World

**What it is.** The closed world of the `Eff` program IR as OCaml carriers: `OTy`, the carrier
alphabet a field or constructor argument is carried by; `Spec`/`blocks`, the Lean families in
the order their OCaml `type … and …` groups are emitted; and `readBlocks`, which reads every
family's constructors and their carriers off the Lean environment (`Effect4.Program.Native`).
`OCaml5.Eff.Emit` writes the OCaml library from it, `OCaml5.Eff.Goldens` the corpus.

**Depends on.** `Effect4.Program.Native` (the IR and its native signature), `Lean.Meta`.

**Properties.**
* **Closed.** A field whose type has no carrier is an error at generation time, never a hole in
  the output — *by construction* (`ocamlTy` throws).
* **Declaration order.** Constructors come in the environment's order, so `ctor_index_<t>` is the
  wire tag `Effect4.Store.Canonical` assigns — *by construction*.
* **`Effect4.Row α` is carried as `α list`**, the one non-structural rule — *by construction*.
-/

open Lean Meta
open Effect4.Program
open Effect4.Supervision (MaskMode ForkOptions ObserverMode)
open Effect4 (FinalizerStrategy ServiceKey)
open Effect4.Machine (FnName)

namespace OCaml5.Eff

/-! ## OCaml carriers -/

/-- The OCaml type an argument or field is carried by. -/
inductive OTy
  | int | bool | string | unit
  | option (a : OTy)
  | list (a : OTy)
  | prod (a b : OTy)
  | named (n : String)
deriving Repr, BEq, Inhabited

mutual
partial def OTy.render : OTy → String
  | .int => "int"
  | .bool => "bool"
  | .string => "string"
  | .unit => "unit"
  | .option a => a.renderArg ++ " option"
  | .list a => a.renderArg ++ " list"
  | .prod a b => a.renderArg ++ " * " ++ b.renderArg
  | .named n => n
/-- As a constructor argument or a type-constructor argument: products parenthesised. -/
partial def OTy.renderArg : OTy → String
  | .prod a b => "(" ++ OTy.render (.prod a b) ++ ")"
  | t => t.render
end

/-- The OCaml constructor of `<Type>.<ctor>`: the type's OCaml name capitalised, an underscore,
the Lean constructor name verbatim. -/
def octor (oname short : String) : String := oname.capitalize ++ "_" ++ short

/-- The OCaml record field of `<Type>.<field>`. -/
def ofield (oname field : String) : String := oname ++ "_" ++ field

def shortName : Name → String
  | .str _ s => s
  | n => n.toString

/-- `(0, x₀), (1, x₁), …` -/
def enumL {α : Type} (xs : List α) : List (Nat × α) := (List.range xs.length).zip xs

/-! ## The closed world -/

structure Spec where
  leanName : Name
  oname : String
  /-- The OCaml carrier of each type parameter, by position: the instantiation the mirror is
  taken at (`Eff NativeOp`). Parameters without a carrier (instance arguments) get none; a
  field that mentions one is a refusal. -/
  params : List OTy := []

def natOp : OTy := .named "native_op"

/-- The families, grouped as the OCaml `type … and …` groups are emitted: a Lean mutual block
is one group. Order is dependency order. -/
def blocks : List (List Spec) :=
  [ [⟨`Effect4.Program.Ty, "ty", []⟩]
  , [⟨`Effect4.Program.Lit, "lit", []⟩]
  , [⟨`Effect4.Program.Term, "term", []⟩, ⟨`Effect4.Program.Terms, "terms", []⟩]
  , [⟨`Effect4.Program.CauseTerm, "cause_term", []⟩]
  , [⟨`Effect4.Supervision.MaskMode, "mask_mode", []⟩]
  , [⟨`Effect4.Supervision.ForkOptions, "fork_options", []⟩]
  , [⟨`Effect4.Supervision.ObserverMode, "observer_mode", []⟩]
  , [⟨`Effect4.FinalizerStrategy, "finalizer_strategy", []⟩]
  , [⟨`Effect4.Machine.FnName, "fn_name", []⟩]
  , [⟨`Effect4.Program.NativeOp, "native_op", []⟩]
  , [ ⟨`Effect4.Program.Eff, "eff", [natOp]⟩, ⟨`Effect4.Program.Stmt, "stmt", [natOp]⟩
    , ⟨`Effect4.Program.Stmts, "stmts", [natOp]⟩, ⟨`Effect4.Program.Effs, "effs", [natOp]⟩
    , ⟨`Effect4.Program.ActionTerm, "action_term", [natOp]⟩ ]
  , [⟨`Effect4.Program.RowKind, "row_kind", []⟩]
  , [⟨`Effect4.Program.RowShape, "row_shape", []⟩]
  , [⟨`Effect4.ServiceName, "service_name", []⟩]
  , [⟨`Effect4.ServiceTypeCode, "service_type_code", []⟩]
  , [⟨`Effect4.ServiceKey, "service_key", []⟩]
  , [⟨`Effect4.Program.Row, "row", []⟩]
  , [⟨`Effect4.Program.EffTy, "eff_ty", []⟩] ]

def allSpecs : List Spec := blocks.flatten

/-- The carrier of a Lean type expression. `Effect4.Row α` (a canonical list with a proof
field) is carried as `α list`: the one non-structural rule, for `EffTy.requires`. -/
partial def ocamlTy (pm : List (FVarId × OTy)) (e : Expr) : MetaM OTy := do
  let e ← whnfR e
  match e with
  | .fvar id =>
    match pm.find? (·.1 == id) with
    | some (_, t) => pure t
    | none => throwError "EffGen: a field mentions a parameter with no OCaml carrier: {e}"
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let .const n _ := fn | throwError "EffGen: no OCaml carrier for {e}"
    if n == ``Nat then pure .int
    else if n == ``Bool then pure .bool
    else if n == ``String then pure .string
    else if n == ``Unit || n == ``PUnit then pure .unit
    else if n == ``Option then pure (.option (← ocamlTy pm args[0]!))
    else if n == ``List then pure (.list (← ocamlTy pm args[0]!))
    else if n == ``Prod then pure (.prod (← ocamlTy pm args[0]!) (← ocamlTy pm args[1]!))
    else if n == `Effect4.Row then pure (.list (← ocamlTy pm args[0]!))
    else match allSpecs.find? (·.leanName == n) with
      | some s => pure (.named s.oname)
      | none => throwError "EffGen: no OCaml carrier for {e} (head {n})"

structure Ctor where
  name : Name
  short : String
  args : List (String × OTy)
deriving Inhabited

structure Family where
  spec : Spec
  isStruct : Bool
  ctors : List Ctor

/-- `Effect4.Program.Term`, unambiguous beside `Lean.Term`. -/
abbrev PTerm := Effect4.Program.Term

def readFamily (spec : Spec) : MetaM Family := do
  let env ← getEnv
  let info ← getConstInfoInduct spec.leanName
  let isStruct := isStructure env spec.leanName
  let ctors ← info.ctors.mapM fun c => do
    let ci ← getConstInfoCtor c
    forallTelescope ci.type fun xs _ => do
      let pm := (List.range info.numParams).filterMap fun i =>
        match spec.params[i]? with
        | some t => some (xs[i]!.fvarId!, t)
        | none => none
      let mut args : Array (String × OTy) := #[]
      for f in xs[info.numParams:] do
        let t ← inferType f
        if ← isProp t then continue
        let nm ← f.fvarId!.getUserName
        args := args.push (nm.toString, ← ocamlTy pm t)
      pure { name := c, short := shortName c, args := args.toList }
  pure { spec, isStruct, ctors }

def readBlocks : MetaM (List (List Family)) := blocks.mapM (·.mapM readFamily)


end OCaml5.Eff
