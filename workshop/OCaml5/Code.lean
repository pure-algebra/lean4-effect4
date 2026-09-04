/-!
# OCaml 5 spike: js_of_ocaml's block IR

Status: scaffold, 2026-09-03. Module `OCaml5.Code`. Plan:
`docs/research/2026-09-03-ocaml5-deep-plan.md`. Owner: spike O2.

A transcription of `compiler/lib/code.ml:242-372` (js_of_ocaml 5.7.1): SSA blocks with
parameters, `Let`-bound expressions, and the eight terminators. Constants are a parameter `κ`
so the value profile (`OCaml5.Value`) is chosen once, by the machine. `Effects.RawFlow` in the
`effects` package was modelled on this IR (`test/contracts/flow-v2.contract.md:43`); the
additions here are closures, first-class application, `Pushtrap`/`Poptrap` and `Switch`.

Owed by O2: a machine that runs a `Program` with the three effect externs as primitives under
the `effect.js` fiber discipline, then the analysis and transform of `OCaml5.Cps`.
-/

namespace OCaml5.Code

universe u

/-- `Code.Var.t`: a fresh-name variable. -/
structure Var where
  index : Nat
deriving DecidableEq, Repr

/-- `Code.Addr.t`: a block address. -/
abbrev Addr := Nat

/-- `code.ml:242`, `type cont = Addr.t * Var.t list`. -/
structure Cont where
  target : Addr
  args : List Var
deriving DecidableEq, Repr

/-- `code.ml:244-254`. -/
inductive Prim
  | vectlength
  | arrayGet
  | extern (name : String)
  | not
  | isInt
  | eq
  | neq
  | lt
  | le
  | ult
deriving DecidableEq, Repr

namespace Prim

/-- The three effect primitives the analysis and transform recognise
(`partial_cps_analysis.ml:82`, `effects.ml:168`, `:532-552`). -/
def perform : Prim := .extern "%perform"
def reperform : Prim := .extern "%reperform"
def resume : Prim := .extern "%resume"

/-- The runtime functions the transform emits (`effects.ml:365`, `:407`, `:425`, `:522-524`,
`:540`). -/
def camlPerformEffect : Prim := .extern "caml_perform_effect"
def camlResumeStack : Prim := .extern "caml_resume_stack"
def camlPushTrap : Prim := .extern "caml_push_trap"
def camlPopTrap : Prim := .extern "caml_pop_trap"
def camlCallback : Prim := .extern "caml_callback"

end Prim

/-- `code.ml:328-330`. -/
inductive PrimArg (κ : Type u) : Type u
  | pv (x : Var)
  | pc (c : κ)
deriving DecidableEq, Repr

/-- `code.ml:336-347`. `apply.exact` is "the arity is known to match"; the transform turns every
inexact call into a CPS call (`effects.ml:474-478`). -/
inductive Expr (κ : Type u) : Type u
  | apply (fn : Var) (args : List Var) (exact : Bool)
  | block (tag : Nat) (fields : List Var)
  | field (x : Var) (index : Nat)
  | closure (params : List Var) (body : Cont)
  | constant (c : κ)
  | prim (p : Prim) (args : List (PrimArg κ))
deriving DecidableEq, Repr

/-- `code.ml:349-354`. -/
inductive Instr (κ : Type u) : Type u
  | letIn (x : Var) (e : Expr κ)
  | assign (x y : Var)
  | setField (x : Var) (index : Nat) (y : Var)
  | offsetRef (x : Var) (delta : Int)
  | arraySet (x i y : Var)
deriving DecidableEq, Repr

/-- `code.ml:358`. -/
inductive RaiseMode
  | normal
  | notrace
  | reraise
deriving DecidableEq, Repr

/-- `code.ml:356-364`, the terminators. -/
inductive Last
  | return (x : Var)
  | raise (x : Var) (mode : RaiseMode)
  | stop
  | branch (c : Cont)
  | cond (x : Var) (onTrue onFalse : Cont)
  | switch (x : Var) (cases : List Cont)
  | pushtrap (body : Cont) (exn : Var) (handler : Cont)
  | poptrap (c : Cont)
deriving DecidableEq, Repr

/-- `code.ml:366-370`. -/
structure Block (κ : Type u) : Type u where
  params : List Var
  body : List (Instr κ)
  branch : Last
deriving DecidableEq, Repr

/-- `code.ml:372-376`: the entry address, the block table, the next free address. -/
structure Program (κ : Type u) : Type u where
  start : Addr
  blocks : List (Addr × Block κ)
  freePc : Addr
deriving Repr

/-- `code.ml:590-603`, `fold_children`: the successor addresses of a block, in the order the
compiler visits them. -/
def Last.children : Last → List Addr
  | .return _ | .raise _ _ | .stop => []
  | .branch c | .poptrap c => [c.target]
  | .pushtrap body _ handler => [body.target, handler.target]
  | .cond _ t f => [t.target, f.target]
  | .switch _ cases => cases.map (·.target)

def Block.children {κ : Type u} (b : Block κ) : List Addr := b.branch.children

namespace Program

variable {κ : Type u}

def block? (p : Program κ) (pc : Addr) : Option (Block κ) :=
  (p.blocks.find? (·.1 = pc)).map (·.2)

end Program

end OCaml5.Code
