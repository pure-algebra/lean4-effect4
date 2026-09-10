import Lean
import Conform.Layout.Types

/-!
# Conform.Layout.Reflect — the environment's constructor information, as plain data

**What it is.** The one place a layout check meets `Lean.Environment`. It reads the names it is
*given* — never a name it chooses — and answers a `Conform.Layout.World`: for each requested
type, its parameters, whether it is a structure, and, per constructor in declaration order, the
computationally relevant fields with their types as `TypeRef`s. Everything downstream is plain
data, which is what keeps `Conform.Layout.Layout` free of any dependency on this repository.

**Depends on.** `Lean.Meta` (`getConstInfoInduct`, `forallTelescope`, `isProp`,
`isTypeFormerType`, `isStructure`), `Conform.Layout.Types`.

**Properties.**
* **Relevance is a stated policy, not a guess.** `Relevance.propsOnly` drops `Prop` fields (what
  `OCaml5.Eff.World.readFamily` does); `Relevance.propsAndTypes` also drops type formers (what
  the compiler erases, `Lean.Compiler.LCNF.Irrelevant`) — *by construction*.
* **A field type this module cannot spell is named, never dropped.** It becomes
  `TypeRef.con `_unspellable []` and the name is collected in `Reading.unspellable` — *by
  construction*.
* **Declaration order is preserved.** `CtorView.index` is the position in `InductiveVal.ctors`,
  which is the canonical wire's tag — *by construction*.
-/

namespace Conform.Layout.Reflect

open Lean Meta
open Conform.Layout

/-- Which fields the target keeps. -/
inductive Relevance where
  /-- Drop `Prop` fields only. -/
  | propsOnly
  /-- Drop `Prop` fields and type formers: what the Lean compiler erases. -/
  | propsAndTypes
deriving Inhabited, BEq

/-- What one run learned. -/
structure Reading where
  world : World := {}
  /-- `<Type>.<ctor>.<field> : <expr>` for every field type this module could not spell. -/
  unspellable : Array String := #[]
deriving Inhabited

/-- The name a field type this module cannot spell is given. -/
def unspellableName : Name := `_unspellable

private def isRelevant (rel : Relevance) (ty : Expr) : MetaM Bool := do
  if ← isProp ty then return false
  match rel with
  | .propsOnly => return true
  | .propsAndTypes => return !(← isTypeFormerType ty)

/-- A Lean type expression as a `TypeRef`, with the declaration's parameter fvars mapped to
their positions. An expression this cannot spell becomes `unspellableName`. -/
private partial def toRef (pm : List (FVarId × Nat)) (e : Expr) : MetaM TypeRef := do
  let e ← whnfR e
  match e with
  | .fvar id =>
    match pm.find? (·.1 == id) with
    | some (_, i) => return .param i
    | none => return .con unspellableName []
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    let .const n _ := fn | return .con unspellableName []
    let mut refs : Array TypeRef := #[]
    for a in args do
      let ta ← inferType a
      if ← isTypeFormerType ta then
        refs := refs.push (← toRef pm a)
    return .con n refs.toList

/-- Read one type. `instantiation` gives the `TypeRef` each parameter is taken at (the way
`OCaml5.Eff.World.Spec.params` does); an empty list keeps the parameters abstract, so
`Option`'s own view has `TypeRef.param 0` in `some`'s field. -/
def readType (rel : Relevance) (n : Name) (instantiation : List TypeRef) :
    MetaM (TypeView × Array String) := do
  let env ← getEnv
  let info ← getConstInfoInduct n
  let isStruct := isStructure env n
  let mut unspellable : Array String := #[]
  let mut ctors : Array CtorView := #[]
  for (c, idx) in info.ctors.zip (List.range info.ctors.length) do
    let ci ← getConstInfoCtor c
    let (fields, us) ← forallTelescope ci.type fun xs _ => do
      let pm : List (FVarId × Nat) :=
        (List.range info.numParams).map fun i => (xs[i]!.fvarId!, i)
      let mut fs : Array FieldView := #[]
      let mut us : Array String := #[]
      for f in xs[info.numParams:] do
        let t ← inferType f
        unless ← isRelevant rel t do continue
        let nm ← f.fvarId!.getUserName
        let ref ← toRef pm t
        if ref.render == unspellableName.toString then
          us := us.push s!"{c}.{nm} : {← ppExpr t}"
        fs := fs.push { name := nm.toString, type := ref }
      pure (fs.toList, us)
    unspellable := unspellable ++ us
    ctors := ctors.push { name := c.getString!, index := idx, fields }
  -- the parameters, instantiated where the caller asked for it
  let paramNames := (List.range info.numParams).map fun i => s!"p{i}"
  let finalCtors :=
    if instantiation.isEmpty then ctors
    else ctors.map fun cv =>
      { cv with fields := cv.fields.map fun f =>
          { f with type := f.type.instantiate instantiation } }
  return ({ name := n, params := if instantiation.isEmpty then paramNames else [],
            isStructure := isStruct, ctors := finalCtors.toList }, unspellable)

/-- Read a whole world: each request is a type name and the `TypeRef`s its parameters are taken
at. Requests are read in order and a repeated name is read once. -/
def readWorld (rel : Relevance) (requests : Array (Name × List TypeRef)) : MetaM Reading := do
  let mut types : Array TypeView := #[]
  let mut unspellable : Array String := #[]
  for (n, inst) in requests do
    if types.any (·.name == n) then continue
    let (tv, us) ← readType rel n inst
    types := types.push tv
    unspellable := unspellable ++ us
  return { world := { types }, unspellable }

end Conform.Layout.Reflect
