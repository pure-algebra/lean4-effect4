import Conform.Source.Description
import Conform.Layout.Types

/-!
# Conform.Layout.Reflect — the environment's constructor information, as plain data

**What it is.** The one place a layout check meets `Lean.Environment`. It reads the names it is
*given* — never a name it chooses — and answers a `Conform.Layout.World`: for each requested
type, its parameters, whether it is a structure, and, per constructor in declaration order, the
computationally relevant fields with their types as `TypeRef`s. Everything downstream is plain
data, which is what keeps `Conform.Layout.Layout` free of any dependency on this repository.

**Depends on.** `Lean.Meta` (`getConstInfoInduct`, `InductiveVal.ctors`, `getConstInfoCtor`,
`ConstructorVal.cidx`/`numParams`/`numFields`, `forallBoundedTelescope`, `inferType`, `isProp`,
`isTypeFormerType`, `isStructure`), `Conform.Layout.Types`. Nothing here recomputes what one of
those answers.

**Properties.**
* **Relevance is a stated policy, not a guess.** `Relevance.propsOnly` drops `Prop` fields (what
  `OCaml5.Eff.World.readFamily` does); `Relevance.propsAndTypes` also drops type formers (what
  the compiler erases, `Lean.Compiler.LCNF.Irrelevant`) — *by construction*.
* **A field type this module cannot spell is named, never dropped.** It becomes
  `TypeRef.con `_unspellable []` and the name is collected in `Reading.unspellable` — *by
  construction*.
* **Declaration order is preserved.** `CtorView.index` is `ConstructorVal.cidx`, the compiler's
  own position of the constructor in `InductiveVal.ctors`, which is the canonical wire's tag —
  *by construction*, and no longer by a hand `zip` against `List.range`.
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
private partial def toRef (erasedInstances : List Name) (pm : List (FVarId × Nat)) (e : Expr) : MetaM TypeRef := do
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
    let info ← getConstInfo n
    let ok ← forallBoundedTelescope info.type args.size fun binders _ => do
      if binders.size != args.size then return false
      for i in [:args.size] do
        let a := args[i]!
        let ta ← inferType a
        if ← isTypeFormerType ta then
          pure ()
        else
          -- A dictionary is not a type argument. Its erasure is declared by the source
          -- description consumer; arbitrary value-indexed applications are unsupported.
          let bi := (← binders[i]!.fvarId!.getDecl).binderInfo
          unless bi == .instImplicit && erasedInstances.contains n do return false
      return true
    unless ok do return .con unspellableName []
    for a in args do
      if ← isTypeFormerType (← inferType a) then
        let ref ← toRef erasedInstances pm a
        if ref == .con unspellableName [] then return .con unspellableName []
        refs := refs.push ref
    return .con n refs.toList

/-- Read one type. `instantiation` gives the `TypeRef` each parameter is taken at (the way
`OCaml5.Eff.World.Spec.params` does); an empty list keeps the parameters abstract, so
`Option`'s own view has `TypeRef.param 0` in `some`'s field. -/
def readType (rel : Relevance) (n : Name) (instantiation : List TypeRef) (erasedInstances : List Name := []) :
    MetaM (TypeView × Array String) := do
  let env ← getEnv
  let info ← getConstInfoInduct n
  let isStruct := isStructure env n
  let mut unspellable : Array String := #[]
  let mut ctors : Array CtorView := #[]
  for c in info.ctors do
    let ci ← getConstInfoCtor c
    -- `ConstructorVal` carries the split the reader needs: `numParams` binders of the
    -- declaration, then `numFields` binders of the constructor, and `cidx` is the position in
    -- `InductiveVal.ctors`, which is the canonical wire's tag.
    let (fields, us) ← Conform.Source.withConstructor c fun _ xs => do
      let pm : List (FVarId × Nat) :=
        (List.range ci.numParams).map fun i => (xs[i]!.fvarId!, i)
      let mut fs : Array FieldView := #[]
      let mut us : Array String := #[]
      for f in xs[ci.numParams:] do
        let t ← inferType f
        unless ← isRelevant rel t do continue
        let nm ← f.fvarId!.getUserName
        let ref ← toRef erasedInstances pm t
        if ref == .con unspellableName [] then
          us := us.push s!"{c}.{nm} : {← ppExpr t}"
        fs := fs.push { name := nm.toString, type := ref }
      pure (fs.toList, us)
    unspellable := unspellable ++ us
    ctors := ctors.push { name := c.getString!, index := ci.cidx, fields }
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
at. Generic declarations are read once; applied requests retain their full arguments. -/
def readWorld (rel : Relevance) (requests : Array (Name × List TypeRef))
    (erasedInstances : List Name := []) : MetaM Reading := do
  let mut types : Array TypeView := #[]
  let mut seen : NameSet := {}
  let mut unspellable : Array String := #[]
  for (n, _) in requests do
    if seen.contains n then continue
    seen := seen.insert n
    let (tv, us) ← readType rel n [] erasedInstances
    types := types.push tv
    unspellable := unspellable ++ us
  let applications := requests.filterMap fun (n, inst) =>
    if inst.isEmpty && ((types.find? (·.name == n)).map (·.params.isEmpty)) != some true then none
    else some (TypeRef.con n inst)
  return { world := { types, applications }, unspellable }

end Conform.Layout.Reflect
