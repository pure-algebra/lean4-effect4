import Lean
import OCaml5.Ml.Syntax
import OCaml5.Lcnf.Naming

/-!
# OCaml5.Lcnf.Types

**What it is.** Lean inductives and structures, read off the environment, as `Ml.Syntax`
type declarations: a `structure` becomes a record, an `inductive` a variant, and a *trivial
structure* — one constructor, exactly one computationally relevant field, the shape the
compiler erases to its field (`Lean.Compiler.LCNF.Irrelevant`) — becomes a type abbreviation,
so that the OCaml types agree with the representation the mono-phase LCNF code assumes
(`FiberId` is `int`, `Cause ε δ ι α` is `(…) reason list`).

**Depends on.** `Lean.Meta` (`forallTelescope`, `inferType`, `isProp`, `isTypeFormerType`),
`Lean.Compiler.LCNF.hasTrivialStructure?`, `OCaml5.Ml.Syntax`, `OCaml5.Lcnf.Naming`.

**Properties.**
* **Representation agreement.** A field is emitted iff the compiler keeps it: relevance is
  `¬ isProp ∧ ¬ isTypeFormerType`, the test `Irrelevant.getRelevantCtorFields?` uses; a
  type is an abbreviation iff `hasTrivialStructure?` says so (the persisted answer of the
  defining module, recomputed by the same criterion when it is absent) — *by construction*.
* **Closure.** `generate` emits a declaration for every type constant reachable from the
  requested ones through relevant fields: the requested ones (and every trivial structure)
  in full, the rest as *placeholders* — a variant with one nullary constructor
  `Placeholder_<type>` — so that a generated file always compiles on its own and a reader
  sees exactly which types this run did not port — *tested* (`gen_check`).
* **One group.** Every declaration goes into one `type … and …` group, so the order of
  discovery is never an OCaml scoping error — *by construction*.
* **Builtins.** `Nat`/`Int`/`UInt*` → `int` (a fidelity caveat: OCaml `int` is 63-bit, Lean
  `Nat` is unbounded), `Bool`, `String`, `Char`, `Float`, `Unit`, `List`, `Option`,
  `Prod` → `*`, `Except ε α` → `(α, ε) result`, `Array` → `list` (the LCNF route's
  Array-as-list shim; `Translate` maps the array operations accordingly).
* **Unknown shapes are visible.** A field type this module cannot spell (a dependent arrow,
  a non-type argument, a `Sort`) becomes the abstract type `lcnf_unknown`, declared once, and
  is listed in the result — never silently dropped — *by construction*.
-/

namespace OCaml5.Lcnf

open Lean Meta

/-! ## Builtin types, shared with `Translate` -/

/-- A Lean type constant with a native OCaml counterpart, applied to already-converted
arguments. -/
def builtinTy? (n : Name) (args : List Ml.Ty) : Option Ml.Ty :=
  match n, args with
  | ``Nat, [] | ``Int, [] => some Ml.Ty.int
  | ``UInt8, [] | ``UInt16, [] | ``UInt32, [] | ``UInt64, [] | ``USize, [] => some Ml.Ty.int
  | ``Bool, [] => some Ml.Ty.bool
  | ``String, [] => some Ml.Ty.string
  | ``Unit, [] | ``PUnit, [] => some Ml.Ty.unit
  | ``Char, [] => some Ml.Ty.char
  | ``Float, [] => some Ml.Ty.float
  | ``List, [a] => some (Ml.Ty.list a)
  | ``Array, [a] => some (Ml.Ty.list a)
  | ``Option, [a] => some (Ml.Ty.option a)
  | ``Prod, [a, b] => some (.tuple [a, b])
  | ``Except, [e, a] => some (.con "result" [a, e])
  | _, _ => none

/-- The type constants `builtinTy?` knows. -/
def builtinTypeNames : List Name :=
  [``Nat, ``Int, ``UInt8, ``UInt16, ``UInt32, ``UInt64, ``USize, ``Bool, ``String, ``Unit,
   ``PUnit, ``Char, ``Float, ``List, ``Array, ``Option, ``Prod, ``Except]

def isBuiltinType (n : Name) : Bool := builtinTypeNames.contains n

/-- The name of the abstract type standing for a type this module could not spell. -/
def unknownTypeName : String := "lcnf_unknown"

/-! ## Reading one inductive -/

/-- What the generator learned about one Lean type constant. -/
structure TypeInfo where
  leanName : Name
  /-- The OCaml type parameters, in Lean parameter order (every parameter, so that the
  arity agrees with the mono types `Translate` annotates with). -/
  params : List String
  /-- The declaration to emit in full. -/
  decl : Ml.TypeDecl
  /-- The declaration to emit when the type is not requested: the same name and
  parameters with a single nullary constructor. `none` for an abbreviation, which is
  always emitted in full because its representation *is* another type. -/
  placeholder : Option Ml.TypeDecl
  /-- Every type constant the full declaration refers to. -/
  refs : Array Name
  /-- Field types the generator could not spell, as `<field> : <type>` for the report. -/
  unknown : Array String
  /-- Whether the type is an abbreviation (a trivial structure). -/
  isAlias : Bool
deriving Inhabited

/-- Whether the compiler erases a field of this type: a proof or a type. This is the
`trivialType` predicate `MonoTypes.setHasTrivialStructure?` passes to
`Irrelevant.computeHasTrivialStructure?`. -/
def isIrrelevantFieldType (ty : Lean.Expr) : MetaM Bool :=
  isProp ty <||> isTypeFormerType ty

/-- The compiler's trivial-structure verdict for `n`: the persisted one of the defining
module when present, otherwise recomputed by the same criterion (one constructor, not
recursive, not a runtime builtin, exactly one relevant field). -/
def trivialFieldIdx? (n : Name) : MetaM (Option Nat) := do
  try
    if let some info ← Compiler.LCNF.hasTrivialStructure? n then
      return some info.fieldIdx
    else
      return none
  catch _ =>
    let some (.inductInfo info) := (← getEnv).find? n | return none
    if info.isUnsafe || info.isRec then return none
    let [ctorName] := info.ctors | return none
    let ci ← getConstInfoCtor ctorName
    forallTelescopeReducing ci.type fun xs _ => do
      let mut result := none
      for i in [:xs.size - info.numParams] do
        let x := xs[info.numParams + i]!
        unless ← isIrrelevantFieldType (← inferType x) do
          if result.isSome then return none
          result := some i
      return result

/-- A field type, with the inductive's parameters as free variables, as an OCaml type. Returns
the type constants it mentions and `none` when the shape could not be spelled. -/
partial def kernelTy (params : Std.HashMap FVarId String) (e : Lean.Expr) :
    MetaM (Option Ml.Ty × Array Name) := do
  let e ← whnf e  -- unfold a `def`/`abbrev` head; an inductive head stays
  match e with
  | .fvar id =>
    match params[id]? with
    | some v => return (some (.var v), #[])
    | none => return (none, #[])
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return (none, #[])
    let (d', rd) ← kernelTy params d
    let (b', rb) ← kernelTy params b
    match d', b' with
    | some d', some b' => return (some (.arrow d' b'), rd ++ rb)
    | _, _ => return (none, rd ++ rb)
  | .sort _ => return (none, #[])
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    | .const n _ =>
      let mut tys : Array Ml.Ty := #[]
      let mut refs : Array Name := #[]
      let mut ok := true
      for a in args do
        let (t, r) ← kernelTy params a
        refs := refs ++ r
        match t with
        | some t => tys := tys.push t
        | none => ok := false
      unless ok do return (none, refs)
      if let some t := builtinTy? n tys.toList then return (some t, refs)
      return (some (.con (OCaml5.Lcnf.typeName n) tys.toList), refs.push n)
    | _ => return (none, #[])

/-- Read one inductive. `none` when `n` is not an inductive type. -/
def typeInfo? (n : Name) : MetaM (Option TypeInfo) := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? n | return none
  -- the parameter names, from the type's own telescope; made unique
  let pnames ← forallTelescope info.type fun xs _ => do
    let mut seen : Std.HashSet String := {}
    let mut out : Array String := #[]
    for x in xs[:info.numParams] do
      let base := tyVar (← x.fvarId!.getUserName)
      let mut v := base
      let mut i := 1
      while seen.contains v do
        v := s!"{base}{i}"
        i := i + 1
      seen := seen.insert v
      out := out.push v
    return out
  let trivialIdx? ← trivialFieldIdx? n
  let mut ctors : Array Ml.Ctor := #[]
  let mut fields : Array Ml.Field := #[]
  let mut aliasTy : Option Ml.Ty := none
  let mut refs : Array Name := #[]
  let mut unknown : Array String := #[]
  for ctorName in info.ctors do
    let ci ← getConstInfoCtor ctorName
    let (ctor, fs, alias, r, u) ← forallTelescope ci.type fun xs _ => do
      let mut pmap : Std.HashMap FVarId String := {}
      for x in xs[:info.numParams], v in pnames do
        pmap := pmap.insert x.fvarId! v
      let mut args : Array Ml.Ty := #[]
      let mut fs : Array Ml.Field := #[]
      let mut alias : Option Ml.Ty := none
      let mut r : Array Name := #[]
      let mut u : Array String := #[]
      let mut idx := 0
      for x in xs[info.numParams:] do
        let fname ← x.fvarId!.getUserName
        let fty ← inferType x
        let relevant := !(← isIrrelevantFieldType fty)
        if relevant then
          let (t?, rr) ← kernelTy pmap fty
          r := r ++ rr
          let t ← match t? with
            | some t => pure t
            | none =>
              u := u.push s!"{n}.{fname} : {← ppExpr fty}"
              pure (Ml.Ty.named unknownTypeName)
          args := args.push t
          fs := fs.push { name := fieldName fname.toString, ty := t }
          if trivialIdx? == some idx then alias := some t
        idx := idx + 1
      let short := shortName ctorName
      let ctor : Ml.Ctor := { name := OCaml5.Lcnf.ctorName n short, args := args.toList }
      return (ctor, fs, alias, r, u)
    ctors := ctors.push ctor
    fields := fs
    if alias.isSome then aliasTy := alias
    refs := refs ++ r
    unknown := unknown ++ u
  let params := pnames.toList
  let tname := OCaml5.Lcnf.typeName n
  let body : Ml.TyBody :=
    match aliasTy with
    | some t => .alias t
    | none =>
      if isStructure env n && info.ctors.length == 1 then .record fields.toList
      else .variant ctors.toList
  let decl : Ml.TypeDecl := { name := tname, params := params, body := body }
  let placeholder : Option Ml.TypeDecl :=
    if aliasTy.isSome then none
    else some { name := tname, params := params, body := .variant [{ name := placeholderCtor n }] }
  return some { leanName := n, params := params, decl := decl, placeholder := placeholder,
                refs := refs, unknown := unknown, isAlias := aliasTy.isSome }

/-! ## The closure -/

/-- What `generate` produced. -/
structure Generated where
  /-- The one `type … and …` group, in discovery order. -/
  decls : Array Ml.TypeDecl := #[]
  /-- Types emitted in full. -/
  full : Array Name := #[]
  /-- Types emitted as abbreviations. -/
  aliases : Array Name := #[]
  /-- Types emitted as placeholders. -/
  placeholders : Array Name := #[]
  /-- Names that were requested but are not inductive types. -/
  notInductive : Array Name := #[]
  /-- Field types that could not be spelled. -/
  unknown : Array String := #[]
  /-- OCaml type names claimed twice by different Lean constants; the second is renamed. -/
  collisions : Array (String × Name × Name) := #[]

/-- Emit the closure. `full` are the types to emit in full (every type `Translate` destructs
or constructs, plus whatever the caller asks for); `mentioned` are types that need at least
a placeholder (those in the annotations of translated code). -/
partial def generate (full : Array Name) (mentioned : Array Name) : MetaM Generated := do
  let fullSet : NameSet := full.foldl (·.insert ·) {}
  let mut g : Generated := {}
  let mut done : NameSet := {}
  let mut taken : Std.HashMap String Name := {}
  let mut queue : Array (Name × Bool) := full.map (·, true) ++ mentioned.map (·, false)
  let mut i := 0
  while i < queue.size do
    let (n, wantFull) := queue[i]!
    i := i + 1
    if done.contains n || isBuiltinType n then continue
    done := done.insert n
    let info? ← typeInfo? n
    if info?.isNone then
      g := { g with notInductive := g.notInductive.push n }
      continue
    let info := info?.get!
    -- resolve a name collision by falling back to the full path
    let mut decl := info.decl
    let mut ph := info.placeholder
    if let some other := taken[info.decl.name]? then
      if other != n then
        let renamed := snake ("_".intercalate (components n))
        g := { g with collisions := g.collisions.push (info.decl.name, other, n) }
        decl := { decl with name := renamed }
        ph := ph.map fun p => { p with name := renamed }
    taken := taken.insert decl.name n
    let emitFull := wantFull || fullSet.contains n || info.isAlias
    if emitFull then
      g := { g with decls := g.decls.push decl, unknown := g.unknown ++ info.unknown }
      if info.isAlias then g := { g with aliases := g.aliases.push n }
      else g := { g with full := g.full.push n }
      -- a full declaration's references need at least a placeholder; the queue decides
      for r in info.refs do
        queue := queue.push (r, fullSet.contains r)
    else
      match ph with
      | some p => g := { g with decls := g.decls.push p, placeholders := g.placeholders.push n }
      | none => pure ()
  if g.unknown.size > 0 then
    g := { g with decls := g.decls.push { name := unknownTypeName, body := .abstract } }
  return g

/-- The generated group as one structure item. -/
def Generated.item (g : Generated) : Ml.Decl :=
  .types g.decls.toList

end OCaml5.Lcnf
