import Lean
import OCaml5.Lcnf.Index
import OCaml5.Ml.Syntax
import OCaml5.Ml.Fold
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.TypeRows

/-!
# OCaml5.Lcnf.Types

**What it is.** Lean inductives and structures, read off the environment, as `Ml.Syntax`
type declarations: a `structure` becomes a record, an `inductive` a variant, and a *trivial
structure* — one constructor, exactly one computationally relevant field, the shape the
compiler erases to its field (`Lean.Compiler.LCNF.Irrelevant`) — becomes a type abbreviation,
so that the OCaml types agree with the representation the mono-phase LCNF code assumes
(`FiberId` is `int`, `Cause ε δ ι α` is `(…) reason list`).

**Depends on.** `Lean.Meta` (`forallTelescope`, `inferType`, `isProp`, `isTypeFormerType`),
`Lean.Compiler.LCNF.hasTrivialStructure?`, `OCaml5.Ml.Syntax`, `OCaml5.Lcnf.Naming`,
`OCaml5.Lcnf.TypeRows` (the type rows: `builtinTy?`, `isBuiltinType`).

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
* **One group, or one module per type at its owner.** Every declaration goes into one
  `type … and …` group, so the order of discovery is never an OCaml scoping error — *by
  construction*. The program types' owner (`ocaml/eff/eff_types.ml`, `TypeNames.modules`)
  declares each type as its own module instead, in the order of the reference graph's
  components, a cycle as one `module rec` of type-only signatures (`Generated.items`) — *by
  construction*; *tested* by `dune build` of `ocaml/` and the client `ocaml/eff/test/test_owner.ml`,
  which traverses `Eff`–`Stmt`–`Stmts` with its type parameter kept. A cycle's parameters are
  invariant, since OCaml checks a recursive group against approximations of its members.
* **Builtins.** A type constant with a row of the type table is spelled by its row
  (`OCaml5.Lcnf.typeRows`): `Nat`, `Int`, `Char` and the `UInt*` are `int`, `Except ε α` is
  `(α, ε) result`, `Array α` is `α Lcnf_array.t` (the runtime library's persistent vector,
  `ocaml/lcnf/lcnf_array.mli`), and so on. No declaration is emitted for it — *by construction*.
* **Parameters by binder kind.** A type's OCaml parameters are its type parameters, in source
  order. A family over a finite index (`R : I → Type u`, with `I` an inductive whose
  constructors take no argument) is one OCaml parameter per constructor of `I`, and an instance
  reads each by reducing `R c`: exact, with no cast (F3). An instance parameter and a value
  parameter are dropped, as the compiler erases both from the type's representation
  (`typeParameterSlots`) — *by construction*; *tested* by the rule's controls
  (`Conform.Effect4.CompilerControls`).
* **Unknown shapes are visible.** A field type this module cannot spell (a dependent arrow,
  a non-type argument, a `Sort`, a family at a variable such as `R fam`) becomes the abstract
  type `lcnf_unknown`, declared once, and is listed in the result — never silently dropped —
  *by construction*.
-/

namespace OCaml5.Lcnf

open Lean Meta

/-- The name of the abstract type standing for a type this module could not spell. -/
def unknownTypeName : String := "lcnf_unknown"

/-! ## Reading one inductive -/

/-- What the generator learned about one Lean type constant. -/
structure TypeInfo where
  leanName : Name
  /-- Supported type/carrier parameters in source order; explicit dictionary policy matches
  applications and constructor declarations. Term dictionaries remain computational. -/
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
  /-- The `field` extern rows this declaration used, as `<Struct>.<field>`. -/
  usedFields : Array Name := #[]
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
    withConstructor ctorName fun _ xs => do
      let mut result := none
      for i in [:ci.numFields] do
        let x := xs[info.numParams + i]!
        unless ← isIrrelevantFieldType (← inferType x) do
          if result.isSome then return none
          result := some i
      return result

def unwrapParam (e : Lean.Expr) : Lean.Expr :=
  match e with
  | .app (.app (.const `optParam _) inner) _ => unwrapParam inner
  | .app (.app (.const `autoParam _) inner) _ => unwrapParam inner
  | .app (.const `outParam _) inner => unwrapParam inner
  | .app (.const `semiOutParam _) inner => unwrapParam inner
  | d => d

/-- Whether a parameter domain represents an OCaml type parameter. Handles sorts,
service universes, and parameter wrappers (`optParam`, `autoParam`, `outParam`, `semiOutParam`). -/
def isTypeParameter (domain : Lean.Expr) : Bool :=
  let ty := unwrapParam domain
  ty.isSort || ty.isConstOf `Effect4.ServiceUniverse

/-- The constructors of a *finite index*, in declaration order: an inductive type with no
parameter and no index whose every constructor takes no argument (`EffFam`, `TermFam`,
`CauseTermFam`). `none` for any other constant. -/
def finiteIndexIn (env : Environment) (n : Name) : Option (List Name) := do
  let .inductInfo info ← env.find? n | none
  guard (info.numParams == 0 && info.numIndices == 0)
  guard (info.ctors.all fun c => match env.find? c with
    | some (.ctorInfo ci) => ci.numFields == 0
    | _ => false)
  return info.ctors

/-- One kept parameter of a type, with the OCaml type parameters it becomes. -/
inductive ParamSlot where
  /-- A type parameter (`isTypeParameter`): one OCaml type parameter. -/
  | type (pos : Nat)
  /-- A family over a finite index, `R : I → Type u` (F3): one OCaml type parameter per
  constructor of `I`, in declaration order. `levels` are the universe levels of the constant `I`
  as the type's telescope writes them. -/
  | family (pos : Nat) (levels : List Level) (ctors : List Name)
deriving Inhabited, BEq

/-- The parameter's position in the type's telescope. -/
def ParamSlot.pos : ParamSlot → Nat
  | .type p => p
  | .family p _ _ => p

/-- How many OCaml type parameters a slot spells. -/
def ParamSlot.width : ParamSlot → Nat
  | .type _ => 1
  | .family _ _ cs => cs.length

/-- The index of a family parameter's domain `I → Type u`, with the universe levels of `I` and its
constructors, when `index` reads `I` as a finite index (`finiteIndexIn`). -/
def familyIndex? (index : Name → Option (List Name)) (domain : Lean.Expr) :
    Option (List Level × List Name) :=
  match unwrapParam domain with
  | .forallE _ (.const i us) (.sort (.succ _)) _ => (index i).map (us, ·)
  | _ => none

/-- The OCaml parameter slots of a type among its first `count` parameters, by binder kind. A type
parameter (`isTypeParameter`) is a slot of one OCaml parameter. A family over a finite index
(`familyIndex?`) is a slot of one OCaml parameter per constructor of the index, which an instance
reads by reducing its family at that constructor (F3): exact, and no cast. An instance parameter
and a value parameter are dropped: the compiler erases both from the type's representation, so a
value of the type carries neither. `index` reads the finite indexes (`finiteIndexIn`). The one
refusal is a telescope shorter than `count`. -/
def typeParameterSlots (index : Name → Option (List Name)) (owner : Name) (count : Nat)
    (type : Lean.Expr) : Except String (Array ParamSlot) :=
  go count 0 type #[]
where
  go : Nat → Nat → Lean.Expr → Array ParamSlot → Except String (Array ParamSlot)
    | 0, _, _, out => .ok out
    | k + 1, i, .forallE _ domain body _, out =>
      let slot? : Option ParamSlot :=
        if isTypeParameter domain then some (.type i)
        else (familyIndex? index domain).map fun (us, cs) => .family i us cs
      go k (i + 1) body (match slot? with | some s => out.push s | none => out)
    | _, _, _, _ => .error s!"{owner}: incomplete parameter telescope"

/-- The number of OCaml type parameters of a type's first `count` parameters: what an annotation
that says nothing about them spells as anonymous types. A refused telescope has none. -/
def typeParameterWidth (env : Environment) (owner : Name) (count : Nat) (type : Lean.Expr) : Nat :=
  ((typeParameterSlots (finiteIndexIn env) owner count type).toOption.getD #[]).foldl
    (fun n slot => n + slot.width) 0

/-- The OCaml type variables of a type's parameters, by each parameter's free variable: one for a
type parameter, and one for each constructor of a family's index (F3). -/
structure ParamVars where
  vars : Std.HashMap FVarId String := {}
  families : Std.HashMap FVarId (List (Name × String)) := {}

/-- A field type, with the inductive's parameters as free variables, as an OCaml type. Returns
the type constants it mentions and `none` when the shape could not be spelled. -/
partial def kernelTy (ex : Externs) (tn : TypeNames) (params : ParamVars)
    (e : Lean.Expr) : MetaM (Option Ml.Ty × Array Name) := do
  -- unfold a `def`/`abbrev` head; an inductive head stays. Each reduction has its own heartbeat
  -- budget: the counter counts every allocation of the run, so a shared budget bounded the
  -- closure's size, not the reduction (seams S6, `Tool.serve`'s closure).
  let e ← withCurrHeartbeats (whnf e)
  match e with
  | .fvar id =>
    match params.vars[id]? with
    | some v => return (some (.var v), #[])
    | none => return (none, #[])
  | .forallE _ d b _ =>
    if b.hasLooseBVars then return (none, #[])
    let (d', rd) ← kernelTy ex tn params d
    let (b', rb) ← kernelTy ex tn params b
    match d', b' with
    | some d', some b' => return (some (.arrow d' b'), rd ++ rb)
    | _, _ => return (none, rd ++ rb)
  | .sort _ => return (none, #[])
  -- `U.Carrier code` as a projection: the universe's parameter is the carrier type
  | .proj s 0 u =>
    if s == `Effect4.ServiceUniverse then kernelTy ex tn params u else return (none, #[])
  | _ =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn with
    -- `R c`, a family parameter at a constructor of its index: that constructor's variable (F3)
    | .fvar id =>
      match params.families[id]?, args with
      | some vars, #[.const c _] => return ((vars.lookup c).map Ml.Ty.var, #[])
      | _, _ => return (none, #[])
    | .const n us =>
      -- A service universe is read as its carrier type: `Carrier U k` (and the projection it
      -- unfolds to) is the universe's own parameter (`'u service = { value : 'u }`), and a
      -- closed universe `⟨fun _ => T⟩` (`Env.ValU`) is `T`, so `Context ValU` is `val_ context`.
      if n == `Effect4.ServiceKey.Carrier || n == `Effect4.ServiceUniverse.Carrier then
        match args[0]? with
        | some u => kernelTy ex tn params u
        | none => return (none, #[])
      else if n == `Effect4.ServiceUniverse.mk then
        match args[0]? with
        | some f =>
          if f.isLambda && !f.bindingBody!.hasLooseBVars then kernelTy ex tn params f.bindingBody!
          else return (none, #[])
        | none => return (none, #[])
      else
        let mut tys : Array Ml.Ty := #[]
        let mut refs : Array Name := #[]
        let mut ok := true
        let info ← getConstInfo n
        let .ok slots := typeParameterSlots (finiteIndexIn (← getEnv)) n args.size info.type
          | return (none, #[])
        for slot in slots do
          -- a type parameter is its argument; a family is its argument at each constructor of
          -- the index, reduced by `kernelTy`'s `whnf` (F3)
          let parts : List Lean.Expr := match slot with
            | .type i => [args[i]!]
            | .family i levels ctors =>
              let levels := levels.map (·.instantiateParams info.levelParams us)
              ctors.map fun c => mkApp args[i]! (mkConst c levels)
          for a in parts do
            let (t, r) ← kernelTy ex tn params a
            refs := refs ++ r
            match t with
            | some t => tys := tys.push t
            | none => ok := false
        unless ok do return (none, refs)
        -- an extern type row: the carrier chain applied to the Lean arguments. `n` is still
        -- pushed as a reference so `generate` sees the row was hit.
        if let some chain := ex.tys[n]? then
          return (some (applyChain chain tys.toList), refs.push n)
        -- an extern element row: `List T` is the carrier, wherever it is spelled
        if let some chain := ex.elemChain? n args.toList then
          return (some (applyChain chain tys.toList), refs)
        if let some t := builtinTy? n tys.toList then return (some t, refs)
        return (some (.con (OCaml5.Lcnf.typeNameIn tn n) tys.toList), refs.push n)
    -- `U.Carrier code` applied: `whnf` unfolds `ServiceKey.Carrier U k` to this shape
    | .proj s 0 u =>
      if s == `Effect4.ServiceUniverse then kernelTy ex tn params u else return (none, #[])
    | _ => return (none, #[])

/-- A `field` extern row applied to a field's spelled type. The field must be a `list` (that is
what a Lean `List _` carrier is); a `List (κ × v)` carrier keeps only `v`, which is how
`MemoMap.entries : List (LayerId × MemoEntry)` becomes `memo_entry L.t`. -/
def externField (chain : List String) (owner : Name) (field : String) (t : Ml.Ty) :
    Except String Ml.Ty :=
  match t with
  | .con "list" [elem] =>
    let elem := match elem with | .tuple [_, v] => v | e => e
    .ok (applyChain chain [elem])
  | _ => .error s!"{owner}.{field}: a `field` extern row needs a `list` field type"

/-- Read one inductive. `none` when `n` is not an inductive type. -/
def typeInfo? (ex : Externs) (tn : TypeNames) (n : Name) : MetaM (Option TypeInfo) :=
  -- one heartbeat budget per type spelled (seams S6; see `kernelTy`)
  withCurrHeartbeats do
  let env ← getEnv
  let some (.inductInfo info) := env.find? n | return none
  let slots ← match typeParameterSlots (finiteIndexIn env) n info.numParams info.type with
    | .ok slots => pure slots
    | .error message => throwError message
  -- each slot's parameter names, from the type's own telescope; made unique. A family's names are
  -- its own name and each constructor of its index (`'r_eff` for `R .eff`).
  let slotNames ← forallBoundedTelescope info.type info.numParams fun xs _ => do
    let mut seen : Std.HashSet String := {}
    let mut out : Array (List String) := #[]
    for slot in slots do
      let base := tyVar (← xs[slot.pos]!.fvarId!.getUserName)
      let bases := match slot with
        | .type _ => [base]
        | .family _ _ ctors => ctors.map fun c => base ++ "_" ++ snake (shortName c)
      let mut names : List String := []
      for b in bases do
        let mut v := b
        let mut i := 1
        while seen.contains v do
          v := s!"{b}{i}"
          i := i + 1
        seen := seen.insert v
        names := names ++ [v]
      out := out.push names
    return out
  let trivialIdx? ← trivialFieldIdx? n
  let mut ctors : Array Ml.Ctor := #[]
  let mut fields : Array Ml.Field := #[]
  let mut aliasTy : Option Ml.Ty := none
  let mut refs : Array Name := #[]
  let mut unknown : Array String := #[]
  let mut usedFields : Array Name := #[]
  for ctorName in info.ctors do
    let (ctor, fs, alias, r, u, uf) ← withConstructor ctorName fun _ xs => do
      let mut pmap : ParamVars := {}
      for slot in slots, names in slotNames do
        let id := xs[slot.pos]!.fvarId!
        match slot with
        | .type _ => pmap := { pmap with vars := pmap.vars.insert id (names.headD "_") }
        | .family _ _ ctors => pmap := { pmap with families := pmap.families.insert id (ctors.zip names) }
      let mut args : Array Ml.Ty := #[]
      let mut fs : Array Ml.Field := #[]
      let mut alias : Option Ml.Ty := none
      let mut r : Array Name := #[]
      let mut u : Array String := #[]
      let mut uf : Array Name := #[]
      let mut idx := 0
      for x in xs[info.numParams:] do
        let fname ← x.fvarId!.getUserName
        let fty ← inferType x
        let relevant := !(← isIrrelevantFieldType fty)
        if relevant then
          let (t?, rr) ← kernelTy ex tn pmap fty
          r := r ++ rr
          let t ← match t? with
            | some t => pure t
            | none =>
              u := u.push s!"{n}.{fname} : {← ppExpr fty}"
              pure (Ml.Ty.named unknownTypeName)
          -- a `field` extern row: the carrier replaces the list, here and in the alias body
          let key := n ++ fname
          let t ← match ex.fields[key]? with
            | none => pure t
            | some chain =>
              match externField chain n fname.toString t with
              | .ok t' => do uf := uf.push key; pure t'
              | .error msg => throwError msg
          args := args.push t
          fs := fs.push { name := fieldName fname.toString, ty := t }
          if trivialIdx? == some idx then alias := some t
        idx := idx + 1
      let short := shortName ctorName
      let ctor : Ml.Ctor := { name := OCaml5.Lcnf.declCtorNameIn tn n short, args := args.toList }
      return (ctor, fs, alias, r, u, uf)
    ctors := ctors.push ctor
    fields := fs
    if alias.isSome then aliasTy := alias
    refs := refs ++ r
    unknown := unknown ++ u
    usedFields := usedFields ++ uf
  let params := slotNames.toList.flatten
  let tname := OCaml5.Lcnf.declTypeNameIn tn n
  -- A structure whose every field is erased (`ServiceUniverse`: one `Type`-valued field) has
  -- no relevant data: OCaml refuses an empty record, so it is the abbreviation `unit`, and
  -- its constructions are `()` (`Translate.ctorExpr`).
  if aliasTy.isNone && isStructure env n && info.ctors.length == 1 && fields.isEmpty then
    aliasTy := some Ml.Ty.unit
  let body : Ml.TyBody :=
    match aliasTy with
    | some t => .alias t
    | none =>
      if isStructure env n && info.ctors.length == 1 then .record fields.toList
      else .variant ctors.toList
  let decl : Ml.TypeDecl := { name := tname, params := params, body := body }
  let placeholder : Option Ml.TypeDecl :=
    if aliasTy.isSome then none
    else some { name := tname, params := params,
                body := .variant [{ name := placeholderCtorIn tn n }] }
  return some { leanName := n, params := params, decl := decl, placeholder := placeholder,
                refs := refs, unknown := unknown, isAlias := aliasTy.isSome,
                usedFields := usedFields }

/-! ## The closure -/

/-- What `generate` produced. -/
structure Generated where
  /-- The one `type … and …` group, in discovery order. -/
  decls : Array Ml.TypeDecl := #[]
  /-- Each declaration of `decls`, in the same order, with its Lean constant and the type
  constants it refers to: what `items` orders the modules of a type at its owner by. -/
  entries : Array (Name × Ml.TypeDecl × Array Name) := #[]
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
  /-- `type` extern rows that a declaration referred to. -/
  usedTys : Array Name := #[]
  /-- `field` extern rows that a declaration used. -/
  usedFields : Array Name := #[]
  /-- `elem` extern rows whose element type this run reached. A weaker ledger than the other
  three: it says the row's type is live, not that every `List` of it was rewritten (that is
  what `ocamlopt` says). -/
  usedElems : Array Name := #[]

/-- Emit the closure. `full` are the types to emit in full (every type `Translate` destructs
or constructs, plus whatever the caller asks for); `mentioned` are types that need at least
a placeholder (those in the annotations of translated code). A `provided` type is declared by an
opened module (`Gen.Args.opens`): it claims its OCaml name and is emitted nowhere, so a type of
this run that shares the name is reported as a collision and renamed. -/
partial def generate (full : Array Name) (mentioned : Array Name) (tn : TypeNames := {})
    (ex : Externs := {}) (provided : NameSet := {}) : MetaM Generated := do
  let fullSet : NameSet := full.foldl (·.insert ·) {}
  let mut g : Generated := {}
  let mut done : NameSet := provided
  let mut taken : Std.HashMap String Name :=
    provided.foldl (fun m n => m.insert (typeNameIn tn n) n) {}
  let mut queue : Array (Name × Bool) := full.map (·, true) ++ mentioned.map (·, false)
  let mut i := 0
  while i < queue.size do
    let (n, wantFull) := queue[i]!
    i := i + 1
    if done.contains n || isBuiltinType n then continue
    -- `Extract Constant` on a type: the carrier is spelled by the row, nothing is emitted
    if ex.tys.contains n then
      unless g.usedTys.contains n do g := { g with usedTys := g.usedTys.push n }
      continue
    done := done.insert n
    let info? ← typeInfo? ex tn n
    if info?.isNone then
      g := { g with notInductive := g.notInductive.push n }
      continue
    let info := info?.get!
    -- A name claimed twice is *reported*, not patched here: renaming a declaration after its
    -- annotations and constructors have been rendered makes the two disagree (the U0 probe's
    -- `val_` failure). The driver re-runs with the collision in `TypeNames`, so `typeInfo?`,
    -- `kernelTy` and `Translate` all spell the renamed type the same way. The claim is the name
    -- a use spells: a type at its owner declares `t`, and claims its module's `M.t`.
    let decl := info.decl
    let ph := info.placeholder
    let claim := typeNameIn tn n
    if let some other := taken[claim]? then
      if other != n then
        g := { g with collisions := g.collisions.push (claim, other, n) }
    taken := taken.insert claim n
    if ex.elems.contains n then
      unless g.usedElems.contains n do g := { g with usedElems := g.usedElems.push n }
    for f in info.usedFields do
      unless g.usedFields.contains f do g := { g with usedFields := g.usedFields.push f }
    let emitFull := wantFull || fullSet.contains n || info.isAlias
    if emitFull then
      g := { g with decls := g.decls.push decl, entries := g.entries.push (n, decl, info.refs),
                    unknown := g.unknown ++ info.unknown }
      if info.isAlias then g := { g with aliases := g.aliases.push n }
      else g := { g with full := g.full.push n }
      -- a full declaration's references need at least a placeholder; the queue decides
      for r in info.refs do
        queue := queue.push (r, fullSet.contains r)
    else
      match ph with
      | some p => g := { g with decls := g.decls.push p, entries := g.entries.push (n, p, #[]),
                                placeholders := g.placeholders.push n }
      | none => pure ()
  if g.unknown.size > 0 then
    g := { g with decls := g.decls.push { name := unknownTypeName, body := .abstract } }
  return g

/-- The generated group as one structure item. -/
def Generated.item (g : Generated) : Ml.Decl :=
  .types g.decls.toList

/-- A declaration's type expressions with its own module's `M.t` written `t`: inside its module a
type names itself so, since `M` is not yet defined there. -/
def selfNamed (m : String) (d : Ml.TypeDecl) : Ml.TypeDecl :=
  let own := m ++ ".t"
  let ty : Ml.Ty → Ml.Ty := Ml.cata_ty
    { Ml.TyAlgebra.id with ty_con := fun c args => .con (if c == own then "t" else c) args }
  let body : Ml.TyBody := match d.body with
    | .record fs => .record (fs.map fun f => { f with ty := ty f.ty })
    | .variant cs => .variant (cs.map fun c => { c with args := c.args.map ty })
    | .alias t => .alias (ty t)
    | .abstract => .abstract
  { d with body := body }

/-- The types at their owner as structure items, one module per type: the components of the
reference graph, dependencies first, a component of one type as `module M = struct … end` and a
cycle as one `module rec` of type-only signatures (`Eff`–`Stmt`–`Stmts`). A declaration that
is no type at its owner stays in the flat group, first. A plain module keeps OCaml's variance
for its parameters; a cycle's parameters are invariant, since OCaml checks a recursive group
against approximations of its members. -/
def Generated.items (g : Generated) (tn : TypeNames) : List Ml.Decl :=
  let flat := g.entries.filter fun (n, _, _) => !tn.modules.contains n
  let owned := g.entries.filter fun (n, _, _) => tn.modules.contains n
  let index : Std.HashMap Name Nat := owned.foldl (init := {}) fun m (n, _, _) => m.insert n m.size
  let edges (i : Nat) : List Nat :=
    (owned[i]!.2.2.toList.filterMap (index[·]?)).eraseDups
  let groups := Lean.SCC.scc (List.range owned.size) edges
  let modOf (n : Name) : String := tn.modules.getD n (moduleName n)
  let items := groups.map fun comp =>
    let comp := comp.mergeSort (· ≤ ·)
    match comp with
    | [i] =>
      let (n, d, _) := owned[i]!
      .moduleD (modOf n) [] [.types [selfNamed (modOf n) d]]
    | _ => .moduleRecD (comp.map fun i =>
        let (n, d, _) := owned[i]!
        (modOf n, [Ml.SigItem.type (selfNamed (modOf n) d)]))
  (if flat.isEmpty then [] else [Ml.Decl.types (flat.map (·.2.1)).toList]) ++ items

/-- A set of types declared in full at their owner, as the owner's own run declares them: each
type of the closure its own module (`TypeNames.modules`), no extern table, and the renaming loop
of the generator, here over module names, whose decided names come back with the declarations.
A placeholder, a collision or an unspelled field is fatal: a module that opens these types
would otherwise miss one. The owner's run (`OCaml5.Lcnf.Gen.run`, `--modules`) declares its
types so, `Gen.run` reads an opened artifact's types so, and the `eff/` emitter reads the
interface of `Eff_types` so. -/
def generateInFull (types : Array Name) : MetaM (Generated × TypeNames) := do
  -- the closure first, under flat names; then every type of it at its owner
  let first ← generate types #[] {} {}
  let mut tn : TypeNames :=
    { modules := (first.full ++ first.aliases).foldl (fun m n => m.insert n (moduleName n)) {} }
  let mut g ← generate types #[] tn {}
  for _ in [:4] do
    if g.collisions.isEmpty then break
    for (_, _, n) in g.collisions do tn := { tn with modules := tn.modules.insert n (fullModuleName n) }
    g ← generate types #[] tn {}
  unless g.placeholders.isEmpty && g.collisions.isEmpty && g.unknown.isEmpty do
    throwError s!"the types are not all declared in full (fatal): placeholders {g.placeholders}, \
      collisions {g.collisions}, unknown {g.unknown}"
  return (g, tn)

end OCaml5.Lcnf
