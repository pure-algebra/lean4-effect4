module

public meta import Lean
public meta import Effect4.Data.FieldOrder
public import Effect4.Schema.Modeled

/-!
# Schema.Modeled.Derive — the instance of a structure, written from its fields

`deriving Modeled` on a structure, or `derive_modeled S (field := "spelling")*` after it, writes
the structure's `Modeled` instance. The command also renames fields: a field's spelling is its
name unless a rename gives another. Both run one function (`deriveModeled`), which checks the
declaration before it writes anything:

- the structure has no parameters and no universe parameters: the first profile is monomorphic;
- each rename names a field that exists, and each field is renamed at most once;
- no two fields share a spelling;
- no field's type depends on another field, and each field's type has a `Modeled` instance.

Each refusal is located at the syntax it is about, and so is a generated name that already
exists. Then it writes, under the structure's name: the record type in canonical field order
(`modeledTy`), its proof of the checked domain (`modeled_checked`: the names' order by `decide`,
and each field instance's own `checked`, so a field instance may be opaque), the two maps to and from the carrier (`modeledToC`, `modeledOfC`),
their two inverse equations (`modeled_to_of`, `modeled_of_to`), the staged image
(`modeledStaged`: the fold's image at the type written as its combinators, each field's column
its instance's staged image) with its proof that it is the fold's (`modeled_staged_eq`), and the
instance. If a
generated declaration fails, the environment is restored: the command keeps all or none.
-/

public meta section

namespace Effect4.Schema.Modeled.Derive

open Lean Elab Command Term Meta

/-- A field's spelling by default: its name, unescaped. -/
def defaultSpelling : Name → String
  | .str .anonymous s => s
  | n => n.toString (escape := false)

/-- Spellings in canonical order: ascending by their bytes (`Field.canonBy`). -/
def canonicalOrder (names : List String) : List String :=
  (Effect4.Field.canonBy Effect4.Field.bytesKey (names.map fun n => (n, ()))).map Prod.fst

/-- A constructor's tag: its name's last component. -/
def ctorTag : Name → String
  | .str _ s => s
  | n => n.toString (escape := false)

/-- One constructor of an inductive: its name, its tag and its fields, each a name and a type. -/
structure Ctor where
  name : Name
  tag : String
  fields : List (Name × Term)

/-- Each field of a constructor is named, independent of the others, no proposition, and has an
instance. -/
def ctorFields (ref : Syntax) (c : Name) : CommandElabM (List (Name × Term)) := do
  let info ← liftCoreM (getConstInfoCtor c)
  withRef ref <| liftTermElabM <| forallTelescope info.type fun xs _ => do
    xs.toList.mapM fun x => do
      let decl ← x.fvarId!.getDecl
      let n := decl.userName
      if n.hasMacroScopes || n.isAnonymous then
        throwError "derive_modeled: a field of {c} has no name; name each field"
      let t ← inferType x
      if t.hasAnyFVar (fun v => xs.any (·.fvarId! == v)) then
        throwError "derive_modeled: field type {t} depends on another field"
      if ← isProp t then
        throwError "derive_modeled: field type {t} is a proposition"
      let inst ← mkAppM ``Effect4.Schema.Modeled #[t]
      unless (← trySynthInstance inst) matches .some _ do
        throwError "derive_modeled: field type {t} has no Modeled instance"
      pure (n, ← PrettyPrinter.delab t)

/-- The right-nested union of members, as `Ty.ofMembers` nests it. -/
def unionOf : List Term → MacroM Term
  | [] => `(Effect4.Program.Ty.never)
  | [m] => pure m
  | m :: rest => do `(Effect4.Program.Ty.union $m $(← unionOf rest))

/-- The checked proof of `unionOf`'s union, from each member's. -/
def checkedOf : List Term → MacroM Term
  | [] => `(rfl)
  | [p] => pure p
  | p :: rest => do `(Effect4.Schema.Model.refusal_union $p $(← checkedOf rest))

/-- The staged image of `unionOf`'s union: the members' staged images, right-nested by
`Image.union` as the type nests `Ty.union`. -/
def stagedUnionOf : List Term → MacroM Term
  | [] => `(Effect4.Store.Image.empty)
  | [m] => pure m
  | m :: rest => do `(Effect4.Store.Image.union $m $(← stagedUnionOf rest))

/-- The proof that a record's staged image is the fold's: each field's staged image is its fold's
(`Modeled.staged_eq`), so a field instance may be opaque, and the rest is the fold unfolded at
the type, by definition. With no field it is definitional alone. -/
def stagedEqProof (stagedId : Ident) (hasFields : Bool) : MacroM Term :=
  if hasFields then
    `(by unfold $stagedId:ident; simp only [Effect4.Schema.Modeled.staged_eq]; rfl)
  else `(rfl)

/-- Fold a list of terms into the right-nested pair that a record carrier is, ending in `()`. -/
def nest (items : List Term) : MacroM Term := do
  items.foldrM (fun x acc => `(($x, $acc))) (← `(()))

/-- Check an inductive type and write its `Modeled` instance: a union, right-nested, of one member
per constructor. A constructor is the record of its fields and its `_tag`, the constructor's name,
in canonical order; when no constructor has a field, each is its tag's literal, so the type is a
union of string literals (Probe T, rows 12, 13 and 39: rc.112's `Data.TaggedEnum` and a
TypeScript enum). The members' images never overlap: two records differ in their names or in
their `_tag` column, which reads before any lowercase field, so each proof of the union carrier
(`Image.union`) is `rfl`. -/
def deriveModeledSum (ref : Syntax) (tName : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.inductInfo info) := env.find? tName
    | throwErrorAt ref "derive_modeled: {tName} is not a structure or an inductive type"
  unless info.numParams == 0 && info.numIndices == 0 do
    throwErrorAt ref "derive_modeled: {tName} has parameters or indices; the first profile is \
      monomorphic"
  unless info.levelParams.isEmpty do
    throwErrorAt ref
      "derive_modeled: {tName} has universe parameters; the first profile is monomorphic"
  if info.isRec then
    throwErrorAt ref "derive_modeled: {tName} is recursive; a value type has no recursion"
  if info.ctors.isEmpty then
    throwErrorAt ref "derive_modeled: {tName} has no constructor"
  let ctors ← info.ctors.mapM fun c => do
    pure ({ name := c, tag := ctorTag c, fields := ← ctorFields ref c } : Ctor)
  for c in ctors do
    if (ctors.filter (·.tag == c.tag)).length > 1 then
      throwErrorAt ref "derive_modeled: two constructors of {tName} share the tag {c.tag}"
    if c.fields.any (fun f => defaultSpelling f.1 == "_tag") then
      throwErrorAt ref "derive_modeled: {c.name} has a field named _tag, which its tag takes"
  let enum := ctors.all (·.fields.isEmpty)
  -- each constructor's columns in canonical order: `none` is the tag, `some i` the `i`th field
  let columns (c : Ctor) : List (Option Nat) :=
    if enum then [] else
    let spellings := ("_tag", none) :: (c.fields.zipIdx.map fun ((f, _), i) =>
      (defaultSpelling f, some i))
    (canonicalOrder (spellings.map (·.1))).filterMap fun sp => (spellings.find? (·.1 == sp)).map (·.2)
  let member (c : Ctor) : MacroM Term := do
    if enum then `(Effect4.Program.Ty.lit $(quote c.tag)) else
    let items ← (columns c).mapM fun
      | none => `(("_tag", false, Effect4.Program.Ty.lit $(quote c.tag)))
      | some i => do
        let (f, t) := c.fields[i]!
        `(($(quote (defaultSpelling f)), false, (Effect4.Schema.Modeled.ty (α := $t))))
    `(Effect4.Program.Ty.record [$(items.toArray),*])
  let memberChecked (c : Ctor) : MacroM Term := do
    if enum then `(Effect4.Schema.Model.refusal_lit $(quote c.tag)) else
    let fields ← (columns c).foldrM (fun col acc => match col with
      | none => `(⟨rfl, Effect4.Schema.Model.refusal_lit $(quote c.tag), $acc⟩)
      | some i => do
        let t := c.fields[i]!.2
        `(⟨rfl, Effect4.Schema.Modeled.checked (α := $t), $acc⟩)) (← `(trivial))
    `(Effect4.Schema.Model.refusal_record (by decide) $fields)
  -- a member's staged image: its columns' combinators, or its tag's literal
  let stagedMember (c : Ctor) : MacroM Term := do
    if enum then `(Effect4.Store.Image.lit $(quote c.tag)) else
    let cols ← (columns c).foldrM (fun col acc => match col with
      | none => `(Effect4.Store.Columns.cons "_tag" (Effect4.Store.Image.lit $(quote c.tag)) $acc)
      | some i => do
        let (f, t) := c.fields[i]!
        `(Effect4.Store.Columns.cons $(quote (defaultSpelling f))
          (Effect4.Schema.Modeled.staged (α := $t)) $acc)) (← `(Effect4.Store.Columns.nil))
    `(Effect4.Store.Image.record $cols)
  let n := ctors.length
  -- a member's carrier value placed at its position of the right-nested union
  let wrap (k : Nat) (v : Term) : MacroM Term := do
    let mut acc : Term ← if k + 1 < n then `(⟨Sum.inl $v, rfl⟩) else pure v
    for _ in [0:k] do acc ← `(⟨Sum.inr $acc, rfl⟩)
    pure acc
  let wrapPat (k : Nat) (p : Term) : MacroM Term := do
    let mut acc : Term ← if k + 1 < n then `(⟨Sum.inl $p, _⟩) else pure p
    for _ in [0:k] do acc ← `(⟨Sum.inr $acc, _⟩)
    pure acc
  -- the equation that a member's value is unchanged, at its position
  let wrapEq (k : Nat) (e : Term) : MacroM Term := do
    let mut acc : Term ← if k + 1 < n then `(Subtype.ext (congrArg Sum.inl $e)) else pure e
    for _ in [0:k] do acc ← `(Subtype.ext (congrArg Sum.inr $acc))
    pure acc
  let s := mkCIdent tName
  let tyId := mkIdent (`_root_ ++ tName ++ `modeledTy)
  let checkedId := mkIdent (`_root_ ++ tName ++ `modeled_checked)
  let toId := mkIdent (`_root_ ++ tName ++ `modeledToC)
  let ofId := mkIdent (`_root_ ++ tName ++ `modeledOfC)
  let toOfId := mkIdent (`_root_ ++ tName ++ `modeled_to_of)
  let ofToId := mkIdent (`_root_ ++ tName ++ `modeled_of_to)
  let stagedId := mkIdent (`_root_ ++ tName ++ `modeledStaged)
  let stagedEqId := mkIdent (`_root_ ++ tName ++ `modeled_staged_eq)
  for suffix in [`modeledTy, `modeled_checked, `modeledToC, `modeledOfC, `modeled_to_of,
      `modeled_of_to, `modeledStaged, `modeled_staged_eq] do
    if (← getEnv).contains (tName ++ suffix) then
      throwErrorAt ref "derive_modeled: {tName ++ suffix} already exists"
  let members ← liftMacroM <| ctors.mapM member
  let staged ← liftMacroM do stagedUnionOf (← ctors.mapM stagedMember)
  -- A union's carrier names its members' images, so its staged image elaborates only where they
  -- are the fold's by definition, and the proof is that definition.
  let stagedEq ← liftMacroM `(rfl)
  let ty ← liftMacroM <| unionOf members
  let checked ← liftMacroM do checkedOf (← ctors.mapM memberChecked)
  let vars (c : Ctor) : List Ident :=
    c.fields.zipIdx.map fun (_, i) => mkIdent (.mkSimple s!"x{i}")
  -- toC: each constructor's record of its fields' carriers, placed at its position
  let toAlts ← liftMacroM <| ctors.zipIdx.mapM fun (c, k) => do
    let vs := vars c
    let cols ← (columns c).mapM fun
      | none => `(())
      | some i => `(Effect4.Schema.Modeled.toC $(vs[i]!))
    let v ← if enum then `(()) else nest cols
    `(Lean.Parser.Term.matchAltExpr| | $(mkCIdent c.name) $(vs.toArray.map (⟨·.raw⟩)):term* =>
        $(← wrap k v))
  -- ofC: each position's record read back into its constructor
  let ofAlts ← liftMacroM <| ctors.zipIdx.mapM fun (c, k) => do
    let vs := vars c
    let cols ← (columns c).mapM fun
      | none => `(_)
      | some i => pure (⟨vs[i]!.raw⟩ : Term)
    let p ← if enum then `(_) else nest cols
    let args ← vs.mapM fun (v : Ident) => `(Effect4.Schema.Modeled.ofC $v)
    `(Lean.Parser.Term.matchAltExpr| | $(← wrapPat k p) =>
        $(mkCIdent c.name) $(args.toArray):term*)
  -- to_of: the same patterns, each column's `to_of`
  let invAlts ← liftMacroM <| ctors.zipIdx.mapM fun (c, k) => do
    let vs := vars c
    let cols ← (columns c).mapM fun
      | none => `(_)
      | some i => pure (⟨vs[i]!.raw⟩ : Term)
    let p ← if enum then `(_) else nest cols
    let e ← if enum then `(rfl) else
      (columns c).foldrM (fun col acc => match col with
        | none => `(Prod.ext rfl $acc)
        | some i => `(Prod.ext (Effect4.Schema.Modeled.to_of $(vs[i]!)) $acc)) (← `(rfl))
    `(Lean.Parser.Term.matchAltExpr| | $(← wrapPat k p) => $(← wrapEq k e))
  let xId := mkIdent `x
  let envBefore ← getEnv
  elabCommand (← `(def $tyId : Effect4.Program.Ty := $ty))
  elabCommand (← `(theorem $checkedId : Effect4.Schema.Model.refusal $tyId = none := $checked))
  let cId := mkIdent `c
  elabCommand (← `(def $toId ($xId : $s) : Effect4.Schema.Model.Carrier $tyId :=
    match $xId:ident with $(toAlts.toArray):matchAlt*))
  elabCommand (← `(def $ofId ($cId : Effect4.Schema.Model.Carrier $tyId) : $s :=
    match $cId:ident with $(ofAlts.toArray):matchAlt*))
  elabCommand (← `(theorem $toOfId ($cId : Effect4.Schema.Model.Carrier $tyId) :
      $toId ($ofId $cId) = $cId :=
    match $cId:ident with $(invAlts.toArray):matchAlt*))
  elabCommand (← `(theorem $ofToId ($xId : $s) : $ofId ($toId $xId) = $xId := by
    cases $xId:ident <;> simp only [$toId:ident, $ofId:ident, Effect4.Schema.Modeled.of_to]))
  elabCommand (← `(def $stagedId : Effect4.Store.Image (Effect4.Schema.Model.Carrier $tyId) :=
    $staged))
  elabCommand (← `(theorem $stagedEqId : $stagedId = Effect4.Schema.Model.image $tyId := $stagedEq))
  elabCommand (← `(instance : Effect4.Schema.Modeled $s :=
    ⟨$tyId, $checkedId, $toId, $ofId, $toOfId, $ofToId, $stagedId, $stagedEqId⟩))
  if (← get).messages.hasErrors then
    setEnv envBefore

/-- Check a structure and its renames, then write its `Modeled` instance. An inductive type that
is no structure takes `deriveModeledSum`, with no renames. -/
def deriveModeled (ref : Syntax) (sName : Name) (renames : Array (Ident × String)) :
    CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env sName do
    if renames.isEmpty then
      deriveModeledSum ref sName
      return
    throwErrorAt ref "derive_modeled: {sName} is not a structure; an inductive takes no renames"
  let ctor := getStructureCtor env sName
  unless ctor.numParams == 0 do
    throwErrorAt ref "derive_modeled: {sName} has parameters; the first profile is monomorphic"
  unless ctor.levelParams.isEmpty do
    throwErrorAt ref
      "derive_modeled: {sName} has universe parameters; the first profile is monomorphic"
  let fields := (getStructureFields env sName).toList
  -- Each rename names an existing field, once.
  let mut seen : List Name := []
  for (f, _) in renames do
    unless fields.contains f.getId do
      throwErrorAt f "derive_modeled: {sName} has no field {f.getId}"
    if seen.contains f.getId then
      throwErrorAt f "derive_modeled: field {f.getId} is renamed twice"
    seen := f.getId :: seen
  let table : List (Name × String) := renames.toList.map fun (f, n) => (f.getId, n)
  let spelling (f : Name) : String := (table.lookup f).getD (defaultSpelling f)
  -- The spellings are distinct.
  let spellings := fields.map spelling
  for f in fields do
    if (spellings.filter (· == spelling f)).length > 1 then
      throwErrorAt ref "derive_modeled: two fields of {sName} are spelled {spelling f}"
  -- Each field is independent of the others, and its type has an instance.
  let fieldTys ← withRef ref <| liftTermElabM <| forallTelescope ctor.type fun xs _ => do
    unless xs.size == fields.length do
      throwError "derive_modeled: {sName}'s constructor does not match its fields"
    xs.toList.mapM fun x => do
      let t ← inferType x
      if t.hasAnyFVar (fun v => xs.any (·.fvarId! == v)) then
        throwError "derive_modeled: field type {t} depends on another field"
      if ← isProp t then
        throwError "derive_modeled: field type {t} is a proposition"
      let inst ← mkAppM ``Effect4.Schema.Modeled #[t]
      unless (← trySynthInstance inst) matches .some _ do
        throwError "derive_modeled: field type {t} has no Modeled instance"
      PrettyPrinter.delab t
  let entries := (fields.zip fieldTys).map fun (f, t) => (f, spelling f, t)
  let order := canonicalOrder (entries.map (·.2.1))
  let sorted := order.filterMap fun sp => entries.find? (·.2.1 == sp)
  let s := mkCIdent sName
  let tyItems ← liftMacroM <| sorted.mapM fun (_, sp, t) =>
    `(($(quote sp), false, (Effect4.Schema.Modeled.ty (α := $t))))
  let cId := mkIdent `c
  let sId := mkIdent `s
  let proj (k : Nat) : MacroM (TSyntax `term) := do
    let mut acc : TSyntax `term ← `($cId)
    for _ in [0:k] do acc ← `(($acc).2)
    `(($acc).1)
  let toItems ← liftMacroM <| sorted.mapM fun (f, _, _) =>
    `(Effect4.Schema.Modeled.toC ($(mkCIdent (sName ++ f)) $sId))
  let tuple ← liftMacroM <| toItems.foldrM (fun x acc => `(($x, $acc))) (← `(()))
  let ofFields ← liftMacroM <| entries.mapM fun (f, sp, _) => do
    let k := (sorted.findIdx? (·.2.1 == sp)).getD 0
    let p ← proj k
    `(Lean.Parser.Term.structInstField| $(mkIdent f):ident := Effect4.Schema.Modeled.ofC $p)
  let vars : List (TSyntax `term) :=
    (List.range sorted.length).map fun i => ⟨(mkIdent (.mkSimple s!"x{i}")).raw⟩
  let pat ← liftMacroM <| vars.foldrM (fun x acc => `(($x, $acc))) (← `(()))
  let inv ← liftMacroM <| vars.foldrM
    (fun x acc => `(Prod.ext (Effect4.Schema.Modeled.to_of $x) $acc)) (← `(rfl))
  let tyId := mkIdent (`_root_ ++ sName ++ `modeledTy)
  let checkedId := mkIdent (`_root_ ++ sName ++ `modeled_checked)
  let toId := mkIdent (`_root_ ++ sName ++ `modeledToC)
  let ofId := mkIdent (`_root_ ++ sName ++ `modeledOfC)
  let toOfId := mkIdent (`_root_ ++ sName ++ `modeled_to_of)
  let ofToId := mkIdent (`_root_ ++ sName ++ `modeled_of_to)
  let stagedId := mkIdent (`_root_ ++ sName ++ `modeledStaged)
  let stagedEqId := mkIdent (`_root_ ++ sName ++ `modeled_staged_eq)
  let fieldsArr := ofFields.toArray
  -- The staged image: one column per field in canonical order, each its instance's staged image.
  let stagedCols ← liftMacroM <| sorted.foldrM (fun (_, sp, t) acc =>
    `(Effect4.Store.Columns.cons $(quote sp) (Effect4.Schema.Modeled.staged (α := $t)) $acc))
    (← `(Effect4.Store.Columns.nil))
  let stagedEq ← liftMacroM <| stagedEqProof stagedId (!sorted.isEmpty)
  -- Every generated name is free before anything is written (overwatch finding OW-02).
  for suffix in [`modeledTy, `modeled_checked, `modeledToC, `modeledOfC, `modeled_to_of,
      `modeled_of_to, `modeledStaged, `modeled_staged_eq] do
    if (← getEnv).contains (sName ++ suffix) then
      throwErrorAt ref "derive_modeled: {sName ++ suffix} already exists"
  -- The checked proof composes each field instance's own `checked`, and decides only the names'
  -- order, so a field instance may be opaque (overwatch finding OW-01).
  let checkedFields ← liftMacroM <| sorted.foldrM
    (fun (_, _, t) acc => `(⟨rfl, Effect4.Schema.Modeled.checked (α := $t), $acc⟩)) (← `(trivial))
  let envBefore ← getEnv
  elabCommand (← `(def $tyId : Effect4.Program.Ty := .record [$(tyItems.toArray),*]))
  elabCommand (← `(theorem $checkedId : Effect4.Schema.Model.refusal $tyId = none :=
    Effect4.Schema.Model.refusal_record (by decide) $checkedFields))
  elabCommand (← `(def $toId ($sId : $s) : Effect4.Schema.Model.Carrier $tyId := $tuple))
  elabCommand (← `(def $ofId ($cId : Effect4.Schema.Model.Carrier $tyId) : $s :=
    { $fieldsArr:structInstField,* }))
  elabCommand (← `(theorem $toOfId : ∀ $cId : Effect4.Schema.Model.Carrier $tyId,
      $toId ($ofId $cId) = $cId :=
    fun $pat => $inv))
  elabCommand (← `(theorem $ofToId ($sId : $s) : $ofId ($toId $sId) = $sId := by
    cases $sId:ident
    simp only [$toId:ident, $ofId:ident, Effect4.Schema.Modeled.of_to]))
  elabCommand (← `(def $stagedId : Effect4.Store.Image (Effect4.Schema.Model.Carrier $tyId) :=
    Effect4.Store.Image.record $stagedCols))
  elabCommand (← `(theorem $stagedEqId : $stagedId = Effect4.Schema.Model.image $tyId := $stagedEq))
  elabCommand (← `(instance : Effect4.Schema.Modeled $s :=
    ⟨$tyId, $checkedId, $toId, $ofId, $toOfId, $ofToId, $stagedId, $stagedEqId⟩))
  -- A declaration that failed leaves nothing behind: the command keeps all or none.
  if (← get).messages.hasErrors then
    setEnv envBefore

/-- `derive_modeled S (field := "spelling")*`: write `S`'s `Modeled` instance, with renames. -/
syntax (name := deriveModeledCmd) "derive_modeled " ident ("(" ident " := " str ")")* : command

@[command_elab deriveModeledCmd]
def elabDeriveModeled : CommandElab
  | `(derive_modeled $s:ident $[($rf:ident := $rn:str)]*) => do
    let sName ← liftCoreM (realizeGlobalConstNoOverload s)
    deriveModeled s sName (rf.zip (rn.map (·.getString)))
  | _ => throwUnsupportedSyntax

/-- `deriving Modeled`: each field under its own name. -/
def modeledHandler (typeNames : Array Name) : CommandElabM Bool := do
  for t in typeNames do
    deriveModeled (← getRef) t #[]
  return true

initialize registerDerivingHandler ``Effect4.Schema.Modeled modeledHandler

end Effect4.Schema.Modeled.Derive
