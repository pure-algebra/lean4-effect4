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

Each refusal is located at the syntax it is about. Then it writes, under the structure's name:
the record type in canonical field order (`modeledTy`), its proof of the checked domain by
`decide` (`modeled_checked`), the two maps to and from the carrier (`modeledToC`, `modeledOfC`),
their two inverse equations (`modeled_to_of`, `modeled_of_to`), and the instance.
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

/-- Check a structure and its renames, then write its `Modeled` instance. -/
def deriveModeled (ref : Syntax) (sName : Name) (renames : Array (Ident × String)) :
    CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env sName do
    throwErrorAt ref "derive_modeled: {sName} is not a structure"
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
  let fieldsArr := ofFields.toArray
  elabCommand (← `(def $tyId : Effect4.Program.Ty := .record [$(tyItems.toArray),*]))
  elabCommand (← `(theorem $checkedId : Effect4.Schema.Model.refusal $tyId = none := by decide))
  elabCommand (← `(def $toId ($sId : $s) : Effect4.Schema.Model.Carrier $tyId := $tuple))
  elabCommand (← `(def $ofId ($cId : Effect4.Schema.Model.Carrier $tyId) : $s :=
    { $fieldsArr:structInstField,* }))
  elabCommand (← `(theorem $toOfId : ∀ $cId : Effect4.Schema.Model.Carrier $tyId,
      $toId ($ofId $cId) = $cId :=
    fun $pat => $inv))
  elabCommand (← `(theorem $ofToId ($sId : $s) : $ofId ($toId $sId) = $sId := by
    cases $sId:ident
    simp only [$toId:ident, $ofId:ident, Effect4.Schema.Modeled.of_to]))
  elabCommand (← `(instance : Effect4.Schema.Modeled $s :=
    ⟨$tyId, $checkedId, $toId, $ofId, $toOfId, $ofToId⟩))

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
