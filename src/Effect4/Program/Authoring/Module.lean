module

public meta import Lean
public import Effect4.Program.Authoring.Defs
public import Effect4.Program.Authoring.Declare

/-!
# Program.Authoring.Module — a group of declared operations

`eff_module` writes an authoring record, its constructor, and its module helpers.
Each operation declares its runtime parameters and columns once.
The constructor uses `Def.of` on the written body and stores its invocation.
Named `definitions` fields retain each existing `DefSrc`; `defs` projects them in declaration order.
The record stores authoring functions, never stored program syntax.

Separate entries with semicolons. Group parameters are explicit typed Lean binders.
The optional `using self` header supplies named invocations before the bodies are built.
A body may call a forward or recursive operation through that record.
The module checker decides admission; no termination property is claimed.
-/

public meta section

namespace Effect4.Program.Authoring

open Lean

/-- An explicit parameter of a group or operation. -/
declare_syntax_cat effModuleBinder
syntax "(" ident " : " term ")" : effModuleBinder

/-- One operation, with an optional error column and service requirements. -/
declare_syntax_cat effModuleOperation
syntax (Lean.Parser.Command.docComment)? ident effModuleBinder* " : " term:max
  ( &"error" term:max)? ( &"requires" term:max)?
  " := " term : effModuleOperation

/-- Declare an authoring record and its constructor from a nonempty operation group. -/
syntax (name := effModuleDecl) (Lean.Parser.Command.docComment)? "eff_module " ident effModuleBinder* ( &"using" ident)? " where "
  sepBy1(effModuleOperation, "; ") : command

/-- Parse explicit binders and reject repeated names. -/
def parseModuleBinders (binders : Array Syntax) : MacroM (Array (Ident × TSyntax `term)) := do
  let mut out := #[]
  for binder in binders do
    let `(effModuleBinder| ($name:ident : $ty:term)) := binder
      | Macro.throwErrorAt binder "expected an explicit typed binder `(name : type)`"
    unless name.getId.isStr && name.getId.getPrefix == .anonymous && name.getId != `_ do
      Macro.throwErrorAt name "a parameter needs one simple name"
    if out.any (fun entry => entry.1.getId == name.getId) then
      Macro.throwErrorAt name "duplicate parameter name"
    out := out.push (name, ty)
  return out

/-- A parsed operation and its declared columns. -/
structure ModuleOperation where
  doc : Option (TSyntax ``Lean.Parser.Command.docComment)
  name : Ident
  params : Array (Ident × TSyntax `term)
  answer : TSyntax `term
  error : TSyntax `term
  requires : TSyntax `term
  body : TSyntax `term

/-- Parse operation entries and their optional columns. -/
def parseModuleOperations (entries : Array Syntax)
    (group : Array (Ident × TSyntax `term)) : MacroM (Array ModuleOperation) := do
  let mut out := #[]
  for entry in entries do
    let `(effModuleOperation| $[$doc:docComment]? $name:ident $binders:effModuleBinder* : $answer:term
        $[error $error:term]? $[requires $requires:term]? := $body:term) := entry
      | Macro.throwErrorAt entry "expected `operation (argument : Ty) : answer := body`"
    unless name.getId.isStr && name.getId.getPrefix == .anonymous && name.getId != `_ do
      Macro.throwErrorAt name "an operation needs one simple name"
    if [`defs, `definition, `definitions, `Calls, `calls, `make, `install, `module, `mk, `rec, `recOn, `casesOn,
        `noConfusion, `noConfusionType, `ctorIdx, `brecOn, `below].contains name.getId then
      Macro.throwErrorAt name "operation name is reserved by the generated record"
    if out.any (fun operation => operation.name.getId == name.getId) then
      Macro.throwErrorAt name "duplicate operation name"
    let params ← parseModuleBinders binders
    for (param, _) in params do
      if group.any (fun pair => pair.1.getId == param.getId) then
        Macro.throwErrorAt param "runtime parameter collides with a group parameter"
    let error ← match error with | some value => pure value | none => `(Effect4.Program.Ty.never)
    let requires ← match requires with | some value => pure value | none => `([])
    out := out.push { doc, name, params, answer, error, requires, body }
  return out

macro_rules
  | `($[$doc:docComment]? eff_module $name:ident $binders:effModuleBinder* $[using $selfId:ident]? where $entries;*) => do
    let group ← parseModuleBinders binders
    let operations ← parseModuleOperations entries.getElems group
    if let some selfId := selfId then
      unless selfId.getId.isStr && selfId.getId.getPrefix == .anonymous && selfId.getId != `_ do
        Macro.throwErrorAt selfId "the call record needs one simple name"
      if group.any (fun pair => pair.1.getId == selfId.getId) ||
          operations.any (fun op => op.params.any (fun pair => pair.1.getId == selfId.getId)) then
        Macro.throwErrorAt selfId "call record name collides with a parameter"
    let fields ← operations.mapM fun op => do
      let ty ← termArrows op.params.size (← `(Effect4.Program.Authoring.Src Effect4.Program.NativeOp))
      `(Lean.Parser.Command.structSimpleBinder| $[$op.doc:docComment]? $op.name:ident : $ty)
    let currentNamespace ← Macro.getCurrNamespace
    let moduleName := if (`_root_).isPrefixOf name.getId then
        name.getId.replacePrefix `_root_ .anonymous
      else currentNamespace ++ name.getId
    -- Exact references keep operation and parameter names from capturing generated types.
    let definitionsTyName := moduleName.appendAfter "Declarations"
    let definitionsTyId := mkIdentFrom name (name.getId.appendAfter "Declarations")
    let definitionsTyRef := mkCIdentFrom name definitionsTyName
    let declarationFields ← operations.mapM fun op =>
      `(Lean.Parser.Command.structSimpleBinder| $[$op.doc:docComment]? $op.name:ident :
        Effect4.Program.Authoring.DefSrc Effect4.Program.NativeOp)
    let declarationsRecord ← `(command| structure $definitionsTyId where
      $[$declarationFields:structSimpleBinder]*)
    let record ← `(command| $[$doc:docComment]? structure $name:ident where
      definitions : $definitionsTyRef
      $[$fields:structSimpleBinder]*)
    let instanceId ← withFreshMacroScope `(ident| instanceName)
    let callsTyId := mkIdentFrom name (name.getId ++ `Calls)
    let callsId := mkIdentFrom name (name.getId ++ `calls)
    let mut callsDecls : Array Syntax := #[]
    let mut selfBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder := #[]
    let mut selfArgs : TSyntaxArray `term := #[]
    if let some selfId := selfId then
      let callsRecord ← `(command| structure $callsTyId where $[$fields:structSimpleBinder]*)
      let assignments ← operations.mapM fun op => do
        let ty ← termArrows op.params.size (← `(Effect4.Program.Authoring.Src Effect4.Program.NativeOp))
        let spelling ← `(Effect4.Program.Authoring.Def.qualifiedName $instanceId
          $(Syntax.mkStrLit (identToString op.name)))
        `(Lean.Parser.Term.structInstField| $op.name:ident :=
          (Effect4.Program.Authoring.Params.curry
            (Effect4.Program.Authoring.Def.invoke $spelling) : $ty))
      let callsDecl ← `(command| def $callsId ($instanceId : String) : $callsTyId :=
        { $assignments:structInstField,* })
      callsDecls := #[callsRecord.raw, callsDecl.raw]
      let selfBinder ← `(Lean.Parser.Term.bracketedBinderF| ($selfId : $callsTyId))
      selfBinders := #[⟨selfBinder.raw⟩]
      selfArgs := #[⟨selfId.raw⟩]
    let groupBinders : TSyntaxArray ``Lean.Parser.Term.bracketedBinder ← group.mapM fun (x, ty) => do
      let binder ← `(Lean.Parser.Term.bracketedBinderF| ($x : $ty))
      pure ⟨binder.raw⟩
    let mut locals : Array Ident := #[]
    let mut values : Array (TSyntax `term) := #[]
    let mut definitions : Array Syntax := #[]
    let groupArgs : TSyntaxArray `term := group.map fun (x, _) => ⟨x.raw⟩
    for op in operations do
      let localId ← withFreshMacroScope `(ident| operation)
      locals := locals.push localId
      let spelling ← `(Effect4.Program.Authoring.Def.qualifiedName $instanceId
          $(Syntax.mkStrLit (identToString op.name)))
      let params ← op.params.mapM fun (x, ty) =>
        `(($(Syntax.mkStrLit (identToString x)), ($ty : Effect4.Program.Ty)))
      let args : TSyntaxArray `term := op.params.map fun (x, _) => ⟨x.raw⟩
      let ty ← termArrows args.size (← `(Effect4.Program.Authoring.Src Effect4.Program.NativeOp))
      let body ← if args.isEmpty then pure op.body else `(fun $args* => $op.body)
      let definitionId := mkIdentFrom op.name (name.getId ++ `definition ++ op.name.getId)
      let fullNameId ← withFreshMacroScope `(ident| definitionName)
      let definition ← `(command| $[$op.doc:docComment]? def $definitionId ($fullNameId : String)
          $groupBinders:bracketedBinder* $selfBinders:bracketedBinder* : Effect4.Program.Authoring.Defined $ty :=
        Effect4.Program.Authoring.Def.of $fullNameId [$params,*]
          $op.answer ($body : $ty) $op.error $op.requires)
      definitions := definitions.push definition.raw
      values := values.push (← `($definitionId $spelling $groupArgs* $selfArgs*))
    let declarationAssignments ← (operations.zip locals).mapM fun (op, x) =>
      `(Lean.Parser.Term.structInstField| $op.name:ident := ($x).src)
    let assignments ← (operations.zip locals).mapM fun (op, x) =>
      `(Lean.Parser.Term.structInstField| $op.name:ident := ($x).call)
    let declarationValue ← `(({ $declarationAssignments:structInstField,* } : $definitionsTyRef))
    let declarationField ← `(Lean.Parser.Term.structInstField| definitions := $declarationValue)
    let allAssignments := #[declarationField] ++ assignments
    let mut result ← `(({ $allAssignments:structInstField,* } : $name))
    for (localId, value) in (locals.zip values).reverse do
      result ← `(let $localId := $value; $result)
    if let some selfId := selfId then
      result ← `(let $selfId := $callsId $instanceId; $result)
    let makeId := mkIdentFrom name (name.getId ++ `make)
    let installId := mkIdentFrom name (name.getId ++ `install)
    let moduleId := mkIdentFrom name (name.getId ++ `module)
    let makeDecl ← `(command| def $makeId ($instanceId : String) $groupBinders:bracketedBinder* :
      $name := $result)
    let selfArg ← withFreshMacroScope `(ident| self)
    let moduleArg ← withFreshMacroScope `(ident| m)
    let mainArg ← withFreshMacroScope `(ident| main)
    let defsId := mkIdentFrom name (name.getId ++ `defs)
    let sources ← operations.mapM fun op => do
      let projection := mkCIdentFrom op.name (definitionsTyName ++ op.name.getId)
      `($projection (($selfArg).definitions))
    let defsDecl ← `(command| def $defsId ($selfArg : $name) :
        List (Effect4.Program.Authoring.DefSrc Effect4.Program.NativeOp) := [$sources,*])
    let install ← `(command| def $installId ($selfArg : $name)
        ($moduleArg : Effect4.Program.Authoring.Module Effect4.Program.NativeOp) :
        Effect4.Program.Authoring.Module Effect4.Program.NativeOp :=
      { $moduleArg with defs := ($selfArg).defs ++ ($moduleArg).defs })
    let asModule ← `(command| def $moduleId ($selfArg : $name)
        ($mainArg : Effect4.Program.Authoring.Src Effect4.Program.NativeOp) :
        Effect4.Program.Authoring.Module Effect4.Program.NativeOp :=
      $installId $selfArg { main := $mainArg })
    return mkNullNode (#[declarationsRecord.raw, record.raw] ++ callsDecls ++ definitions ++
      #[makeDecl.raw, defsDecl.raw, install.raw, asModule.raw])

end Effect4.Program.Authoring
