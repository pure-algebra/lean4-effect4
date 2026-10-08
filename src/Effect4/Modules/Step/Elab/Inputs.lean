module

public meta import Lean
public import Effect4.Modules.Step.Inputs
public import Effect4.Modules.Step.Rename

/-!
# Named inputs for step authoring

`step_context% Inputs (count : .nat, id : idTy)` declares one input-name/type list.
`step_inputs% Inputs => body` binds typed step variables from that declaration.
`input_sources% (Inputs) { id := request, count := amount }` orders caller sources from the same declaration.
Names exist at elaboration only; the generated step holds ordinary positional input data.
`fold_step% xs from acc := initial with item => body` names the two fold inputs.
It lifts visible outer step locals structurally, including derived local steps.
Repeated names and local shadowing refuse; generic declarations retain their type parameters.
-/

public meta section
namespace Effect4.Modules.Step.Elab.Inputs
open Lean Meta Elab Term Command

syntax (name := stepContextStx) "step_context% " ident " (" (ident " : " term),* ")" : command
syntax (name := paramStepContextStx) "step_context% " ident bracketedBinder* " where " "(" (ident " : " term),* ")" : command
syntax (name := namedInputsStx) "step_inputs% " term " => " term : term
syntax (name := inputSourcesStx) "input_sources% " "(" term ")" "{" (ident " := " term),* "}" : term

syntax (name := foldStepStx) "fold_step% " term " from " ident " := " term " with " ident " => " term : term

private def duplicate (names : Array Ident) : TermElabM Unit := do
  for name in names do
    if (names.filter fun other => other.getId.eraseMacroScopes == name.getId.eraseMacroScopes).size > 1 then
      throwErrorAt name "input_sources%: repeated name {name}"

@[command_elab stepContextStx]
def elabStepContext : CommandElab := fun stx => do
  match stx with
  | `(step_context% $name:ident ($[$names:ident : $types:term],*)) =>
    for input in names do
      if (names.filter fun other => other.getId.eraseMacroScopes == input.getId.eraseMacroScopes).size > 1 then
        throwErrorAt input "step_context%: repeated name {input}"
    let pairs ← names.zip types |>.mapM fun (input, ty) => do
      `(( $(quote (input.getId.toString (escape := false))), $ty ))
    elabCommand (← `(def $name : Effect4.Modules.InputContext := [$pairs,*]))
  | _ => throwUnsupportedSyntax

@[command_elab paramStepContextStx]
def elabParamStepContext : CommandElab := fun stx => do
  match stx with
  | `(step_context% $name:ident $binders:bracketedBinder* where ($[$names:ident : $types:term],*)) =>
    for input in names do
      if (names.filter fun other => other.getId.eraseMacroScopes == input.getId.eraseMacroScopes).size > 1 then
        throwErrorAt input "step_context%: repeated name {input}"
    let pairs ← names.zip types |>.mapM fun (input, ty) => do
      `(( $(quote (input.getId.toString (escape := false))), $ty ))
    elabCommand (← `(def $name $binders* : Effect4.Modules.InputContext := [$pairs,*]))
  | _ => throwUnsupportedSyntax

private def contextEntries (stx : Syntax) : TermElabM (Array (String × Expr)) := do
  let context ← elabTerm stx (Option.some (Lean.mkConst ``Effect4.Modules.InputContext))
  let rec read (fuel : Nat) (xs : Expr) : TermElabM (Array (String × Expr)) := do
    match fuel with
    | 0 => throwErrorAt stx "step inputs: declaration exceeds the literal reader budget"
    | fuel + 1 =>
      let xs ← whnf (← instantiateMVars xs)
      if xs.isAppOfArity ``List.nil 1 then return #[]
      unless xs.isAppOfArity ``List.cons 3 do
        throwErrorAt stx "step inputs: declaration must reduce to a literal input list"
      let pair ← whnf (xs.getArg! 1)
      unless pair.isAppOfArity ``Prod.mk 4 do
        throwErrorAt stx "step inputs: declaration entry must be a name/type pair"
      let nameExpr ← whnf (pair.getArg! 2)
      let .lit (.strVal name) := nameExpr | throwErrorAt stx "step inputs: names must be string literals"
      let rest ← read fuel (xs.getArg! 2)
      if rest.any (fun entry => entry.1 == name) then
        throwErrorAt stx "step inputs: declaration repeats {name}"
      return #[(name, pair.getArg! 3)] ++ rest
  read 4096 context

private def withInputs (entries : Array (String × Expr)) (body : Syntax) (expected? : Option Expr) : TermElabM Expr := do
  for (name, _) in entries do
    if (← getLCtx).findFromUserName? (Name.mkSimple name) |>.isSome then
      throwErrorAt body "step_inputs%: input {name} shadows an existing local"
  let ty := Lean.mkConst ``Effect4.Program.Ty
  let types := entries.map Prod.snd
  let context ← mkListLit ty types.toList
  let result ← mkFreshExprMVar ty
  let expected := mkApp2 (Lean.mkConst ``Effect4.Modules.Step) context result
  let rec bind (index : Nat) (locals : Array Expr) : TermElabM Expr := do
    if index < entries.size then
      let (name, inputTy) := entries[index]!
      let rest ← mkListLit ty (types.toList.drop (index + 1))
      let mut input ← mkAppM ``Effect4.Modules.Input.here #[inputTy, rest]
      for prior in (types.toList.take index).reverse do
        input ← mkAppM ``Effect4.Modules.Input.there #[prior, input]
      let value ← mkAppM ``Effect4.Modules.Step.var #[input]
      let localTy := mkApp2 (Lean.mkConst ``Effect4.Modules.Step) context inputTy
      withLetDecl (Name.mkSimple name) localTy value fun inputLocal => bind (index + 1) (locals.push inputLocal)
    else
      let term ← elabTermEnsuringType body expected
      mkLetFVars locals term
  let term ← bind 0 #[]
  if let Option.some outer := expected? then
    unless ← isDefEq expected outer do throwErrorAt body "step_inputs%: inferred input context or result differs from expected type"
  instantiateMVars term

@[term_elab namedInputsStx]
def elabNamedInputs : TermElab := fun stx expected? => do
  match stx with
  | `(step_inputs% $context:term => $body:term) =>
    withInputs (← contextEntries context) body expected?
  | _ => throwUnsupportedSyntax

@[term_elab inputSourcesStx]
def elabInputSources : TermElab := fun stx expected? => do
  match stx with
  | `(input_sources% ($context:term) { $[$names:ident := $values:term],* }) =>
    duplicate names
    let entries ← contextEntries context
    let supplied := names.zip values
    for (name, _) in supplied do
      unless entries.any (fun entry => entry.1 == name.getId.toString (escape := false)) do
        throwErrorAt name "input_sources%: unknown input {name}"
    let mut ordered : Array (TSyntax `term) := #[]
    for (name, _) in entries do
      let Option.some (_, value) := supplied.find? (fun pair => pair.1.getId.toString (escape := false) == name)
        | throwErrorAt stx "input_sources%: missing input {name}"
      ordered := ordered.push value
    elabTerm (← `(Effect4.Modules.Input.source [$ordered,*])) expected?
  | _ => throwUnsupportedSyntax

@[term_elab foldStepStx]
def elabFoldStep : TermElab := fun stx expected? => do
  match stx with
  | `(fold_step% $xs:term from $accName:ident := $init:term with $itemName:ident => $body:term) =>
    if accName.getId.eraseMacroScopes == itemName.getId.eraseMacroScopes then
      throwErrorAt itemName "fold_step%: accumulator and item names must differ"
    let lctx ← getLCtx
    for binder in [accName, itemName] do
      if lctx.any (fun decl => !decl.isImplementationDetail &&
          decl.userName.eraseMacroScopes == binder.getId.eraseMacroScopes) then
        throwErrorAt binder "fold_step%: binder {binder} shadows an existing local"
    let list ← elabTerm xs Option.none
    let listType ← whnf (← inferType list)
    unless listType.isAppOfArity ``Effect4.Modules.Step 2 do
      throwErrorAt xs "fold_step%: source must be a Step list"
    let context := listType.getArg! 0
    let listResult ← whnf (listType.getArg! 1)
    unless listResult.isAppOfArity ``Effect4.Program.Ty.list 1 do
      throwErrorAt xs "fold_step%: source step must answer a list"
    let itemTy := listResult.getArg! 0
    let ty := Lean.mkConst ``Effect4.Program.Ty
    let accTy ← mkFreshExprMVar ty
    let init ← elabTermEnsuringType init (mkApp2 (Lean.mkConst ``Effect4.Modules.Step) context accTy)
    let accTy ← instantiateMVars accTy
    let itemContext ← mkAppM ``List.cons #[itemTy, context]
    let bodyContext ← mkAppM ``List.cons #[accTy, itemContext]
    let rho ← withLocalDecl `t BinderInfo.implicit ty fun t => do
      let inputType := mkApp2 (Lean.mkConst ``Effect4.Modules.Input) context t
      withLocalDeclD `input inputType fun input => do
        let itemLift ← mkAppM ``Effect4.Modules.Input.there #[itemTy, input]
        let accLift ← mkAppM ``Effect4.Modules.Input.there #[accTy, itemLift]
        mkLambdaFVars #[t, input] accLift
    let mut captured : Array (Name × Expr × Expr × Option FVarId) := #[]
    for decl in lctx do
      if decl.isImplementationDetail then continue
      if let Option.some visible := lctx.findFromUserName? decl.userName then
        if visible.fvarId != decl.fvarId then continue
      let localType ← whnf decl.type
      if localType.isAppOfArity ``Effect4.Modules.Step 2 then
        if ← isDefEq (localType.getArg! 0) context then
          let value ← mkAppM ``Effect4.Modules.Step.rename #[rho, decl.toExpr]
          let newType := mkApp2 (Lean.mkConst ``Effect4.Modules.Step) bodyContext (localType.getArg! 1)
          captured := captured.push (decl.userName, newType, value, Option.some decl.fvarId)
    let accInput ← mkAppM ``Effect4.Modules.Input.here #[accTy, itemContext]
    let accValue ← mkAppM ``Effect4.Modules.Step.var #[accInput]
    let itemInput ← mkAppM ``Effect4.Modules.Input.here #[itemTy, context]
    let itemInput ← mkAppM ``Effect4.Modules.Input.there #[accTy, itemInput]
    let itemValue ← mkAppM ``Effect4.Modules.Step.var #[itemInput]
    let accStep := mkApp2 (Lean.mkConst ``Effect4.Modules.Step) bodyContext accTy
    let itemStep := mkApp2 (Lean.mkConst ``Effect4.Modules.Step) bodyContext itemTy
    captured := captured.push (accName.getId, accStep, accValue, Option.none)
    captured := captured.push (itemName.getId, itemStep, itemValue, Option.none)
    let rec bind (index : Nat) (locals : Array Expr) : TermElabM Expr := do
      if index < captured.size then
        let (name, type, value, original?) := captured[index]!
        withLetDecl name type value fun inputLocal => do
          if let Option.some original := original? then
            pushInfoLeaf (.ofFVarAliasInfo { id := inputLocal.fvarId!, baseId := original, userName := name })
          bind (index + 1) (locals.push inputLocal)
      else
        let term ← elabTermEnsuringType body accStep
        mkLetFVars locals term
    let bodyTerm ← bind 0 #[]
    let result ← mkAppM ``Effect4.Modules.Step.fold #[list, init, bodyTerm]
    if let Option.some expected := expected? then
      unless ← isDefEq (← inferType result) expected do
        throwErrorAt stx "fold_step%: result differs from expected type"
    instantiateMVars result
  | _ => throwUnsupportedSyntax

end Effect4.Modules.Step.Elab.Inputs
