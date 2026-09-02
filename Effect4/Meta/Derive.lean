import Lean
import Effects.Family
import Effect4.Target.TypeScript.EffectV4

/-!
# Meta.Derive

Two command elaborators. From one declaration each emits the algebra and the
first-order rows beside it, and nothing else; every rendering is a pure
function over the rows (`Effect4/Target/TypeScript/EffectV4.lean`).

```lean
effect_signature Cell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫
```

emits `Cell.Name` (inductive), `Cell.Param` and `Cell.Answer` (abbrevs by
match), `Cell : Effects.Family`, `Cell.Sig : Effects.Signature`, one smart
constructor per operation (`Cell.put : Nat → Effects.Program Cell.Sig Unit`),
and `Cell.rows : ServiceRow`. A handler is a `Cell.Service M`.

```lean
effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  return x
```

emits `incr : Nat → Effects.Program Cell.Sig Nat` and `incr.script : Script`.

This module is metaprogramming: `MetaM` reaches `Classical.choice`, so it sits
behind the target-implementation exemption of the axiom gate and declares no
theorem.
-/

open Lean Elab Command Term

namespace Effect4.Meta

declare_syntax_cat effectParam
syntax "(" ident " : " term ")" : effectParam

declare_syntax_cat effectOp
syntax "| " ident effectParam* " : " term " ⟪ " str,* " ⟫" : effectOp

syntax "effect_signature " ident " where " effectOp+ : command

declare_syntax_cat effectStep
syntax "let " binderIdent " ← " ident "(" term,* ")" : effectStep
syntax "return " term : effectStep

syntax "effect_program " ident "(" ident " : " term ")" " over " ident " : " term " := " effectStep+ : command

/-! ## Stratum V spellings, syntax directed -/

private partial def tsOfType (stx : Term) : CommandElabM String := do
  if stx.raw.isIdent then
    match stx.raw.getId.eraseMacroScopes with
    | `Nat | `Int => return "number"
    | `String => return "string"
    | `Bool => return "boolean"
    | `Unit => return "void"
    | other => throwErrorAt stx "effect_signature: no TypeScript spelling for `{other}`; add a Stratum V row first"
  match stx with
  | `($f:ident $arg:term) =>
      let inner ← tsOfType arg
      match f.getId.eraseMacroScopes with
      | `Option => return s!"Option.Option<{inner}>"
      | `List => return s!"ReadonlyArray<{inner}>"
      | other => throwErrorAt stx "effect_signature: no TypeScript spelling for `{other}`"
  | _ => throwErrorAt stx "effect_signature: unsupported type syntax"

private def strLit (s : String) : Term := ⟨(Syntax.mkStrLit s).raw⟩
private def natLit (n : Nat) : Term := ⟨(Syntax.mkNumLit (toString n)).raw⟩

private def pairLit (a b : String) : CommandElabM Term :=
  `(($(strLit a), $(strLit b)))

private def listLit (items : Array Term) : CommandElabM Term :=
  `([$items,*])

/-- A parameter list as one type: `Unit`, the type, or a right-nested product. -/
private def productOf (types : List Term) : CommandElabM Term :=
  match types with
  | [] => `(Unit)
  | [t] => pure t
  | t :: rest => do `($t × $(← productOf rest))

/-- The matching value: `()`, the variable, or a right-nested tuple. -/
private def tupleOf (vars : List Term) : CommandElabM Term :=
  match vars with
  | [] => `(())
  | [x] => pure x
  | x :: rest => do `(($x, $(← tupleOf rest)))

/-! ## `effect_signature` -/

elab_rules : command
  | `(effect_signature $name:ident where $ops:effectOp*) => do
    let famName := name.getId
    let nameTy := mkIdent (famName ++ `Name)
    let paramFn := mkIdent (famName ++ `Param)
    let answerFn := mkIdent (famName ++ `Answer)
    let sigName := mkIdent (famName ++ `Sig)
    let mut ctors : Array (TSyntax ``Lean.Parser.Command.ctor) := #[]
    let mut paramAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut answerAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut rowTerms : Array Term := #[]
    let mut smart : Array (TSyntax `command) := #[]
    let mut index := 0
    for op in ops do
      match op with
      | `(effectOp| | $opName:ident $params:effectParam* : $answer:term ⟪ $cues:str,* ⟫) => do
          unless TypeScript.targetIdentifier opName.getId.toString do
            throwErrorAt opName "effect_signature: `{opName.getId}` is not a legal target identifier"
          let ctorName := mkIdent (famName ++ `Name ++ opName.getId)
          let smartName := mkIdent (famName ++ opName.getId)
          let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
          let mut types : List Term := []
          let mut args : List Term := []
          let mut paramRows : Array Term := #[]
          let mut tsParamRows : Array Term := #[]
          for param in params do
            match param with
            | `(effectParam| ($x:ident : $t:term)) => do
                binders := binders.push (← `(Lean.Parser.Term.bracketedBinderF| ($x : $t)))
                types := types ++ [t]
                args := args ++ [(x : Term)]
                paramRows := paramRows.push (← pairLit x.getId.toString t.raw.reprint.get!.trimAscii.toString)
                tsParamRows := tsParamRows.push (← pairLit x.getId.toString (← tsOfType t))
            | _ => throwUnsupportedSyntax
          ctors := ctors.push (← `(Lean.Parser.Command.ctor| | $opName:ident))
          paramAlts := paramAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorName => $(← productOf types)))
          answerAlts := answerAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorName => $answer))
          let packed ← tupleOf args
          smart := smart.push (← `(def $smartName:ident $binders:bracketedBinder* : Effects.Program $sigName $answer :=
            Effects.Family.perform $name $ctorName $packed))
          let cueTerms : Array Term := cues.getElems.map fun c => (⟨c.raw⟩ : Term)
          rowTerms := rowTerms.push (← `({ name := $(strLit opName.getId.toString), index := $(natLit index), params := $(← listLit paramRows), tsParams := $(← listLit tsParamRows), answer := $(strLit answer.raw.reprint.get!.trimAscii.toString), tsAnswer := $(strLit (← tsOfType answer)), cues := $(← listLit cueTerms) : Effect4.Target.EffectV4.OpRow }))
          index := index + 1
      | _ => throwUnsupportedSyntax
    elabCommand (← `(inductive $nameTy where $ctors* deriving DecidableEq, Repr))
    elabCommand (← `(abbrev $paramFn : $nameTy → Type := fun name => match name with $paramAlts:matchAlt*))
    elabCommand (← `(abbrev $answerFn : $nameTy → Type := fun name => match name with $answerAlts:matchAlt*))
    elabCommand (← `(abbrev $name : Effects.Family.{0, 0, 0} := ⟨$nameTy, $paramFn, $answerFn⟩))
    elabCommand (← `(abbrev $sigName : Effects.Signature.{0, 0} := Effects.Family.toSignature $name))
    for command in smart do elabCommand command
    let rowsName := mkIdent (famName ++ `rows)
    elabCommand (← `(def $rowsName : Effect4.Target.EffectV4.ServiceRow := { name := $(strLit famName.toString), ops := $(← listLit rowTerms) }))

/-! ## `effect_program` -/

private partial def pureOfTerm (stx : Term) : CommandElabM (Term × Term) := do
  match stx with
  | `(($inner)) => pureOfTerm inner
  | _ =>
    if stx.raw.isIdent then
      return (stx, ← `(Effect4.Target.EffectV4.PureTerm.var $(strLit stx.raw.getId.eraseMacroScopes.toString)))
    if let some n := stx.raw.isNatLit? then
      return (stx, ← `(Effect4.Target.EffectV4.PureTerm.nat $(natLit n)))
    if let some s := stx.raw.isStrLit? then
      return (stx, ← `(Effect4.Target.EffectV4.PureTerm.str $(strLit s)))
    match stx with
    | `($f:ident $args*) =>
        let rows ← args.mapM fun a => do pure (← pureOfTerm a).2
        return (stx, ← `(Effect4.Target.EffectV4.PureTerm.app $(strLit f.getId.eraseMacroScopes.toString) $(← listLit rows)))
    | _ => throwErrorAt stx "effect_program: pure fragment not admitted at the lowering face: {stx}"

elab_rules : command
  | `(effect_program $name:ident ($param:ident : $paramTy:term) over $famId:ident : $result:term := $steps:effectStep*) => do
    let sigName := mkIdent (famId.getId ++ `Sig)
    let mut stepRows : Array Term := #[]
    let mut body : Option Term := none
    let mut discard := 0
    for step in steps.reverse do
      match step with
      | `(effectStep| return $value:term) =>
          let (leanValue, row) ← pureOfTerm value
          stepRows := stepRows.push (← `(Effect4.Target.EffectV4.Step.ret $row))
          body := some (← `(pure $leanValue))
      | `(effectStep| let $x:binderIdent ← $opRef:ident ($args:term,*)) =>
          let some rest := body | throwErrorAt step "effect_program: the last step must be `return`"
          let (isHole, x) ← match x with
            | `(binderIdent| $id:ident) => pure (false, id)
            | _ => pure (true, mkIdent (Name.mkSimple s!"_discard{discard}"))
          let components := opRef.getId.components
          unless components.length = 2 && components.head! == famId.getId do
            throwErrorAt opRef "effect_program: operation must be spelled `{famId.getId}.<op>`"
          let opName := components.getLast!.toString
          let pairs ← args.getElems.mapM pureOfTerm
          let leanArgs : Array Term := pairs.map (·.1)
          let rows : Array Term := pairs.map (·.2)
          let call : Term ← if leanArgs.isEmpty then pure (opRef : Term) else `($opRef $leanArgs*)
          let bindName := if isHole then s!"_{discard}" else x.getId.eraseMacroScopes.toString
          if isHole then discard := discard + 1
          stepRows := stepRows.push (← `(Effect4.Target.EffectV4.Step.perform $(strLit bindName) $(strLit opName) $(← listLit rows)))
          body := some (← `($call >>= fun $x => $rest))
      | _ => throwUnsupportedSyntax
    let some programTerm := body | throwError "effect_program: empty body"
    elabCommand (← `(set_option linter.unusedVariables false in
      def $name ($param : $paramTy) : Effects.Program $sigName $result := $programTerm))
    let scriptName := mkIdent (name.getId ++ `script)
    let stepList ← listLit stepRows.reverse
    elabCommand (← `(def $scriptName : Effect4.Target.EffectV4.Script := { family := $(strLit famId.getId.toString), name := $(strLit name.getId.toString), param := ($(strLit param.getId.toString), $(strLit (← tsOfType paramTy))), steps := $stepList }))

end Effect4.Meta
