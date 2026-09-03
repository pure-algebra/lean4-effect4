import Lean
import Effects.Family
import Effects.Trace
import Effect4.Semantics.Observation
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
`Cell.rows : ServiceRow`, and the trace face `Cell.Name.spelling`,
`Cell.encodeParam`, `Cell.encodeAnswer`, `Cell.traced`, `Cell.tracedExcept`. A
handler is a `Cell.Service M`; `Cell.traced handler` logs every operation and
`Cell.tracedExcept` does the same for a handler into `ExceptT E M`.

An operation may take or answer an opaque host handle, spelled
`Handle "TypeScriptType"`: the Lean carrier is an index, the wire value is that
index, and the target prints the given type. See `Handle` below.

An aborting operation is declared `| op (p : T) : A !! E ⟪…⟫` (`!` alone would
parse as a prefix negation applied to `E`): the family's
answer stays `A`, the row carries the error spellings, the method type gains
`E`, and the handler kind is `X.Service (ExceptT E M)`. A returned error is an
ordinary answer `Except E A`, spelled `Result.Result<A, E>`.

```lean
effect_program incr (n : Nat) over Cell : Nat :=
  let x ← Cell.get()
  let _ ← Cell.put(succ x)
  return x
```

emits `incr : Nat → Effects.Program Cell.Sig Nat` and `incr.script : Script`,
and beside them one receipt, checked by `rfl` at the declaration site:

```lean
example : Effect4.Target.EffectV4.performedNames Cell.Name.spelling Cell.answerDefault
    (incr default) = Effect4.Target.EffectV4.Script.operationNames incr.script := rfl
```

The elaborator builds the `Program` value and the `Script` from the same steps
but by two independent traversals, and until packet D5 nothing related them.
The receipt says they perform the same operations in the same order. It is the
strongest statement of that agreement the two faces admit; the one D5 asked for
is owed, in these words:

> **Owed (D5).** `example : denoteScript <rows> <name>.script = <name> := by rfl`
> cannot be stated. `denoteScript` (`Effect4/Target/TypeScript/ScriptDenotation.lean`)
> lands in `Program (Sig (tableAlphabet id table)) Val` — every request and
> every answer a wire `Effects.Trace.Val` — while `<name>` lands in
> `Program X.Sig A` at the Lean types the family declares. Relating them needs
> a decoding `Val → X.Answer name`, the converse of `X.encodeAnswer`; the DSL
> has only the encoding direction (`Effects.Trace.ToVal`), and a decoding is a
> partial function that no admitted spelling currently carries. Row
> `E4-TARGET-CE-016`. The receipt above is what is emitted instead.

A third elaborator declares the pure atoms a program's `PureTerm.app` names:

```lean
effect_atoms Atoms where
  | succ (n : Nat) : Nat ⟪ "n + 1" ⟫ := n + 1
```

emits the Lean function `succ`, the row list `Atoms.rows : List AtomRow`, the
flow embedding's `Atoms.table`, the wire dispatcher
`Atoms.eval : String → Val → Val` (through `Effect4.Target.EffectV4.OfVal`,
the converse of `ToVal`), and `Atoms.source`, the generated `atoms.ts`. One
declaration, every face: an atom that exists in one face only is
`E4-TARGET-CE-023`. The string is the host body, one TypeScript expression over
the binder; the Lean body is last, so a `match` body must be parenthesised —
its alternatives would otherwise swallow the next atom.

This module is metaprogramming: `MetaM` reaches `Classical.choice`, so it sits
behind the target-implementation exemption of the axiom gate and declares no
theorem.
-/

open Lean Elab Command Term

namespace Effect4.Meta

declare_syntax_cat effectParam
syntax "(" ident " : " term ")" : effectParam

declare_syntax_cat effectOp
syntax "| " ident effectParam* " : " term (" !! " term)? " ⟪ " str,* " ⟫" : effectOp

syntax "effect_signature " ident " where " effectOp+ : command

declare_syntax_cat effectStep
syntax "let " binderIdent " ← " ident "(" term,* ")" : effectStep
syntax "return " term : effectStep

syntax "effect_program " ident "(" ident " : " term ")" " over " ident " : " term " := " effectStep+ : command

declare_syntax_cat atomOp
syntax "| " ident effectParam " : " term " ⟪ " str " ⟫ " " := " term : atomOp

syntax "effect_atoms " ident " where " atomOp+ : command

/-! ## Opaque host handles -/

/-- An opaque host handle: an operation may take one or answer one, and the
only thing the wire ever says about it is a stable index.

The Lean carrier is that index, so `DecidableEq`, `Repr` and `ToVal` come free
and the wire value is an ordinary `nat` — the trace alphabet needs no new
constructor. `spelling` is a phantom parameter carrying the TypeScript type the
target must print for it: `Handle "Scope.Closeable"` is answered by rc.112's
opaque `Scope.Closeable` on the host, and `tsOfType` spells it exactly that.
Nothing else about the host object is describable, which is the point: the Lean
face names scopes `0, 1, 2, …` in creation order, and the host tracer indexes
the objects it is handed in first-seen order (`harness/trace/tracer.ts`
`registerHandle`). The two agree because the handle only ever leaves the host
as an answer of the operation that made it.

This is the whole DSL feature M1 needs; `effect_signature` admits the type
`Handle "T"` wherever it admits a Stratum V spelling. -/
structure Handle (spelling : String) where
  /-- The index this handle takes on the wire. -/
  index : Nat
deriving DecidableEq, Repr, Inhabited

instance {spelling : String} : Effects.Trace.ToVal (Handle spelling) :=
  ⟨fun handle => .nat handle.index⟩

/-! ## The answer-type profile, syntax directed

Lean type syntax is parsed into `Effect4.Target.EffectV4.Spelling`, which owns
the TypeScript spelling, the depth measure and the wire inhabitant. This
elaborator only decides which syntax reaches which constructor; the profile
itself is frozen in `test/contracts/answer-profile.contract.md`.

Stratum V is depth one (`Nat`, `Int`, `String`, `Bool`, `Unit`, `Handle "T"`);
depth two adds one `Option`, `List`, `Except` or `×` over it; depth three nests
one more, which is `Option (Except E A)`, `Except E (Option A)`,
`List (A × B)`, `Option (A × B)` and `A × Except E B`. Depth four is refused,
with its depth in the message. -/

open Effect4.Target.EffectV4 (Spelling)

/-- Type syntax nesting is bounded by this fuel. The profile's own bound is
`Spelling.profileDepth`; this only keeps the parser total. -/
private def typeFuel : Nat := 16

private def spellingOfTypeFuel : Nat → Term → CommandElabM Spelling
  | 0, stx => throwErrorAt stx "effect_signature: type syntax nested too deeply"
  | fuel + 1, stx => do
  match stx with
  | `(($inner:term)) => spellingOfTypeFuel fuel inner
  | _ =>
  if stx.raw.isIdent then
    match stx.raw.getId.eraseMacroScopes with
    | `Nat => return .nat
    | `Int => return .int
    | `String => return .string
    | `Bool => return .bool
    | `Unit => return .unit
    | other => throwErrorAt stx "effect_signature: no TypeScript spelling for `{other}`; add a Stratum V row first"
  match stx with
  | `(Handle $target:str) => return .handle target.getString
  | `($leftTy:term × $rightTy:term) =>
      return .prod (← spellingOfTypeFuel fuel leftTy) (← spellingOfTypeFuel fuel rightTy)
  | `(Except $errorTy:term $valueTy:term) =>
      return .except (← spellingOfTypeFuel fuel errorTy) (← spellingOfTypeFuel fuel valueTy)
  | `($f:ident $arg:term) =>
      let inner ← spellingOfTypeFuel fuel arg
      match f.getId.eraseMacroScopes with
      | `Option => return .option inner
      | `List => return .list inner
      | other => throwErrorAt stx "effect_signature: no TypeScript spelling for `{other}`"
  | _ => throwErrorAt stx "effect_signature: unsupported type syntax"

/-- The spelling of a type, refused above `Spelling.profileDepth`. -/
private def spellingOfType (stx : Term) : CommandElabM Spelling := do
  let spelling ← spellingOfTypeFuel typeFuel stx
  unless spelling.admitted do
    throwErrorAt stx
      "effect_signature: the answer-type profile admits depth {Spelling.profileDepth} at most; this spelling has depth {spelling.depth}"
  return spelling

private def tsOfType (stx : Term) : CommandElabM String := do
  return (← spellingOfType stx).render

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
    let mut spellingAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut encodeParamAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut encodeAnswerAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut answerDefaultAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    let mut index := 0
    for op in ops do
      match op with
      | `(effectOp| | $opName:ident $params:effectParam* : $answer:term $[!! $error:term]? ⟪ $cues:str,* ⟫) => do
          unless Effect4.Target.EffectV4.bindingName opName.getId.toString do
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
          let paramTy ← productOf types
          spellingAlts := spellingAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorName => $(strLit opName.getId.toString)))
          encodeParamAlts := encodeParamAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorName => fun (p : $paramTy) => Effects.Trace.ToVal.toVal p))
          encodeAnswerAlts := encodeAnswerAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorName => fun (a : $answer) => Effects.Trace.ToVal.toVal a))
          answerDefaultAlts := answerDefaultAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $ctorName => (default : $answer)))
          smart := smart.push (← `(def $smartName:ident $binders:bracketedBinder* : Effects.Program $sigName $answer :=
            Effects.Family.perform $name $ctorName $packed))
          let cueTerms : Array Term := cues.getElems.map fun c => (⟨c.raw⟩ : Term)
          let errorRow : Term ← match error with
            | some errorTy => do
                let leanSpelling := strLit errorTy.raw.reprint.get!.trimAscii.toString
                let tsSpelling := strLit (← tsOfType errorTy)
                `(some ($leanSpelling, $tsSpelling))
            | none => `(none)
          rowTerms := rowTerms.push (← `({ name := $(strLit opName.getId.toString), index := $(natLit index), params := $(← listLit paramRows), tsParams := $(← listLit tsParamRows), answer := $(strLit answer.raw.reprint.get!.trimAscii.toString), tsAnswer := $(strLit (← tsOfType answer)), cues := $(← listLit cueTerms), error := $errorRow : Effect4.Target.EffectV4.OpRow }))
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
    -- The trace face: spellings, wire encoders, and the traced service.
    let spellingName := mkIdent (famName ++ `Name ++ `spelling)
    let encodeParamName := mkIdent (famName ++ `encodeParam)
    let encodeAnswerName := mkIdent (famName ++ `encodeAnswer)
    let tracedName := mkIdent (famName ++ `traced)
    elabCommand (← `(def $spellingName : $nameTy → String := fun name => match name with $spellingAlts:matchAlt*))
    elabCommand (← `(def $encodeParamName : (name : $nameTy) → $paramFn name → Effects.Trace.Val := fun name => match name with $encodeParamAlts:matchAlt*))
    elabCommand (← `(def $encodeAnswerName : (name : $nameTy) → $answerFn name → Effects.Trace.Val := fun name => match name with $encodeAnswerAlts:matchAlt*))
    elabCommand (← `(def $tracedName {M : Type → Type} [Monad M] (service : Effects.Family.Service $name M) :
        Effects.Family.Service $name (StateT Effect4.Trace.Log M) :=
      Effects.Family.Service.traced (δ := Nat) (ρ := Nat) $spellingName $encodeParamName $encodeAnswerName service))
    -- One inhabitant per answer, so a program's operation sequence can be read
    -- off the program itself (`Effect4.Target.EffectV4.performedNames`); the
    -- straight-line fragment never branches on an answer, so which inhabitant
    -- is chosen does not change the sequence.
    let answerDefaultName := mkIdent (famName ++ `answerDefault)
    elabCommand (← `(def $answerDefaultName : (name : $nameTy) → $answerFn name :=
      fun name => match name with $answerDefaultAlts:matchAlt*))
    let tracedExceptName := mkIdent (famName ++ `tracedExcept)
    elabCommand (← `(def $tracedExceptName {E : Type} [Effects.Trace.ToVal E] {M : Type → Type} [Monad M]
        (service : Effects.Family.Service $name (ExceptT E M)) :
        Effects.Family.Service $name (ExceptT E (StateT Effect4.Trace.Log M)) :=
      Effects.Family.Service.tracedExcept (δ := Nat) (ρ := Nat) $spellingName $encodeParamName $encodeAnswerName
        Effects.Trace.ToVal.toVal service))

/-! ## `effect_program` -/

private def pureOfTermFuel : Nat → Term → CommandElabM (Term × Term)
  | 0, stx => throwErrorAt stx "effect_program: pure term nested too deeply"
  | fuel + 1, stx => do
  match stx with
  | `(($inner)) => pureOfTermFuel fuel inner
  | _ =>
    if stx.raw.isIdent then
      return (stx, ← `(Effect4.Target.EffectV4.PureTerm.var $(strLit stx.raw.getId.eraseMacroScopes.toString)))
    if let some n := stx.raw.isNatLit? then
      return (stx, ← `(Effect4.Target.EffectV4.PureTerm.nat $(natLit n)))
    if let some s := stx.raw.isStrLit? then
      return (stx, ← `(Effect4.Target.EffectV4.PureTerm.str $(strLit s)))
    match stx with
    | `($f:ident $args*) =>
        let rows ← args.mapM fun a => do pure (← pureOfTermFuel fuel a).2
        return (stx, ← `(Effect4.Target.EffectV4.PureTerm.app $(strLit f.getId.eraseMacroScopes.toString) $(← listLit rows)))
    | _ => throwErrorAt stx "effect_program: pure fragment not admitted at the lowering face: {stx}"

private def pureOfTerm (stx : Term) : CommandElabM (Term × Term) :=
  pureOfTermFuel typeFuel stx

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
          let bindRow : Term ← if isHole then `(none) else `(some $(strLit x.getId.eraseMacroScopes.toString))
          if isHole then discard := discard + 1
          stepRows := stepRows.push (← `(Effect4.Target.EffectV4.Step.perform $bindRow $(strLit opName) $(← listLit rows)))
          body := some (← `($call >>= fun $x => $rest))
      | _ => throwUnsupportedSyntax
    let some programTerm := body | throwError "effect_program: empty body"
    elabCommand (← `(set_option linter.unusedVariables false in
      def $name ($param : $paramTy) : Effects.Program $sigName $result := $programTerm))
    let scriptName := mkIdent (name.getId ++ `script)
    let stepList ← listLit stepRows.reverse
    elabCommand (← `(def $scriptName : Effect4.Target.EffectV4.Script := { family := $(strLit famId.getId.toString), name := $(strLit name.getId.toString), param := ($(strLit param.getId.toString), $(strLit (← tsOfType paramTy))), result := $(strLit (← tsOfType result)), steps := $stepList }))
    -- The per-program receipt: the value and the script perform the same
    -- operations in the same order (packet D5).
    let spellingName := mkIdent (famId.getId ++ `Name ++ `spelling)
    let answerDefaultName := mkIdent (famId.getId ++ `answerDefault)
    elabCommand (← `(example :
      Effect4.Target.EffectV4.performedNames (F := $famId) $spellingName $answerDefaultName
          ($name default)
        = Effect4.Target.EffectV4.Script.operationNames $scriptName := by rfl))

/-! ## `effect_atoms` -/

elab_rules : command
  | `(effect_atoms $name:ident where $atoms:atomOp*) => do
    let tableName := mkIdent (name.getId ++ `rows)
    let entryName := mkIdent (name.getId ++ `table)
    let evalName := mkIdent (name.getId ++ `eval)
    let sourceName := mkIdent (name.getId ++ `source)
    let mut rowTerms : Array Term := #[]
    let mut defs : Array (TSyntax `command) := #[]
    let mut evalAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
    for atom in atoms do
      match atom with
      | `(atomOp| | $atomName:ident ($x:ident : $requestTy:term) : $answerTy:term ⟪ $body:str ⟫ := $leanBody:term) => do
          unless Effect4.Target.EffectV4.bindingName atomName.getId.toString do
            throwErrorAt atomName "effect_atoms: `{atomName.getId}` is not a legal target identifier"
          unless Effect4.Target.EffectV4.bindingName x.getId.toString do
            throwErrorAt x "effect_atoms: `{x.getId}` is not a legal target identifier"
          defs := defs.push (← `(def $atomName ($x : $requestTy) : $answerTy := $leanBody))
          rowTerms := rowTerms.push (← `({ name := $(strLit atomName.getId.toString)
                                           binder := $(strLit x.getId.toString)
                                           request := $(strLit requestTy.raw.reprint.get!.trimAscii.toString)
                                           tsRequest := $(strLit (← tsOfType requestTy))
                                           answer := $(strLit answerTy.raw.reprint.get!.trimAscii.toString)
                                           tsAnswer := $(strLit (← tsOfType answerTy))
                                           body := $body : Effect4.Target.EffectV4.AtomRow }))
          evalAlts := evalAlts.push (← `(Lean.Parser.Term.matchAltExpr|
            | $(strLit atomName.getId.toString) =>
                fun value =>
                  match (Effect4.Target.EffectV4.OfVal.ofVal value : Option $requestTy) with
                  | Option.some argument => Effects.Trace.ToVal.toVal ($atomName argument)
                  | Option.none => Effects.Trace.Val.unit))
      | _ => throwUnsupportedSyntax
    for command in defs do elabCommand command
    evalAlts := evalAlts.push (← `(Lean.Parser.Term.matchAltExpr| | _ => fun _ => Effects.Trace.Val.unit))
    elabCommand (← `(def $tableName : List Effect4.Target.EffectV4.AtomRow := $(← listLit rowTerms)))
    elabCommand (← `(def $entryName : List (String × String × String) :=
      $tableName |>.map Effect4.Target.EffectV4.AtomRow.entry))
    elabCommand (← `(def $evalName : String → Effects.Trace.Val → Effects.Trace.Val :=
      fun name => match name with $evalAlts:matchAlt*))
    elabCommand (← `(def $sourceName : String := Effect4.Target.EffectV4.atomsModule $tableName))

end Effect4.Meta
