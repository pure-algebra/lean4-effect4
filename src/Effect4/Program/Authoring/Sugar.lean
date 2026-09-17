import Effect4.Program.Authoring.Lifts
import Effect4.Program.Authoring.Rows

/-!
# Program.Authoring.Sugar — binders over a fresh name, and derived forms

The native rows' wrappers (`Ref.make`, `Deferred.await`) are generated from the row table
(`Authoring/Rows.lean`) and the derived forms (`Forms.tapContinuation`, `Forms.ensuring`)
from the form table (`Authoring/Forms.lean`, each pinned against the printer's expansion);
this module is the five conveniences that are neither: the binders over a fresh name and
the short spellings `flatMap`, `andThen`, `map`, `ifElse`, `Src`-level functions over the
generated lifts with no constructor and no second expansion owner.
-/

namespace Effect4.Program.Authoring

open Effect4.Program

/-! ## Binders as Lean functions over a fresh name.

The fresh name is minted from the scope's length, so it can shadow nothing an author wrote
with a different spelling and resolves to itself at the nearest binder. -/

/-- `bindWith first (fun r => rest)` is `bind "_<level>" first rest` with `r` the variable. -/
def bindWith {Op : Type} (first : Src Op) (rest : TermSrc → Src Op) : Src Op := fun env p =>
  let x := "_" ++ toString env.names.length
  bind x first (rest (var x)) env p

/-- `bindName name first (fun x => rest)` is `bind name first (rest (var name))` with user-chosen name. -/
def bindName {Op : Type} (name : String) (first : Src Op) (rest : TermSrc → Src Op) : Src Op := fun env p =>
  bind name first (rest (var name)) env p

/-- `Effect.flatMap` under its Effect name. -/
def flatMap {Op : Type} (answer : String) (first rest : Src Op) : Src Op := bind answer first rest

/-- `Effect.andThen` with a discarded answer. -/
def andThen {Op : Type} (first rest : Src Op) : Src Op := bind "_" first rest

/-- `Effect.map` through a pure atom: `bind` then `succeed` of the atom applied to the answer. -/
def map {Op : Type} (atom : String) (effect : Src Op) : Src Op :=
  bindWith effect fun v => succeed (app atom [v])

/-- `Effect.if`: `if` is a Lean keyword. -/
def ifElse {Op : Type} (test : TermSrc) (thenB elseB : Src Op) : Src Op :=
  selectBool test thenB elseB

/-! ## Ergonomic literals and coercions for source terms -/

instance (n : Nat) : OfNat TermSrc n where
  ofNat := nat n

instance : Coe Nat TermSrc where
  coe := nat

instance : Coe String TermSrc where
  coe := str

instance : Coe Bool TermSrc where
  coe := bool

instance : Coe Unit TermSrc where
  coe _ := unit

/-! ## The `eff` authoring macro -/

open Lean Parser Term

/-- Formats a `Name` into a string identifier without calling `Name.toString`,
avoiding `Classical.choice` from string rendering. -/
def nameToString : Name → String
  | .anonymous => ""
  | .str .anonymous s => s
  | .str p s =>
    let ps := nameToString p
    if ps.isEmpty then s else ps ++ "." ++ s
  | .num p n =>
    let ps := nameToString p
    let ns := toString n
    if ps.isEmpty then ns else ps ++ "." ++ ns

/-- Extracts the string identifier from an `Ident` preserving hierarchical names
without calling `Name.toString`. -/
def identToString (x : Ident) : String :=
  nameToString x.getId

/-- Deconstructs a `doSeq` syntax node into its constituent `doElem` elements. -/
def getDoSeqElems (seq : TSyntax `Lean.Parser.Term.doSeq) : List (TSyntax `doElem) :=
  let raw := seq.raw
  if raw.getKind == `Lean.Parser.Term.doSeqBracketed then
    raw[1].getArgs.toList.map fun arg => ⟨arg[0]⟩
  else if raw.getKind == `Lean.Parser.Term.doSeqIndent then
    raw[0].getArgs.toList.map fun arg => ⟨arg[0]⟩
  else
    []

/-- Unnests a singleton `doNested` element if `eff do ...` was passed. -/
def unnestElems : List (TSyntax `doElem) → List (TSyntax `doElem)
  | [elem] =>
    if elem.raw.getKind == `Lean.Parser.Term.doNested then
      getDoSeqElems ⟨elem.raw[1]⟩
    else
      [elem]
  | elems => elems

/-- `eff { ... }` or `eff do ...` authoring block for `Src Op` programs. -/
syntax (name := effDo) "eff " doSeq : term

/-- Expands a list of `doElem` into an authored `Src Op` program. -/
def expandDoElems : List (TSyntax `doElem) → MacroM (TSyntax `term)
  | [] => `(succeed unit)
  | [elem] =>
    match elem with
    | `(doElem| return $t:term) => `(succeed $t)
    | `(doElem| return) => `(succeed unit)
    | `(doElem| if $c:term then $t:doSeq else $e:doSeq) =>
      `(if $c then eff $t else eff $e)
    | `(doElem| if $c:term then $t:doSeq) =>
      `(if $c then eff $t else succeed unit)
    | `(doElem| $e:term) => `($e)
    | `(doElem| let $_:term $[: $_:term]? ← $_:term) =>
      Macro.throwErrorAt elem "an eff block cannot end with a `let ←` binding"
    | `(doElem| let $_:term $[: $_:term]? := $_:term) =>
      Macro.throwErrorAt elem "an eff block cannot end with a `let :=` binding"
    | `(doElem| $_:term ← $_:term) =>
      Macro.throwErrorAt elem "an eff block cannot end with a `←` binding"
    | _ => Macro.throwErrorAt elem "unsupported final statement in eff block"
  | elem :: rest => do
    let restTerm ← expandDoElems rest
    match elem with
    | `(doElem| let $x:ident $[: $_:term]? ← $e:term) =>
      if x.getId == `_ then
        `(andThen $e $restTerm)
      else
        let s := identToString x
        `(bindName $(Syntax.mkStrLit s) $e (fun $x => $restTerm))
    | `(doElem| let _ $[: $_:term]? ← $e:term) =>
      `(andThen $e $restTerm)
    | `(doElem| let $pat:term $[: $_:term]? ← $_:term) =>
      Macro.throwErrorAt pat "destructuring pattern bindings are not supported in eff blocks; bind to a variable and project instead"
    | `(doElem| $x:ident ← $e:term) =>
      if x.getId == `_ then
        `(andThen $e $restTerm)
      else
        let s := identToString x
        `(bindName $(Syntax.mkStrLit s) $e (fun $x => $restTerm))
    | `(doElem| _ ← $e:term) =>
      `(andThen $e $restTerm)
    | `(doElem| $pat:term ← $_:term) =>
      Macro.throwErrorAt pat "destructuring pattern bindings are not supported in eff blocks; bind to a variable and project instead"
    | `(doElem| let $x:ident $[: $ty:term]? := $v:term) =>
      match ty with
      | some t => `(let $x : $t := $v; $restTerm)
      | none   => `(let $x := $v; $restTerm)
    | `(doElem| if $c:term then $t:doSeq else $e:doSeq) =>
      `(andThen (if $c then eff $t else eff $e) $restTerm)
    | `(doElem| if $c:term then $t:doSeq) =>
      `(andThen (if $c then eff $t else succeed unit) $restTerm)
    | `(doElem| return $t:term) =>
      `(andThen (succeed $t) $restTerm)
    | `(doElem| $e:term) =>
      `(andThen $e $restTerm)
    | _ => Macro.throwErrorAt elem "unsupported statement in eff block"

macro_rules
  | `(eff $seq:doSeq) => expandDoElems (unnestElems (getDoSeqElems seq))

end Effect4.Program.Authoring
