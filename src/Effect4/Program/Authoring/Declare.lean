module

public meta import Lean
public import Effect4.Program.Authoring
public import Effect4.Program.Authoring.Records
public import Effect4.Program.Authoring.Sugar

/-!
# Program.Authoring.Declare — declared records, tagged failures and host rows as commands

Three commands write the declarations that a program's author writes by hand today:
`eff_record`, `eff_failure` and `eff_rows`. Each expands to the same trees
(`Test/Program/AuthoringDeclare.lean` compares them; `Test/Dogfood/Scenario/Todo.lean` uses them).
Design: `docs/research/2026-10-07-packet-authoring-sugar.md`, sections 3.3 to 3.5.
-/

public meta section

namespace Effect4.Program.Authoring

open Lean

/-- One field of a declaration: a name and a type of the language. -/
declare_syntax_cat effField
syntax ident " : " term : effField

/-- `eff_record Name where f₁ : t₁, …`: the record's fields, its type, its constructor and one
projection for each field. -/
syntax (name := effRecordDecl) "eff_record " ident " where " sepBy1(effField, ", ") : command

/-- `eff_failure Name where f₁ : t₁, …`: a tagged failure as a record whose first field is the
tag. It declares the fields, the type, the constructor, the test of a handler and `raise`.
`eff_failure Name message` is a tagged failure whose one field is its message: the pair of the
tag and the message (decisions row 120). The word `message` is no reserved keyword. -/
syntax (name := effFailureDecl) "eff_failure " ident " where " sepBy1(effField, ", ") : command
syntax (name := effMessageDecl) "eff_failure " ident &" message" : command

/-- One row of a block: its name, its request type and its answer type. -/
declare_syntax_cat effRow
syntax ident "(" term ")" " : " term : effRow

/-- `eff_rows Name error E cite "…" where r₁(request₁) : answer₁, …`: one host row for each
entry, spelled `Name.rᵢ`, with the block's error column and citation. It declares each row
under `Name.row`, the list `Name.rows` in the written order, and one call of each row under
`Name`. The words `error` and `cite` are no reserved keywords. -/
syntax (name := effRowsDecl) "eff_rows " ident &" error " term:max &" cite " str " where "
  sepBy1(effRow, ", ") : command

/-- The fields of a declaration, each as its name and its type. -/
def parseEffFields (fields : Array Lean.Syntax) :
    Lean.MacroM (Array (Lean.Ident × Lean.TSyntax `term)) :=
  fields.mapM fun f => match f with
    | `(effField| $x:ident : $t:term) => pure (x, t)
    | _ => Lean.Macro.throwUnsupported

/-- The type `TermSrc → … → result`, with one argument for each field. -/
def termArrows (count : Nat) (result : Lean.TSyntax `term) : Lean.MacroM (Lean.TSyntax `term) :=
  match count with
  | 0 => pure result
  | n + 1 => do
    let rest ← termArrows n result
    `(Effect4.Program.Authoring.TermSrc → $rest)

macro_rules
  | `(eff_record $name:ident where $fields,*) => do
    let parsed ← parseEffFields fields.getElems
    let n := name.getId
    let fieldsId := mkIdent (n ++ `fields)
    let tyId := mkIdent (n ++ `ty)
    let mkId := mkIdent (n ++ `mk)
    let entries ← parsed.mapM fun (x, t) =>
      `(($(Syntax.mkStrLit (identToString x)), false, ($t : Effect4.Program.Ty)))
    let args : TSyntaxArray `term := parsed.map fun (x, _) => ⟨x.raw⟩
    let present ← parsed.mapM fun (x, _) => `(($(Syntax.mkStrLit (identToString x)), $x))
    let mkTy ← termArrows parsed.size (← `(Effect4.Program.Authoring.TermSrc))
    let decls ← parsed.mapM fun (x, _) =>
      `(def $(mkIdent (n ++ x.getId)) (self : Effect4.Program.Authoring.TermSrc) :
            Effect4.Program.Authoring.TermSrc :=
          Effect4.Program.Authoring.field self $(Syntax.mkStrLit (identToString x)))
    let d1 ← `(def $fieldsId : List (String × Bool × Effect4.Program.Ty) := [$entries,*])
    let d2 ← `(def $tyId : Effect4.Program.Ty := Effect4.Program.Ty.record $fieldsId)
    let d3 ← `(def $mkId : $mkTy := fun $args* =>
        Effect4.Program.Authoring.record $fieldsId [$present,*])
    return mkNullNode (#[d1.raw, d2.raw, d3.raw] ++ decls.map (·.raw))
  | `(eff_failure $name:ident where $fields,*) => do
    let parsed ← parseEffFields fields.getElems
    let n := name.getId
    let tag := Syntax.mkStrLit (identToString name)
    let fieldsId := mkIdent (n ++ `fields)
    let tyId := mkIdent (n ++ `ty)
    let mkId := mkIdent (n ++ `mk)
    let isId := mkIdent (n ++ `is)
    let raiseId := mkIdent (n ++ `raise)
    let entries ← parsed.mapM fun (x, t) =>
      `(($(Syntax.mkStrLit (identToString x)), false, ($t : Effect4.Program.Ty)))
    let args : TSyntaxArray `term := parsed.map fun (x, _) => ⟨x.raw⟩
    let present ← parsed.mapM fun (x, _) => `(($(Syntax.mkStrLit (identToString x)), $x))
    let mkTy ← termArrows parsed.size (← `(Effect4.Program.Authoring.TermSrc))
    let raiseTy ← termArrows parsed.size (← `(Effect4.Program.Authoring.Src Op))
    let d1 ← `(def $fieldsId : List (String × Bool × Effect4.Program.Ty) :=
        ("_tag", false, Effect4.Program.Ty.lit $tag) :: [$entries,*])
    let d2 ← `(def $tyId : Effect4.Program.Ty := Effect4.Program.Ty.record $fieldsId)
    let d3 ← `(def $mkId : $mkTy := fun $args* =>
        Effect4.Program.Authoring.record $fieldsId
          (("_tag", Effect4.Program.Authoring.str $tag) :: [$present,*]))
    let d4 ← `(def $isId (failure : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.TermSrc :=
        Effect4.Program.Authoring.app "tagIs" [Effect4.Program.Authoring.str $tag, failure])
    let d5 ← `(def $raiseId {Op : Type} : $raiseTy := fun $args* =>
        Effect4.Program.Authoring.fail ($mkId $args*))
    return mkNullNode #[d1.raw, d2.raw, d3.raw, d4.raw, d5.raw]
  | `(eff_failure $name:ident message) => do
    let n := name.getId
    let tag := Syntax.mkStrLit (identToString name)
    let tyId := mkIdent (n ++ `ty)
    let mkId := mkIdent (n ++ `mk)
    let isId := mkIdent (n ++ `is)
    let raiseId := mkIdent (n ++ `raise)
    let d1 ← `(def $tyId : Effect4.Program.Ty :=
        Effect4.Program.Ty.prod (Effect4.Program.Ty.lit $tag) Effect4.Program.Ty.string)
    let d2 ← `(def $mkId (text : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.TermSrc :=
        Effect4.Program.Authoring.app "pair" [Effect4.Program.Authoring.str $tag, text])
    let d3 ← `(def $isId (failure : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.TermSrc :=
        Effect4.Program.Authoring.app "tagIs" [Effect4.Program.Authoring.str $tag, failure])
    let d4 ← `(def $raiseId {Op : Type} (text : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.Src Op :=
        Effect4.Program.Authoring.fail ($mkId text))
    return mkNullNode #[d1.raw, d2.raw, d3.raw, d4.raw]
  | `(eff_rows $name:ident error $err:term cite $cite:str where $rows,*) => do
    let n := name.getId
    let parsed ← rows.getElems.mapM fun r => match r with
      | `(effRow| $x:ident ($req:term) : $ans:term) => pure (x, req, ans)
      | _ => Macro.throwUnsupported
    let mut out : Array Syntax := #[]
    let mut rowIds : Array (TSyntax `term) := #[]
    for (x, req, ans) in parsed do
      let rowId := mkIdent (n ++ `row ++ x.getId)
      let callId := mkIdent (n ++ x.getId)
      let spelling := Syntax.mkStrLit (identToString name ++ "." ++ identToString x)
      rowIds := rowIds.push ⟨rowId.raw⟩
      out := out.push (← `(def $rowId : Effect4.Program.Authoring.RowDef :=
        Effect4.Program.Authoring.Row.host $spelling $req $ans $err $cite)).raw
      out := out.push (← `(def $callId (request : Effect4.Program.Authoring.TermSrc) :
          Effect4.Program.Authoring.Src Effect4.Program.NativeOp :=
        Effect4.Program.Authoring.Row.call $rowId request)).raw
    out := out.push (← `(def $(mkIdent (n ++ `rows)) : List Effect4.Program.Authoring.RowDef :=
      [$rowIds,*])).raw
    return mkNullNode out

end Effect4.Program.Authoring
