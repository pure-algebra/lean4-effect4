import Effect4.Codegen.Read
import Effect4.Codegen.EraseTermTypes

/-!
# Codegen.EraseTypes — remove inferred call arguments before the existing reader

The existing template table identifies each capture's sort and printer depth.
The normalizer maps those captures and reinstantiates the same template.
Program captures recurse through their families; pure terms use the target-syntax fold.
Layer captures restart at zero through `argDepth`.
Complete row calls identify inferred arguments after their term children erase.
Operation-carried and row-declared arguments remain in the syntax.
The existing reader consumes the result; exactness refers to that erased input.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open TypeScript
open Effect4.Program
open Template Templates

variable {Op : Type}

/-- The node inverse increases no syntax size. It serves the template capture recursion
of the proposed typed-print erasure claim (exact-codecs, R8). -/
theorem eraseNode_size (n : Nat) (x : Expr) :
    sizeOf (EraseTermTypes.eraseNode n x) ≤ sizeOf x := by
  fun_cases EraseTermTypes.eraseNode n x <;>
    simp only [Expr.call.sizeOf_spec, Expr.generic.sizeOf_spec, Expr.ident.sizeOf_spec,
      Expr.arrow.sizeOf_spec, Expr.lambda.sizeOf_spec, Expr.str.sizeOf_spec,
      Expr.arrowBlock.sizeOf_spec, TypeScript.Stmt.exprStmt.sizeOf_spec,
      TypeScript.Stmt.ret.sizeOf_spec,
      List.cons.sizeOf_spec, List.nil.sizeOf_spec, Nat.le_refl] <;> omega

/-- Remove a generic call head only when the existing reader recognizes the bare operation
and that operation owns no type argument. `readPerform` also checks the complete call shape.
`splitHeadTypes` restores method syntax, rather than leaving a member as a function head. -/
def eraseRowJoin (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (x : Expr) : Expr :=
  match splitHeadTypes x with
  | none => x
  | some (bare, _) =>
    match readPerform classes sig spell n bare with
    | .ok (.perform op _) =>
      if (sig.typeArgsOf op).isEmpty && (sig.rowOf op).typeArgs.isEmpty then bare else x
    | _ => x

/-- At a program row, the head retains its type arguments while its request, receiver,
trailing values and binder function use the term inverse. -/
def eraseRowChildren (n : Nat) : Expr → Expr
  | .call head args =>
    .call (EraseTermTypes.eraseTerm n head) (args.map (EraseTermTypes.eraseTerm n))
  | .method receiver name args =>
    .method (EraseTermTypes.eraseTerm n receiver) name (args.map (EraseTermTypes.eraseTerm n))
  | x => x

/-- One target capture follows the existing row's sort and printer depth.
The callback keeps the original membership fact used by the reader's size laws. -/
def eraseCapture (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt) :
    { pair : Nat × Arg // pair ∈ σ } → Arg :=
  fun ⟨(i, capture), hi⟩ =>
    let sort := sorts[i]?
    let depth := argDepth row.fam (sort.getD .op) n (row.out.levelAt i)
    match capture with
    | .expr y => match sort with
      | some (.child fam) => .expr (child fam depth y i hi)
      | some .term | some .optTerm => .expr (EraseTermTypes.eraseTerm depth y)
      | some .cause => .expr (EraseTermTypes.eraseCause depth y)
      | _ => .expr y
    | .exprs ys => match sort with
      | some (.child fam) => .exprs (children fam depth ys i hi)
      | _ => .exprs ys
    | .stmts ss => match sort with
      | some (.child .stmts) => .stmts (block depth ss i hi)
      | _ => .stmts ss
    | a => a

/-- Map target captures without changing their keys or their first-match lookup order. -/
def eraseCaptures (row : Templates.Row) (sorts : List ArgSort) (n : Nat) (σ : Subst)
    (child : EffFam → Nat → (y : Expr) → (i : Nat) → (i, .expr y) ∈ σ → Expr)
    (children : EffFam → Nat → (ys : List Expr) → (i : Nat) → (i, .exprs ys) ∈ σ → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, .stmts ss) ∈ σ → List TypeScript.Stmt) :
    Subst :=
  σ.attach.map fun entry => (entry.val.1, eraseCapture row sorts n σ child children block entry)

/-- One expression template, at the reader's existing matching and family recursion seam.
This maps target syntax captures without constructing an `Eff` program. -/
def eraseExprRow (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (fam : EffFam) (n : Nat) (x : Expr)
    (row : Templates.Row)
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf x → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf x → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf x → List TypeScript.Stmt)
    (same : (fam' : EffFam) → famRank fam' < famRank fam → Nat → Option Expr) : Option Expr :=
  if row.fam = fam then
    match row.out with
    | .tpl t =>
      match hσ : matchT n t x with
      | none => none
      | some σ =>
        match argSorts fam row.ctor with
        | none => none
        | some sorts =>
          if hr : t.rigid = true then
            some ((inst n (eraseCaptures row sorts n σ
              (fun fam' d y i hy => child fam' d y (match_below n t x σ hr hσ (i, .expr y) hy))
              (fun fam' d ys i hy => children fam' d ys (match_below n t x σ hr hσ (i, .exprs ys) hy))
              (fun d ss i hy => block d ss (match_below n t x σ hr hσ (i, .stmts ss) hy))) t).getD x)
          else match sorts with
            | [.child fam'] =>
              if hk : famRank fam' < famRank fam then
                same fam' hk (argDepth fam (.child fam') n 0)
              else none
            | [sort] => some (match sort with
              | .term | .optTerm => EraseTermTypes.eraseTerm (argDepth fam sort n 0) x
              | .cause => EraseTermTypes.eraseCause (argDepth fam sort n 0) x
              | _ => x)
            | _ => none
    | .rowCall => match fam with
      | .eff =>
        let erased := eraseRowJoin classes sig spell n (eraseRowChildren n x)
        match readPerform classes sig spell n erased with
        | .ok _ => some erased
        | .error _ => none
      | _ => none
    | _ => none
  else none

/-- A statement template maps captures and returns its declaration count.
The statement spine threads that count, as the printer and reader do. -/
def eraseStmtRow (n : Nat) (s : TypeScript.Stmt) (row : Templates.Row)
    (child : EffFam → Nat → (y : Expr) → sizeOf y < sizeOf s → Expr)
    (children : EffFam → Nat → (ys : List Expr) → sizeOf ys < sizeOf s → List Expr)
    (block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf s → List TypeScript.Stmt) :
    Option (TypeScript.Stmt × Nat) :=
  if row.fam = .stmt then
    match row.out with
    | .stmt t =>
      match hσ : matchStmt n t s with
      | none => none
      | some σ =>
        match argSorts .stmt row.ctor with
        | none => none
        | some sorts =>
          some ((instStmt n (eraseCaptures row sorts n σ
            (fun fam' d y i hy => child fam' d y (matchStmt_below n t s σ hσ (i, .expr y) hy))
            (fun fam' d ys i hy => children fam' d ys (matchStmt_below n t s σ hσ (i, .exprs ys) hy))
            (fun d ss i hy => block d ss (matchStmt_below n t s σ hσ (i, .stmts ss) hy))) t).getD s,
            t.declares)
    | _ => none
  else none

mutual
  /-- The family inverse uses the existing template order and capture depth laws. -/
  def eraseT (classes : Classes.Classes) (sig : Signature Op)
      (spell : String → List String → Option Op) (fam : EffFam) (n : Nat) (x : Expr) : Option Expr :=
    let y := EraseTermTypes.eraseNode n x
    (Templates.table.findSome? fun row => eraseExprRow classes sig spell fam n y row
      (fun fam' d child _ => (eraseT classes sig spell fam' d child).getD child)
      (fun fam' d children _ => eraseSpine classes sig spell fam' d children)
      (fun d body _ => eraseStmts classes sig spell d body)
      (fun fam' _ d => eraseT classes sig spell fam' d y))
  termination_by (sizeOf x, famRank fam)
  decreasing_by
    all_goals dsimp (config := { zetaDelta := true, failIfUnchanged := false }) only at *
    all_goals have h := eraseNode_size n x
    all_goals simp only [Prod.lex_def]
    · omega
    · omega
    · omega
    · rcases Nat.lt_or_eq_of_le h with smaller | equal
      · exact Or.inl smaller
      · refine Or.inr ⟨equal, ?_⟩
        assumption

  /-- Program and layer lists recurse through their corresponding expression families. -/
  def eraseSpine (classes : Classes.Classes) (sig : Signature Op)
      (spell : String → List String → Option Op) (fam : EffFam) (n : Nat) : List Expr → List Expr
    | [] => []
    | x :: xs =>
      (eraseT classes sig spell (if fam = .layers then .layer else .eff) n x).getD x ::
        eraseSpine classes sig spell fam n xs
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals simp only [Prod.lex_def, List.cons.sizeOf_spec] <;> omega

  /-- Statement templates identify their captured programs and declaration counts. -/
  def eraseStmts (classes : Classes.Classes) (sig : Signature Op)
      (spell : String → List String → Option Op) (n : Nat) : List TypeScript.Stmt → List TypeScript.Stmt
    | [] => []
    | s :: ss =>
      let head := Templates.table.findSome? fun row => eraseStmtRow n s row
        (fun fam' d child _ => (eraseT classes sig spell fam' d child).getD child)
        (fun fam' d children _ => eraseSpine classes sig spell fam' d children)
        (fun d body _ => eraseStmts classes sig spell d body)
      match head with
      | some (s', declared) => s' :: eraseStmts classes sig spell (n + declared) ss
      | none => s :: eraseStmts classes sig spell n ss
  termination_by ss => (sizeOf ss, 0)
  decreasing_by all_goals simp only [Prod.lex_def, List.cons.sizeOf_spec] <;> omega
end

/-- The named erasure before the typed reader. It changes approved inferred call arguments
only; the ordinary reader retains ownership of every other syntax check. -/
def eraseJoinArgs (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (x : Expr) : Expr :=
  (eraseT classes sig spell .eff n x).getD x

/-- The existing reader after erasure. Exactness is stated modulo `eraseJoinArgs`, never as
raw equality with every source spelling carrying explicit type arguments. -/
def readTyped (classes : Classes.Classes) (sig : Signature Op)
    (spell : String → List String → Option Op) (n : Nat) (x : Expr) :
    Except ReadRefusal (Eff Op) :=
  readEff classes sig spell n (eraseJoinArgs classes sig spell n x)

end Effect4.Codegen
