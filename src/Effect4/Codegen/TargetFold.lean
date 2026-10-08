import TypeScript.Syntax

/-!
# Codegen.TargetFold — a fold of the pinned target syntax

The target package exposes a nested recursor that Lean cannot compile directly. This algebra
and its structural fold keep that constructor inventory in one place. `Codegen.mapCalls`
is its consumer: reconstruction at every field except a call head. Types and parameter
annotations are scalar data. No target program representation is added.
-/

set_option autoImplicit false

namespace Effect4.Codegen.TargetFold

open TypeScript

/-- One field per expression, statement, and object-entry constructor of the target syntax.
The erasure fold supplies the constructor algebra with one changed call field. -/
structure Algebra (E S O : Type) where
  expr_ident : String → E
  expr_str : String → E
  expr_int : Int → E
  expr_float64Bits : UInt64 → E
  expr_bool : Bool → E
  expr_jsNull : E
  expr_call : E → (List E) → E
  expr_object : (List (String × E)) → E
  expr_objectML : (List (String × E)) → E
  expr_objectQuoted : (List (String × E)) → E
  expr_objectQuotedML : (List (String × E)) → E
  expr_objectFromEntries : (List (String × E)) → E
  expr_arr : (List E) → E
  expr_arrow : (Option TypeRef) → E → E
  expr_generic : E → (List TypeRef) → E
  expr_lambda : (List Parameter) → E → (Option TypeRef) → E
  expr_method : E → String → (List E) → E
  expr_member : E → String → E
  expr_generator : (List S) → E
  expr_cond : E → E → E → E
  expr_arrowBlock : (List Parameter) → (List S) → (Option TypeRef) → E
  expr_index : E → E → E
  expr_new : E → (List E) → E
  expr_objectWith : KeyForm → (List O) → E
  stmt_constYield : String → E → (Option TypeRef) → S
  stmt_ret : E → S
  stmt_yieldDiscard : E → S
  stmt_letDefinite : String → TypeRef → S
  stmt_letInit : String → E → (Option TypeRef) → S
  stmt_assign : String → E → S
  stmt_whileTrue : (Option String) → (List S) → S
  stmt_switch : E → (List (Nat × List S)) → S
  stmt_ifElse : E → (List S) → (List S) → S
  stmt_labelled : String → (List S) → S
  stmt_scopedGen : String → (List S) → E → S
  stmt_scopedGenMasked : String → (List S) → E → S
  stmt_breakTo : (Option String) → S
  stmt_continueTo : (Option String) → S
  stmt_exprStmt : E → S
  entry_property : String → E → O
  entry_spread : E → O

variable {E S O : Type}

mutual
  /-- The Expr component of the target-syntax fold. -/
  def expr (alg : Algebra E S O) : Expr → E
    | .ident name => alg.expr_ident name
    | .str value => alg.expr_str value
    | .int value => alg.expr_int value
    | .float64Bits bits => alg.expr_float64Bits bits
    | .bool value => alg.expr_bool value
    | .jsNull => alg.expr_jsNull
    | .call fn args => alg.expr_call (expr alg fn) (exprs alg args)
    | .object fields => alg.expr_object (TargetFold.fields alg fields)
    | .objectML fields => alg.expr_objectML (TargetFold.fields alg fields)
    | .objectQuoted fields => alg.expr_objectQuoted (TargetFold.fields alg fields)
    | .objectQuotedML fields => alg.expr_objectQuotedML (TargetFold.fields alg fields)
    | .objectFromEntries fields => alg.expr_objectFromEntries (TargetFold.fields alg fields)
    | .arr items => alg.expr_arr (exprs alg items)
    | .arrow returnType body => alg.expr_arrow returnType (expr alg body)
    | .generic fn typeArgs => alg.expr_generic (expr alg fn) typeArgs
    | .lambda params body returnType => alg.expr_lambda params (expr alg body) returnType
    | .method target name args => alg.expr_method (expr alg target) name (exprs alg args)
    | .member target name => alg.expr_member (expr alg target) name
    | .generator body => alg.expr_generator (stmts alg body)
    | .cond test thenBranch elseBranch => alg.expr_cond (expr alg test) (expr alg thenBranch) (expr alg elseBranch)
    | .arrowBlock params body returnType => alg.expr_arrowBlock params (stmts alg body) returnType
    | .index target key => alg.expr_index (expr alg target) (expr alg key)
    | .new callee args => alg.expr_new (expr alg callee) (exprs alg args)
    | .objectWith keys entries => alg.expr_objectWith keys (TargetFold.entries alg entries)
  /-- The Stmt component of the target-syntax fold. -/
  def stmt (alg : Algebra E S O) : Stmt → S
    | .constYield name value type => alg.stmt_constYield name (expr alg value) type
    | .ret value => alg.stmt_ret (expr alg value)
    | .yieldDiscard value => alg.stmt_yieldDiscard (expr alg value)
    | .letDefinite name type => alg.stmt_letDefinite name type
    | .letInit name value type => alg.stmt_letInit name (expr alg value) type
    | .assign name value => alg.stmt_assign name (expr alg value)
    | .whileTrue label body => alg.stmt_whileTrue label (stmts alg body)
    | .switch scrutinee cases_ => alg.stmt_switch (expr alg scrutinee) (branches alg cases_)
    | .ifElse condition thenBranch elseBranch => alg.stmt_ifElse (expr alg condition) (stmts alg thenBranch) (stmts alg elseBranch)
    | .labelled label body => alg.stmt_labelled label (stmts alg body)
    | .scopedGen name body onExit => alg.stmt_scopedGen name (stmts alg body) (expr alg onExit)
    | .scopedGenMasked name body onExit => alg.stmt_scopedGenMasked name (stmts alg body) (expr alg onExit)
    | .breakTo label => alg.stmt_breakTo label
    | .continueTo label => alg.stmt_continueTo label
    | .exprStmt value => alg.stmt_exprStmt (expr alg value)
  /-- The ObjectEntry component of the target-syntax fold. -/
  def entry (alg : Algebra E S O) : ObjectEntry → O
    | .property name value => alg.entry_property name (expr alg value)
    | .spread value => alg.entry_spread (expr alg value)
  /-- The list component for Expr. -/
  def exprs (alg : Algebra E S O) : List Expr → List E
    | [] => []
    | x :: xs => expr alg x :: exprs alg xs
  /-- The list component for Stmt. -/
  def stmts (alg : Algebra E S O) : List Stmt → List S
    | [] => []
    | x :: xs => stmt alg x :: stmts alg xs
  /-- The list component for ObjectEntry. -/
  def entries (alg : Algebra E S O) : List ObjectEntry → List O
    | [] => []
    | x :: xs => entry alg x :: entries alg xs
  /-- Object fields, retaining names and order. -/
  def fields (alg : Algebra E S O) : List (String × Expr) → List (String × E)
    | [] => []
    | (name, value) :: rest => (name, expr alg value) :: fields alg rest
  /-- Switch branches, retaining tags and order. -/
  def branches (alg : Algebra E S O) : List (Nat × List Stmt) → List (Nat × List S)
    | [] => []
    | (tag, body) :: rest => (tag, stmts alg body) :: branches alg rest
end

end Effect4.Codegen.TargetFold

namespace Effect4.Codegen

open TypeScript

/-- Read every child at the same binder depth. -/
def atDepth {α : Type} (n : Nat) (children : List (Nat → α)) : List α :=
  children.map fun child => child n

/-- A statement spine threads the depth that each declaration returns. -/
def statementSpine : List (Nat → Stmt × Nat) → Nat → List Stmt × Nat
  | [], n => ([], n)
  | statement :: rest, n =>
    let (head, next) := statement n
    let (tail, finalDepth) := statementSpine rest next
    (head :: tail, finalDepth)

/-- The constructor algebra with a changed call field. Its consumer is `eraseJoinArgs`.
Every other expression reconstructs itself from the folded children. -/
def callAlgebra (call : Nat → Expr → Expr) :
    TargetFold.Algebra (Nat → Expr) (Nat → Stmt × Nat) (Nat → ObjectEntry) where
  expr_ident name _ := .ident name
  expr_str value _ := .str value
  expr_int value _ := .int value
  expr_float64Bits bits _ := .float64Bits bits
  expr_bool value _ := .bool value
  expr_jsNull _ := .jsNull
  expr_call fn args n := call n (.call (fn n) (atDepth n args))
  expr_object fields n := .object (fields.map fun (name, value) => (name, value n))
  expr_objectML fields n := .objectML (fields.map fun (name, value) => (name, value n))
  expr_objectQuoted fields n := .objectQuoted (fields.map fun (name, value) => (name, value n))
  expr_objectQuotedML fields n := .objectQuotedML (fields.map fun (name, value) => (name, value n))
  expr_objectFromEntries fields n := .objectFromEntries (fields.map fun (name, value) => (name, value n))
  expr_arr items n := .arr (atDepth n items)
  expr_arrow ty body n := .arrow ty (body n)
  expr_generic fn types n := .generic (fn n) types
  expr_lambda params body ty n := .lambda params (body (n + params.length)) ty
  expr_method receiver name args n := .method (receiver n) name (atDepth n args)
  expr_member receiver name n := .member (receiver n) name
  expr_generator body n := .generator (statementSpine body n).1
  expr_cond test yes no n := .cond (test n) (yes n) (no n)
  expr_arrowBlock params body ty n := .arrowBlock params (statementSpine body (n + params.length)).1 ty
  expr_index target key n := .index (target n) (key n)
  expr_new callee args n := .new (callee n) (atDepth n args)
  expr_objectWith keys entries n := .objectWith keys (atDepth n entries)
  stmt_constYield name value ty n := (.constYield name (value n) ty, n + 1)
  stmt_ret value n := (.ret (value n), n)
  stmt_yieldDiscard value n := (.yieldDiscard (value n), n)
  stmt_letDefinite name ty n := (.letDefinite name ty, n + 1)
  stmt_letInit name value ty n := (.letInit name (value n) ty, n + 1)
  stmt_assign name value n := (.assign name (value n), n)
  stmt_whileTrue label body n := (.whileTrue label (statementSpine body n).1, n)
  stmt_switch scrutinee branches n :=
    (.switch (scrutinee n) (branches.map fun (tag, body) => (tag, (statementSpine body n).1)), n)
  stmt_ifElse test yes no n := (.ifElse (test n) (statementSpine yes n).1 (statementSpine no n).1, n)
  stmt_labelled label body n := (.labelled label (statementSpine body n).1, n)
  stmt_scopedGen name body onExit n := (.scopedGen name (statementSpine body n).1 (onExit n), n + 1)
  stmt_scopedGenMasked name body onExit n :=
    (.scopedGenMasked name (statementSpine body n).1 (onExit n), n + 1)
  stmt_breakTo label n := (.breakTo label, n)
  stmt_continueTo label n := (.continueTo label, n)
  stmt_exprStmt value n := (.exprStmt (value n), n)
  entry_property name value n := .property name (value n)
  entry_spread value n := .spread (value n)

/-- The target-syntax fold with the call transformation and lexical binder depth. -/
def mapCalls (call : Nat → Expr → Expr) : Expr → Nat → Expr :=
  TargetFold.expr (callAlgebra call)

end Effect4.Codegen
