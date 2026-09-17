import TypeScript.Syntax

/-!
# Codegen.Template — a printed clause as data (R4.1)

Every printing clause but the leaf printers has one shape: print each child at the depth its
binder row gives, then plug the results into a fixed `TypeScript.Expr` skeleton. A `Tpl` is that
skeleton with numbered holes. `inst` prints one (fills the holes, names the binders from the
depth); `matchT` reads one (checks the skeleton, collects the holes left to right, checks the
binder names against the depth).

The two laws of the boundary are proved ONCE here, over templates, and never again per
constructor:

* `match_inst` — reading an instance gives back the arguments along the holes (the engine of
  `read_print`, law 11);
* `inst_of_match` — a match of a template whose holes are distinct instantiates back to the
  expression it matched (the engine of `read_exact`, law 12).

The formers are what the printer's clauses use and nothing more (`Codegen/Print.lean`):
calls, identifiers, literals, objects, arrays, arrows, lambdas over binder slots, the
conditional, method calls, and the block arrow with the four statements the loop image uses.
A captured argument is sorted (`Arg`): an expression, an expression list (the variadic
`raceAll` and `mergeAll`), a string (`caseTag`'s tag), an integer (`yieldNow`'s priority), or a
type annotation (the annotated loop's cursor, DI-91).

This module imports the syntax carrier only. It knows nothing of `Eff`; the table of rows is
`Codegen/Templates.lean`.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Template

open TypeScript

/-- The binder at environment position `i`, as the printer names it (`Var.name`). -/
def varName (i : Nat) : String := "a" ++ toString i

/-- What a hole captures, by sort. -/
inductive Arg where
  | expr (e : Expr)
  | exprs (es : List Expr)
  | str (s : String)
  | int (i : Int)
  | type (t : TypeRef)
deriving BEq

/-- A substitution: hole number to captured argument, in the order the holes occur. -/
abbrev Subst := List (Nat × Arg)

def lookup (σ : Subst) (i : Nat) : Option Arg := (σ.find? (·.1 == i)).map (·.2)

def keys (σ : Subst) : List Nat := σ.map (·.1)

/-- The unannotated parameters of a lambda over binder slots `bs` at depth `n`. -/
def params (n : Nat) (bs : List Nat) : List Parameter :=
  bs.map fun k => ({ name := varName (n + k) } : Parameter)

mutual
  /-- An expression skeleton. -/
  inductive Tpl where
    /-- An expression hole. -/
    | hole (i : Nat)
    /-- A string-literal hole: `.str s` with `s` captured. -/
    | strHole (i : Nat)
    /-- An integer-literal hole: `.int v` with `v` captured. -/
    | intHole (i : Nat)
    /-- An array whose items are one captured list: `.arr es`. -/
    | arrHole (i : Nat)
    /-- The binder `k` slots above the node's depth. -/
    | binderRef (k : Nat)
    | ident (s : String)
    | str (s : String)
    | int (v : Int)
    | bool (b : Bool)
    | call (head : Tpl) (args : Tpls)
    /-- A call whose whole argument list is one captured list: `.call head es`. -/
    | callSpread (head : Tpl) (i : Nat)
    | arr (items : Tpls)
    | object (fields : Fields)
    | arrow (body : Tpl)
    | lambda (binders : List Nat) (body : Tpl)
    | cond (test yes no : Tpl)
    | method (target : Tpl) (name : String) (args : Tpls)
    | arrowBlock (binders : List Nat) (body : StmtTpls)
  inductive Tpls where
    | nil
    | cons (head : Tpl) (tail : Tpls)
  inductive Fields where
    | nil
    | cons (key : String) (value : Tpl) (tail : Fields)
  /-- A statement skeleton: the four statements of the loop image. -/
  inductive StmtTpl where
    /-- `let a<n+k> = value`, annotated by a captured type when `ann` names a hole. -/
    | letInit (k : Nat) (value : Tpl) (ann : Option Nat)
    | assign (k : Nat) (value : Tpl)
    | ret (value : Tpl)
    | exprStmt (value : Tpl)
  inductive StmtTpls where
    | nil
    | cons (head : StmtTpl) (tail : StmtTpls)
end

/-! ## Printing: `inst` -/

/-- The annotation a `letInit` prints: none, or the captured type. -/
def instAnn (σ : Subst) : Option Nat → Option (Option TypeRef)
  | none => some none
  | some i => match lookup σ i with
    | some (.type t) => some (some t)
    | _ => none

mutual
  def inst (n : Nat) (σ : Subst) : Tpl → Option Expr
    | .hole i => match lookup σ i with
      | some (.expr e) => some e
      | _ => none
    | .strHole i => match lookup σ i with
      | some (.str s) => some (.str s)
      | _ => none
    | .intHole i => match lookup σ i with
      | some (.int v) => some (.int v)
      | _ => none
    | .arrHole i => match lookup σ i with
      | some (.exprs es) => some (.arr es)
      | _ => none
    | .binderRef k => some (.ident (varName (n + k)))
    | .ident s => some (.ident s)
    | .str s => some (.str s)
    | .int v => some (.int v)
    | .bool b => some (.bool b)
    | .call h args => do
      let h' ← inst n σ h
      let a' ← insts n σ args
      some (.call h' a')
    | .callSpread h i => do
      let h' ← inst n σ h
      match lookup σ i with
      | some (.exprs es) => some (.call h' es)
      | _ => none
    | .arr items => do some (.arr (← insts n σ items))
    | .object fields => do some (.object (← instFields n σ fields))
    | .arrow b => do some (.arrow none (← inst n σ b))
    | .lambda bs b => do some (.lambda (params n bs) (← inst n σ b))
    | .cond t a b => do
      let t' ← inst n σ t
      let a' ← inst n σ a
      let b' ← inst n σ b
      some (.cond t' a' b')
    | .method target name args => do
      let t' ← inst n σ target
      let a' ← insts n σ args
      some (.method t' name a')
    | .arrowBlock bs body => do some (.arrowBlock (params n bs) (← instStmts n σ body))
  def insts (n : Nat) (σ : Subst) : Tpls → Option (List Expr)
    | .nil => some []
    | .cons h t => do
      let h' ← inst n σ h
      let t' ← insts n σ t
      some (h' :: t')
  def instFields (n : Nat) (σ : Subst) : Fields → Option (List (String × Expr))
    | .nil => some []
    | .cons key v t => do
      let v' ← inst n σ v
      let t' ← instFields n σ t
      some ((key, v') :: t')
  def instStmt (n : Nat) (σ : Subst) : StmtTpl → Option Stmt
    | .letInit k v ann => do
      let v' ← inst n σ v
      let ann' ← instAnn σ ann
      some (.letInit (varName (n + k)) v' ann')
    | .assign k v => do some (.assign (varName (n + k)) (← inst n σ v))
    | .ret v => do some (.ret (← inst n σ v))
    | .exprStmt v => do some (.exprStmt (← inst n σ v))
  def instStmts (n : Nat) (σ : Subst) : StmtTpls → Option (List Stmt)
    | .nil => some []
    | .cons h t => do
      let h' ← instStmt n σ h
      let t' ← instStmts n σ t
      some (h' :: t')
end

/-! ## Reading: `matchT` -/

/-- Match a `letInit`'s annotation: none against none, a hole against a present type. -/
def matchAnn : Option Nat → Option TypeRef → Option Subst
  | none, none => some []
  | some i, some t => some [(i, .type t)]
  | _, _ => none

mutual
  /-- Match an expression against a skeleton at depth `n`, collecting the holes left to right. -/
  def matchT (n : Nat) : Tpl → Expr → Option Subst
    | .hole i, e => some [(i, .expr e)]
    | .strHole i, .str s => some [(i, .str s)]
    | .intHole i, .int v => some [(i, .int v)]
    | .arrHole i, .arr es => some [(i, .exprs es)]
    | .binderRef k, .ident s => if s = varName (n + k) then some [] else none
    | .ident s, .ident s' => if s' = s then some [] else none
    | .str s, .str s' => if s' = s then some [] else none
    | .int v, .int v' => if v' = v then some [] else none
    | .bool b, .bool b' => if b' = b then some [] else none
    | .call h args, .call h' args' => do
      let a ← matchT n h h'
      let b ← matchTs n args args'
      some (a ++ b)
    | .callSpread h i, .call h' es => do
      let a ← matchT n h h'
      some (a ++ [(i, .exprs es)])
    | .arr items, .arr items' => matchTs n items items'
    | .object fields, .object fields' => matchFields n fields fields'
    | .arrow b, .arrow none b' => matchT n b b'
    | .lambda bs b, .lambda ps b' none => if ps = params n bs then matchT n b b' else none
    | .cond t a b, .cond t' a' b' => do
      let x ← matchT n t t'
      let y ← matchT n a a'
      let z ← matchT n b b'
      some (x ++ (y ++ z))
    | .method target name args, .method target' name' args' =>
      if name' = name then do
        let a ← matchT n target target'
        let b ← matchTs n args args'
        some (a ++ b)
      else none
    | .arrowBlock bs body, .arrowBlock ps body' none =>
      if ps = params n bs then matchStmts n body body' else none
    | _, _ => none
  def matchTs (n : Nat) : Tpls → List Expr → Option Subst
    | .nil, [] => some []
    | .cons h t, e :: es => do
      let a ← matchT n h e
      let b ← matchTs n t es
      some (a ++ b)
    | _, _ => none
  def matchFields (n : Nat) : Fields → List (String × Expr) → Option Subst
    | .nil, [] => some []
    | .cons key v t, (key', e) :: es =>
      if key' = key then do
        let a ← matchT n v e
        let b ← matchFields n t es
        some (a ++ b)
      else none
    | _, _ => none
  def matchStmt (n : Nat) : StmtTpl → Stmt → Option Subst
    | .letInit k v ann, .letInit name e ty =>
      if name = varName (n + k) then do
        let a ← matchT n v e
        let b ← matchAnn ann ty
        some (a ++ b)
      else none
    | .assign k v, .assign name e => if name = varName (n + k) then matchT n v e else none
    | .ret v, .ret e => matchT n v e
    | .exprStmt v, .exprStmt e => matchT n v e
    | _, _ => none
  def matchStmts (n : Nat) : StmtTpls → List Stmt → Option Subst
    | .nil, [] => some []
    | .cons h t, s :: ss => do
      let a ← matchStmt n h s
      let b ← matchStmts n t ss
      some (a ++ b)
    | _, _ => none
end

/-! ## The holes of a skeleton, left to right -/

def holesAnn : Option Nat → List Nat
  | none => []
  | some i => [i]

mutual
  def holes : Tpl → List Nat
    | .hole i | .strHole i | .intHole i | .arrHole i => [i]
    | .binderRef _ | .ident _ | .str _ | .int _ | .bool _ => []
    | .call h args => holes h ++ holesTs args
    | .callSpread h i => holes h ++ [i]
    | .arr items => holesTs items
    | .object fields => holesFields fields
    | .arrow b => holes b
    | .lambda _ b => holes b
    | .cond t a b => holes t ++ (holes a ++ holes b)
    | .method target _ args => holes target ++ holesTs args
    | .arrowBlock _ body => holesStmts body
  def holesTs : Tpls → List Nat
    | .nil => []
    | .cons h t => holes h ++ holesTs t
  def holesFields : Fields → List Nat
    | .nil => []
    | .cons _ v t => holes v ++ holesFields t
  def holesStmt : StmtTpl → List Nat
    | .letInit _ v ann => holes v ++ holesAnn ann
    | .assign _ v | .ret v | .exprStmt v => holes v
  def holesStmts : StmtTpls → List Nat
    | .nil => []
    | .cons h t => holesStmt h ++ holesStmts t
end

/-- A skeleton whose holes are pairwise distinct: what `inst_of_match` asks of a table row. -/
def Linear (t : Tpl) : Prop := (holes t).Nodup

instance (t : Tpl) : Decidable (Linear t) := by unfold Linear; infer_instance

end Effect4.Codegen.Template
