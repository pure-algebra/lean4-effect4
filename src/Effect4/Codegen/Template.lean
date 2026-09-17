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

The reader's measure is here too, because a definition's termination needs it: what a match
captures is within the size of what it matched (`match_within`), and strictly below it under a
rigid top (`match_below`).

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

/-! ## The binders in scope at each hole

A skeleton shows its own binding structure: a lambda or a block arrow brings its slots into
scope for its body, and a `let` brings its slot into scope for the statements after it. Slots
count from the node's own depth, so a hole at level `k` is printed, and read, at `n + k`. A
table row therefore states no depth: it is read off the skeleton. -/

/-- The scope after binding the slots `bs`: slot `b` in scope means `b + 1` binders are. -/
def scopeWith (k : Nat) (bs : List Nat) : Nat := bs.foldl (fun acc b => max acc (b + 1)) k

mutual
  /-- Each hole with the number of binders in scope at it, `k` being in scope outside. -/
  def levels (k : Nat) : Tpl → List (Nat × Nat)
    | .hole i | .strHole i | .intHole i | .arrHole i => [(i, k)]
    | .binderRef _ | .ident _ | .str _ | .int _ | .bool _ => []
    | .call h args => levels k h ++ levelsTs k args
    | .callSpread h i => levels k h ++ [(i, k)]
    | .arr items => levelsTs k items
    | .object fields => levelsFields k fields
    | .arrow b => levels k b
    | .lambda bs b => levels (scopeWith k bs) b
    | .cond t a b => levels k t ++ (levels k a ++ levels k b)
    | .method target _ args => levels k target ++ levelsTs k args
    | .arrowBlock bs body => levelsStmts (scopeWith k bs) body
  def levelsTs (k : Nat) : Tpls → List (Nat × Nat)
    | .nil => []
    | .cons h t => levels k h ++ levelsTs k t
  def levelsFields (k : Nat) : Fields → List (Nat × Nat)
    | .nil => []
    | .cons _ v t => levels k v ++ levelsFields k t
  /-- A statement list: a `let` of slot `s` is in scope for the statements after it. -/
  def levelsStmts (k : Nat) : StmtTpls → List (Nat × Nat)
    | .nil => []
    | .cons (.letInit s v ann) t =>
      levels k v ++ (holesAnn ann).map (·, k) ++ levelsStmts (max k (s + 1)) t
    | .cons (.assign _ v) t | .cons (.ret v) t | .cons (.exprStmt v) t =>
      levels k v ++ levelsStmts k t
end

/-- The binders in scope at hole `i` of a skeleton; `0` for a hole it does not have. -/
def levelAt (t : Tpl) (i : Nat) : Nat :=
  match (levels 0 t).find? (·.1 == i) with
  | some (_, k) => k
  | none => 0

/-- A skeleton whose holes are pairwise distinct: what `inst_of_match` asks of a table row. -/
def Linear (t : Tpl) : Prop := (holes t).Nodup

instance (t : Tpl) : Decidable (Linear t) := by unfold Linear; infer_instance

/-! ## What a match captures is no larger than what it matched

The measure of the generic reader: it recurses on the expressions a row's skeleton captured, and
a skeleton with a rigid top (every row's but the two transparent ones) captures only proper
sub-expressions. -/

/-- A capture is within a bound: an expression's size, or an expression list's; the other sorts
hold no expression. (A predicate, not a size function: `sizeOf` has no compiled code.) -/
def Arg.Within (bound : Nat) : Arg → Prop
  | .expr e => sizeOf e ≤ bound
  | .exprs es => sizeOf es ≤ bound
  | _ => True

theorem Arg.Within.mono {a b : Nat} (hab : a ≤ b) : ∀ {x : Arg}, x.Within a → x.Within b
  | .expr _, h => Nat.le_trans h hab
  | .exprs _, h => Nat.le_trans h hab
  | .str _, _ => trivial
  | .int _, _ => trivial
  | .type _, _ => trivial

/-- Every capture of `σ` is within `bound`. -/
def Within (bound : Nat) (σ : Subst) : Prop := ∀ p ∈ σ, p.2.Within bound

theorem Within.nil (bound : Nat) : Within bound [] := fun _ hp => absurd hp List.not_mem_nil

theorem Within.single {bound i : Nat} {a : Arg} (h : a.Within bound) : Within bound [(i, a)] := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

theorem Within.mono {a b : Nat} {σ : Subst} (hab : a ≤ b) (h : Within a σ) : Within b σ :=
  fun p hp => (h p hp).mono hab

theorem Within.append {bound : Nat} {x y : Subst} (hx : Within bound x) (hy : Within bound y) :
    Within bound (x ++ y) := by
  intro p hp
  rw [List.mem_append] at hp
  cases hp with
  | inl h => exact hx p h
  | inr h => exact hy p h

theorem matchAnn_within (bound : Nat) : ∀ (ann : Option Nat) (ty : Option TypeRef) (σ : Subst),
    matchAnn ann ty = some σ → Within bound σ
  | none, none, σ, h => by
    simp only [matchAnn, Option.some.injEq] at h
    subst h
    exact Within.nil bound
  | some i, some t, σ, h => by
    simp only [matchAnn, Option.some.injEq] at h
    subst h
    exact Within.single trivial

mutual
  theorem match_within (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ : Subst),
      matchT n t e = some σ → Within (sizeOf e) σ
    | .hole i, e, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      exact Within.single (show sizeOf e ≤ sizeOf e from Nat.le_refl _)
    | .strHole i, .str s, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      exact Within.single trivial
    | .intHole i, .int v, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      exact Within.single trivial
    | .arrHole i, .arr es, σ, h => by
      simp only [matchT, Option.some.injEq] at h
      subst h
      have hsz : sizeOf (Expr.arr es) = 1 + sizeOf es := Expr.arr.sizeOf_spec es
      exact Within.single (show sizeOf es ≤ sizeOf (Expr.arr es) by omega)
    | .binderRef k, .ident s, σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Within.nil _
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .ident s, .ident s', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Within.nil _
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .str s, .str s', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Within.nil _
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .int v, .int v', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Within.nil _
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .bool b, .bool b', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        exact Within.nil _
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .call hd args, .call hd' args', σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      have hsz : sizeOf (Expr.call hd' args') = 1 + sizeOf hd' + sizeOf args' :=
        Expr.call.sizeOf_spec hd' args'
      exact Within.append ((match_within n hd hd' a ha).mono (by omega))
        ((matchs_within n args args' b hb).mono (by omega))
    | .callSpread hd i, .call hd' es, σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, rfl⟩ := h
      have hsz : sizeOf (Expr.call hd' es) = 1 + sizeOf hd' + sizeOf es :=
        Expr.call.sizeOf_spec hd' es
      exact Within.append ((match_within n hd hd' a ha).mono (by omega))
        (Within.single (show sizeOf es ≤ sizeOf (Expr.call hd' es) by omega))
    | .arr items, .arr items', σ, h => by
      simp only [matchT] at h
      have hsz : sizeOf (Expr.arr items') = 1 + sizeOf items' := Expr.arr.sizeOf_spec items'
      exact (matchs_within n items items' σ h).mono (by omega)
    | .object fields, .object fields', σ, h => by
      simp only [matchT] at h
      have hsz : sizeOf (Expr.object fields') = 1 + sizeOf fields' := Expr.object.sizeOf_spec fields'
      exact (matchFields_within n fields fields' σ h).mono (by omega)
    | .arrow b, .arrow none b', σ, h => by
      simp only [matchT] at h
      have hsz := Expr.arrow.sizeOf_spec none b'
      exact (match_within n b b' σ h).mono (by omega)
    | .lambda bs b, .lambda ps b' none, σ, h => by
      simp only [matchT] at h
      split at h
      · have hsz := Expr.lambda.sizeOf_spec ps b' none
        exact (match_within n b b' σ h).mono (by omega)
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .cond t a b, .cond t' a' b', σ, h => by
      simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
      have hsz := Expr.cond.sizeOf_spec t' a' b'
      exact Within.append ((match_within n t t' x hx).mono (by omega))
        (Within.append ((match_within n a a' y hy).mono (by omega))
          ((match_within n b b' z hz).mono (by omega)))
    | .method target name args, .method target' name' args', σ, h => by
      simp only [matchT] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        have hsz := Expr.method.sizeOf_spec target' name' args'
        exact Within.append ((match_within n target target' a ha).mono (by omega))
          ((matchs_within n args args' b hb).mono (by omega))
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .arrowBlock bs body, .arrowBlock ps body' none, σ, h => by
      simp only [matchT] at h
      split at h
      · have hsz := Expr.arrowBlock.sizeOf_spec ps body' none
        exact (matchStmts_within n body body' σ h).mono (by omega)
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  theorem matchs_within (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ : Subst),
      matchTs n ts es = some σ → Within (sizeOf es) σ
    | .nil, [], σ, h => by
      simp only [matchTs, Option.some.injEq] at h
      subst h
      exact Within.nil _
    | .cons hd tl, e :: es, σ, h => by
      simp only [matchTs, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      have hsz : sizeOf (e :: es) = 1 + sizeOf e + sizeOf es := List.cons.sizeOf_spec e es
      exact Within.append ((match_within n hd e a ha).mono (by omega))
        ((matchs_within n tl es b hb).mono (by omega))
  theorem matchFields_within (n : Nat) : ∀ (fs : Fields) (es : List (String × Expr)) (σ : Subst),
      matchFields n fs es = some σ → Within (sizeOf es) σ
    | .nil, [], σ, h => by
      simp only [matchFields, Option.some.injEq] at h
      subst h
      exact Within.nil _
    | .cons key v tl, (key', e) :: es, σ, h => by
      simp only [matchFields] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        have hsz : sizeOf ((key', e) :: es) = 1 + sizeOf (key', e) + sizeOf es :=
          List.cons.sizeOf_spec (key', e) es
        have hpair : sizeOf (key', e) = 1 + sizeOf key' + sizeOf e := Prod.mk.sizeOf_spec key' e
        exact Within.append ((match_within n v e a ha).mono (by omega))
          ((matchFields_within n tl es b hb).mono (by omega))
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  theorem matchStmt_within (n : Nat) : ∀ (t : StmtTpl) (s : Stmt) (σ : Subst),
      matchStmt n t s = some σ → Within (sizeOf s) σ
    | .letInit k v ann, .letInit name e ty, σ, h => by
      simp only [matchStmt] at h
      split at h
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
        obtain ⟨a, ha, b, hb, rfl⟩ := h
        have hsz := Stmt.letInit.sizeOf_spec name e ty
        exact Within.append ((match_within n v e a ha).mono (by omega))
          (matchAnn_within _ ann ty b hb)
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .assign k v, .assign name e, σ, h => by
      simp only [matchStmt] at h
      split at h
      · have hsz := Stmt.assign.sizeOf_spec name e
        exact (match_within n v e σ h).mono (by omega)
      · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
    | .ret v, .ret e, σ, h => by
      simp only [matchStmt] at h
      have hsz := Stmt.ret.sizeOf_spec e
      exact (match_within n v e σ h).mono (by omega)
    | .exprStmt v, .exprStmt e, σ, h => by
      simp only [matchStmt] at h
      have hsz := Stmt.exprStmt.sizeOf_spec e
      exact (match_within n v e σ h).mono (by omega)
  theorem matchStmts_within (n : Nat) : ∀ (ts : StmtTpls) (ss : List Stmt) (σ : Subst),
      matchStmts n ts ss = some σ → Within (sizeOf ss) σ
    | .nil, [], σ, h => by
      simp only [matchStmts, Option.some.injEq] at h
      subst h
      exact Within.nil _
    | .cons hd tl, s :: ss, σ, h => by
      simp only [matchStmts, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      have hsz : sizeOf (s :: ss) = 1 + sizeOf s + sizeOf ss := List.cons.sizeOf_spec s ss
      exact Within.append ((matchStmt_within n hd s a ha).mono (by omega))
        ((matchStmts_within n tl ss b hb).mono (by omega))
end

/-! ## Strictly smaller, under a rigid top -/

/-- A skeleton with a rigid top: anything but a bare expression hole. A row with a bare hole is
transparent (`withFiber` prints as its action, a layer reference as its name). -/
def Tpl.rigid : Tpl → Bool
  | .hole _ => false
  | _ => true

def Arg.Below (bound : Nat) : Arg → Prop
  | .expr e => sizeOf e < bound
  | .exprs es => sizeOf es < bound
  | _ => True

/-- Every capture of `σ` is strictly below `bound`. -/
def Below (bound : Nat) (σ : Subst) : Prop := ∀ p ∈ σ, p.2.Below bound

theorem Arg.Within.below {a b : Nat} (hab : a < b) : ∀ {x : Arg}, x.Within a → x.Below b
  | .expr _, h => Nat.lt_of_le_of_lt h hab
  | .exprs _, h => Nat.lt_of_le_of_lt h hab
  | .str _, _ => trivial
  | .int _, _ => trivial
  | .type _, _ => trivial

theorem Within.below {a b : Nat} {σ : Subst} (hab : a < b) (h : Within a σ) : Below b σ :=
  fun p hp => (h p hp).below hab

theorem Below.nil (bound : Nat) : Below bound [] := fun _ hp => absurd hp List.not_mem_nil

theorem Below.single {bound i : Nat} {a : Arg} (h : a.Below bound) : Below bound [(i, a)] := by
  intro p hp
  rw [List.mem_singleton] at hp
  subst hp
  exact h

theorem Below.append {bound : Nat} {x y : Subst} (hx : Below bound x) (hy : Below bound y) :
    Below bound (x ++ y) := by
  intro p hp
  rw [List.mem_append] at hp
  cases hp with
  | inl h => exact hx p h
  | inr h => exact hy p h

/-- An element of a captured list is below whatever the list is below. -/
theorem Arg.Below.elem {bound : Nat} {es : List Expr} (h : (Arg.exprs es).Below bound)
    {y : Expr} (hy : y ∈ es) : sizeOf y < bound :=
  Nat.lt_trans (List.sizeOf_lt_of_mem hy) h

/-- The reader's measure: a rigid skeleton captures only proper sub-expressions. -/
theorem match_below (n : Nat) : ∀ (t : Tpl) (e : Expr) (σ : Subst),
    t.rigid = true → matchT n t e = some σ → Below (sizeOf e) σ
  | .strHole i, .str s, σ, _, h => by
    simp only [matchT, Option.some.injEq] at h
    subst h
    exact Below.single trivial
  | .intHole i, .int v, σ, _, h => by
    simp only [matchT, Option.some.injEq] at h
    subst h
    exact Below.single trivial
  | .arrHole i, .arr es, σ, _, h => by
    simp only [matchT, Option.some.injEq] at h
    subst h
    have hsz : sizeOf (Expr.arr es) = 1 + sizeOf es := Expr.arr.sizeOf_spec es
    exact Below.single (show sizeOf es < sizeOf (Expr.arr es) by omega)
  | .binderRef k, .ident s, σ, _, h => by
    simp only [matchT] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Below.nil _
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .ident s, .ident s', σ, _, h => by
    simp only [matchT] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Below.nil _
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .str s, .str s', σ, _, h => by
    simp only [matchT] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Below.nil _
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .int v, .int v', σ, _, h => by
    simp only [matchT] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Below.nil _
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .bool b, .bool b', σ, _, h => by
    simp only [matchT] at h
    split at h
    · simp only [Option.some.injEq] at h
      subst h
      exact Below.nil _
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .call hd args, .call hd' args', σ, _, h => by
    simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    have hsz : sizeOf (Expr.call hd' args') = 1 + sizeOf hd' + sizeOf args' :=
      Expr.call.sizeOf_spec hd' args'
    exact Below.append ((match_within n hd hd' a ha).below (by omega))
      ((matchs_within n args args' b hb).below (by omega))
  | .callSpread hd i, .call hd' es, σ, _, h => by
    simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨a, ha, rfl⟩ := h
    have hsz : sizeOf (Expr.call hd' es) = 1 + sizeOf hd' + sizeOf es :=
      Expr.call.sizeOf_spec hd' es
    exact Below.append ((match_within n hd hd' a ha).below (by omega))
      (Below.single (show sizeOf es < sizeOf (Expr.call hd' es) by omega))
  | .arr items, .arr items', σ, _, h => by
    simp only [matchT] at h
    have hsz : sizeOf (Expr.arr items') = 1 + sizeOf items' := Expr.arr.sizeOf_spec items'
    exact (matchs_within n items items' σ h).below (by omega)
  | .object fields, .object fields', σ, _, h => by
    simp only [matchT] at h
    have hsz : sizeOf (Expr.object fields') = 1 + sizeOf fields' := Expr.object.sizeOf_spec fields'
    exact (matchFields_within n fields fields' σ h).below (by omega)
  | .arrow b, .arrow none b', σ, _, h => by
    simp only [matchT] at h
    have hsz := Expr.arrow.sizeOf_spec none b'
    exact (match_within n b b' σ h).below (by omega)
  | .lambda bs b, .lambda ps b' none, σ, _, h => by
    simp only [matchT] at h
    split at h
    · have hsz := Expr.lambda.sizeOf_spec ps b' none
      exact (match_within n b b' σ h).below (by omega)
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .cond t a b, .cond t' a' b', σ, _, h => by
    simp only [matchT, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, z, hz, rfl⟩ := h
    have hsz := Expr.cond.sizeOf_spec t' a' b'
    exact Below.append ((match_within n t t' x hx).below (by omega))
      (Below.append ((match_within n a a' y hy).below (by omega))
        ((match_within n b b' z hz).below (by omega)))
  | .method target name args, .method target' name' args', σ, _, h => by
    simp only [matchT] at h
    split at h
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
      obtain ⟨a, ha, b, hb, rfl⟩ := h
      have hsz := Expr.method.sizeOf_spec target' name' args'
      exact Below.append ((match_within n target target' a ha).below (by omega))
        ((matchs_within n args args' b hb).below (by omega))
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])
  | .arrowBlock bs body, .arrowBlock ps body' none, σ, _, h => by
    simp only [matchT] at h
    split at h
    · have hsz := Expr.arrowBlock.sizeOf_spec ps body' none
      exact (matchStmts_within n body body' σ h).below (by omega)
    · exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

end Effect4.Codegen.Template
