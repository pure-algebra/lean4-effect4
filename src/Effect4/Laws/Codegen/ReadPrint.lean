import Effect4.Laws.Codegen.Read

/-!
# Laws.Codegen.ReadPrint — what the printer prints of a readable program reads back (R5.2)

`read_print`, law 11, over the table. The proof has no case per constructor: it is the generic
row step, with the recursion as a hypothesis, and rests on

* `match_inst` (matching an instance reads the substitution back along the holes) and the
  fact that an instantiation captures every hole (`holes_of_inst`);
* the leaf round trips (`readTerm_printTerm`, `readCause_printCause`, `readKey_printKey`,
  `readForkOptions_print`, `readLiteral_print`, `read_printRow`);
* the reader's commitment to the first row whose skeleton matches: no row before the printing
  row matches its image. Rows with different heads cannot match one tree (`head_of_match`);
  the few pairs of rows with one head are apart by a former (`arrow` against `arrowBlock`, an
  annotation against none, an argument count), each stated once; which pairs those are is a
  decided fact of the table (`table_overlap`).

The domain, `Readable`, is a fold: a program is readable when the printer chooses a skeleton
row for every node and every leaf reads back at its depth (a term or cause in scope, a key with
a spelled type, fork options whose daemon flag the row spells, no type annotation).
-/

set_option autoImplicit false

namespace Effect4.Codegen.Template

open TypeScript (Expr Stmt TypeRef Parameter)

attribute [local simp] inst insts instFields instStmt instStmts matchT matchTs matchFields
  matchStmt matchStmts holes holesTs holesFields holesStmt holesStmts holesAnn instAnn

/-! ## An instantiation captures every hole -/

theorem holesAnn_of_instAnn (σ : Subst) : ∀ (ann : Option Nat) (ty : Option TypeRef),
    instAnn σ ann = some ty → ∀ i ∈ holesAnn ann, ∃ a, lookup σ i = some a
  | none, _, _ => by aesop
  | some i, ty, h => by aesop

mutual
  theorem holes_of_inst (n : Nat) (σ : Subst) : ∀ (t : Tpl) (e : Expr),
      inst n σ t = some e → ∀ i ∈ holes t, ∃ a, lookup σ i = some a
    | .hole i, e, h => by aesop
    | .strHole i, e, h => by aesop
    | .intHole i, e, h => by aesop
    | .arrHole i, e, h => by aesop
    | .binderRef k, e, h => by aesop
    | .ident s, e, h => by aesop
    | .str s, e, h => by aesop
    | .int v, e, h => by aesop
    | .bool b, e, h => by aesop
    | .call hd args, e, h => by
      have ih1 := holes_of_inst n σ hd
      have ih2 := holess_of_insts n σ args
      aesop
    | .callSpread hd i, e, h => by
      have ih1 := holes_of_inst n σ hd
      aesop
    | .arr items, e, h => by
      have ih := holess_of_insts n σ items
      aesop
    | .object fields, e, h => by
      have ih := holesFields_of_instFields n σ fields
      aesop
    | .arrow b, e, h => by
      have ih := holes_of_inst n σ b
      aesop
    | .lambda bs b, e, h => by
      have ih := holes_of_inst n σ b
      aesop
    | .cond t a b, e, h => by
      have ih1 := holes_of_inst n σ t
      have ih2 := holes_of_inst n σ a
      have ih3 := holes_of_inst n σ b
      aesop
    | .method target name args, e, h => by
      have ih1 := holes_of_inst n σ target
      have ih2 := holess_of_insts n σ args
      aesop
    | .arrowBlock bs body, e, h => by
      have ih := holesStmts_of_instStmts n σ body
      aesop
    | .generator body, e, h => by
      have ih := holesStmts_of_instStmts n σ body
      aesop
  theorem holess_of_insts (n : Nat) (σ : Subst) : ∀ (ts : Tpls) (es : List Expr),
      insts n σ ts = some es → ∀ i ∈ holesTs ts, ∃ a, lookup σ i = some a
    | .nil, es, h => by aesop
    | .cons hd tl, es, h => by
      have ih1 := holes_of_inst n σ hd
      have ih2 := holess_of_insts n σ tl
      aesop
  theorem holesFields_of_instFields (n : Nat) (σ : Subst) :
      ∀ (fs : Fields) (es : List (String × Expr)),
      instFields n σ fs = some es → ∀ i ∈ holesFields fs, ∃ a, lookup σ i = some a
    | .nil, es, h => by aesop
    | .cons key v tl, es, h => by
      have ih1 := holes_of_inst n σ v
      have ih2 := holesFields_of_instFields n σ tl
      aesop
  theorem holesStmt_of_instStmt (n : Nat) (σ : Subst) : ∀ (t : StmtTpl) (s : Stmt),
      instStmt n σ t = some s → ∀ i ∈ holesStmt t, ∃ a, lookup σ i = some a
    | .letInit k v ann, s, h => by
      have ih := holes_of_inst n σ v
      have ih2 := holesAnn_of_instAnn σ ann
      aesop
    | .assign k v, s, h => by
      have ih := holes_of_inst n σ v
      aesop
    | .ret v, s, h => by
      have ih := holes_of_inst n σ v
      aesop
    | .exprStmt v, s, h => by
      have ih := holes_of_inst n σ v
      aesop
    | .constYield k v, s, h => by
      have ih := holes_of_inst n σ v
      aesop
    | .yieldDiscard v, s, h => by
      have ih := holes_of_inst n σ v
      aesop
    | .ifElse t a b, s, h => by
      have ih1 := holes_of_inst n σ t
      have ih2 := holesStmts_of_instStmts n σ a
      have ih3 := holesStmts_of_instStmts n σ b
      aesop
    | .whileTrue body, s, h => by
      have ih := holesStmts_of_instStmts n σ body
      aesop
    | .breakTo, s, h => by aesop
  theorem holesStmts_of_instStmts (n : Nat) (σ : Subst) : ∀ (ts : StmtTpls) (ss : List Stmt),
      instStmts n σ ts = some ss → ∀ i ∈ holesStmts ts, ∃ a, lookup σ i = some a
    | .nil, ss, h => by aesop
    | .cons hd tl, ss, h => by
      have ih1 := holesStmt_of_instStmt n σ hd
      have ih2 := holesStmts_of_instStmts n σ tl
      aesop
    | .hole i, ss, h => by aesop
end

/-- Reading a substitution along holes it has: the result exists and agrees with it there. -/
theorem along_of_exists (σ : Subst) : ∀ (hs : List Nat), (∀ i ∈ hs, ∃ a, lookup σ i = some a) →
    ∃ σ', along σ hs = some σ' ∧ ∀ i ∈ hs, lookup σ' i = lookup σ i
  | [], _ => ⟨[], rfl, by simp⟩
  | i :: rest, h => by
    obtain ⟨a, ha⟩ := h i List.mem_cons_self
    obtain ⟨σ', hσ', hl⟩ := along_of_exists σ rest (fun j hj => h j (List.mem_cons_of_mem _ hj))
    refine ⟨(i, a) :: σ', by unfold along at hσ' ⊢; rw [List.mapM_cons, ha, hσ']; rfl, ?_⟩
    intro j hj
    by_cases hij : j = i
    · subst hij; rw [lookup_cons_self, ha]
    · rw [Effect4.Program.lookup_cons_ne i j a σ' (Ne.symm hij)]
      exact hl j (by aesop)

/-- Matching an instance of a skeleton gives a substitution that agrees with the printing one
at the skeleton's holes. -/
theorem match_of_inst (n : Nat) (σ : Subst) (t : Tpl) (e : Expr) (h : inst n σ t = some e) :
    ∃ σ', matchT n t e = some σ' ∧ ∀ i ∈ holes t, lookup σ' i = lookup σ i := by
  obtain ⟨σ', hσ', hl⟩ := along_of_exists σ (holes t) (holes_of_inst n σ t e h)
  exact ⟨σ', (match_inst n σ t e h).trans hσ', hl⟩

theorem matchStmt_of_instStmt (n : Nat) (σ : Subst) (t : StmtTpl) (s : Stmt)
    (h : instStmt n σ t = some s) :
    ∃ σ', matchStmt n t s = some σ' ∧ ∀ i ∈ holesStmt t, lookup σ' i = lookup σ i := by
  obtain ⟨σ', hσ', hl⟩ := along_of_exists σ (holesStmt t) (holesStmt_of_instStmt n σ t s h)
  exact ⟨σ', (matchStmt_inst n σ t s h).trans hσ', hl⟩

/-! ## A match forces the head; an instantiation carries it -/

open Effect4.Program (exprHead?)

theorem head_of_match (n : Nat) (t : Tpl) (x : Expr) (σ : Subst) (h : matchT n t x = some σ)
    {name : String} (hh : t.head? = some name) : exprHead? x = some name := by
  cases t <;> cases x <;> simp_all [Tpl.head?, exprHead?] <;> aesop

theorem head_of_inst (n : Nat) (σ : Subst) (t : Tpl) (x : Expr) (h : inst n σ t = some x)
    {name : String} (hh : t.head? = some name) : exprHead? x = some name := by
  cases t <;> simp_all [Tpl.head?] <;> aesop (add norm simp exprHead?)

/-- A call, an identifier or a method call: what every child image is. -/
def nodeLike : Expr → Bool
  | .ident _ | .call _ _ | .method _ _ _ => true
  | _ => false

theorem matchT_arrow_arrowBlock (n : Nat) (b : Tpl) (ps : List Parameter) (ss : List Stmt)
    (rt : Option TypeRef) : matchT n (.arrow b) (.arrowBlock ps ss rt) = none := by simp

theorem matchT_arrowBlock_arrow (n : Nat) (bs : List Nat) (body : StmtTpls) (rt : Option TypeRef)
    (y : Expr) : matchT n (.arrowBlock bs body) (.arrow rt y) = none := by simp

theorem matchT_cond_nodeLike (n : Nat) (t a b : Tpl) (y : Expr) (hy : nodeLike y = true) :
    matchT n (.cond t a b) y = none := by
  cases y <;> simp_all [nodeLike]


/-! ## Two skeletons apart: no instance of the second matches the first

The table is read first match wins, so the printing row's image must match no row before it.
Rows with different heads are apart by `head_of_match`. The rows that share a head are apart by
a former: an arrow against a block, a block whose first `let` is annotated against one whose
is not, argument lists of different lengths, a conditional against a hole that a child image
fills (a child image is a call, an identifier or a method call, never a conditional), and
`pipe` receivers of different inner heads. `apartBy` names exactly those reasons; a table with
a new overlap fails `table_apart` and asks for a reason here. -/

/-- Whether hole `i` of the later skeleton is filled by a child image. -/
def childHole (sorts : List Effect4.Program.ArgSort) (i : Nat) : Bool :=
  match sorts[i]? with
  | some (.child .eff) | some (.child .action) | some (.child .layer) => true
  | _ => false

def Tpls.length : Tpls → Nat
  | .nil => 0
  | .cons _ t => Tpls.length t + 1

/-- `shapeApart sorts earlier later`: a reason, by shape, no instance of `later` (its child
holes filled by child images) matches `earlier`: formers that never cross, an arrow against a
block, a conditional against a child hole, an unannotated first `let` against an annotated one,
argument lists of different lengths, `pipe` receivers of different inner heads. -/
def shapeApart (sorts : List Effect4.Program.ArgSort) : Tpl → Tpl → Bool
  | .call _ args', .call _ args =>
    match args', args with
    | .cons (.arrow _) .nil, .cons (.arrowBlock _ _) .nil => true
    | .cons (.arrowBlock _ _) .nil, .cons (.arrow _) .nil => true
    | .cons (.arrow (.cond _ _ _)) .nil, .cons (.arrow (.hole i)) .nil => childHole sorts i
    | .cons (.arrowBlock _ (.cons (.letInit _ _ none) _)) .nil,
      .cons (.arrowBlock _ (.cons (.letInit _ _ (some _)) _)) .nil => true
    | _, _ => args'.length != args.length
  | .method (.hole _) name' (.cons (.call (.ident a) _) .nil),
    .method (.hole _) name (.cons (.call (.ident b) _) .nil) => name' != name || a != b
  | .ident _, .call _ _ | .call _ _, .ident _ => true
  | .call _ _, .method _ _ _ | .method _ _ _, .call _ _ => true
  | .ident _, .method _ _ _ | .method _ _ _, .ident _ => true
  | .callSpread _ _, .method _ _ _ | .method _ _ _, .callSpread _ _ => true
  | _, _ => false

/-- Apart by head (`head_of_match`: a match forces the head) or by shape. -/
def apartBy (sorts : List Effect4.Program.ArgSort) (t' t : Tpl) : Bool :=
  (match t'.head?, t.head? with
    | some h', some h => h' != h
    | _, _ => false) || shapeApart sorts t' t

theorem matchTs_length (n : Nat) : ∀ (ts : Tpls) (es : List Expr) (σ : Subst),
    matchTs n ts es = some σ → Tpls.length ts = es.length
  | .nil, es, σ, h => by cases es <;> aesop (add norm simp Tpls.length)
  | .cons t ts, es, σ, h => by
    have ih := matchTs_length n ts
    cases es <;> aesop (add norm simp Tpls.length)

theorem insts_length (n : Nat) (τ : Subst) : ∀ (ts : Tpls) (es : List Expr),
    insts n τ ts = some es → Tpls.length ts = es.length
  | .nil, es, h => by aesop (add norm simp Tpls.length)
  | .cons t ts, es, h => by
    have ih := insts_length n τ ts
    aesop (add norm simp Tpls.length)

/-- The calculus lemma of apartness: an instance of the later skeleton, its child holes filled
by node-like images, matches no earlier skeleton it is apart from. -/
theorem match_apart (n : Nat) (τ : Subst) (sorts : List Effect4.Program.ArgSort) (t' t : Tpl)
    (x : Expr) (hapart : apartBy sorts t' t = true) (hinst : inst n τ t = some x)
    (hnode : ∀ i y, childHole sorts i = true → i ∈ holes t → lookup τ i = some (.expr y) →
      nodeLike y = true) :
    matchT n t' x = none := by
  unfold apartBy at hapart
  rw [Bool.or_eq_true] at hapart
  rcases hapart with hhead | hshape
  · -- different heads
    cases hx : matchT n t' x with
    | none => rfl
    | some σ =>
      cases h' : t'.head? with
      | none => simp only [h'] at hhead; cases hhead
      | some a =>
        cases h : t.head? with
        | none => simp only [h', h] at hhead; cases hhead
        | some b =>
          have h1 := head_of_match n _ x σ hx h'
          have h2 := head_of_inst n τ _ x hinst h
          rw [h1, Option.some.injEq] at h2
          subst h2
          simp only [h', h, bne_self_eq_false] at hhead; cases hhead
  · unfold shapeApart at hshape
    split at hshape
    · split at hshape
      · aesop (add norm simp matchT_arrow_arrowBlock)
      · aesop (add norm simp matchT_arrowBlock_arrow)
      · -- the conditional against a child hole: the hole's capture is a child image
        have hn : ∀ y, lookup τ _ = some (.expr y) → nodeLike y = true :=
          fun y hy => hnode _ y hshape (by simp) hy
        aesop (add norm simp matchT_cond_nodeLike, safe forward hn)
      · aesop (add norm simp matchAnn)
      · aesop (add safe forward [matchTs_length, insts_length])
    all_goals aesop

/-- A skeleton with a node-like top: what every rigid row of an expression family has. -/
def Tpl.nodeTop : Tpl → Bool
  | .ident _ | .call _ _ | .callSpread _ _ | .method _ _ _ => true
  | _ => false

theorem inst_nodeLike (n : Nat) (τ : Subst) (t : Tpl) (x : Expr) (ht : t.nodeTop = true)
    (h : inst n τ t = some x) : nodeLike x = true := by
  cases t <;> aesop (add norm simp [Tpl.nodeTop, nodeLike])

/-- A skeleton that no identifier matches. -/
def Tpl.notName : Tpl → Bool
  | .hole _ | .ident _ | .binderRef _ => false
  | _ => true

theorem matchT_ident_none (n : Nat) (t : Tpl) (s : String) (ht : t.notName = true) :
    matchT n t (.ident s) = none := by
  cases t <;> aesop (add norm simp Tpl.notName)

/-- The former of a statement skeleton, for telling statement rows apart. -/
def StmtTpl.former : StmtTpl → Nat
  | .letInit _ _ _ => 0 | .assign _ _ => 1 | .ret _ => 2 | .exprStmt _ => 3
  | .constYield _ _ => 4 | .yieldDiscard _ => 5 | .ifElse _ _ _ => 6 | .whileTrue _ => 7
  | .breakTo => 8

/-- The former of a statement, numbered as its skeleton's. -/
def Stmt.former : Stmt → Nat
  | .letInit _ _ _ => 0 | .assign _ _ => 1 | .ret _ => 2 | .exprStmt _ => 3
  | .constYield _ _ _ => 4 | .yieldDiscard _ => 5 | .ifElse _ _ _ => 6 | .whileTrue _ _ => 7
  | .breakTo _ => 8 | _ => 9

theorem instStmt_former (n : Nat) (τ : Subst) (t : StmtTpl) (s : Stmt)
    (h : instStmt n τ t = some s) : Stmt.former s = t.former := by
  cases t <;> aesop (add norm simp [StmtTpl.former, Stmt.former])

theorem matchStmt_former_eq (n : Nat) (t' : StmtTpl) (s : Stmt) (σ : Subst)
    (h : matchStmt n t' s = some σ) : Stmt.former s = t'.former := by
  cases t' <;> cases s <;> aesop (add norm simp [StmtTpl.former, Stmt.former])

theorem matchStmt_former (n : Nat) (τ : Subst) (t' t : StmtTpl) (s : Stmt)
    (hne : t'.former ≠ t.former) (h : instStmt n τ t = some s) : matchStmt n t' s = none := by
  cases hm : matchStmt n t' s with
  | none => rfl
  | some σ => exact absurd ((matchStmt_former_eq n t' s σ hm).symm.trans (instStmt_former n τ t s h)) hne

end Effect4.Codegen.Template

namespace Effect4.Program

open TypeScript (Expr Stmt)
open Effect4.Codegen
open Effect4.Codegen.Template
open Effect4.Codegen.Templates (RowOut ArgPat Fixed table tableLayer printAlg printArg printArgs
  argDepth argSortOf Carrier Out)

variable {Op : Type}

/-! ## The domain: a fold that says whether every leaf reads back -/

/-- The carrier of the domain: readable at an environment length, leaving the binders a
statement declares for what follows it (`0` at every other family). -/
abbrev Dom (_ : EffFam) : Type := Nat → Option Nat

/-- A leaf reads back from its printing at depth `d`: a term or cause in scope, a key whose type
spells, fork options whose daemon flag the row spells, no type annotation (B19: types are not
read), and a layer path whose declared name decodes (the name codec has no law of its own; the
domain runs it). -/
def leafReadable {R : EffFam → Type} (sig : Signature Op) (d : Nat) (daemon : Bool) :
    ArgF Op R → Bool
  | .term t => t.scoped d
  | .optTerm (some t) => t.scoped d
  | .cause c => CauseTerm.scoped d c
  | .key k => keyReadable sig k
  | .forkOptions o => o.daemon == daemon
  | .optTy (some _) => false
  | .path p => decide (LayerTerm.readRefName (LayerTerm.refName p) = some p)
  | _ => true

/-- One argument reads back at depth `d`: a child by its own fold, a leaf by `leafReadable`. -/
def argReadable (sig : Signature Op) (d : Nat) (daemon : Bool) : ArgF Op Dom → Bool
  | .child _ r => (r d).isSome
  | a => leafReadable sig d daemon a

/-- Every argument of a row reads back at the depth the printer gives it. -/
def argsReadable (sig : Signature Op) (fam : EffFam) (n : Nat) (out : RowOut) (daemon : Bool) :
    List (ArgF Op Dom) → Nat → Bool
  | [], _ => true
  | a :: as, i =>
    argReadable sig (argDepth fam (argSortOf a) n (out.levelAt i)) daemon a &&
    argsReadable sig fam n out daemon as (i + 1)

/-- The domain, per layer: the row the printer chooses must be a skeleton or the row call, and
its arguments must read back; the spines are readable item by item, statements threading the
binders they declare. -/
def domLayer (sig : Signature Op) : (fam : EffFam) → String → List (ArgF Op Dom) → Dom fam
  | .eff, ctor, args => fun n => rowDom sig .eff ctor args n
  | .action, ctor, args => fun n => rowDom sig .action ctor args n
  | .layer, ctor, args => fun n => rowDom sig .layer ctor args n
  | .stmt, ctor, args => fun n =>
    match table.find? fun row => row.selects .stmt ctor args with
    | some row => match row.out with
      | .stmt t =>
        if argsReadable sig .stmt n (.stmt t) (rowDaemon row) args 0 then some t.declares else none
      | _ => none
    | none => none
  | .effs, "nil", [] => fun _ => some 0
  | .effs, "cons", [.child .eff head, .child .effs tail] => fun n => do
    let _ ← head n; let _ ← tail n; some 0
  | .layers, "nil", [] => fun _ => some 0
  | .layers, "cons", [.child .layer head, .child .layers tail] => fun n => do
    let _ ← head n; let _ ← tail n; some 0
  | .stmts, "nil", [] => fun _ => some 0
  | .stmts, "cons", [.child .stmt head, .child .stmts tail] => fun n => do
    let declared ← head n; let _ ← tail (n + declared); some 0
  | .effs, _, _ | .layers, _, _ | .stmts, _, _ => fun _ => none
where
  rowDom (sig : Signature Op) (fam : EffFam) (ctor : String) (args : List (ArgF Op Dom))
      (n : Nat) : Option Nat :=
    match table.find? fun row => row.selects fam ctor args with
    | none => none
    | some row => match row.out with
      | .refuse _ | .stmt _ => none
      | .rowCall => match args with
        | [.op op, .term request] =>
          if sig.dom op && requestReadable (sig.rowOf op) n request then some 0 else none
        | _ => none
      | .tpl t => if argsReadable sig fam n (.tpl t) (rowDaemon row) args 0 then some 0 else none

/-- The domain's algebra: the layer function and nothing else, so `cata_build` speaks of it. -/
def readableAlg (sig : Signature Op) : EffAlgebra Op Dom := EffAlgebra.ofLayer (domLayer sig)

/-- A node of a family is readable at an environment length. -/
def ReadableAt (sig : Signature Op) (fam : EffFam) (e : EffSelfCarrier Op fam) (n : Nat) : Prop :=
  ∃ d, cataFam (readableAlg sig) fam e n = some d

/-- The structural domain of the round trip: the fold says every leaf reads back. -/
def Readable (sig : Signature Op) (n : Nat) (e : Eff Op) : Bool :=
  (cata_eff (readableAlg sig) e n).isSome

/-! ## The reader side of `PrintsTo` -/

/-- A capture reads to a node at a depth: what the recursion establishes of each child, and the
theorem of the whole tree. -/
def ReadsTo (sig : Signature Op) (spell : String → List String → Option Op) (d : Nat) :
    (fam : EffFam) → EffSelfCarrier Op fam → Arg → Prop
  | .eff, v, .expr y => readT sig spell .eff d y = some (.ok v)
  | .action, v, .expr y => readT sig spell .action d y = some (.ok v)
  | .layer, v, .expr y => readT sig spell .layer d y = some (.ok v)
  | .effs, v, .exprs ys => readSpine sig spell .effs d ys = .ok v
  | .layers, v, .exprs ys => readSpine sig spell .layers d ys = .ok v
  | .stmts, v, .stmts ss => readStmts sig spell d ss = .ok v
  | _, _, _ => False

/-! ## The leaves read back -/

attribute [local aesop safe forward] readTerm_printTerm readCause_printCause readKey_printKey

/-- A readable leaf prints, and what it prints reads back at the same depth and sort. -/
theorem readLeaf_print {sig : Signature Op} {d : Nat} {daemon : Bool}
    {v : ArgF Op (EffSelfCarrier Op)} (hleaf : ∀ fam, argSortOf v ≠ .child fam)
    (hr : leafReadable sig d daemon v = true)
    {a : Arg} (hp : printArg sig d (ArgF.fold (printAlg sig) v) = .ok (some a)) :
    readLeaf sig d daemon (argSortOf v) a = .ok v := by
  cases v <;> aesop (add norm simp [leafReadable, ArgF.fold, printArg, argSortOf, readLeaf,
    readLiteral_print, readForkOptions_print])


/-! ## The arguments read back -/

theorem argsReadable_at {sig : Signature Op} {fam : EffFam} {n : Nat} {out : RowOut}
    {daemon : Bool} : ∀ (as : List (ArgF Op Dom)) (i k : Nat) (a : ArgF Op Dom),
    argsReadable sig fam n out daemon as i = true → as[k]? = some a →
    argReadable sig (argDepth fam (argSortOf a) n (out.levelAt (i + k))) daemon a = true
  | [], _, _, _, _, hk => by aesop
  | b :: bs, i, 0, a, h, hk => by aesop (add norm simp argsReadable)
  | b :: bs, i, k + 1, a, h, hk => by
    have ih := argsReadable_at (sig := sig) (fam := fam) (n := n) (out := out) (daemon := daemon) bs (i + 1) k a
    aesop (add norm simp [argsReadable, Nat.add_right_comm, Nat.add_assoc])

/-- What the printed substitution has at an argument's index: that argument's printing; and
nothing below the first index. -/
theorem printArgs_lookup {sig : Signature Op} {fam : EffFam} {n : Nat} {out : RowOut} :
    ∀ (as : List (ArgF Op Carrier)) (i : Nat) (τ : Subst), printArgs sig fam n out as i = .ok τ →
    (∀ (k : Nat) (a : ArgF Op Carrier), as[k]? = some a →
      printArg sig (argDepth fam (argSortOf a) n (out.levelAt (i + k))) a = .ok (lookup τ (i + k))) ∧
    (∀ j, j < i → lookup τ j = none)
  | [], _, _, _ => by aesop (add norm simp [printArgs, lookup])
  | b :: bs, i, τ, h => by
    simp only [printArgs, bind_eq_ok] at h
    obtain ⟨x, hx, rest, hrest, hτ⟩ := h
    obtain ⟨ih, ihlow⟩ := printArgs_lookup (sig := sig) (fam := fam) (n := n) (out := out)
      bs (i + 1) rest hrest
    cases x with
    | none =>
      cases hτ
      refine ⟨fun k a hk => ?_, fun j hj => ihlow j (by omega)⟩
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
                simpa only [Nat.add_zero, ihlow i (by omega)] using hx
      | succ k => rw [show i + (k + 1) = i + 1 + k by omega]; exact ih k a hk
    | some v =>
      cases hτ
      have hup : ∀ k, lookup ((i, v) :: rest) (i + (k + 1)) = lookup rest (i + (k + 1)) :=
        fun k => lookup_cons_ne i _ v rest (by omega)
      have hlow : ∀ j, j < i → lookup ((i, v) :: rest) j = lookup rest j :=
        fun j hj => lookup_cons_ne i j v rest (by omega)
      refine ⟨fun k a hk => ?_, fun j hj => by rw [hlow j hj]; exact ihlow j (by omega)⟩
      cases k with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hk; subst hk
                simpa only [Nat.add_zero, lookup_cons_self] using hx
      | succ k => rw [hup k, show i + (k + 1) = i + 1 + k by omega]; exact ih k a hk

/-- A capture `lookup` finds, `captured` finds. -/
theorem captured_of_lookup : ∀ (σ : Subst) (i : Nat) (a : Arg), lookup σ i = some a →
    ∃ h : (i, a) ∈ σ, captured σ i = some ⟨a, h⟩
  | [], _, _, h => by aesop (add norm simp lookup)
  | (j, b) :: rest, i, a, h => by
    have ih := captured_of_lookup rest i a
    by_cases hji : j = i
    · subst hji
      aesop (add norm simp [captured, lookup_cons_self])
    · have hl := lookup_cons_ne j i b rest hji
      aesop (add norm simp captured)

/-- A fixed value's pattern holds of one argument only. -/
theorem Fixed.holds_eq {R : EffFam → Type} (v : Fixed) (a : ArgF Op R) (h : v.holds a = true) :
    a = v.arg := by
  cases v <;> cases a <;> aesop (add norm simp [Templates.Fixed.holds, Templates.Fixed.arg])


/-- A child that printed to a capture prints to it (the inverse of `printArg_child`). -/
theorem printsTo_of_printArg {sig : Signature Op} {d : Nat} {fam : EffFam}
    {c : EffSelfCarrier Op fam} {a : Arg}
    (h : printArg sig d (ArgF.fold (printAlg sig) (.child fam c)) = .ok (some a)) :
    PrintsTo sig d fam c a := by
  cases fam <;> cases a <;>
    aesop (add norm simp [PrintsTo, ArgF.fold, cataFam, printArg, bind, Except.bind, pure,
      Except.pure])

/-- A readable leaf argument is a readable leaf: the fold changes only children. -/
theorem leafReadable_of_argReadable {sig : Signature Op} {d : Nat} {daemon : Bool}
    {v : ArgF Op (EffSelfCarrier Op)} (hleaf : ∀ fam, argSortOf v ≠ .child fam)
    (h : argReadable sig d daemon (ArgF.fold (readableAlg sig) v) = true) :
    leafReadable sig d daemon v = true := by
  cases v <;> aesop (add norm simp [argReadable, ArgF.fold, leafReadable, argSortOf])

/-- A readable child is readable at its depth, as `ReadableAt` says it. -/
theorem readableAt_of_argReadable {sig : Signature Op} {d : Nat} {daemon : Bool} {fam : EffFam}
    {c : EffSelfCarrier Op fam}
    (h : argReadable sig d daemon (ArgF.fold (readableAlg sig) (.child fam c)) = true) :
    ReadableAt sig fam c d := by
  aesop (add norm simp [argReadable, ArgF.fold, ReadableAt, Option.isSome_iff_exists])

section Args

variable (sig : Signature Op) (σ : Subst)
  {child : (fam : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
    Except ReadFailure (EffSelfCarrier Op fam)}
  {children : (fam : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
    Except ReadFailure (EffSelfCarrier Op fam)}
  {block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, Arg.stmts ss) ∈ σ →
    Except ReadFailure (EffSelfCarrier Op .stmts)}

/-- `readCapture` at a child, by the capture's shape (the definition, at each arm). -/
theorem readCapture_expr_child (daemon : Bool) (d : Nat) (fam : EffFam) (i : Nat) (y : Expr)
    (hmem : (i, Arg.expr y) ∈ σ) :
    readCapture sig daemon σ child children block d (.child fam) i (.expr y) hmem =
      (child fam d y i hmem).map (.child fam) := rfl

theorem readCapture_exprs_child (daemon : Bool) (d : Nat) (fam : EffFam) (i : Nat)
    (ys : List Expr) (hmem : (i, Arg.exprs ys) ∈ σ) :
    readCapture sig daemon σ child children block d (.child fam) i (.exprs ys) hmem =
      (children fam d ys i hmem).map (.child fam) := rfl

theorem readCapture_stmts_child (daemon : Bool) (d : Nat) (i : Nat) (ss : List TypeScript.Stmt)
    (hmem : (i, Arg.stmts ss) ∈ σ) :
    readCapture sig daemon σ child children block d (.child .stmts) i (.stmts ss) hmem =
      (block d ss i hmem).map (.child .stmts) := rfl

/-- A readable leaf that printed to a capture reads back from it. -/
theorem readCapture_print_leaf (daemon : Bool) (d : Nat) (v : ArgF Op (EffSelfCarrier Op))
    (hr : argReadable sig d daemon (ArgF.fold (readableAlg sig) v) = true)
    (a : Arg) (hp : printArg sig d (ArgF.fold (printAlg sig) v) = .ok (some a))
    (hleaf : ∀ fam, argSortOf v ≠ .child fam) (i : Nat) (hmem : (i, a) ∈ σ) :
    readCapture sig daemon σ child children block d (argSortOf v) i a hmem = .ok v := by
  have hl := readLeaf_print (daemon := daemon) hleaf (leafReadable_of_argReadable hleaf hr) hp
  cases v <;> cases a <;> aesop (add norm simp [readCapture, argSortOf, ArgF.fold, printArg])

/-- A readable argument that printed to a capture reads back from it, at its sort. -/
theorem readCapture_print
    (hchild : ∀ fam d y i h c, ReadableAt sig fam c d → PrintsTo sig d fam c (.expr y) →
      child fam d y i h = .ok c)
    (hchildren : ∀ fam d ys i h c, ReadableAt sig fam c d → PrintsTo sig d fam c (.exprs ys) →
      children fam d ys i h = .ok c)
    (hblock : ∀ d ss i h c, ReadableAt sig .stmts c d → PrintsTo sig d .stmts c (.stmts ss) →
      block d ss i h = .ok c)
    (daemon : Bool) (d : Nat) (v : ArgF Op (EffSelfCarrier Op))
    (hr : argReadable sig d daemon (ArgF.fold (readableAlg sig) v) = true)
    (a : Arg) (hp : printArg sig d (ArgF.fold (printAlg sig) v) = .ok (some a))
    (i : Nat) (hmem : (i, a) ∈ σ) :
    readCapture sig daemon σ child children block d (argSortOf v) i a hmem = .ok v := by
  cases v with
  | child fam c =>
    have hra := readableAt_of_argReadable hr
    have hpa := printsTo_of_printArg hp
    cases fam <;> cases a <;> simp only [PrintsTo] at hpa <;>
      aesop (add norm simp [readCapture_expr_child, readCapture_exprs_child,
        readCapture_stmts_child, argSortOf, PrintsTo], safe forward [hchild, hchildren, hblock])
  | _ => exact readCapture_print_leaf sig σ daemon d _ hr a hp (fun _ h => by cases h) i hmem


/-! ### One argument, then all of them -/

variable (n : Nat) (row : Templates.Row)

/-- An argument the classifier supplies is the argument the printer tested: the row selects
the arguments only when every fixed pattern holds of them. -/
theorem supplied_eq_of_selects {fam : EffFam} {ctor : String}
    {args : List (ArgF Op (EffSelfCarrier Op))} (hsel : row.selects fam ctor args = true)
    (j : Nat) (v : ArgF Op (EffSelfCarrier Op)) (hv : args[j]? = some v)
    (a : ArgF Op (EffSelfCarrier Op)) (ha : row.supplied j = some a) : a = v := by
  unfold Templates.Row.supplied at ha
  have hall : ∀ p ∈ row.fixed, Templates.patternAt args p.1 p.2 = true := by
    simp only [Templates.Row.selects, Bool.and_eq_true, List.all_eq_true] at hsel
    exact hsel.2
  obtain ⟨p, hfind, hp⟩ := Option.bind_eq_some_iff.mp ha
  have hj : p.1 = j := by simpa only [beq_iff_eq] using List.find?_some hfind
  have hpat := hall p (List.mem_of_find?_eq_some hfind)
  cases p with
  | mk k pat =>
    cases pat <;> aesop (add norm simp [Templates.ArgPat.supplies, Templates.patternAt,
      Templates.ArgPat.holds], safe forward Fixed.holds_eq)

/-- One argument of a readable node reads back: supplied when the classifier fixes it, else
from what the skeleton captured, which is what the printer put there. -/
theorem readArg_print
    (hchild : ∀ fam d y i h c, ReadableAt sig fam c d → PrintsTo sig d fam c (.expr y) →
      child fam d y i h = .ok c)
    (hchildren : ∀ fam d ys i h c, ReadableAt sig fam c d → PrintsTo sig d fam c (.exprs ys) →
      children fam d ys i h = .ok c)
    (hblock : ∀ d ss i h c, ReadableAt sig .stmts c d → PrintsTo sig d .stmts c (.stmts ss) →
      block d ss i h = .ok c)
    (i : Nat) (v : ArgF Op (EffSelfCarrier Op)) {τ : Subst}
    (hsup : ∀ a, row.supplied i = some a → a = v)
    (hhole : (row.supplied (Op := Op) (R := EffSelfCarrier Op) i).isSome = false →
      i ∈ row.out.holes)
    (hlook : i ∈ row.out.holes → ∃ a, lookup τ i = some a)
    (hσ : i ∈ row.out.holes → lookup σ i = lookup τ i)
    (hprint : printArg sig (argDepth row.fam (argSortOf v) n (row.out.levelAt i))
      (ArgF.fold (printAlg sig) v) = .ok (lookup τ i))
    (hr : argReadable sig (argDepth row.fam (argSortOf v) n (row.out.levelAt i)) (rowDaemon row)
      (ArgF.fold (readableAlg sig) v) = true) :
    readArg sig n row σ child children block (argSortOf v) i = .ok v := by
  unfold readArg
  cases hs : row.supplied i with
  | some a => simp only [hsup a hs]
  | none =>
    have hin := hhole (by simp only [hs, Option.isSome_none])
    obtain ⟨a, ha⟩ := hlook hin
    have hσa : lookup σ i = some a := by rw [hσ hin, ha]
    obtain ⟨hmem, hcap⟩ := captured_of_lookup σ i a hσa
    rw [ha] at hprint
    simp only [hcap]
    exact readCapture_print sig σ hchild hchildren hblock (rowDaemon row) _ v hr a hprint i hmem

/-- The arguments of a readable node, in declaration order, read back to themselves. -/
theorem readArgs_print
    (hchild : ∀ fam d y i h c, ReadableAt sig fam c d → PrintsTo sig d fam c (.expr y) →
      child fam d y i h = .ok c)
    (hchildren : ∀ fam d ys i h c, ReadableAt sig fam c d → PrintsTo sig d fam c (.exprs ys) →
      children fam d ys i h = .ok c)
    (hblock : ∀ d ss i h c, ReadableAt sig .stmts c d → PrintsTo sig d .stmts c (.stmts ss) →
      block d ss i h = .ok c)
    {τ : Subst}
    (hlook : ∀ j ∈ row.out.holes, ∃ a, lookup τ j = some a)
    (hσ : ∀ j ∈ row.out.holes, lookup σ j = lookup τ j) :
    ∀ (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat),
    (∀ k v, args[k]? = some v → ∀ a, row.supplied (i + k) = some a → a = v) →
    (∀ k v, args[k]? = some v →
      (row.supplied (Op := Op) (R := EffSelfCarrier Op) (i + k)).isSome = false →
        (i + k) ∈ row.out.holes) →
    (∀ k v, args[k]? = some v →
      printArg sig (argDepth row.fam (argSortOf v) n (row.out.levelAt (i + k)))
        (ArgF.fold (printAlg sig) v) = .ok (lookup τ (i + k))) →
    (∀ k v, args[k]? = some v →
      argReadable sig (argDepth row.fam (argSortOf v) n (row.out.levelAt (i + k))) (rowDaemon row)
        (ArgF.fold (readableAlg sig) v) = true) →
    readArgs sig n row σ child children block (args.map argSortOf) i = .ok args
  | [], _, _, _, _, _ => rfl
  | v :: rest, i, hsup, hhole, hprint, hr => by
    have h0 := readArg_print sig σ n row hchild hchildren hblock i v
      (by simpa only [Nat.add_zero] using hsup 0 v rfl)
      (by simpa only [Nat.add_zero] using hhole 0 v rfl)
      (hlook i) (hσ i)
      (by simpa only [Nat.add_zero] using hprint 0 v rfl)
      (by simpa only [Nat.add_zero] using hr 0 v rfl)
    have ih := readArgs_print hchild hchildren hblock hlook hσ rest (i + 1)
      (fun k v hk => by rw [show i + 1 + k = i + (k + 1) by omega]; exact hsup (k + 1) v hk)
      (fun k v hk => by rw [show i + 1 + k = i + (k + 1) by omega]; exact hhole (k + 1) v hk)
      (fun k v hk => by rw [show i + 1 + k = i + (k + 1) by omega]; exact hprint (k + 1) v hk)
      (fun k v hk => by rw [show i + 1 + k = i + (k + 1) by omega]; exact hr (k + 1) v hk)
    simp only [List.map_cons, readArgs, h0, Except.mapError, ih, ok_bind]

end Args

/-- The table's sort column is the constructor's: the view of every node has the sorts the
table lists for its constructor. -/
theorem argSorts_view : ∀ (fam : EffFam) (e : EffSelfCarrier Op fam),
    argSorts fam (view fam e).1 = some ((view fam e).2.map argSortOf)
  | .eff, e => by cases e <;> rfl
  | .stmt, e => by cases e <;> rfl
  | .stmts, e => by cases e <;> rfl
  | .effs, e => by cases e <;> rfl
  | .action, e => by cases e <;> rfl
  | .layer, e => by cases e <;> rfl
  | .layers, e => by cases e <;> rfl


/-! ## Facts of the table, decided -/

/-- Every argument of a skeleton row is a hole of the skeleton or fixed by the classifier: the
reader has somewhere to take it from. -/
def rowComplete (row : Templates.Row) : Bool :=
  match row.out with
  | .tpl _ | .stmt _ =>
    match argSorts row.fam row.ctor with
    | some sorts => (List.range sorts.length).all fun j =>
        row.out.holes.contains j || (row.fixed.find? (·.1 == j)).any (·.2.fixes)
    | none => true
  | _ => true

theorem table_complete : table.all rowComplete = true := by decide

/-- At a row of the table, an argument the classifier does not supply is a hole. -/
theorem hole_of_not_supplied {row : Templates.Row} (hmem : row ∈ table) {t : Tpl}
    (hout : row.out = .tpl t) {sorts : List ArgSort} (hsorts : argSorts row.fam row.ctor = some sorts)
    (j : Nat) (hj : j < sorts.length)
    (hsup : (row.supplied (Op := Op) (R := EffSelfCarrier Op) j).isSome = false) :
    j ∈ row.out.holes := by
  have hc := table_fact table_complete hmem
  simp only [rowComplete, hout, hsorts, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.contains_eq_mem, decide_eq_true_eq] at hc
  unfold Templates.Row.supplied at hsup
  have hc := hc j hj
  cases hf : List.find? (fun x => x.1 == j) row.fixed with
  | none => rw [hout]; simpa only [hf, Option.any, Bool.false_eq_true, or_false] using hc
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only [hf, Option.bind_some, Option.any] at hc hsup
    rw [← ArgPat.supplies_isSome (Op := Op) (R := EffSelfCarrier Op), hsup] at hc
    rw [hout]; simpa only [Option.isSome_none, Bool.false_eq_true, or_false] using hc

/-- The same at a statement row. -/
theorem hole_of_not_supplied_stmt {row : Templates.Row} (hmem : row ∈ table) {t : StmtTpl}
    (hout : row.out = .stmt t) {sorts : List ArgSort} (hsorts : argSorts row.fam row.ctor = some sorts)
    (j : Nat) (hj : j < sorts.length)
    (hsup : (row.supplied (Op := Op) (R := EffSelfCarrier Op) j).isSome = false) :
    j ∈ row.out.holes := by
  have hc := table_fact table_complete hmem
  simp only [rowComplete, hout, hsorts, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    List.contains_eq_mem, decide_eq_true_eq] at hc
  unfold Templates.Row.supplied at hsup
  have hc := hc j hj
  cases hf : List.find? (fun x => x.1 == j) row.fixed with
  | none => rw [hout]; simpa only [hf, Option.any, Bool.false_eq_true, or_false] using hc
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only [hf, Option.bind_some, Option.any] at hc hsup
    rw [← ArgPat.supplies_isSome (Op := Op) (R := EffSelfCarrier Op), hsup] at hc
    rw [hout]; simpa only [Option.isSome_none, Bool.false_eq_true, or_false] using hc


/-! ## Lists: the index of what `find?` finds; `findSome?` over an indexed list -/

theorem find?_index {α : Type} (p : α → Bool) : ∀ (l : List α) (a : α), l.find? p = some a →
    ∃ k, l[k]? = some a ∧ l.findIdx? p = some k ∧ ∀ j < k, ∀ b, l[j]? = some b → p b = false
  | [], a, h => by aesop
  | x :: xs, a, h => by
    have ih := find?_index p xs a
    by_cases hx : p x = true
    · exact ⟨0, by aesop, by simp [List.findIdx?_cons, hx], fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · rw [List.find?_cons_of_neg hx] at h
      obtain ⟨k, hk, hidx, hbefore⟩ := ih h
      refine ⟨k + 1, by simpa using hk, by simp [List.findIdx?_cons, hx, hidx], fun j hj b hb => ?_⟩
      cases j with
      | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at hb; subst hb; simpa using hx
      | succ j => exact hbefore j (by omega) b (by simpa using hb)

theorem findSome?_zipIdx {α β : Type} (f : α × Nat → Option β) :
    ∀ (l : List α) (start k : Nat) (a : α) (v : β),
    (∀ j < k, ∀ b, l[j]? = some b → f (b, start + j) = none) →
    l[k]? = some a → f (a, start + k) = some v → (l.zipIdx start).findSome? f = some v
  | [], _, _, _, _, _, hk, _ => by aesop
  | x :: xs, start, 0, a, v, hbefore, hk, hv => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
    subst hk
    simp only [List.zipIdx_cons, List.findSome?_cons, Nat.add_zero] at hv ⊢
    rw [hv]
  | x :: xs, start, k + 1, a, v, hbefore, hk, hv => by
    have ih := findSome?_zipIdx f xs (start + 1) k a v
      (fun j hj b hb => by
        rw [show start + 1 + j = start + (j + 1) by omega]
        exact hbefore (j + 1) (by omega) b (by simpa using hb))
      (by simpa using hk) (by rw [show start + 1 + k = start + (k + 1) by omega]; exact hv)
    have h0 := hbefore 0 (by omega) x rfl
    rw [Nat.add_zero] at h0
    simp only [List.zipIdx_cons, List.findSome?_cons, h0]
    exact ih

/-! ## What the row call prints: its head is the spelling or none, and it is node-like -/

theorem printRow_head {row : Row} {r : Term} {x : Expr} (h : printRow row r = .ok x) :
    exprHead? x = none ∨ exprHead? x = some row.spelling := by
  unfold printRow at h
  aesop (add norm simp [printRowHead, printMethod, exprHead?])

theorem printRow_nodeLike {row : Row} {r : Term} {x : Expr} (h : printRow row r = .ok x) :
    nodeLike x = true := by
  unfold printRow at h
  aesop (add norm simp [printRowHead, printMethod, nodeLike])


/-! ## The pairwise fact of the table: no row before the printing row matches its image -/

/-- The heads of the action rows: what a `withFiber` image is headed by. -/
def actionHeads : List String := table.filterMap fun r =>
  if r.fam = .action then match r.out with | .tpl t => t.head? | _ => none else none

/-- `rowsApart earlier later`: the reason `earlier` cannot match an image of `later`, by the
shape of `later`'s output. A skeleton against a rigid skeleton: `apartBy`. A skeleton against a
transparent row: the image is an action's (headed by an action head the skeleton does not have)
or a name (which no rigid skeleton matches). A skeleton against the row call: its head is
reserved, and the row call's image is headed by a spelling or nothing; the transparent row
before the row call hands the image to the action family, whose rows are all such skeletons.
Statement rows are apart by former. -/
def rowsApart (rj rk : Templates.Row) : Bool :=
  match rk.out with
  | .tpl t =>
    match rj.out with
    | .refuse _ | .stmt _ => true
    | .rowCall => false
    | .tpl t' =>
      if t.rigid then
        t'.rigid && (match argSorts rk.fam rk.ctor with
          | some sorts => apartBy sorts t' t
          | none => false)
      else
        t'.rigid && (match argSorts rk.fam rk.ctor with
          | some [.child .action] => (t'.head?).any fun h => !actionHeads.contains h
          | some [.path] => t'.notName
          | _ => false)
  | .rowCall =>
    match rj.out with
    | .refuse _ | .stmt _ => true
    | .rowCall => false
    | .tpl t' =>
      (t'.rigid && (t'.head?).any (reserved.contains ·)) ||
        (!t'.rigid && argSorts rj.fam rj.ctor == some [.child .action])
  | .stmt t => match rj.out with | .stmt t' => t'.former != t.former | _ => true
  | .refuse _ => true

theorem table_apart : (List.range table.length).all (fun k => (List.range k).all fun j =>
    match table[j]?, table[k]? with
    | some rj, some rk => rj.fam != rk.fam || rowsApart rj rk
    | _, _ => true) = true := by decide

/-- The shape of the rows of the expression families: a rigid skeleton has a node-like top and
a head, a transparent one hands to the action family or reads a name; every action row is a
rigid skeleton with a reserved head, or a refusal. -/
def rowShape (row : Templates.Row) : Bool :=
  match row.fam, row.out with
  | .eff, .tpl t | .action, .tpl t | .layer, .tpl t =>
    if t.rigid then t.nodeTop
    else (row.fam == .eff && argSorts row.fam row.ctor == some [.child .action]) ||
      (row.fam == .layer && argSorts row.fam row.ctor == some [.path])
  | _, _ => true

theorem table_shape : table.all rowShape = true := by decide

def actionRowHeaded (row : Templates.Row) : Bool :=
  row.fam != .action || match row.out with
    | .tpl t => t.rigid && (t.head?).any (reserved.contains ·)
    | .refuse _ => true
    | _ => false

theorem table_actionHeaded : table.all actionRowHeaded = true := by decide


/-! ## The printer and the domain at a node, inverted -/

section Node

variable {sig : Signature Op} {spell : String → List String → Option Op}

/-- What the printer did at a node of an expression family. -/
theorem rowPrint_inv {fam : EffFam} {ctor : String} {args : List (ArgF Op Carrier)} {n : Nat}
    {x : Expr} (h : tableLayer.rowPrint sig fam ctor args n = .ok x) :
    ∃ row, table.find? (fun r => r.selects fam ctor args) = some row ∧
      ((∃ t τ, row.out = .tpl t ∧ printArgs sig fam n (.tpl t) args 0 = .ok τ ∧
          inst n τ t = some x) ∨
       (∃ op r, row.out = .rowCall ∧ args = [.op op, .term r] ∧
          printRow (sig.rowOf op) r = .ok x)) := by
  unfold tableLayer.rowPrint at h
  aesop

/-- What the domain said at a node of an expression family. -/
theorem rowDom_inv {fam : EffFam} {ctor : String} {args : List (ArgF Op Dom)} {n d : Nat}
    (h : domLayer.rowDom sig fam ctor args n = some d) :
    ∃ row, table.find? (fun r => r.selects fam ctor args) = some row ∧
      ((∃ t, row.out = .tpl t ∧ argsReadable sig fam n (.tpl t) (rowDaemon row) args 0 = true) ∨
       (∃ op r, row.out = .rowCall ∧ args = [.op op, .term r] ∧ sig.dom op = true ∧
          requestReadable (sig.rowOf op) n r = true)) := by
  unfold domLayer.rowDom at h
  aesop

/-- The row the printer chooses is chosen by the classifier alone: folding the children with
either algebra finds the same row. -/
theorem find?_selects_fold {R R' : EffFam → Type} (alg : EffAlgebra Op R) (alg' : EffAlgebra Op R')
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op))) :
    (table.find? fun r => r.selects fam ctor (args.map (ArgF.fold alg))) =
      table.find? fun r => r.selects fam ctor (args.map (ArgF.fold alg')) := by
  simp only [selects_fold]

/-- A node of an expression family whose view is `(ctor, args)` is `perform op r` when its
arguments are an operation and a term. -/
theorem eff_of_view_op_term (e : Eff Op) (op : Op) (r : Term)
    (h : (view .eff e).2 = [.op op, .term r]) : e = .perform op r := by
  cases e <;> simp_all [view, view_eff]

/-! ## Rows that do not fire -/

variable {fam : EffFam} {n : Nat} {x : Expr} {k : Nat}
  {child : (fam' : EffFam) → Nat → (y : Expr) → sizeOf y < sizeOf x →
    Except ReadFailure (EffSelfCarrier Op fam')}
  {children : (fam' : EffFam) → Nat → (ys : List Expr) → sizeOf ys < sizeOf x →
    Except ReadFailure (EffSelfCarrier Op fam')}
  {block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf x →
    Except ReadFailure (EffSelfCarrier Op .stmts)}
  {same : (fam' : EffFam) → famRank fam' < famRank fam → Nat →
    Option (Except ReadFailure (EffSelfCarrier Op fam'))}

theorem readRow_none_of_fam {row : Templates.Row} (h : row.fam ≠ fam) :
    readRow sig spell fam n x row k child children block same = none := by
  unfold readRow; simp only [h, ↓reduceIte]

theorem readRow_none_of_refuse {row : Templates.Row} {name : String} (h : row.out = .refuse name) :
    readRow sig spell fam n x row k child children block same = none := by
  unfold readRow; aesop

theorem readRow_none_of_stmt {row : Templates.Row} {t : StmtTpl} (h : row.out = .stmt t) :
    readRow sig spell fam n x row k child children block same = none := by
  unfold readRow; aesop

theorem readRow_none_of_nomatch {row : Templates.Row} {t : Tpl} (hout : row.out = .tpl t)
    (hm : matchT n t x = none) :
    readRow sig spell fam n x row k child children block same = none := by
  unfold readRow; aesop

/-- A transparent row whose lower family reads nothing reads nothing. -/
theorem readRow_none_of_same {row : Templates.Row} {i : Nat} (hout : row.out = .tpl (.hole i))
    {fam' : EffFam} (hsorts : argSorts row.fam row.ctor = some [.child fam'])
    (hsame : ∀ hk d, same fam' hk d = none) :
    readRow sig spell fam n x row k child children block same = none := by
  unfold readRow
  aesop (add norm simp [Tpl.rigid, hsame])


/-! ## The printing row reads its image back -/

theorem selects_fam_ctor {R : EffFam → Type} {row : Templates.Row} {ctor : String}
    {args : List (ArgF Op R)} (hsel : row.selects fam ctor args = true) :
    row.fam = fam ∧ row.ctor = ctor := by
  simp only [Templates.Row.selects, Bool.and_eq_true, beq_iff_eq] at hsel
  exact ⟨hsel.1.1, hsel.1.2⟩

theorem buildRow_of_findIdx? {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    {e : EffSelfCarrier Op fam} (hbuild : build fam ctor args = some e)
    (hidx : table.findIdx? (fun r => r.selects fam ctor args) = some k) :
    buildRow fam ctor args k = .ok e := by
  unfold buildRow printedRow
  simp only [hidx, decide_true, ↓reduceIte, hbuild]

/-- The arguments of a readable node at the printing row read back, from the substitution the
skeleton's match returns. -/
theorem readArgs_at_print {row : Templates.Row} (hmem : row ∈ table)
    {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    (hsel : row.selects fam ctor args = true) (hsorts : argSorts fam ctor = some (args.map argSortOf))
    {t : Tpl} (hout : row.out = .tpl t)
    {τ : Subst} (hτ : printArgs sig fam n (.tpl t) (args.map (ArgF.fold (printAlg sig))) 0 = .ok τ)
    (hinst : inst n τ t = some x)
    (hr : argsReadable sig fam n (.tpl t) (rowDaemon row) (args.map (ArgF.fold (readableAlg sig))) 0
      = true)
    {σ : Subst} (hagree : ∀ i ∈ holes t, lookup σ i = lookup τ i)
    {child' : (fam' : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam')}
    {children' : (fam' : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op fam')}
    {block' : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, Arg.stmts ss) ∈ σ →
      Except ReadFailure (EffSelfCarrier Op .stmts)}
    (hchild : ∀ fam' d y i h c, ReadableAt sig fam' c d → PrintsTo sig d fam' c (.expr y) →
      child' fam' d y i h = .ok c)
    (hchildren : ∀ fam' d ys i h c, ReadableAt sig fam' c d → PrintsTo sig d fam' c (.exprs ys) →
      children' fam' d ys i h = .ok c)
    (hblock : ∀ d ss i h c, ReadableAt sig .stmts c d → PrintsTo sig d .stmts c (.stmts ss) →
      block' d ss i h = .ok c) :
    readArgs sig n row σ child' children' block' (args.map argSortOf) 0 = .ok args := by
  obtain ⟨hfam, hctor⟩ := selects_fam_ctor hsel
  obtain ⟨hprint, _⟩ := printArgs_lookup (args.map (ArgF.fold (printAlg sig))) 0 τ hτ
  have hsorts' : argSorts row.fam row.ctor = some (args.map argSortOf) := by
    rw [hfam, hctor]; exact hsorts
  refine readArgs_print sig σ n row hchild hchildren hblock (τ := τ) ?_ ?_ args 0 ?_ ?_ ?_ ?_
  · intro j hj
    rw [hout] at hj
    exact holes_of_inst n τ t x hinst j hj
  · intro j hj
    rw [hout] at hj
    exact hagree j hj
  · intro k v hk a ha
    exact supplied_eq_of_selects row hsel (0 + k) v (by simpa using hk) a ha
  · intro k v hk hsup
    exact hole_of_not_supplied hmem hout hsorts' (0 + k)
      (by simp only [List.length_map, Nat.zero_add]; exact (List.getElem?_eq_some_iff.mp hk).1) hsup
  · intro k v hk
    have := hprint k (ArgF.fold (printAlg sig) v) (by simp only [List.getElem?_map, hk, Option.map_some])
    rw [argSortOf_fold] at this
    simpa only [hfam, hout] using this
  · intro k v hk
    have := argsReadable_at (args.map (ArgF.fold (readableAlg sig))) 0 k (ArgF.fold (readableAlg sig) v)
      hr (by simp only [List.getElem?_map, hk, Option.map_some])
    rw [argSortOf_fold] at this
    simpa only [hfam, hout] using this


/-- **The printing row reads its image back**, when it is a rigid skeleton. -/
theorem readRow_rigid_print {row : Templates.Row} (hk : table[k]? = some row)
    {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))} {e : EffSelfCarrier Op fam}
    (hbuild : build fam ctor args = some e) (hsorts : argSorts fam ctor = some (args.map argSortOf))
    (hsel : row.selects fam ctor args = true)
    (hidx : table.findIdx? (fun r => r.selects fam ctor args) = some k)
    {t : Tpl} (hout : row.out = .tpl t) (hrigid : t.rigid = true)
    {τ : Subst} (hτ : printArgs sig fam n (.tpl t) (args.map (ArgF.fold (printAlg sig))) 0 = .ok τ)
    (hinst : inst n τ t = some x)
    (hr : argsReadable sig fam n (.tpl t) (rowDaemon row) (args.map (ArgF.fold (readableAlg sig))) 0
      = true)
    (hchild : ∀ fam' d y (hy : sizeOf y < sizeOf x) c, ReadableAt sig fam' c d →
      PrintsTo sig d fam' c (.expr y) → child fam' d y hy = .ok c)
    (hchildren : ∀ fam' d ys (hy : sizeOf ys < sizeOf x) c, ReadableAt sig fam' c d →
      PrintsTo sig d fam' c (.exprs ys) → children fam' d ys hy = .ok c)
    (hblock : ∀ d ss (hy : sizeOf ss < sizeOf x) c, ReadableAt sig .stmts c d →
      PrintsTo sig d .stmts c (.stmts ss) → block d ss hy = .ok c) :
    readRow sig spell fam n x row k child children block same = some (.ok e) := by
  obtain ⟨hfam, hctor⟩ := selects_fam_ctor hsel
  obtain ⟨σ, hσ, hagree⟩ := match_of_inst n τ t x hinst
  have hargs := readArgs_at_print (List.mem_of_getElem? hk) hsel hsorts hout hτ hinst hr hagree
    (child' := fun fam' d y i hy => child fam' d y (match_below n t x σ hrigid hσ (i, .expr y) hy))
    (children' := fun fam' d ys i hy =>
      children fam' d ys (match_below n t x σ hrigid hσ (i, .exprs ys) hy))
    (block' := fun d body i hy => block d body (match_below n t x σ hrigid hσ (i, .stmts body) hy))
    (fun fam' d y i hy c hr hp => hchild fam' d y _ c hr hp)
    (fun fam' d ys i hy c hr hp => hchildren fam' d ys _ c hr hp)
    (fun d ss i hy c hr hp => hblock d ss _ c hr hp)
  have hb := buildRow_of_findIdx? hbuild hidx
  obtain ⟨rfam, rctor, rfixed, rout⟩ := row
  simp only at hfam hctor hout
  subst hfam hctor hout
  unfold readRow
  simp only [↓reduceIte, hsorts, hrigid, ↓reduceDIte]
  split
  · rename_i hnone; rw [hσ] at hnone; cases hnone
  · rename_i σ' hσ'
    rw [hσ] at hσ'
    obtain rfl := Option.some.inj hσ'
    simp only [hargs, ok_bind, hb]


/-- The printing row, transparent to the action family (`withFiber`), reads its image back:
the same tree read as an action, then the node rebuilt. -/
theorem readRow_action_print {row : Templates.Row} (hk : table[k]? = some row)
    {ctor : String} {c : EffSelfCarrier Op .action} {e : EffSelfCarrier Op fam}
    (hbuild : build fam ctor ([.child .action c] : List (ArgF Op (EffSelfCarrier Op))) = some e)
    (hsorts : argSorts fam ctor = some [.child .action])
    (hsel : row.selects fam ctor ([.child .action c] : List (ArgF Op (EffSelfCarrier Op))) = true)
    (hidx : table.findIdx? (fun r => r.selects fam ctor ([.child .action c] : List (ArgF Op (EffSelfCarrier Op)))) = some k)
    {i : Nat} (hout : row.out = .tpl (.hole i)) (hrank : famRank .action < famRank fam)
    (hprint : cata_action (printAlg sig) c (argDepth fam (.child .action) n 0) = .ok x)
    (hr : ReadableAt sig .action c (argDepth fam (.child .action) n 0))
    (hsame : ∀ fam' hlt d (c' : EffSelfCarrier Op fam'), ReadableAt sig fam' c' d →
      PrintsTo sig d fam' c' (.expr x) → same fam' hlt d = some (.ok c')) :
    readRow sig spell fam n x row k child children block same = some (.ok e) := by
  obtain ⟨hfam, hctor⟩ := selects_fam_ctor hsel
  have hb := buildRow_of_findIdx? hbuild hidx
  have hs := hsame .action hrank _ c hr (by simpa only [PrintsTo] using hprint)
  obtain ⟨rfam, rctor, rfixed, rout⟩ := row
  simp only at hfam hctor hout
  subst hfam hctor hout
  unfold readRow
  simp only [↓reduceIte, matchT, hsorts, Tpl.rigid, Bool.false_eq_true, ↓reduceDIte, hrank, hs,
    Option.map_some, Except.mapError, ok_bind, hb]

/-- The printing row that reads a name (`ref`) reads its image back. -/
theorem readRow_path_print {row : Templates.Row} (hk : table[k]? = some row)
    {ctor : String} {p : List Nat} {e : EffSelfCarrier Op fam}
    (hbuild : build fam ctor ([.path p] : List (ArgF Op (EffSelfCarrier Op))) = some e)
    (hsorts : argSorts fam ctor = some [.path])
    (hsel : row.selects fam ctor ([.path p] : List (ArgF Op (EffSelfCarrier Op))) = true)
    (hidx : table.findIdx? (fun r => r.selects fam ctor ([.path p] : List (ArgF Op (EffSelfCarrier Op)))) = some k)
    {i : Nat} (hout : row.out = .tpl (.hole i))
    (hx : x = .ident (LayerTerm.refName p))
    (hr : LayerTerm.readRefName (LayerTerm.refName p) = some p) :
    readRow sig spell fam n x row k child children block same = some (.ok e) := by
  obtain ⟨hfam, hctor⟩ := selects_fam_ctor hsel
  have hb := buildRow_of_findIdx? hbuild hidx
  obtain ⟨rfam, rctor, rfixed, rout⟩ := row
  simp only at hfam hctor hout
  subst hfam hctor hout hx
  unfold readRow
  simp only [↓reduceIte, matchT, hsorts, Tpl.rigid, Bool.false_eq_true, ↓reduceDIte, readLeaf, hr,
    ↓reduceIte, hb, Except.toOption, Option.map_some]

/-- The row call reads its image back: the printed row of `perform` reads to `perform`. -/
theorem readRow_rowCall_print (hl : LawfulSpelling sig spell) {row : Templates.Row}
    (hrow : row.out = .rowCall) (hfam : row.fam = .eff) {op : Op} {r : Term}
    (hd : sig.dom op = true) (hreq : requestReadable (sig.rowOf op) n r = true)
    (hp : printRow (sig.rowOf op) r = .ok x) (hfam' : fam = .eff) :
    readRow sig spell fam n x row k child children block same =
      some (.ok (hfam' ▸ (Eff.perform op r : EffSelfCarrier Op .eff))) := by
  subst hfam'
  obtain ⟨rfam, rctor, rfixed, rout⟩ := row
  simp only at hfam hrow
  subst hfam hrow
  unfold readRow
  simp only [↓reduceIte, read_printRow hl op hd r hreq hp, rowAnswer, Except.mapError]


/-! ## No row before the printing row fires -/

/-- A skeleton with a reserved head does not match the row call's image. -/
theorem matchT_none_of_reserved (hl : LawfulSpelling sig spell) {op : Op} {r : Term}
    (hp : printRow (sig.rowOf op) r = .ok x) {t : Tpl} {h : String} (hh : t.head? = some h)
    (hres : h ∈ reserved) : matchT n t x = none := by
  cases hm : matchT n t x with
  | none => rfl
  | some σ =>
    have h1 := head_of_match n t x σ hm hh
    rcases printRow_head hp with h2 | h2 <;> rw [h1] at h2
    · cases h2
    · exact absurd (Option.some.inj h2 ▸ hres) (hl.spelling_not_reserved op)

/-- No action row reads the row call's image. -/
theorem readT_action_none_of_printRow (hl : LawfulSpelling sig spell) {op : Op} {r : Term}
    (hp : printRow (sig.rowOf op) r = .ok x) (d : Nat) : readT sig spell .action d x = none := by
  rw [readT, List.findSome?_eq_none_iff]
  intro p hmem
  obtain ⟨row, k⟩ := p
  have hrow : row ∈ table := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hmem)
  have hshape := table_fact table_actionHeaded hrow
  simp only [actionRowHeaded, bne_iff_ne, ne_eq, Bool.or_eq_true] at hshape
  rcases hshape with hfam | hshape
  · exact readRow_none_of_fam hfam
  · split at hshape
    · rename_i t hout
      simp only [Bool.and_eq_true, Option.any_eq_true] at hshape
      obtain ⟨_, h, hh, hres⟩ := hshape
      exact readRow_none_of_nomatch hout
        (matchT_none_of_reserved hl hp hh (List.mem_of_elem_eq_true hres))
    · rename_i name hout
      exact readRow_none_of_refuse hout
    · cases hshape

/-- The heads of the images of the action family are action heads. -/
theorem mem_actionHeads {row : Templates.Row} (hmem : row ∈ table) (hfam : row.fam = .action)
    {t : Tpl} (hout : row.out = .tpl t) {h : String} (hh : t.head? = some h) :
    h ∈ actionHeads := by
  unfold actionHeads
  rw [List.mem_filterMap]
  exact ⟨row, hmem, by simp only [hfam, ↓reduceIte, hout, hh]⟩

section Earlier

variable {rj : Templates.Row} {j : Nat} {row : Templates.Row} (hap : rowsApart rj row = true)
include hap

/-- Before a rigid printing row. -/
theorem earlier_none_rigid {t : Tpl} (hout : row.out = .tpl t) (hrigid : t.rigid = true)
    {sorts : List ArgSort} (hsorts : argSorts row.fam row.ctor = some sorts) {τ : Subst}
    (hinst : inst n τ t = some x)
    (hnode : ∀ i y, childHole sorts i = true → i ∈ holes t → lookup τ i = some (.expr y) →
      nodeLike y = true) :
    readRow sig spell fam n x rj j child children block same = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only [hrigid, ↓reduceIte, hsorts] at hap
  split at hap
  · rename_i name h; exact readRow_none_of_refuse h
  · rename_i st h; exact readRow_none_of_stmt h
  · cases hap
  · rename_i t' h
    simp only [Bool.and_eq_true] at hap
    exact readRow_none_of_nomatch h (match_apart n τ sorts t' t x hap.2 hinst hnode)

/-- Before the transparent row that hands to the action family: the image is an action's. -/
theorem earlier_none_action {i : Nat} (hout : row.out = .tpl (.hole i))
    (hsorts : argSorts row.fam row.ctor = some [.child .action]) {h : String}
    (hx : exprHead? x = some h) (hact : h ∈ actionHeads) :
    readRow sig spell fam n x rj j child children block same = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only [Tpl.rigid, Bool.false_eq_true, ↓reduceIte, hsorts] at hap
  split at hap
  · rename_i name h; exact readRow_none_of_refuse h
  · rename_i st h; exact readRow_none_of_stmt h
  · cases hap
  · rename_i t' h'
    simp only [Bool.and_eq_true, Option.any_eq_true] at hap
    obtain ⟨_, h'', hh, hnot⟩ := hap
    refine readRow_none_of_nomatch h' ?_
    cases hm : matchT n t' x with
    | none => rfl
    | some σ =>
      have := head_of_match n t' x σ hm hh
      rw [hx, Option.some.injEq] at this
      subst this
      simp only [List.contains_eq_mem, hact, decide_true, Bool.not_true, Bool.false_eq_true] at hnot

/-- Before the transparent row that reads a name: the image is an identifier. -/
theorem earlier_none_path {i : Nat} (hout : row.out = .tpl (.hole i))
    (hsorts : argSorts row.fam row.ctor = some [.path]) {s : String} (hx : x = .ident s) :
    readRow sig spell fam n x rj j child children block same = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only [Tpl.rigid, Bool.false_eq_true, ↓reduceIte, hsorts] at hap
  split at hap
  · rename_i name h; exact readRow_none_of_refuse h
  · rename_i st h; exact readRow_none_of_stmt h
  · cases hap
  · rename_i t' h'
    simp only [Bool.and_eq_true] at hap
    subst hx
    exact readRow_none_of_nomatch h' (matchT_ident_none n t' s hap.2)

/-- Before the row call: a skeleton's head is reserved and the image's is a spelling; the
transparent row hands the image to the action family, which reads nothing of it. -/
theorem earlier_none_rowCall (hl : LawfulSpelling sig spell) (hrow : row.out = .rowCall)
    {op : Op} {r : Term} (hp : printRow (sig.rowOf op) r = .ok x)
    (hsame : ∀ hk d, same .action hk d = none) :
    readRow sig spell fam n x rj j child children block same = none := by
  unfold rowsApart at hap
  rw [hrow] at hap
  simp only at hap
  split at hap
  · rename_i name h; exact readRow_none_of_refuse h
  · rename_i st h; exact readRow_none_of_stmt h
  · cases hap
  · rename_i t' h'
    simp only [Bool.or_eq_true, Bool.and_eq_true, Option.any_eq_true, Bool.not_eq_true',
      beq_iff_eq] at hap
    rcases hap with ⟨_, h, hh, hres⟩ | ⟨hnr, hsorts⟩
    · exact readRow_none_of_nomatch h'
        (matchT_none_of_reserved hl hp hh (List.mem_of_elem_eq_true hres))
    · cases t' with
      | hole i => exact readRow_none_of_same h' hsorts hsame
      | _ => cases hnr

end Earlier


/-! ## The reader reaches the printing row -/

/-- Rows before `k` in the table are apart from row `k`, or of another family. -/
theorem apart_of_lt {j : Nat} {rj : Templates.Row} (hj : table[j]? = some rj)
    {row : Templates.Row} (hk : table[k]? = some row) (hlt : j < k) :
    rj.fam ≠ row.fam ∨ rowsApart rj row = true := by
  have h := table_apart
  simp only [List.all_eq_true, List.mem_range] at h
  have := h k (List.getElem?_eq_some_iff.mp hk).1 j hlt
  simp only [hj, hk, Bool.or_eq_true, bne_iff_ne, ne_eq] at this
  exact this

/-- `readT` is the first row that fires: when every earlier row returns `none` and row `k`
returns the node, `readT` returns the node. -/
theorem readT_of_row {row : Templates.Row} (hk : table[k]? = some row)
    {e : EffSelfCarrier Op fam}
    (hbefore : ∀ j < k, ∀ rj, table[j]? = some rj →
      readRow sig spell fam n x rj j
        (fun fam' d y _ => (readT sig spell fam' d y).getD (.error (.here (unread fam'))))
        (fun fam' d ys _ => readSpine sig spell fam' d ys)
        (fun d body _ => readStmts sig spell d body)
        (fun fam' _ d => readT sig spell fam' d x) = none)
    (hat : readRow sig spell fam n x row k
        (fun fam' d y _ => (readT sig spell fam' d y).getD (.error (.here (unread fam'))))
        (fun fam' d ys _ => readSpine sig spell fam' d ys)
        (fun d body _ => readStmts sig spell d body)
        (fun fam' _ d => readT sig spell fam' d x) = some (.ok e)) :
    readT sig spell fam n x = some (.ok e) := by
  rw [readT]
  refine findSome?_zipIdx (fun (p : Templates.Row × Nat) => readRow sig spell fam n x p.1 p.2
      (fun fam' d y _ => (readT sig spell fam' d y).getD (.error (.here (unread fam'))))
      (fun fam' d ys _ => readSpine sig spell fam' d ys)
      (fun d body _ => readStmts sig spell d body)
      (fun fam' _ d => readT sig spell fam' d x)) table 0 k row (.ok e)
    (fun j hj rj hrj => ?_) hk ?_
  · simpa only [Nat.zero_add] using hbefore j hj rj hrj
  · simpa only [Nat.zero_add] using hat


/-! ## The node step -/

/-- An action's image is headed by an action head: every action row is a rigid skeleton with a
head (or a refusal, which prints nothing). -/
theorem action_image_head {c : EffSelfCarrier Op .action} {d : Nat} {x : Expr}
    (hx : cata_action (printAlg sig) c d = .ok x) : ∃ h, exprHead? x = some h ∧ h ∈ actionHeads := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view .action c = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build .action ctor args = some c := by have := build_view .action c; rwa [hview] at this
  have hp : tableLayer.rowPrint sig .action ctor (args.map (ArgF.fold (printAlg sig))) d = .ok x := by
    have := cata_build (tableLayer sig) .action ctor args c hbuild
    simp only [cataFam] at this
    rw [show printAlg sig = EffAlgebra.ofLayer (tableLayer sig) from rfl, this] at hx
    exact hx
  obtain ⟨row, hfind, hcase⟩ := rowPrint_inv hp
  have hmem := List.mem_of_find?_eq_some hfind
  have hfam : row.fam = .action := by
    have := List.find?_some hfind
    exact (selects_fam_ctor this).1
  have hshape := table_fact table_actionHeaded hmem
  simp only [actionRowHeaded, hfam, bne_self_eq_false, Bool.false_or] at hshape
  rcases hcase with ⟨t, τ, hout, _, hinst⟩ | ⟨_, _, hout, _, _⟩
  · rw [hout] at hshape
    simp only [Bool.and_eq_true, Option.any_eq_true] at hshape
    obtain ⟨_, h, hh, _⟩ := hshape
    exact ⟨h, head_of_inst d τ t x hinst hh, mem_actionHeads hmem hfam hout hh⟩
  · rw [hout] at hshape; cases hshape

/-- The row call's arguments, through the fold. -/
theorem fold_eq_op_term {R : EffFam → Type} (alg : EffAlgebra Op R)
    {args : List (ArgF Op (EffSelfCarrier Op))} {op : Op} {r : Term}
    (h : args.map (ArgF.fold alg) = [.op op, .term r]) : args = [.op op, .term r] :=
  match args, h with
  | [a, b], h => by
    cases a <;> cases b <;> simp only [List.map_cons, List.map_nil, ArgF.fold, List.cons.injEq,
      reduceCtorEq, and_true, and_false, false_and, ArgF.op.injEq, ArgF.term.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | [], h => by simp only [List.map_nil, reduceCtorEq] at h
  | [_], h => by simp only [List.map_cons, List.map_nil, List.cons.injEq, reduceCtorEq, and_false] at h
  | _ :: _ :: _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq, reduceCtorEq, and_false] at h


section Step

variable (hl : LawfulSpelling sig spell) {fam : EffFam} {n : Nat} {x : Expr}
  {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))} {e : EffSelfCarrier Op fam}
  (hbuild : build fam ctor args = some e) (hsorts : argSorts fam ctor = some (args.map argSortOf))
  {row : Templates.Row} {k : Nat} (hk : table[k]? = some row)
  (hsel : row.selects fam ctor args = true)
  (hidx : table.findIdx? (fun r => r.selects fam ctor args) = some k)
  (hchild : ∀ fam' d (y : Expr), sizeOf y < sizeOf x → ∀ c, ReadableAt sig fam' c d →
    PrintsTo sig d fam' c (.expr y) → readT sig spell fam' d y = some (.ok c) ∧ nodeLike y = true)
  (hchildren : ∀ fam' d (ys : List Expr), sizeOf ys < sizeOf x → ∀ c, ReadableAt sig fam' c d →
    PrintsTo sig d fam' c (.exprs ys) → readSpine sig spell fam' d ys = .ok c)
  (hblock : ∀ d (ss : List TypeScript.Stmt), sizeOf ss < sizeOf x → ∀ c, ReadableAt sig .stmts c d →
    PrintsTo sig d .stmts c (.stmts ss) → readStmts sig spell d ss = .ok c)
  (hsame : ∀ fam', famRank fam' < famRank fam → ∀ d c, ReadableAt sig fam' c d →
    PrintsTo sig d fam' c (.expr x) → readT sig spell fam' d x = some (.ok c) ∧ nodeLike x = true)

/-- A capture `lookup` finds is a member. -/
theorem mem_of_lookup {σ : Subst} {i : Nat} {a : Arg} (h : lookup σ i = some a) : (i, a) ∈ σ := by
  unfold lookup at h
  obtain ⟨p, hfind, hp⟩ := Option.map_eq_some_iff.mp h
  have hi := List.find?_some hfind
  obtain ⟨j, b⟩ := p
  simp only [beq_iff_eq] at hi
  simp only at hp
  subst hi hp
  exact List.mem_of_find?_eq_some hfind

include hchild in
/-- The child at a hole of the printing skeleton is node-like: its image is captured there, it
is smaller than the tree, and it is readable, so the recursion says so. -/
theorem child_at_hole {t : Tpl} (_hout : row.out = .tpl t) (hrigid : t.rigid = true) {τ : Subst}
    (hτ : printArgs sig fam n (.tpl t) (args.map (ArgF.fold (printAlg sig))) 0 = .ok τ)
    (hinst : inst n τ t = some x)
    (hr : argsReadable sig fam n (.tpl t) (rowDaemon row) (args.map (ArgF.fold (readableAlg sig))) 0
      = true)
    (i : Nat) (y : Expr) (hc : childHole (args.map argSortOf) i = true) (hin : i ∈ holes t)
    (hlook : lookup τ i = some (.expr y)) : nodeLike y = true := by
  obtain ⟨σ, hσ, hagree⟩ := match_of_inst n τ t x hinst
  obtain ⟨hprint, _⟩ := printArgs_lookup (args.map (ArgF.fold (printAlg sig))) 0 τ hτ
  have hlt : sizeOf y < sizeOf x :=
    match_below n t x σ hrigid hσ (i, .expr y) (mem_of_lookup (by rw [hagree i hin, hlook]))
  -- the argument at `i` is a child of an expression family
  unfold childHole at hc
  rw [List.getElem?_map] at hc
  cases ha : args[i]? with
  | none => rw [ha] at hc; exact absurd hc Bool.false_ne_true
  | some a =>
    rw [ha] at hc
    have hp := hprint i (ArgF.fold (printAlg sig) a) (by simp only [List.getElem?_map, ha, Option.map_some])
    have hra := argsReadable_at (args.map (ArgF.fold (readableAlg sig))) 0 i
      (ArgF.fold (readableAlg sig) a) hr (by simp only [List.getElem?_map, ha, Option.map_some])
    rw [argSortOf_fold] at hp hra
    rw [Nat.zero_add, hlook] at hp
    rw [Nat.zero_add] at hra
    cases a with
    | child fam' c =>
      exact (hchild fam' _ y hlt c (readableAt_of_argReadable hra) (printsTo_of_printArg hp)).2
    | _ => exact absurd hc Bool.false_ne_true


/-- The single argument of a transparent row, from the sort column. -/
theorem args_of_sorts_single {args : List (ArgF Op (EffSelfCarrier Op))} {s : ArgSort}
    (h : args.map argSortOf = [s]) : ∃ a, args = [a] ∧ argSortOf a = s := by
  cases args with
  | nil => cases h
  | cons a rest =>
    cases rest with
    | nil => exact ⟨a, rfl, by simpa only [List.map_cons, List.map_nil, List.cons.injEq, and_true] using h⟩
    | cons b rest' => simp only [List.map_cons, List.cons.injEq, reduceCtorEq, and_false] at h

/-- The hole of a transparent row is hole `0`: it is an argument, and there is one. -/
theorem hole_zero {row : Templates.Row} (hmem : row ∈ table) {i : Nat}
    (hout : row.out = .tpl (.hole i)) {s : ArgSort} (hsorts : argSorts row.fam row.ctor = some [s]) :
    i = 0 := by
  obtain ⟨_, _, hlt⟩ := table_row hmem
  rw [hout] at hlt
  have := hlt [s] hsorts i (by simp only [Templates.RowOut.holes, holes, List.mem_singleton])
  simp only [List.length_singleton] at this
  omega

include hl hchild hchildren hblock hsame in
/-- **The node step.** A readable node of an expression family whose image is `x` reads back
from `x`, and `x` is node-like — given the recursion below the node and at the lower families. -/
theorem readT_print (hfam : fam = .eff ∨ fam = .action ∨ fam = .layer)
    {e : EffSelfCarrier Op fam} (hx : PrintsTo sig n fam e (.expr x))
    (hr : ReadableAt sig fam e n) :
    readT sig spell fam n x = some (.ok e) ∧ nodeLike x = true := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view fam e = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build fam ctor args = some e := by
    have := build_view fam e; rwa [hview] at this
  have hsorts : argSorts fam ctor = some (args.map argSortOf) := by
    have := argSorts_view fam e; rwa [hview] at this
  have hp : tableLayer.rowPrint sig fam ctor (args.map (ArgF.fold (printAlg sig))) n = .ok x := by
    have := cata_build (tableLayer sig) fam ctor args e hbuild
    rcases hfam with rfl | rfl | rfl <;> simp only [PrintsTo, cataFam] at hx this <;>
      (rw [show printAlg sig = EffAlgebra.ofLayer (tableLayer sig) from rfl, this] at hx; exact hx)
  obtain ⟨d, hd⟩ := hr
  have hdom : domLayer.rowDom sig fam ctor (args.map (ArgF.fold (readableAlg sig))) n = some d := by
    have := cata_build (domLayer sig) fam ctor args e hbuild
    rw [show readableAlg sig = EffAlgebra.ofLayer (domLayer sig) from rfl, this] at hd
    rcases hfam with rfl | rfl | rfl <;> exact hd
  obtain ⟨row, hfind, hcase⟩ := rowPrint_inv hp
  obtain ⟨row', hfind', hcase'⟩ := rowDom_inv hdom
  rw [find?_selects_fold (readableAlg sig) (printAlg sig), hfind, Option.some.injEq] at hfind'
  subst hfind'
  obtain ⟨k, hk, hidx, _⟩ := find?_index _ table row hfind
  have hpred : (fun r : Templates.Row => r.selects fam ctor (args.map (ArgF.fold (printAlg sig)))) =
      fun r => r.selects fam ctor args := funext fun r => selects_fold _ r fam ctor args
  rw [hpred] at hidx
  have hsel : row.selects fam ctor args = true := by
    have := List.find?_some hfind; rwa [selects_fold] at this
  obtain ⟨hfamrow, hctor⟩ := selects_fam_ctor hsel
  have hmem := List.mem_of_getElem? hk
  have hshape := table_fact table_shape hmem
  have hsorts' : argSorts row.fam row.ctor = some (args.map argSortOf) := by
    rw [hfamrow, hctor]; exact hsorts
  have hsorts'' : argSorts fam row.ctor = some (args.map argSortOf) := by
    rw [hctor]; exact hsorts
  -- the recursion, in the shape `readRow` asks for
  have hchild' : ∀ fam' d (y : Expr) (hy : sizeOf y < sizeOf x) c, ReadableAt sig fam' c d →
      PrintsTo sig d fam' c (.expr y) →
      (readT sig spell fam' d y).getD (.error (.here (unread fam'))) = .ok c :=
    fun fam' d y hy c hr hp => by rw [(hchild fam' d y hy c hr hp).1]; rfl
  -- an earlier row of another family reads nothing
  have hother : ∀ j < k, ∀ rj, table[j]? = some rj → rj.fam ≠ fam ∨ rowsApart rj row = true :=
    fun j hj rj hrj => by rw [← hfamrow]; exact apart_of_lt hrj hk hj
  rcases hcase with ⟨t, τ, hout, hτ, hinst⟩ | ⟨op, r, hout, hargs, hp'⟩
  · -- a skeleton row
    rcases hcase' with ⟨t', hout', hr'⟩ | ⟨_, _, hout', _⟩
    swap; · rw [hout] at hout'; cases hout'
    rw [hout, RowOut.tpl.injEq] at hout'
    subst hout'
    by_cases hrigid : t.rigid = true
    · -- rigid: the arguments read back at the row, and nothing before it fires
      have hnode := child_at_hole hchild hout hrigid hτ hinst hr'
      refine ⟨readT_of_row hk (fun j hj rj hrj => ?_) ?_, ?_⟩
      · rcases hother j hj rj hrj with hne | hap
        · exact readRow_none_of_fam hne
        · exact earlier_none_rigid hap hout hrigid hsorts' hinst hnode
      · exact readRow_rigid_print hk hbuild hsorts hsel hidx hout hrigid hτ hinst hr' hchild'
          (fun fam' d ys hy c hr hp => hchildren fam' d ys hy c hr hp)
          (fun d ss hy c hr hp => hblock d ss hy c hr hp)
      · have htop : t.nodeTop = true := by
          rcases hfam with rfl | rfl | rfl <;>
            simpa only [rowShape, hfamrow, hout, hrigid, ↓reduceIte] using hshape
        exact inst_nodeLike n τ t x htop hinst
    · -- transparent: a bare hole
      cases t with
      | hole i =>
        have hkind : (fam = .eff ∧ args.map argSortOf = [.child .action]) ∨
            (fam = .layer ∧ args.map argSortOf = [.path]) := by
          unfold rowShape at hshape
          rw [hfamrow, hout] at hshape
          rcases hfam with rfl | rfl | rfl <;>
            simp only [Tpl.rigid, Bool.false_eq_true, ↓reduceIte, hsorts'', Bool.or_eq_true,
              Bool.and_eq_true, beq_iff_eq, beq_self_eq_true, Option.some.injEq, true_and,
              reduceCtorEq, false_and, or_false, false_or] at hshape <;> aesop
        rcases hfam with rfl | rfl | rfl
        · -- the eff row that hands to the action family (`withFiber`)
          have hact : args.map argSortOf = [.child .action] := by
            rcases hkind with ⟨_, h⟩ | ⟨h, _⟩
            · exact h
            · cases h
          obtain ⟨a, rfl, ha⟩ := args_of_sorts_single hact
          have hi := hole_zero hmem hout (s := .child .action) (by rw [hsorts', hact])
          subst hi
          cases a with
          | child fam' c =>
            simp only [argSortOf, ArgSort.child.injEq] at ha
            subst ha
            -- the child's image is the tree, at the row's depth
            obtain ⟨hprint, _⟩ := printArgs_lookup _ 0 τ hτ
            have hp0 := hprint 0 (ArgF.fold (printAlg sig) (.child .action c)) rfl
            simp only [inst] at hinst
            rw [Nat.add_zero, argSortOf_fold, argSortOf] at hp0
            have hlook : lookup τ 0 = some (.expr x) := by
              revert hinst; cases lookup τ 0 <;> aesop
            rw [hlook] at hp0
            have hpa : cata_action (printAlg sig) c
                (argDepth .eff (.child .action) n ((RowOut.tpl (.hole 0)).levelAt 0)) = .ok x :=
              printsTo_of_printArg hp0
            have hlevel : (RowOut.tpl (.hole 0)).levelAt 0 = 0 := rfl
            rw [hlevel] at hpa
            have hra : ReadableAt sig .action c (argDepth .eff (.child .action) n 0) := by
              have := argsReadable_at _ 0 0 (ArgF.fold (readableAlg sig) (.child .action c)) hr' rfl
              rw [Nat.add_zero, argSortOf_fold, argSortOf, hlevel] at this
              exact readableAt_of_argReadable this
            have hrank : famRank .action < famRank .eff := by decide
            obtain ⟨h, hxh, hh⟩ := action_image_head hpa
            refine ⟨readT_of_row hk (fun j hj rj hrj => ?_) ?_, ?_⟩
            · rcases hother j hj rj hrj with hne | hap
              · exact readRow_none_of_fam hne
              · exact earlier_none_action hap hout (by rw [hsorts', hact]) hxh hh
            · exact readRow_action_print hk hbuild (by rw [hsorts, hact]) hsel hidx hout hrank hpa hra
                (fun fam' hlt d c' hr hp => (hsame fam' hlt d c' hr hp).1)
            · exact (hsame .action hrank _ c hra (by simpa only [PrintsTo] using hpa)).2
          | _ => cases ha
        · -- no action row is transparent
          rcases hkind with ⟨h, _⟩ | ⟨h, _⟩ <;> cases h
        · -- the layer row that reads a name (`ref`)
          have hpath : args.map argSortOf = [.path] := by
            rcases hkind with ⟨h, _⟩ | ⟨_, h⟩
            · cases h
            · exact h
          obtain ⟨a, rfl, ha⟩ := args_of_sorts_single hpath
          have hi := hole_zero hmem hout (s := .path) (by rw [hsorts', hpath])
          subst hi
          cases a with
          | path p =>
            obtain ⟨hprint, _⟩ := printArgs_lookup _ 0 τ hτ
            have hp0 := hprint 0 (ArgF.fold (printAlg sig) (.path p)) rfl
            simp only [inst] at hinst
            simp only [Nat.add_zero, ArgF.fold, printArg, Except.ok.injEq] at hp0
            have hx : x = .ident (LayerTerm.refName p) := by
              rw [← hp0] at hinst; simpa only [Option.some.injEq] using hinst.symm
            have hrp : LayerTerm.readRefName (LayerTerm.refName p) = some p := by
              have := argsReadable_at _ 0 0 (ArgF.fold (readableAlg sig) (.path p)) hr' rfl
              simpa only [argReadable, ArgF.fold, leafReadable, decide_eq_true_eq] using this
            refine ⟨readT_of_row hk (fun j hj rj hrj => ?_) ?_, ?_⟩
            · rcases hother j hj rj hrj with hne | hap
              · exact readRow_none_of_fam hne
              · exact earlier_none_path hap hout (by rw [hsorts', hpath]) hx
            · exact readRow_path_print hk hbuild (by rw [hsorts, hpath]) hsel hidx hout hx hrp
            · subst hx; rfl
          | _ => cases ha
      | _ => exact absurd rfl hrigid
  · -- the row call
    rcases hcase' with ⟨_, hout', _⟩ | ⟨op', r', hout', hargs', hd', hreq⟩
    · rw [hout] at hout'; cases hout'
    have hfamily := table_fact table_family hmem
    simp only [rowFamily, hout, beq_iff_eq] at hfamily
    rw [hfamily] at hfamrow
    subst hfamrow
    have hargs := fold_eq_op_term (printAlg sig) hargs
    have hargs' := fold_eq_op_term (readableAlg sig) hargs'
    rw [hargs, List.cons.injEq, List.cons.injEq, ArgF.op.injEq, ArgF.term.injEq] at hargs'
    obtain ⟨rfl, rfl, _⟩ := hargs'
    have he : e = .perform op r := eff_of_view_op_term e op r (by rw [hview]; exact hargs)
    subst he
    refine ⟨readT_of_row hk (fun j hj rj hrj => ?_) ?_, printRow_nodeLike hp'⟩
    · rcases hother j hj rj hrj with hne | hap
      · exact readRow_none_of_fam hne
      · exact earlier_none_rowCall hap hl hout hp' (fun hk d => readT_action_none_of_printRow hl hp' d)
    · exact readRow_rowCall_print hl hout hfamily hd' hreq hp' rfl

end Step

/-! ## The statement row -/

section StmtRow

variable {n : Nat} {s : TypeScript.Stmt} {k : Nat}

/-- What the printer did at a statement. -/
theorem stmtPrint_inv {ctor : String} {args : List (ArgF Op Carrier)} {declared : Nat}
    (h : tableLayer sig .stmt ctor args n = .ok (s, declared)) :
    ∃ row t τ, table.find? (fun r => r.selects .stmt ctor args) = some row ∧ row.out = .stmt t ∧
      printArgs sig .stmt n (.stmt t) args 0 = .ok τ ∧ instStmt n τ t = some s ∧
      declared = t.declares := by
  unfold tableLayer at h
  aesop

/-- What the domain said at a statement. -/
theorem stmtDom_inv {ctor : String} {args : List (ArgF Op Dom)} {d : Nat}
    (h : domLayer sig .stmt ctor args n = some d) :
    ∃ row t, table.find? (fun r => r.selects .stmt ctor args) = some row ∧ row.out = .stmt t ∧
      argsReadable sig .stmt n (.stmt t) (rowDaemon row) args 0 = true ∧ d = t.declares := by
  unfold domLayer at h
  aesop

variable {child : (fam' : EffFam) → Nat → (y : Expr) → sizeOf y < sizeOf s →
    Except ReadFailure (EffSelfCarrier Op fam')}
  {children : (fam' : EffFam) → Nat → (ys : List Expr) → sizeOf ys < sizeOf s →
    Except ReadFailure (EffSelfCarrier Op fam')}
  {block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf s →
    Except ReadFailure (EffSelfCarrier Op .stmts)}

theorem readStmtRow_none_of_fam {row : Templates.Row} (h : row.fam ≠ .stmt) :
    readStmtRow sig n s row k child children block = none := by
  unfold readStmtRow; simp only [h, ↓reduceIte]

theorem readStmtRow_none_of_out {row : Templates.Row} (h : ∀ t, row.out ≠ .stmt t) :
    readStmtRow sig n s row k child children block = none := by
  unfold readStmtRow; aesop

theorem readStmtRow_none_of_nomatch {row : Templates.Row} {t : StmtTpl} (hout : row.out = .stmt t)
    (hm : matchStmt n t s = none) :
    readStmtRow sig n s row k child children block = none := by
  unfold readStmtRow; aesop

/-- A statement row before the printing one is apart by former. -/
theorem earlier_stmt_none {rj : Templates.Row} {row : Templates.Row} (hap : rowsApart rj row = true)
    {t : StmtTpl} (hout : row.out = .stmt t) {τ : Subst} (hinst : instStmt n τ t = some s) :
    readStmtRow sig n s rj k child children block = none := by
  unfold rowsApart at hap
  rw [hout] at hap
  simp only at hap
  split at hap
  · rename_i t' h'
    simp only [bne_iff_ne, ne_eq] at hap
    exact readStmtRow_none_of_nomatch h' (matchStmt_former n τ t' t s hap hinst)
  · rename_i h'
    exact readStmtRow_none_of_out fun t ht => h' t ht

/-- The printing statement row reads its image back, with the binders it declares. -/
theorem readStmtRow_print {row : Templates.Row} (hk : table[k]? = some row)
    {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))} {st : Program.Stmt Op}
    (hbuild : build .stmt ctor args = some st)
    (hsorts : argSorts .stmt ctor = some (args.map argSortOf))
    (hsel : row.selects .stmt ctor args = true)
    (hidx : table.findIdx? (fun r => r.selects .stmt ctor args) = some k)
    {t : StmtTpl} (hout : row.out = .stmt t) {τ : Subst}
    (hτ : printArgs sig .stmt n (.stmt t) (args.map (ArgF.fold (printAlg sig))) 0 = .ok τ)
    (hinst : instStmt n τ t = some s)
    (hr : argsReadable sig .stmt n (.stmt t) (rowDaemon row) (args.map (ArgF.fold (readableAlg sig))) 0
      = true)
    (hchild : ∀ fam' d y (hy : sizeOf y < sizeOf s) c, ReadableAt sig fam' c d →
      PrintsTo sig d fam' c (.expr y) → child fam' d y hy = .ok c)
    (hchildren : ∀ fam' d ys (hy : sizeOf ys < sizeOf s) c, ReadableAt sig fam' c d →
      PrintsTo sig d fam' c (.exprs ys) → children fam' d ys hy = .ok c)
    (hblock : ∀ d ss (hy : sizeOf ss < sizeOf s) c, ReadableAt sig .stmts c d →
      PrintsTo sig d .stmts c (.stmts ss) → block d ss hy = .ok c) :
    readStmtRow sig n s row k child children block = some (.ok (st, t.declares)) := by
  obtain ⟨hfam, hctor⟩ := selects_fam_ctor hsel
  obtain ⟨σ, hσ, hagree⟩ := matchStmt_of_instStmt n τ t s hinst
  have hmem := List.mem_of_getElem? hk
  obtain ⟨hprint, _⟩ := printArgs_lookup (args.map (ArgF.fold (printAlg sig))) 0 τ hτ
  have hsorts' : argSorts row.fam row.ctor = some (args.map argSortOf) := by
    rw [hfam, hctor]; exact hsorts
  have hargs := readArgs_print sig σ n row (τ := τ)
    (child := fun fam' d y i hy => child fam' d y (matchStmt_below n t s σ hσ (i, .expr y) hy))
    (children := fun fam' d ys i hy => children fam' d ys (matchStmt_below n t s σ hσ (i, .exprs ys) hy))
    (block := fun d body i hy => block d body (matchStmt_below n t s σ hσ (i, .stmts body) hy))
    (fun fam' d y i hy c hr hp => hchild fam' d y _ c hr hp)
    (fun fam' d ys i hy c hr hp => hchildren fam' d ys _ c hr hp)
    (fun d ss i hy c hr hp => hblock d ss _ c hr hp)
    (fun j hj => holesStmt_of_instStmt n τ t s hinst j (by rwa [hout] at hj))
    (fun j hj => hagree j (by rwa [hout] at hj)) args 0
    (fun k v hk a ha => supplied_eq_of_selects row hsel (0 + k) v (by simpa using hk) a ha)
    (fun m v hm hsup => hole_of_not_supplied_stmt hmem hout hsorts' (0 + m)
      (by simp only [List.length_map, Nat.zero_add]; exact (List.getElem?_eq_some_iff.mp hm).1) hsup)
    (fun k v hk => by
      have := hprint k (ArgF.fold (printAlg sig) v) (by simp only [List.getElem?_map, hk, Option.map_some])
      rw [argSortOf_fold] at this
      simpa only [hfam, hout] using this)
    (fun k v hk => by
      have := argsReadable_at (args.map (ArgF.fold (readableAlg sig))) 0 k (ArgF.fold (readableAlg sig) v)
        hr (by simp only [List.getElem?_map, hk, Option.map_some])
      rw [argSortOf_fold] at this
      simpa only [hfam, hout] using this)
  have hb := buildRow_of_findIdx? hbuild hidx
  obtain ⟨rfam, rctor, rfixed, rout⟩ := row
  simp only at hfam hctor hout
  subst hfam hctor hout
  unfold readStmtRow
  simp only [↓reduceIte, hsorts]
  split
  · rename_i hnone; rw [hσ] at hnone; cases hnone
  · rename_i σ' hσ'
    rw [hσ] at hσ'
    obtain rfl := Option.some.inj hσ'
    simp only [hargs, ok_bind, hb]

end StmtRow

end Node

/-! ## The theorem: induction on the size of the image -/

section Theorem

variable {sig : Signature Op} {spell : String → List String → Option Op}

/-- Everything readable whose image has size at most `m` reads back from its image; the
images of the expression families are node-like. -/
def PrintsBackUpTo (sig : Signature Op) (spell : String → List String → Option Op) (m : Nat) :
    Prop :=
  (∀ fam n (e : EffSelfCarrier Op fam) (x : Expr), sizeOf x ≤ m → ReadableAt sig fam e n →
    PrintsTo sig n fam e (.expr x) → readT sig spell fam n x = some (.ok e) ∧ nodeLike x = true) ∧
  (∀ fam n (e : EffSelfCarrier Op fam) (xs : List Expr), sizeOf xs ≤ m → ReadableAt sig fam e n →
    PrintsTo sig n fam e (.exprs xs) → readSpine sig spell fam n xs = .ok e) ∧
  (∀ n (e : Stmts Op) (ss : List TypeScript.Stmt), sizeOf ss ≤ m → ReadableAt sig .stmts e n →
    PrintsTo sig n .stmts e (.stmts ss) → readStmts sig spell n ss = .ok e)

/-- The node step, from the induction hypothesis. -/
theorem readT_print_step (hl : LawfulSpelling sig spell) {m : Nat}
    (ih : ∀ m', m' < m → PrintsBackUpTo sig spell m') {fam : EffFam} {n : Nat}
    {e : EffSelfCarrier Op fam} {x : Expr} (hx : sizeOf x ≤ m)
    (hsame : ∀ fam', famRank fam' < famRank fam → ∀ d c, ReadableAt sig fam' c d →
      PrintsTo sig d fam' c (.expr x) → readT sig spell fam' d x = some (.ok c) ∧ nodeLike x = true)
    (hr : ReadableAt sig fam e n) (hp : PrintsTo sig n fam e (.expr x)) :
    readT sig spell fam n x = some (.ok e) ∧ nodeLike x = true := by
  have hfam : fam = .eff ∨ fam = .action ∨ fam = .layer := by
    cases fam <;> simp only [PrintsTo] at hp <;> simp
  exact readT_print hl
    (hchild := fun fam' d y hy c hr' hp' => (ih (sizeOf y) (by omega)).1 fam' d c y (Nat.le_refl _) hr' hp')
    (hchildren := fun fam' d ys hy c hr' hp' => (ih (sizeOf ys) (by omega)).2.1 fam' d c ys (Nat.le_refl _) hr' hp')
    (hblock := fun d ss hy c hr' hp' => (ih (sizeOf ss) (by omega)).2.2 d c ss (Nat.le_refl _) hr' hp')
    (hsame := hsame) hfam hp hr


/-- The domain's spines, item by item (the definition, at each cons). -/
theorem dom_effs_cons (e : Eff Op) (es : Effs Op) (n : Nat) :
    cata_effs (readableAlg sig) (.cons e es) n =
      (cata_eff (readableAlg sig) e n).bind fun _ =>
        (cata_effs (readableAlg sig) es n).bind fun _ => some 0 := rfl

theorem dom_layers_cons (l : LayerTerm Op) (ls : LayerTerms Op) (n : Nat) :
    cata_layers (readableAlg sig) (.cons l ls) n =
      (cata_layer (readableAlg sig) l n).bind fun _ =>
        (cata_layers (readableAlg sig) ls n).bind fun _ => some 0 := rfl

theorem dom_stmts_cons (st : Program.Stmt Op) (ss : Stmts Op) (n : Nat) :
    cata_stmts (readableAlg sig) (.cons st ss) n =
      (cata_stmt (readableAlg sig) st n).bind fun d =>
        (cata_stmts (readableAlg sig) ss (n + d)).bind fun _ => some 0 := rfl

/-- The spines' step: item by item, from the induction hypothesis. -/
theorem readSpine_print_step {m : Nat} (ih : ∀ m', m' < m → PrintsBackUpTo sig spell m') :
    ∀ (fam : EffFam) (n : Nat) (e : EffSelfCarrier Op fam) (xs : List Expr),
      sizeOf xs ≤ m → ReadableAt sig fam e n → PrintsTo sig n fam e (.exprs xs) →
      readSpine sig spell fam n xs = .ok e
  | .effs, n, e, xs, hx, hr, hp => by
    cases e with
    | nil =>
      simp only [PrintsTo] at hp
      cases hp
      rw [readSpine]
    | cons e es =>
      simp only [PrintsTo, cata_effs_cons, bind_eq_ok] at hp
      obtain ⟨y, hy, rest, hrest, hxs⟩ := hp
      cases hxs
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_effs_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
      have h1 := (ih (sizeOf y) (by omega)).1 .eff n e y (Nat.le_refl _) ⟨d1, hd1⟩ hy
      have h2 := (ih (sizeOf rest) (by omega)).2.1 .effs n es rest (Nat.le_refl _) ⟨d2, hd2⟩ hrest
      rw [readSpine]
      simp only [h1.1, Option.getD_some, Except.mapError, h2, ok_bind]
  | .layers, n, e, xs, hx, hr, hp => by
    cases e with
    | nil =>
      simp only [PrintsTo] at hp
      cases hp
      rw [readSpine]
    | cons l ls =>
      simp only [PrintsTo, cata_layers_cons, bind_eq_ok] at hp
      obtain ⟨y, hy, rest, hrest, hxs⟩ := hp
      cases hxs
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_layers_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
      have h1 := (ih (sizeOf y) (by omega)).1 .layer n l y (Nat.le_refl _) ⟨d1, hd1⟩ hy
      have h2 := (ih (sizeOf rest) (by omega)).2.1 .layers n ls rest (Nat.le_refl _) ⟨d2, hd2⟩ hrest
      rw [readSpine]
      simp only [h1.1, Option.getD_some, Except.mapError, h2, ok_bind]
  | .eff, _, _, _, _, _, hp => by simp only [PrintsTo] at hp
  | .action, _, _, _, _, _, hp => by simp only [PrintsTo] at hp
  | .layer, _, _, _, _, _, hp => by simp only [PrintsTo] at hp
  | .stmt, _, _, _, _, _, hp => by simp only [PrintsTo] at hp
  | .stmts, _, _, _, _, _, hp => by simp only [PrintsTo] at hp


/-- A readable statement whose image is `(s, declared)` reads back from `s` through the first
statement row that fires, declaring `declared`, given the recursion below it. -/
theorem readStmt_print {m : Nat} (ih : ∀ m', m' < m → PrintsBackUpTo sig spell m') {n : Nat}
    {st : Program.Stmt Op} {s : TypeScript.Stmt} {declared : Nat} (hs : sizeOf s ≤ m)
    (hp : cata_stmt (printAlg sig) st n = .ok (s, declared)) {d : Nat}
    (hr : cata_stmt (readableAlg sig) st n = some d) :
    (table.zipIdx.findSome? fun (row, k) =>
      readStmtRow sig n s row k
        (fun fam' d y _ => (readT sig spell fam' d y).getD (.error (.here (unread fam'))))
        (fun fam' d ys _ => readSpine sig spell fam' d ys)
        (fun d body _ => readStmts sig spell d body)) = some (.ok (st, declared)) ∧ d = declared := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view .stmt st = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build .stmt ctor args = some st := by
    have := build_view .stmt st; rwa [hview] at this
  have hsorts : argSorts .stmt ctor = some (args.map argSortOf) := by
    have := argSorts_view .stmt st; rwa [hview] at this
  have hp' : tableLayer sig .stmt ctor (args.map (ArgF.fold (printAlg sig))) n = .ok (s, declared) := by
    have := cata_build (tableLayer sig) .stmt ctor args st hbuild
    simp only [cataFam] at this
    rw [show printAlg sig = EffAlgebra.ofLayer (tableLayer sig) from rfl, this] at hp
    exact hp
  have hd' : domLayer sig .stmt ctor (args.map (ArgF.fold (readableAlg sig))) n = some d := by
    have := cata_build (domLayer sig) .stmt ctor args st hbuild
    simp only [cataFam] at this
    rw [show readableAlg sig = EffAlgebra.ofLayer (domLayer sig) from rfl, this] at hr
    exact hr
  obtain ⟨row, t, τ, hfind, hout, hτ, hinst, rfl⟩ := stmtPrint_inv hp'
  obtain ⟨row', t', hfind', hout', hr', rfl⟩ := stmtDom_inv hd'
  rw [find?_selects_fold (readableAlg sig) (printAlg sig), hfind, Option.some.injEq] at hfind'
  subst hfind'
  rw [hout, RowOut.stmt.injEq] at hout'
  subst hout'
  obtain ⟨k, hk, hidx, _⟩ := find?_index _ table row hfind
  have hpred : (fun r : Templates.Row => r.selects .stmt ctor (args.map (ArgF.fold (printAlg sig)))) =
      fun r => r.selects .stmt ctor args := funext fun r => selects_fold _ r .stmt ctor args
  rw [hpred] at hidx
  have hsel : row.selects .stmt ctor args = true := by
    have := List.find?_some hfind; rwa [selects_fold] at this
  obtain ⟨hfam, _⟩ := selects_fam_ctor hsel
  refine ⟨?_, rfl⟩
  refine findSome?_zipIdx (fun (p : Templates.Row × Nat) => readStmtRow sig n s p.1 p.2
      (fun fam' d y _ => (readT sig spell fam' d y).getD (.error (.here (unread fam'))))
      (fun fam' d ys _ => readSpine sig spell fam' d ys)
      (fun d body _ => readStmts sig spell d body)) table 0 k row (.ok (st, t.declares))
    (fun j hj rj hrj => ?_) hk ?_
  · simp only [Nat.zero_add]
    rcases apart_of_lt hrj hk hj with hne | hap
    · exact readStmtRow_none_of_fam (by rw [hfam] at hne; exact hne)
    · exact earlier_stmt_none hap hout hinst
  · simp only [Nat.zero_add]
    exact readStmtRow_print hk hbuild hsorts hsel hidx hout hτ hinst hr'
      (fun fam' d y hy c hr hp => by
        rw [((ih (sizeOf y) (by omega)).1 fam' d c y (Nat.le_refl _) hr hp).1]; rfl)
      (fun fam' d ys hy c hr hp => (ih (sizeOf ys) (by omega)).2.1 fam' d c ys (Nat.le_refl _) hr hp)
      (fun d ss hy c hr hp => (ih (sizeOf ss) (by omega)).2.2 d c ss (Nat.le_refl _) hr hp)

/-- The statement spine's step: each statement through its row, the rest under what it
declares. -/
theorem readStmts_print_step {m : Nat} (ih : ∀ m', m' < m → PrintsBackUpTo sig spell m') :
    ∀ (n : Nat) (e : Stmts Op) (ss : List TypeScript.Stmt),
      sizeOf ss ≤ m → ReadableAt sig .stmts e n → PrintsTo sig n .stmts e (.stmts ss) →
      readStmts sig spell n ss = .ok e
  | n, e, ss, hx, hr, hp => by
    cases e with
    | nil =>
      simp only [PrintsTo] at hp
      cases hp
      rw [readStmts]
    | cons st rest =>
      simp only [PrintsTo, cata_stmts_cons, bind_eq_ok] at hp
      obtain ⟨⟨s, declared⟩, hs, tail, htail, hss⟩ := hp
      cases hss
      simp only at hx
      obtain ⟨d, hd⟩ := hr
      simp only [cataFam, dom_stmts_cons, Option.bind_eq_some_iff] at hd
      obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
      have hsz : sizeOf (s :: tail) = 1 + sizeOf s + sizeOf tail := List.cons.sizeOf_spec s tail
      obtain ⟨hrow, rfl⟩ := readStmt_print ih (by omega) hs hd1
      have h2 := (ih (sizeOf tail) (by omega)).2.2 (n + d1) rest tail (Nat.le_refl _) ⟨d2, hd2⟩ htail
      rw [readStmts]
      simp only [hrow, Except.mapError, ok_bind, h2]

/-- Everything readable reads back from its image, at every size. -/
theorem printsBackUpTo (hl : LawfulSpelling sig spell) (m : Nat) : PrintsBackUpTo sig spell m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    have hlow : ∀ fam, famRank fam = 0 → ∀ n (e : EffSelfCarrier Op fam) (x : Expr), sizeOf x ≤ m →
        ReadableAt sig fam e n → PrintsTo sig n fam e (.expr x) →
        readT sig spell fam n x = some (.ok e) ∧ nodeLike x = true :=
      fun fam h0 n e x hx hr hp =>
        readT_print_step hl ih hx (fun fam' hlt => absurd hlt (by omega)) hr hp
    refine ⟨fun fam n e x hx hr hp => ?_, readSpine_print_step ih, readStmts_print_step ih⟩
    exact readT_print_step hl ih hx
      (fun fam' hlt d c hr' hp' => hlow fam' (by have := famRank_le_one fam; omega) d c x hx hr' hp')
      hr hp

/-- **Law 11.** What the printer prints of a readable program reads back to it. -/
theorem read_print (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (hr : Readable sig n e = true) {x : Expr} (hp : print sig n e = .ok x) :
    readEff sig spell n x = .ok e := by
  have h := (printsBackUpTo hl (sizeOf x)).1 .eff n e x (Nat.le_refl _)
    (by unfold ReadableAt; simpa only [Readable, cataFam, Option.isSome_iff_exists] using hr) hp
  simp only [readEff, readEffAt, h.1, Option.getD_some, Except.mapError]

/-- The same of a layer, which is closed: read and printed at depth `0`. -/
theorem readLayer_print (hl : LawfulSpelling sig spell) {l : LayerTerm Op}
    (hr : ReadableAt sig .layer l 0) {x : Expr} (hp : printLayer sig l = .ok x) :
    readLayer sig spell x = .ok l := by
  have h := (printsBackUpTo hl (sizeOf x)).1 .layer 0 l x (Nat.le_refl _) hr hp
  simp only [readLayer, readLayerAt, h.1, Option.getD_some, Except.mapError]

/-- A readable program reads back from whatever the printer prints of it. -/
theorem ReadsBack.of_Readable (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op}
    (hr : Readable sig n e = true) : ReadsBack sig spell n e :=
  fun _ hp => read_print hl hr hp

end Theorem

end Effect4.Program
