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

/-- `apartBy sorts earlier later`: a reason no instance of `later` (its child holes filled by
child images) matches `earlier`. -/
def apartBy (sorts : List Effect4.Program.ArgSort) : Tpl → Tpl → Bool
  | .call (.ident h') args', .call (.ident h) args =>
    if h' ≠ h then true else
    match args', args with
    | .cons (.arrow _) .nil, .cons (.arrowBlock _ _) .nil => true
    | .cons (.arrowBlock _ _) .nil, .cons (.arrow _) .nil => true
    | .cons (.arrow (.cond _ _ _)) .nil, .cons (.arrow (.hole i)) .nil => childHole sorts i
    | .cons (.arrowBlock _ (.cons (.letInit _ _ none) _)) .nil,
      .cons (.arrowBlock _ (.cons (.letInit _ _ (some _)) _)) .nil => true
    | _, _ => args'.length != args.length
  | .method (.hole _) name' (.cons (.call (.ident a) _) .nil),
    .method (.hole _) name (.cons (.call (.ident b) _) .nil) => name' != name || a != b
  | .ident h', .call (.ident _) _ => true
  | .call (.ident _) _, .ident _ => true
  | _, _ => false

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
    (x : Expr)
    (hapart : apartBy sorts t' t = true) (hinst : inst n τ t = some x)
    (hnode : ∀ i y, childHole sorts i = true → lookup τ i = some (.expr y) → nodeLike y = true) :
    matchT n t' x = none := by
  unfold apartBy at hapart
  split at hapart
  · -- two calls with identifier heads
    rename_i h' args' h args
    split at hapart
    · -- different heads
      rename_i hne
      cases hx : matchT n (.call (.ident h') args') x with
      | none => rfl
      | some σ =>
        have h1 := head_of_match n _ x σ hx (name := h') rfl
        have h2 := head_of_inst n τ _ x hinst (name := h) rfl
        rw [h1] at h2
        exact absurd (Option.some.inj h2) hne
    · split at hapart <;> aesop (add norm simp [matchT_arrow_arrowBlock, matchT_arrowBlock_arrow,
        matchT_cond_nodeLike, matchAnn], safe forward [matchTs_length, insts_length, hnode])
  · aesop
  · aesop
  · aesop
  · cases hapart


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

/-- `<$>` on `Except`, inverted (the printer maps a capture over a leaf's printing). -/
theorem fmap_eq_ok {ε α β : Type} {m : Except ε α} {f : α → β} {b : β} :
    (f <$> m) = .ok b ↔ ∃ a, m = .ok a ∧ f a = b := by
  cases m <;> simp [Functor.map, Except.map]

attribute [local aesop norm simp] fmap_eq_ok
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

end Effect4.Program
