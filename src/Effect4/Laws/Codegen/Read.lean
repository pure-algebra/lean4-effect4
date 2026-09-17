import Effect4.Codegen.Read
import Effect4.Laws.Codegen.Template

/-!
# Laws.Codegen.Read — the reader and the printer over one table (R5.2)

`read_exact`: what the reader accepts prints back to exactly the tree it read. The proof has no
case per constructor. It is the generic step's, and rests on five things, each stated once:

* the engine lemma of the calculus, `inst_of_match` (a match of a skeleton with distinct holes
  instantiates back), with `inst_congr` (instantiation looks a substitution up at the skeleton's
  holes and nowhere else);
* the generated coherence of the fold with `build`, `cata_build` (the printer's algebra is
  `EffAlgebra.ofLayer` of the table's layer function with no field overridden);
* the reader's own exactness check, `printedRow` (the printer would choose this row);
* the exactness of each leaf reader (`readTerm_exact`, `readCause_exact`, `readKey_exact`, …)
  and of the row call (`readPerform_exact`);
* facts of the table that are decided, not argued (`table_*`): skeletons are linear, a hole is
  an argument, an argument the classifier fixes has no hole.

The recursion enters as a hypothesis of the row lemmas (`readRow` has none of its own), and the
theorem ties the knot by induction on the size of the tree.
-/

set_option autoImplicit false

namespace Effect4.Program

open TypeScript (Expr Stmt)
open Effect4.Codegen
open Effect4.Codegen.Template
open Effect4.Codegen.Templates (RowOut ArgPat Fixed table tableLayer printAlg printArg printArgs
  argDepth argSortOf Carrier Out)

variable {Op : Type}

/-! ## Facts of the table, decided

Each is a Boolean check over the rows, true by `decide`; `table_fact` turns it into the fact
about a row of the table. -/

/-- Whether a pattern fixes its argument (so a reader supplies it). -/
def _root_.Effect4.Codegen.Templates.ArgPat.fixes : ArgPat → Bool
  | .is _ => true
  | _ => false

theorem ArgPat.supplies_isSome {R : EffFam → Type} (p : ArgPat) :
    (p.supplies (Op := Op) (R := R)).isSome = p.fixes := by
  cases p <;> rfl

/-- The holes of whatever a row prints. -/
def _root_.Effect4.Codegen.Templates.RowOut.holes : RowOut → List Nat
  | .tpl t => Template.holes t
  | .stmt t => holesStmt t
  | _ => []

/-- Every skeleton has distinct holes. -/
def rowLinear (row : Templates.Row) : Bool := decide row.out.holes.Nodup

/-- An expression row belongs to a family read from one expression, a statement row to the
statement family, the row call to the programs. -/
def rowFamily (row : Templates.Row) : Bool :=
  match row.out with
  | .tpl _ => row.fam == .eff || row.fam == .action || row.fam == .layer
  | .stmt _ => row.fam == .stmt
  | .rowCall => row.fam == .eff
  | .refuse _ => true

/-- An argument the classifier fixes has no hole: it is no part of the image. -/
def rowFixedNoHole (row : Templates.Row) : Bool :=
  row.fixed.all fun p => !p.2.fixes || !row.out.holes.contains p.1

/-- A hole is an argument: every hole of a row is below its constructor's arity. -/
def rowHolesLt (row : Templates.Row) : Bool :=
  match argSorts row.fam row.ctor with
  | some sorts => row.out.holes.all (· < sorts.length)
  | none => true

theorem table_linear : table.all rowLinear = true := by decide
theorem table_family : table.all rowFamily = true := by decide
theorem table_fixedNoHole : table.all rowFixedNoHole = true := by decide
theorem table_holesLt : table.all rowHolesLt = true := by decide

/-- A decided check, at a row of the table. -/
theorem table_fact {check : Templates.Row → Bool} (h : table.all check = true)
    {row : Templates.Row}
    (hrow : row ∈ table) : check row = true :=
  List.all_eq_true.mp h row hrow

/-! ## Instantiation reads a substitution at the skeleton's holes only -/

theorem instAnn_congr (σ τ : Subst) : ∀ (ann : Option Nat),
    (∀ i ∈ holesAnn ann, lookup σ i = lookup τ i) → instAnn σ ann = instAnn τ ann
  | none, _ => rfl
  | some i, h => by
    simp only [instAnn, h i (by simp only [holesAnn, List.mem_singleton])]

mutual
  theorem inst_congr (n : Nat) (σ τ : Subst) : ∀ (t : Tpl),
      (∀ i ∈ holes t, lookup σ i = lookup τ i) → inst n σ t = inst n τ t
    | .hole i, h => by simp only [inst, h i (by simp only [holes, List.mem_singleton])]
    | .strHole i, h => by simp only [inst, h i (by simp only [holes, List.mem_singleton])]
    | .intHole i, h => by simp only [inst, h i (by simp only [holes, List.mem_singleton])]
    | .arrHole i, h => by simp only [inst, h i (by simp only [holes, List.mem_singleton])]
    | .binderRef _, _ => rfl
    | .ident _, _ => rfl
    | .str _, _ => rfl
    | .int _, _ => rfl
    | .bool _, _ => rfl
    | .call hd args, h => by
      simp only [holes, List.mem_append] at h
      simp only [inst, inst_congr n σ τ hd (fun i hi => h i (.inl hi)),
        insts_congr n σ τ args (fun i hi => h i (.inr hi))]
    | .callSpread hd i, h => by
      simp only [holes, List.mem_append, List.mem_singleton] at h
      simp only [inst, inst_congr n σ τ hd (fun j hj => h j (.inl hj)), h i (.inr rfl)]
    | .arr items, h => by
      simp only [holes] at h
      simp only [inst, insts_congr n σ τ items h]
    | .object fields, h => by
      simp only [holes] at h
      simp only [inst, instFields_congr n σ τ fields h]
    | .arrow b, h => by
      simp only [holes] at h
      simp only [inst, inst_congr n σ τ b h]
    | .lambda _ b, h => by
      simp only [holes] at h
      simp only [inst, inst_congr n σ τ b h]
    | .cond t a b, h => by
      simp only [holes, List.mem_append] at h
      simp only [inst, inst_congr n σ τ t (fun i hi => h i (.inl hi)),
        inst_congr n σ τ a (fun i hi => h i (.inr (.inl hi))),
        inst_congr n σ τ b (fun i hi => h i (.inr (.inr hi)))]
    | .method target _ args, h => by
      simp only [holes, List.mem_append] at h
      simp only [inst, inst_congr n σ τ target (fun i hi => h i (.inl hi)),
        insts_congr n σ τ args (fun i hi => h i (.inr hi))]
    | .arrowBlock _ body, h => by
      simp only [holes] at h
      simp only [inst, instStmts_congr n σ τ body h]
    | .generator body, h => by
      simp only [holes] at h
      simp only [inst, instStmts_congr n σ τ body h]
  theorem insts_congr (n : Nat) (σ τ : Subst) : ∀ (ts : Tpls),
      (∀ i ∈ holesTs ts, lookup σ i = lookup τ i) → insts n σ ts = insts n τ ts
    | .nil, _ => rfl
    | .cons hd tl, h => by
      simp only [holesTs, List.mem_append] at h
      simp only [insts, inst_congr n σ τ hd (fun i hi => h i (.inl hi)),
        insts_congr n σ τ tl (fun i hi => h i (.inr hi))]
  theorem instFields_congr (n : Nat) (σ τ : Subst) : ∀ (fs : Fields),
      (∀ i ∈ holesFields fs, lookup σ i = lookup τ i) → instFields n σ fs = instFields n τ fs
    | .nil, _ => rfl
    | .cons _ v tl, h => by
      simp only [holesFields, List.mem_append] at h
      simp only [instFields, inst_congr n σ τ v (fun i hi => h i (.inl hi)),
        instFields_congr n σ τ tl (fun i hi => h i (.inr hi))]
  theorem instStmt_congr (n : Nat) (σ τ : Subst) : ∀ (t : StmtTpl),
      (∀ i ∈ holesStmt t, lookup σ i = lookup τ i) → instStmt n σ t = instStmt n τ t
    | .letInit _ v ann, h => by
      simp only [holesStmt, List.mem_append] at h
      simp only [instStmt, inst_congr n σ τ v (fun i hi => h i (.inl hi)),
        instAnn_congr σ τ ann (fun i hi => h i (.inr hi))]
    | .assign _ v, h => by
      simp only [holesStmt] at h
      simp only [instStmt, inst_congr n σ τ v h]
    | .ret v, h => by
      simp only [holesStmt] at h
      simp only [instStmt, inst_congr n σ τ v h]
    | .exprStmt v, h => by
      simp only [holesStmt] at h
      simp only [instStmt, inst_congr n σ τ v h]
    | .constYield _ v, h => by
      simp only [holesStmt] at h
      simp only [instStmt, inst_congr n σ τ v h]
    | .yieldDiscard v, h => by
      simp only [holesStmt] at h
      simp only [instStmt, inst_congr n σ τ v h]
    | .ifElse t a b, h => by
      simp only [holesStmt, List.mem_append] at h
      simp only [instStmt, inst_congr n σ τ t (fun i hi => h i (.inl hi)),
        instStmts_congr n σ τ a (fun i hi => h i (.inr (.inl hi))),
        instStmts_congr n σ τ b (fun i hi => h i (.inr (.inr hi)))]
    | .whileTrue body, h => by
      simp only [holesStmt] at h
      simp only [instStmt, instStmts_congr n σ τ body h]
    | .breakTo, _ => rfl
  theorem instStmts_congr (n : Nat) (σ τ : Subst) : ∀ (ts : StmtTpls),
      (∀ i ∈ holesStmts ts, lookup σ i = lookup τ i) → instStmts n σ ts = instStmts n τ ts
    | .nil, _ => rfl
    | .cons hd tl, h => by
      simp only [holesStmts, List.mem_append] at h
      simp only [instStmts, instStmt_congr n σ τ hd (fun i hi => h i (.inl hi)),
        instStmts_congr n σ τ tl (fun i hi => h i (.inr hi))]
    | .hole i, h => by
      simp only [instStmts, h i (by simp only [holesStmts, List.mem_singleton])]
end

/-! ## Lists: the first that satisfies, by position -/

/-- The element at the position `findIdx?` gives is the one `find?` gives. -/
theorem find?_of_findIdx? {α : Type} (p : α → Bool) : ∀ (l : List α) (k : Nat) (a : α),
    l.findIdx? p = some k → l[k]? = some a → l.find? p = some a
  | [], _, _, h, _ => by simp only [List.findIdx?_nil, reduceCtorEq] at h
  | x :: xs, k, a, h, ha => by
    rw [List.findIdx?_cons] at h
    by_cases hx : p x = true
    · simp only [hx, ↓reduceIte, Option.some.injEq] at h
      subst h
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ha
      subst ha
      simp only [List.find?_cons, hx]
    · simp only [hx, Bool.false_eq_true, ↓reduceIte, Option.map_eq_some_iff] at h
      obtain ⟨j, hj, rfl⟩ := h
      simp only [List.getElem?_cons_succ] at ha
      have hx' : p x = false := by simpa only [Bool.not_eq_true] using hx
      simp only [List.find?_cons, hx']
      exact find?_of_findIdx? p xs j a hj ha

/-! ## The classifier looks at leaves, so folding the children does not move it -/

theorem Fixed.holds_fold {R : EffFam → Type} (alg : EffAlgebra Op R) (v : Fixed)
    (a : ArgF Op (EffSelfCarrier Op)) : v.holds (ArgF.fold alg a) = v.holds a := by
  cases a with
  | optTerm o => cases v <;> cases o <;> rfl
  | optTy o => cases v <;> cases o <;> rfl
  | _ => cases v <;> rfl

theorem ArgPat.holds_fold {R : EffFam → Type} (alg : EffAlgebra Op R) (p : ArgPat)
    (a : ArgF Op (EffSelfCarrier Op)) : p.holds (ArgF.fold alg a) = p.holds a := by
  cases p with
  | is v => exact Fixed.holds_fold alg v a
  | decisionTag =>
    cases a with
    | decision d => cases d <;> rfl
    | _ => rfl
  | someTerm =>
    cases a with
    | optTerm o => cases o <;> rfl
    | _ => rfl
  | someTy =>
    cases a with
    | optTy o => cases o <;> rfl
    | _ => rfl
  | daemon b => cases a <;> rfl

theorem patternAt_fold {R : EffFam → Type} (alg : EffAlgebra Op R)
    (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat) (p : ArgPat) :
    Templates.patternAt (args.map (ArgF.fold alg)) i p = Templates.patternAt args i p := by
  unfold Templates.patternAt
  rw [List.getElem?_map]
  cases args[i]? with
  | none => rfl
  | some a => exact ArgPat.holds_fold alg p a

theorem selects_fold {R : EffFam → Type} (alg : EffAlgebra Op R) (row : Templates.Row)
    (fam : EffFam) (ctor : String) (args : List (ArgF Op (EffSelfCarrier Op))) :
    row.selects fam ctor (args.map (ArgF.fold alg)) = row.selects fam ctor args := by
  unfold Templates.Row.selects
  simp only [patternAt_fold]

/-- The row the reader checked is the row the printer finds. -/
theorem find?_selects_of_printedRow (sig : Signature Op) {fam : EffFam} {ctor : String}
    {args : List (ArgF Op (EffSelfCarrier Op))} {k : Nat} {row : Templates.Row}
    (hp : printedRow fam ctor args k = true) (hk : table[k]? = some row) :
    (table.find? fun r => r.selects fam ctor (args.map (ArgF.fold (printAlg sig)))) = some row := by
  have hidx := of_decide_eq_true hp
  simp only [selects_fold]
  exact find?_of_findIdx? _ table k row hidx hk

/-! ## Lookups -/

/-- A capture found by `captured` is what `lookup` finds. -/
theorem lookup_of_captured : ∀ (σ : Subst) (i : Nat) (a : Arg) (h : (i, a) ∈ σ),
    captured σ i = some ⟨a, h⟩ → lookup σ i = some a
  | [], _, _, _, hc => by simp only [captured, reduceCtorEq] at hc
  | (j, b) :: rest, i, a, h, hc => by
    unfold captured at hc
    by_cases hji : j = i
    · simp only [hji, ↓reduceDIte, Option.some.injEq, Subtype.mk.injEq] at hc
      subst hji hc
      exact lookup_cons_self j b rest
    · simp only [hji, ↓reduceDIte, Option.map_eq_some_iff] at hc
      obtain ⟨⟨c, hcmem⟩, hrest, heq⟩ := hc
      simp only [Subtype.mk.injEq] at heq
      subst heq
      have := lookup_of_captured rest i c hcmem hrest
      unfold lookup at this ⊢
      have hne : ((j, b).1 == i) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact hji
      rw [List.find?_cons_of_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
      exact this

/-! ## The leaves: what a leaf reader accepts prints back to what it read -/

/-- A leaf read has the sort it was read at, and prints back, at any depth, to what was read. -/
theorem readLeaf_exact {sig : Signature Op} {d : Nat} {daemon : Bool} {s : ArgSort} {a : Arg}
    {v : ArgF Op (EffSelfCarrier Op)} (h : readLeaf sig d daemon s a = .ok v) :
    argSortOf v = s ∧ ∀ d', printArg sig d' (ArgF.fold (printAlg sig) v) = .ok (some a) := by
  unfold readLeaf at h
  split at h
  · obtain ⟨t, ht, rfl⟩ := map_eq_ok.mp h
    exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, readTerm_exact _ ht]⟩
  · obtain ⟨t, ht, rfl⟩ := map_eq_ok.mp h
    exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, readTerm_exact _ ht]⟩
  · obtain ⟨c, hc, rfl⟩ := map_eq_ok.mp h
    exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, readCause_exact _ hc]⟩
  · obtain ⟨l, hl, rfl⟩ := map_eq_ok.mp h
    exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, readLiteral_exact hl]⟩
  · obtain ⟨key, hk, rfl⟩ := map_eq_ok.mp h
    exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, readKey_exact hk, ok_bind]; rfl⟩
  · obtain ⟨o, ho, rfl⟩ := map_eq_ok.mp h
    exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, (readForkOptions_exact ho).1]⟩
  · cases h
    exact ⟨rfl, fun _ => rfl⟩
  · split at h
    · rename_i hv
      cases h
      refine ⟨rfl, fun _ => ?_⟩
      simp only [ArgF.fold, printArg]
      rw [show Int.ofNat _ = _ from Int.toNat_of_nonneg hv]
    · cases h
  · split at h
    · split at h
      · rename_i hname
        cases h
        exact ⟨rfl, fun _ => by simp only [ArgF.fold, printArg, hname]⟩
      · cases h
    · cases h
  · cases h
  · cases h

/-! ## What `readArgs` read, `printArgs` prints back -/

theorem mapError_eq_ok {ε ε' α : Type} {f : ε → ε'} {x : Except ε α} {a : α} :
    x.mapError f = .ok a ↔ x = .ok a := by
  cases x with
  | error e => simp only [Except.mapError, reduceCtorEq]
  | ok b =>
    constructor
    · intro h; cases h; rfl
    · intro h; cases h; rfl

theorem lookup_cons_ne (i j : Nat) (a : Arg) (rest : Subst) (h : i ≠ j) :
    lookup ((i, a) :: rest) j = lookup rest j := by
  unfold lookup
  have hne : ((i, a).1 == j) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]; exact h
  rw [List.find?_cons_of_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]

/-- A node prints to a capture at a depth: what the reader's recursion must establish of each
child it read, and what the theorem establishes of the whole tree. -/
def PrintsTo (sig : Signature Op) (d : Nat) :
    (fam : EffFam) → EffSelfCarrier Op fam → Arg → Prop
  | .eff, v, .expr y => cata_eff (printAlg sig) v d = .ok y
  | .action, v, .expr y => cata_action (printAlg sig) v d = .ok y
  | .layer, v, .expr y => cata_layer (printAlg sig) v d = .ok y
  | .effs, v, .exprs ys => cata_effs (printAlg sig) v d = .ok ys
  | .layers, v, .exprs ys => cata_layers (printAlg sig) v d = .ok ys
  | .stmts, v, .stmts ss => cata_stmts (printAlg sig) v d = .ok ss
  | _, _, _ => False

theorem printArg_child (sig : Signature Op) (d : Nat) : ∀ (fam : EffFam)
    (v : EffSelfCarrier Op fam) (a : Arg), PrintsTo sig d fam v a →
    printArg sig d (ArgF.fold (printAlg sig) (.child fam v)) = .ok (some a)
  | .eff, v, .expr y, h => by
    simp only [ArgF.fold, cataFam, printArg, show cata_eff (printAlg sig) v d = .ok y from h,
      ok_bind]
    rfl
  | .action, v, .expr y, h => by
    simp only [ArgF.fold, cataFam, printArg, show cata_action (printAlg sig) v d = .ok y from h,
      ok_bind]
    rfl
  | .layer, v, .expr y, h => by
    simp only [ArgF.fold, cataFam, printArg, show cata_layer (printAlg sig) v d = .ok y from h,
      ok_bind]
    rfl
  | .effs, v, .exprs ys, h => by
    simp only [ArgF.fold, cataFam, printArg, show cata_effs (printAlg sig) v d = .ok ys from h,
      ok_bind]
    rfl
  | .layers, v, .exprs ys, h => by
    simp only [ArgF.fold, cataFam, printArg, show cata_layers (printAlg sig) v d = .ok ys from h,
      ok_bind]
    rfl
  | .stmts, v, .stmts ss, h => by
    simp only [ArgF.fold, cataFam, printArg, show cata_stmts (printAlg sig) v d = .ok ss from h,
      ok_bind]
    rfl

/-- An argument the classifier fixes prints (to a capture no hole asks for, or to none). -/
theorem printArg_fixed (sig : Signature Op) (d : Nat) (v : Fixed) :
    ∃ x, printArg sig d (ArgF.fold (printAlg sig) (v.arg (Op := Op))) = .ok x := by
  cases v with
  | term t => exact ⟨_, rfl⟩
  | bool b => exact ⟨_, rfl⟩
  | mode m => exact ⟨_, rfl⟩
  | decision dec => cases dec <;> exact ⟨_, rfl⟩
  | noTerm => exact ⟨_, rfl⟩
  | noTy => exact ⟨_, rfl⟩

/-- The sort of a folded argument is the argument's. -/
theorem argSortOf_fold {R : EffFam → Type} (alg : EffAlgebra Op R)
    (a : ArgF Op (EffSelfCarrier Op)) : argSortOf (ArgF.fold alg a) = argSortOf a := by
  cases a <;> rfl

section Args

variable (sig : Signature Op) (n : Nat) (row : Templates.Row) (σ : Subst)
  {child : (fam : EffFam) → Nat → (y : Expr) → (i : Nat) → (i, Arg.expr y) ∈ σ →
    Except ReadFailure (EffSelfCarrier Op fam)}
  {children : (fam : EffFam) → Nat → (ys : List Expr) → (i : Nat) → (i, Arg.exprs ys) ∈ σ →
    Except ReadFailure (EffSelfCarrier Op fam)}
  {block : Nat → (ss : List TypeScript.Stmt) → (i : Nat) → (i, Arg.stmts ss) ∈ σ →
    Except ReadFailure (EffSelfCarrier Op .stmts)}

/-- One capture read has the sort it was read at, and its fold prints to the capture. -/
theorem readCapture_exact
    (hchild : ∀ fam d y i h c, child fam d y i h = .ok c → PrintsTo sig d fam c (.expr y))
    (hchildren : ∀ fam d ys i h c, children fam d ys i h = .ok c →
      PrintsTo sig d fam c (.exprs ys))
    (hblock : ∀ d ss i h c, block d ss i h = .ok c → PrintsTo sig d .stmts c (.stmts ss))
    (daemon : Bool) (d : Nat) (s : ArgSort) (i : Nat) (a : Arg) (hmem : (i, a) ∈ σ)
    (v : ArgF Op (EffSelfCarrier Op))
    (h : readCapture sig daemon σ child children block d s i a hmem = .ok v) :
    argSortOf v = s ∧ printArg sig d (ArgF.fold (printAlg sig) v) = .ok (some a) := by
  have leaf : ∀ {a' : Arg}, (readLeaf sig d daemon s a').mapError ReadFailure.here = .ok v →
      argSortOf v = s ∧ printArg sig d (ArgF.fold (printAlg sig) v) = .ok (some a') :=
    fun hl => let ⟨hs, hp⟩ := readLeaf_exact (mapError_eq_ok.mp hl); ⟨hs, hp d⟩
  cases a with
  | expr y =>
    simp only [readCapture] at h
    split at h
    · obtain ⟨c, hc, rfl⟩ := map_eq_ok.mp h
      exact ⟨rfl, printArg_child sig d _ c (.expr y) (hchild _ d y i hmem c hc)⟩
    · exact leaf h
  | exprs ys =>
    simp only [readCapture] at h
    split at h
    · obtain ⟨c, hc, rfl⟩ := map_eq_ok.mp h
      exact ⟨rfl, printArg_child sig d _ c (.exprs ys) (hchildren _ d ys i hmem c hc)⟩
    · exact leaf h
  | stmts body =>
    simp only [readCapture] at h
    split at h
    · obtain ⟨c, hc, rfl⟩ := map_eq_ok.mp h
      exact ⟨rfl, printArg_child sig d .stmts c (.stmts body) (hblock d body i hmem c hc)⟩
    · exact leaf h
  | str t => simp only [readCapture] at h; exact leaf h
  | int t => simp only [readCapture] at h; exact leaf h
  | type t => simp only [readCapture] at h; exact leaf h

/-- One argument read is one argument printed: the folded argument prints at the depth the
printer uses, and when its position is a hole of the row, to exactly what the skeleton captured
there. -/
theorem readArg_exact
    (hchild : ∀ fam d y i h c, child fam d y i h = .ok c → PrintsTo sig d fam c (.expr y))
    (hchildren : ∀ fam d ys i h c, children fam d ys i h = .ok c →
      PrintsTo sig d fam c (.exprs ys))
    (hblock : ∀ d ss i h c, block d ss i h = .ok c → PrintsTo sig d .stmts c (.stmts ss))
    (hfixed : ∀ p ∈ row.fixed, p.2.fixes = true → p.1 ∉ row.out.holes)
    (s : ArgSort) (i : Nat) (v : ArgF Op (EffSelfCarrier Op))
    (h : readArg sig n row σ child children block s i = .ok v) :
    ∃ x, printArg sig (argDepth row.fam (argSortOf (ArgF.fold (printAlg sig) v)) n
        (row.out.levelAt i)) (ArgF.fold (printAlg sig) v) = .ok x ∧
      (i ∈ row.out.holes → ∃ c, x = some c ∧ lookup σ i = some c) := by
  unfold readArg at h
  split at h
  · -- supplied by the classifier: no hole asks for it
    rename_i a' hsup
    cases h
    unfold Templates.Row.supplied at hsup
    obtain ⟨p, hfind, hp⟩ := Option.bind_eq_some_iff.mp hsup
    have hi : p.1 = i := by
      simpa only [beq_iff_eq] using List.find?_some hfind
    have hfix : p.2.fixes = true := by
      rw [← ArgPat.supplies_isSome (Op := Op) (R := EffSelfCarrier Op), hp]; rfl
    have hnot : i ∉ row.out.holes := hi ▸ hfixed p (List.mem_of_find?_eq_some hfind) hfix
    cases hp2 : p.2 with
    | is fixed =>
      rw [hp2] at hp
      simp only [Templates.ArgPat.supplies, Option.some.injEq] at hp
      subst hp
      obtain ⟨x, hx⟩ := printArg_fixed sig
        (argDepth row.fam (argSortOf (ArgF.fold (printAlg sig) (fixed.arg (Op := Op)))) n
          (row.out.levelAt i)) fixed
      exact ⟨x, hx, fun hin => absurd hin hnot⟩
    | decisionTag => rw [hp2] at hp; cases hp
    | someTerm => rw [hp2] at hp; cases hp
    | someTy => rw [hp2] at hp; cases hp
    | daemon b => rw [hp2] at hp; cases hp
  · split at h
    · rename_i a hmem hcap
      obtain ⟨hsort, hprint⟩ :=
        readCapture_exact sig σ hchild hchildren hblock _ _ s i a hmem v h
      refine ⟨some a, ?_, fun _ => ⟨a, rfl, lookup_of_captured σ i a hmem hcap⟩⟩
      rw [argSortOf_fold, hsort]
      exact hprint
    · cases h

/-- What `readArgs` read, `printArgs` prints back, and the printed substitution agrees with the
matched one at every hole in range. -/
theorem readArgs_exact
    (hchild : ∀ fam d y i h c, child fam d y i h = .ok c → PrintsTo sig d fam c (.expr y))
    (hchildren : ∀ fam d ys i h c, children fam d ys i h = .ok c →
      PrintsTo sig d fam c (.exprs ys))
    (hblock : ∀ d ss i h c, block d ss i h = .ok c → PrintsTo sig d .stmts c (.stmts ss))
    (hfixed : ∀ p ∈ row.fixed, p.2.fixes = true → p.1 ∉ row.out.holes) :
    ∀ (sorts : List ArgSort) (i : Nat) (args : List (ArgF Op (EffSelfCarrier Op))),
      readArgs sig n row σ child children block sorts i = .ok args →
      ∃ τ, printArgs sig row.fam n row.out (args.map (ArgF.fold (printAlg sig))) i = .ok τ ∧
        ∀ j, i ≤ j → j < i + sorts.length → j ∈ row.out.holes → lookup τ j = lookup σ j
  | [], i, args, h => by
    simp only [readArgs, Except.ok.injEq] at h
    subst h
    exact ⟨[], rfl, fun j h1 h2 _ => absurd h2 (by simp only [List.length_nil]; omega)⟩
  | s :: ss, i, args, h => by
    simp only [readArgs, bind_eq_ok, Except.ok.injEq] at h
    obtain ⟨a, ha, rest, hrest, rfl⟩ := h
    obtain ⟨x, hx, hhole⟩ := readArg_exact sig n row σ hchild hchildren hblock hfixed s i a
      (mapError_eq_ok.mp ha)
    obtain ⟨τ, hτ, hagree⟩ := readArgs_exact hchild hchildren hblock hfixed ss (i + 1) rest hrest
    have below : ∀ j, i ≤ j → j < i + (s :: ss).length → j ≠ i → j ∈ row.out.holes →
        lookup τ j = lookup σ j := fun j h1 h2 hji hj =>
      hagree j (by omega) (by simp only [List.length_cons] at h2; omega) hj
    cases x with
    | none =>
      refine ⟨τ, by simp only [List.map_cons, printArgs, hx, hτ, ok_bind], fun j h1 h2 hj => ?_⟩
      by_cases hji : j = i
      · subst hji
        obtain ⟨c, hc, _⟩ := hhole hj
        cases hc
      · exact below j h1 h2 hji hj
    | some c =>
      refine ⟨(i, c) :: τ, by simp only [List.map_cons, printArgs, hx, hτ, ok_bind],
        fun j h1 h2 hj => ?_⟩
      by_cases hji : j = i
      · subst hji
        obtain ⟨c', hc', hlook⟩ := hhole hj
        cases hc'
        rw [lookup_cons_self, hlook]
      · rw [lookup_cons_ne i j c τ (fun h => hji h.symm)]
        exact below j h1 h2 hji hj

end Args

/-! ## One row: what it read, the printer prints -/

section Row

variable {sig : Signature Op} {spell : String → List String → Option Op}

/-- The decided facts, at a row of the table: distinct holes, no hole for an argument the
classifier fixes, and every hole an argument. -/
theorem table_row {row : Templates.Row} (hmem : row ∈ table) :
    row.out.holes.Nodup ∧
    (∀ p ∈ row.fixed, p.2.fixes = true → p.1 ∉ row.out.holes) ∧
    (∀ sorts, argSorts row.fam row.ctor = some sorts → ∀ j ∈ row.out.holes, j < sorts.length) := by
  refine ⟨?_, fun p hp hfix hin => ?_, fun sorts hsorts => ?_⟩
  · simpa only [rowLinear, decide_eq_true_eq] using table_fact table_linear hmem
  · have := List.all_eq_true.mp (table_fact table_fixedNoHole hmem) p hp
    simp only [hfix, Bool.not_true, Bool.false_or, Bool.not_eq_eq_eq_not, Bool.not_true,
      List.contains_eq_mem, decide_eq_false_iff_not] at this
    exact this hin
  · have := table_fact table_holesLt hmem
    simp only [rowHolesLt, hsorts, List.all_eq_true, decide_eq_true_eq] at this
    exact this

/-- What `buildRow` accepted: the printer would choose the row, and `build` made the node. -/
theorem buildRow_ok {fam : EffFam} {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    {k : Nat} {e : EffSelfCarrier Op fam} (h : buildRow fam ctor args k = .ok e) :
    printedRow fam ctor args k = true ∧ build fam ctor args = some e := by
  unfold buildRow at h
  split at h
  · rename_i hp
    split at h
    · rename_i e' hb
      cases h
      exact ⟨hp, hb⟩
    · cases h
  · cases h

/-- One argument, printed. -/
theorem printArgs_single {fam : EffFam} {n : Nat} {out : RowOut} {a : ArgF Op Carrier} {c : Arg}
    (h : printArg sig (argDepth fam (argSortOf a) n (out.levelAt 0)) a = .ok (some c)) :
    printArgs sig fam n out [a] 0 = .ok [(0, c)] := by
  simp only [printArgs, h, ok_bind]

/-- A family read from one expression prints by the row step. -/
theorem printsTo_of_rowPrint {n : Nat} {fam : EffFam} {v : EffSelfCarrier Op fam} {ctor : String}
    {args : List (ArgF Op Carrier)} {x : Expr}
    (hfam : fam = .eff ∨ fam = .action ∨ fam = .layer)
    (hcata : cataFam (printAlg sig) fam v = tableLayer sig fam ctor args)
    (hrow : tableLayer.rowPrint sig fam ctor args n = .ok x) :
    PrintsTo sig n fam v (.expr x) := by
  rcases hfam with rfl | rfl | rfl
  · show cata_eff (printAlg sig) v n = .ok x
    rw [show cata_eff (printAlg sig) v = _ from hcata]; exact hrow
  · show cata_action (printAlg sig) v n = .ok x
    rw [show cata_action (printAlg sig) v = _ from hcata]; exact hrow
  · show cata_layer (printAlg sig) v n = .ok x
    rw [show cata_layer (printAlg sig) v = _ from hcata]; exact hrow

/-- **An accepted expression row prints.** The node `buildRow` accepted folds, one layer down,
to the layer function on the folded arguments (`cata_build`); the printer finds the same row
(`printedRow`); so when those arguments print to a substitution that instantiates the row's
skeleton to `x`, the node prints to `x`. Every case of `readRow_exact` ends here. -/
theorem accepted_prints {n : Nat} {row : Templates.Row} {k : Nat} (hk : table[k]? = some row)
    {t : Tpl} (hout : row.out = .tpl t)
    {args : List (ArgF Op (EffSelfCarrier Op))} {v : EffSelfCarrier Op row.fam} {τ : Subst}
    {x : Expr} (hb : buildRow row.fam row.ctor args k = .ok v)
    (hprint : printArgs sig row.fam n (.tpl t) (args.map (ArgF.fold (printAlg sig))) 0 = .ok τ)
    (hinst : inst n τ t = some x) : PrintsTo sig n row.fam v (.expr x) := by
  obtain ⟨hp, hbuild⟩ := buildRow_ok hb
  have hcata : cataFam (printAlg sig) row.fam v =
      tableLayer sig row.fam row.ctor (args.map (ArgF.fold (printAlg sig))) :=
    cata_build (tableLayer sig) row.fam row.ctor args v hbuild
  have hrow : tableLayer.rowPrint sig row.fam row.ctor
      (args.map (ArgF.fold (printAlg sig))) n = .ok x := by
    simp only [tableLayer.rowPrint, find?_selects_of_printedRow sig hp hk, hout, hprint, ok_bind,
      hinst]
  have hfamily := table_fact table_family (List.mem_of_getElem? hk)
  simp only [rowFamily, hout, Bool.or_eq_true, beq_iff_eq] at hfamily
  exact printsTo_of_rowPrint (by
    rcases hfamily with (hf | hf) | hf
    · exact .inl hf
    · exact .inr (.inl hf)
    · exact .inr (.inr hf)) hcata hrow

theorem toOption_eq_some {ε α : Type} {e : Except ε α} {a : α} (h : e.toOption = some a) :
    e = .ok a := by
  cases e with
  | error _ => cases h
  | ok b => cases h; rfl

/-- What one row read, the printer prints: the row law of `read_exact`, with the recursion as
hypotheses (`readRow` has none of its own). -/
theorem readRow_exact (hl : LawfulSpelling sig spell) {fam : EffFam} {n : Nat} {x : Expr}
    {row : Templates.Row} {k : Nat} (hk : table[k]? = some row)
    {child : (fam' : EffFam) → Nat → (y : Expr) → sizeOf y < sizeOf x →
      Except ReadFailure (EffSelfCarrier Op fam')}
    {children : (fam' : EffFam) → Nat → (ys : List Expr) → sizeOf ys < sizeOf x →
      Except ReadFailure (EffSelfCarrier Op fam')}
    {block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf x →
      Except ReadFailure (EffSelfCarrier Op .stmts)}
    {same : (fam' : EffFam) → famRank fam' < famRank fam → Nat →
      Option (Except ReadFailure (EffSelfCarrier Op fam'))}
    (hchild : ∀ fam' d y h c, child fam' d y h = .ok c → PrintsTo sig d fam' c (.expr y))
    (hchildren : ∀ fam' d ys h c, children fam' d ys h = .ok c →
      PrintsTo sig d fam' c (.exprs ys))
    (hblock : ∀ d ss h c, block d ss h = .ok c → PrintsTo sig d .stmts c (.stmts ss))
    (hsame : ∀ fam' hlt d c, same fam' hlt d = some (.ok c) → PrintsTo sig d fam' c (.expr x))
    {v : EffSelfCarrier Op fam}
    (h : readRow sig spell fam n x row k child children block same = some (.ok v)) :
    PrintsTo sig n fam v (.expr x) := by
  obtain ⟨hnodup, hfixed, hholes⟩ := table_row (List.mem_of_getElem? hk)
  unfold readRow at h
  split at h
  case isFalse => cases h
  rename_i hfam
  split at h
  · cases h
  · cases h
  · -- the row call
    cases fam with
    | eff =>
      simp only [Option.some.injEq] at h
      exact readPerform_exact hl (mapError_eq_ok.mp h)
    | stmt => cases h
    | stmts => cases h
    | effs => cases h
    | action => cases h
    | layer => cases h
    | layers => cases h
  · -- an expression skeleton
    rename_i t hout
    subst hfam
    rw [hout] at hnodup hholes
    split at h
    · cases h
    · rename_i σ hσ
      split at h
      · cases h
      · rename_i sorts hsorts
        have hlt := hholes sorts hsorts
        split at h
        · -- rigid: the arguments by sort, then the accepted row
          simp only [Option.some.injEq] at h
          obtain ⟨args, hargs, hb⟩ := bind_eq_ok.mp h
          obtain ⟨τ, hτ, hagree⟩ := readArgs_exact sig n row σ
            (fun fam' d y i hy c hc => hchild fam' d y _ c hc)
            (fun fam' d ys i hy c hc => hchildren fam' d ys _ c hc)
            (fun d ss i hy c hc => hblock d ss _ c hc) hfixed sorts 0 args hargs
          rw [hout] at hτ hagree
          refine accepted_prints hk hout hb hτ ?_
          rw [inst_congr n τ σ t fun j hj =>
            hagree j (Nat.zero_le j) (by simpa only [Nat.zero_add] using hlt j hj) hj]
          exact inst_of_match n t x σ hσ hnodup
        · -- transparent: a bare hole, which is argument `0`
          rename_i hrigid
          cases t with
          | hole i =>
            split at h
            · -- the same tree at a strictly lower family
              rename_i fam'
              have hi : i = 0 := by
                have := hlt i (by simp only [Templates.RowOut.holes, holes, List.mem_singleton])
                simp only [List.length_singleton] at this; omega
              subst hi
              split at h
              · rename_i hlt'
                obtain ⟨r, hr, h⟩ := Option.map_eq_some_iff.mp h
                cases r with
                | error f => simp only [Except.mapError, bind, Except.bind, reduceCtorEq] at h
                | ok c =>
                  simp only [Except.mapError, ok_bind] at h
                  exact accepted_prints hk hout h
                    (printArgs_single
                      (printArg_child sig _ fam' c (.expr x) (hsame fam' hlt' _ c hr)))
                    (by simp only [inst, lookup_cons_self])
              · cases h
            · -- one leaf read of the whole tree
              have hi : i = 0 := by
                have := hlt i (by simp only [Templates.RowOut.holes, holes, List.mem_singleton])
                simp only [List.length_singleton] at this; omega
              subst hi
              split at h
              · rename_i a ha
                obtain ⟨e, hb, h⟩ := Option.map_eq_some_iff.mp h
                cases h
                exact accepted_prints hk hout (toOption_eq_some hb)
                  (printArgs_single ((readLeaf_exact ha).2 _))
                  (by simp only [inst, lookup_cons_self])
              · cases h
            · cases h
          | _ => exact absurd rfl hrigid

/-- What one statement row read, the printer prints, with the binders it declares. -/
theorem readStmtRow_exact {n : Nat} {s : TypeScript.Stmt} {row : Templates.Row} {k : Nat}
    (hk : table[k]? = some row)
    {child : (fam' : EffFam) → Nat → (y : Expr) → sizeOf y < sizeOf s →
      Except ReadFailure (EffSelfCarrier Op fam')}
    {children : (fam' : EffFam) → Nat → (ys : List Expr) → sizeOf ys < sizeOf s →
      Except ReadFailure (EffSelfCarrier Op fam')}
    {block : Nat → (ss : List TypeScript.Stmt) → sizeOf ss < sizeOf s →
      Except ReadFailure (EffSelfCarrier Op .stmts)}
    (hchild : ∀ fam' d y h c, child fam' d y h = .ok c → PrintsTo sig d fam' c (.expr y))
    (hchildren : ∀ fam' d ys h c, children fam' d ys h = .ok c →
      PrintsTo sig d fam' c (.exprs ys))
    (hblock : ∀ d ss h c, block d ss h = .ok c → PrintsTo sig d .stmts c (.stmts ss))
    {st : Program.Stmt Op} {declared : Nat}
    (h : readStmtRow sig n s row k child children block = some (.ok (st, declared))) :
    cata_stmt (printAlg sig) st n = .ok (s, declared) := by
  obtain ⟨hnodup, hfixed, hholes⟩ := table_row (List.mem_of_getElem? hk)
  unfold readStmtRow at h
  split at h
  case isFalse => cases h
  rename_i hfam
  split at h
  · rename_i t hout
    rw [hout] at hnodup hholes
    split at h
    · cases h
    · rename_i σ hσ
      split at h
      · cases h
      · rename_i sorts hsorts
        have hlt := hholes sorts (hfam ▸ hsorts)
        simp only [Option.some.injEq] at h
        obtain ⟨args, hargs, h⟩ := bind_eq_ok.mp h
        obtain ⟨e, hb, h⟩ := bind_eq_ok.mp h
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hp, hbuild⟩ := buildRow_ok hb
        obtain ⟨τ, hτ, hagree⟩ := readArgs_exact sig n row σ
          (fun fam' d y i hy c hc => hchild fam' d y _ c hc)
          (fun fam' d ys i hy c hc => hchildren fam' d ys _ c hc)
          (fun d ss i hy c hc => hblock d ss _ c hc) hfixed sorts 0 args hargs
        rw [hout, hfam] at hτ
        rw [hout] at hagree
        have hinst : instStmt n τ t = some s := by
          rw [instStmt_congr n τ σ t fun j hj =>
            hagree j (Nat.zero_le j) (by simpa only [Nat.zero_add] using hlt j hj) hj]
          exact instStmt_of_match n t s σ hσ hnodup
        have hfind := find?_selects_of_printedRow sig hp hk
        have hcata : cataFam (printAlg sig) .stmt e =
            tableLayer sig .stmt row.ctor (args.map (ArgF.fold (printAlg sig))) :=
          cata_build (tableLayer sig) .stmt row.ctor args e hbuild
        show cata_stmt (printAlg sig) e n = .ok (s, t.declares)
        rw [show cata_stmt (printAlg sig) e = _ from hcata]
        obtain ⟨rfam, rctor, rfixed, rout⟩ := row
        simp only at hout
        subst hout
        simp only [tableLayer, hfind, hτ, ok_bind, hinst]
  · cases h

end Row

/-! ## The theorem: induction on the size of the tree -/

section Exact

variable {sig : Signature Op} {spell : String → List String → Option Op}

theorem getD_eq_ok {ε α : Type} {o : Option (Except ε α)} {err : ε} {a : α}
    (h : o.getD (.error err) = .ok a) : o = some (.ok a) := by
  cases o with
  | none => cases h
  | some r => exact congrArg some h

/-- The spines print item by item; the statement spine threads what each statement declares. -/
theorem cata_effs_cons (e : Eff Op) (es : Effs Op) (n : Nat) :
    cata_effs (printAlg sig) (.cons e es) n =
      (cata_eff (printAlg sig) e n >>= fun h =>
        cata_effs (printAlg sig) es n >>= fun t => pure (h :: t)) := rfl

theorem cata_layers_cons (l : LayerTerm Op) (ls : LayerTerms Op) (n : Nat) :
    cata_layers (printAlg sig) (.cons l ls) n =
      (cata_layer (printAlg sig) l n >>= fun h =>
        cata_layers (printAlg sig) ls n >>= fun t => pure (h :: t)) := rfl

theorem cata_stmts_cons (st : Program.Stmt Op) (ss : Stmts Op) (n : Nat) :
    cata_stmts (printAlg sig) (.cons st ss) n =
      (cata_stmt (printAlg sig) st n >>= fun p =>
        cata_stmts (printAlg sig) ss (n + p.2) >>= fun t => pure (p.1 :: t)) := rfl

/-- Everything of size at most `m` that the reader accepts prints back to what was read. -/
def ExactUpTo (sig : Signature Op) (spell : String → List String → Option Op) (m : Nat) : Prop :=
  (∀ fam n (x : Expr) v, sizeOf x ≤ m → readT sig spell fam n x = some (.ok v) →
    PrintsTo sig n fam v (.expr x)) ∧
  (∀ fam n (xs : List Expr) v, sizeOf xs ≤ m → readSpine sig spell fam n xs = .ok v →
    PrintsTo sig n fam v (.exprs xs)) ∧
  (∀ n (ss : List TypeScript.Stmt) v, sizeOf ss ≤ m → readStmts sig spell n ss = .ok v →
    PrintsTo sig n .stmts v (.stmts ss))

/-- The recursion's three hypotheses, from exactness at every smaller size: what the row
theorems ask of whatever reads a row's captures. -/
theorem below {m : Nat} (ih : ∀ m', m' < m → ExactUpTo sig spell m') {bound : Nat}
    (hb : bound ≤ m) :
    (∀ fam' d (y : Expr) (_ : sizeOf y < bound) c,
      (readT sig spell fam' d y).getD (.error (.here (unread fam'))) = .ok c →
        PrintsTo sig d fam' c (.expr y)) ∧
    (∀ fam' d (ys : List Expr) (_ : sizeOf ys < bound) c,
      readSpine sig spell fam' d ys = .ok c → PrintsTo sig d fam' c (.exprs ys)) ∧
    (∀ d (ss : List TypeScript.Stmt) (_ : sizeOf ss < bound) c,
      readStmts sig spell d ss = .ok c → PrintsTo sig d .stmts c (.stmts ss)) :=
  ⟨fun fam' d y hlt c hc =>
      (ih (sizeOf y) (by omega)).1 fam' d y c (Nat.le_refl _) (getD_eq_ok hc),
   fun fam' d ys hlt c hc => (ih (sizeOf ys) (by omega)).2.1 fam' d ys c (Nat.le_refl _) hc,
   fun d ss hlt c hc => (ih (sizeOf ss) (by omega)).2.2 d ss c (Nat.le_refl _) hc⟩

/-- The reader's step at a tree, given exactness below it and at the lower families. -/
theorem readT_exact_step (hl : LawfulSpelling sig spell) {m : Nat}
    (ih : ∀ m', m' < m → ExactUpTo sig spell m') {fam : EffFam} {n : Nat} {x : Expr}
    (hx : sizeOf x ≤ m)
    (hsame : ∀ fam', famRank fam' < famRank fam → ∀ d c,
      readT sig spell fam' d x = some (.ok c) → PrintsTo sig d fam' c (.expr x))
    {v : EffSelfCarrier Op fam} (h : readT sig spell fam n x = some (.ok v)) :
    PrintsTo sig n fam v (.expr x) := by
  rw [readT] at h
  obtain ⟨⟨row, k⟩, hmem, hrow⟩ := List.exists_of_findSome?_eq_some h
  have hk : table[k]? = some row := List.mk_mem_zipIdx_iff_getElem?.mp hmem
  obtain ⟨hchild, hchildren, hblock⟩ := below ih hx
  exact readRow_exact hl hk hchild hchildren hblock
    (fun fam' hlt d c hc => hsame fam' hlt d c hc) hrow

theorem famRank_le_one (fam : EffFam) : famRank fam ≤ 1 := by
  cases fam <;> simp only [famRank, Nat.le_refl, Nat.zero_le]

/-- The spine's step: item by item, given exactness at the readers of smaller trees. -/
theorem readSpine_exact_step {m : Nat} (ih : ∀ m', m' < m → ExactUpTo sig spell m') :
    ∀ (fam : EffFam) (n : Nat) (xs : List Expr) (v : EffSelfCarrier Op fam),
      sizeOf xs ≤ m → readSpine sig spell fam n xs = .ok v → PrintsTo sig n fam v (.exprs xs)
  | .effs, n, [], v, _, h => by
    rw [readSpine] at h
    cases h
    rfl
  | .effs, n, y :: rest, v, hx, h => by
    rw [readSpine] at h
    have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
    obtain ⟨e, he, h⟩ := bind_eq_ok.mp h
    obtain ⟨es, hes, h⟩ := bind_eq_ok.mp h
    cases h
    have h1 := (ih (sizeOf y) (by omega)).1 .eff n y e (Nat.le_refl _)
      (getD_eq_ok (mapError_eq_ok.mp he))
    have h2 := readSpine_exact_step ih .effs n rest es (by omega) (mapError_eq_ok.mp hes)
    show cata_effs (printAlg sig) (.cons e es) n = .ok (y :: rest)
    rw [cata_effs_cons, show cata_eff (printAlg sig) e n = .ok y from h1,
      show cata_effs (printAlg sig) es n = .ok rest from h2]
    rfl
  | .layers, n, [], v, _, h => by
    rw [readSpine] at h
    cases h
    rfl
  | .layers, n, y :: rest, v, hx, h => by
    rw [readSpine] at h
    have hsz : sizeOf (y :: rest) = 1 + sizeOf y + sizeOf rest := List.cons.sizeOf_spec y rest
    obtain ⟨l, hl', h⟩ := bind_eq_ok.mp h
    obtain ⟨ls, hls, h⟩ := bind_eq_ok.mp h
    cases h
    have h1 := (ih (sizeOf y) (by omega)).1 .layer n y l (Nat.le_refl _)
      (getD_eq_ok (mapError_eq_ok.mp hl'))
    have h2 := readSpine_exact_step ih .layers n rest ls (by omega) (mapError_eq_ok.mp hls)
    show cata_layers (printAlg sig) (.cons l ls) n = .ok (y :: rest)
    rw [cata_layers_cons, show cata_layer (printAlg sig) l n = .ok y from h1,
      show cata_layers (printAlg sig) ls n = .ok rest from h2]
    rfl
  | .eff, _, _, _, _, h => by
    rw [readSpine] at h
    · cases h
    all_goals (intros; contradiction)
  | .stmt, _, _, _, _, h => by
    rw [readSpine] at h
    · cases h
    all_goals (intros; contradiction)
  | .stmts, _, _, _, _, h => by
    rw [readSpine] at h
    · cases h
    all_goals (intros; contradiction)
  | .action, _, _, _, _, h => by
    rw [readSpine] at h
    · cases h
    all_goals (intros; contradiction)
  | .layer, _, _, _, _, h => by
    rw [readSpine] at h
    · cases h
    all_goals (intros; contradiction)

/-- The statement spine's step: each statement through its row, the rest under what it
declares. -/
theorem readStmts_exact_step {m : Nat} (ih : ∀ m', m' < m → ExactUpTo sig spell m') :
    ∀ (n : Nat) (ss : List TypeScript.Stmt) (v : Stmts Op),
      sizeOf ss ≤ m → readStmts sig spell n ss = .ok v → PrintsTo sig n .stmts v (.stmts ss)
  | n, [], v, _, h => by
    rw [readStmts] at h
    cases h
    rfl
  | n, s :: rest, v, hx, h => by
    rw [readStmts] at h
    have hsz : sizeOf (s :: rest) = 1 + sizeOf s + sizeOf rest := List.cons.sizeOf_spec s rest
    simp only at h
    split at h
    · rename_i r hfind
      obtain ⟨⟨row, k⟩, hmem, hrow⟩ := List.exists_of_findSome?_eq_some hfind
      have hk : table[k]? = some row := List.mk_mem_zipIdx_iff_getElem?.mp hmem
      obtain ⟨⟨st, declared⟩, hst, h⟩ := bind_eq_ok.mp h
      obtain ⟨tail, htail, h⟩ := bind_eq_ok.mp h
      cases h
      have hr : r = .ok (st, declared) := mapError_eq_ok.mp hst
      subst hr
      obtain ⟨hchild, hchildren, hblock⟩ := below ih (bound := sizeOf s) (by omega)
      have h1 := readStmtRow_exact (sig := sig) hk hchild hchildren hblock hrow
      have h2 := readStmts_exact_step ih (n + declared) rest tail (by omega)
        (mapError_eq_ok.mp htail)
      show cata_stmts (printAlg sig) (.cons st tail) n = .ok (s :: rest)
      rw [cata_stmts_cons, h1]
      simp only [ok_bind]
      rw [show cata_stmts (printAlg sig) tail (n + declared) = .ok rest from h2]
      rfl
    · cases h

/-- Everything the reader accepts prints back to what was read, at every size. -/
theorem exactUpTo (hl : LawfulSpelling sig spell) (m : Nat) : ExactUpTo sig spell m := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    have hlow : ∀ fam, famRank fam = 0 → ∀ n (x : Expr) v, sizeOf x ≤ m →
        readT sig spell fam n x = some (.ok v) → PrintsTo sig n fam v (.expr x) :=
      fun fam h0 n x v hx h =>
        readT_exact_step hl ih hx (fun fam' hlt => absurd hlt (by omega)) h
    refine ⟨fun fam n x v hx h => ?_, readSpine_exact_step ih, readStmts_exact_step ih⟩
    exact readT_exact_step hl ih hx
      (fun fam' hlt d c hc =>
        hlow fam' (by have := famRank_le_one fam; omega) d x c hx hc) h

/-- **Law 12.** What the reader accepts prints back to exactly the tree it read. -/
theorem read_exact (hl : LawfulSpelling sig spell) {n : Nat} {x : Expr} {e : Eff Op}
    (h : readEff sig spell n x = .ok e) : print sig n e = .ok x :=
  (exactUpTo hl (sizeOf x)).1 .eff n x e (Nat.le_refl _)
    (getD_eq_ok (mapError_eq_ok.mp h))

/-- The same of a layer: a layer is closed, so it is read, and printed, at depth `0`. -/
theorem readLayer_exact (hl : LawfulSpelling sig spell) {x : Expr} {l : LayerTerm Op}
    (h : readLayer sig spell x = .ok l) : printLayer sig l = .ok x :=
  (exactUpTo hl (sizeOf x)).1 .layer 0 x l (Nat.le_refl _)
    (getD_eq_ok (mapError_eq_ok.mp h))

end Exact

end Effect4.Program
