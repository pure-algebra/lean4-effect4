import Effect4.Laws.Codegen.ReadPrint
import Effect4.Laws.Program.Size

/-!
# Laws.Codegen.PrintReadable — a readable program prints

The completeness half of the round trip: `Readable sig n e = true → ∃ x, print sig n e = .ok x`.
With law 11 (`read_print`) this gives `Readable e → roundTrip e = ok e`.

The proof is the generic node step again, by induction on the size of the program measured by
a fold (`sizeAlg`, `Laws/Program/Size.lean`: one more than the children), so a child is smaller
by one generic lemma (`size_child_lt`) and no constructor is named. At a node the domain says the printer's row is
a skeleton or the row call and every argument is readable; every readable argument prints
(`printArg_ok`); the skeleton instantiates because every hole has a capture of its kind, which
is a decided fact of the table (`table_holeKinds`) joined to the calculus lemma `inst_of_kinds`.
-/

set_option autoImplicit false

namespace Effect4.Codegen.Template

open TypeScript (Expr Stmt TypeRef)

/-- The kind of capture a hole asks for. -/
inductive HoleKind where
  | expr | exprs | str | int | type | stmts
  deriving DecidableEq, Repr

def Arg.kind : Arg → HoleKind
  | .expr _ => .expr | .exprs _ => .exprs | .str _ => .str | .int _ => .int
  | .type _ => .type | .stmts _ => .stmts

def holeKindsAnn : Option Nat → List (Nat × HoleKind)
  | none => []
  | some i => [(i, .type)]

mutual
  /-- Every hole of a skeleton with the kind of capture it asks for. -/
  def holeKinds : Tpl → List (Nat × HoleKind)
    | .hole i => [(i, .expr)]
    | .strHole i => [(i, .str)]
    | .intHole i => [(i, .int)]
    | .arrHole i => [(i, .exprs)]
    | .binderRef _ | .ident _ | .str _ | .int _ | .bool _ => []
    | .call h args => holeKinds h ++ holeKindsTs args
    | .callSpread h i => holeKinds h ++ [(i, .exprs)]
    | .arr items => holeKindsTs items
    | .object fields => holeKindsFields fields
    | .arrow b => holeKinds b
    | .lambda _ b => holeKinds b
    | .cond t a b => holeKinds t ++ holeKinds a ++ holeKinds b
    | .method target _ args => holeKinds target ++ holeKindsTs args
    | .arrowBlock _ body => holeKindsStmts body
    | .generator body => holeKindsStmts body
  def holeKindsTs : Tpls → List (Nat × HoleKind)
    | .nil => []
    | .cons h t => holeKinds h ++ holeKindsTs t
  def holeKindsFields : Fields → List (Nat × HoleKind)
    | .nil => []
    | .cons _ v t => holeKinds v ++ holeKindsFields t
  def holeKindsStmt : StmtTpl → List (Nat × HoleKind)
    | .letInit _ v ann => holeKinds v ++ holeKindsAnn ann
    | .assign _ v | .ret v | .exprStmt v | .constYield _ v | .yieldDiscard v => holeKinds v
    | .ifElse t a b => holeKinds t ++ holeKindsStmts a ++ holeKindsStmts b
    | .whileTrue body => holeKindsStmts body
    | .breakTo => []
  def holeKindsStmts : StmtTpls → List (Nat × HoleKind)
    | .nil => []
    | .cons h t => holeKindsStmt h ++ holeKindsStmts t
    | .hole i => [(i, .stmts)]
end

/-- A substitution has a capture of the asked kind at every hole of the list. -/
def Kinds (σ : Subst) (ks : List (Nat × HoleKind)) : Prop :=
  ∀ p ∈ ks, ∃ a, lookup σ p.1 = some a ∧ Arg.kind a = p.2

theorem Kinds.left {σ : Subst} {xs ys : List (Nat × HoleKind)} (h : Kinds σ (xs ++ ys)) :
    Kinds σ xs := fun p hp => h p (List.mem_append_left _ hp)

theorem Kinds.right {σ : Subst} {xs ys : List (Nat × HoleKind)} (h : Kinds σ (xs ++ ys)) :
    Kinds σ ys := fun p hp => h p (List.mem_append_right _ hp)

attribute [local simp] inst insts instFields instStmt instStmts instAnn holeKinds holeKindsTs
  holeKindsFields holeKindsStmt holeKindsStmts holeKindsAnn Arg.kind

attribute [local aesop safe forward] Kinds.left Kinds.right

/-- A capture of a kind is the constructor of that kind. -/
theorem kind_expr {a : Arg} (h : Arg.kind a = .expr) : ∃ e, a = .expr e := by
  cases a <;> simp_all
theorem kind_exprs {a : Arg} (h : Arg.kind a = .exprs) : ∃ e, a = .exprs e := by
  cases a <;> simp_all
theorem kind_str {a : Arg} (h : Arg.kind a = .str) : ∃ e, a = .str e := by
  cases a <;> simp_all
theorem kind_int {a : Arg} (h : Arg.kind a = .int) : ∃ e, a = .int e := by
  cases a <;> simp_all
theorem kind_type {a : Arg} (h : Arg.kind a = .type) : ∃ e, a = .type e := by
  cases a <;> simp_all
theorem kind_stmts {a : Arg} (h : Arg.kind a = .stmts) : ∃ e, a = .stmts e := by
  cases a <;> simp_all

attribute [local aesop safe forward] kind_expr kind_exprs kind_str kind_int kind_type kind_stmts

theorem instAnn_of_kinds (σ : Subst) : ∀ (ann : Option Nat), Kinds σ (holeKindsAnn ann) →
    ∃ ty, instAnn σ ann = some ty
  | none, _ => ⟨none, rfl⟩
  | some i, h => by
    obtain ⟨a, ha, hk⟩ := h (i, .type) (by simp)
    aesop

mutual
  /-- A skeleton instantiates under a substitution that captures every hole in its kind. -/
  theorem inst_of_kinds (n : Nat) (σ : Subst) : ∀ (t : Tpl), Kinds σ (holeKinds t) →
      ∃ e, inst n σ t = some e
    | .hole i, h => by
      obtain ⟨a, ha, hk⟩ := h (i, .expr) (by simp)
      aesop
    | .strHole i, h => by
      obtain ⟨a, ha, hk⟩ := h (i, .str) (by simp)
      aesop
    | .intHole i, h => by
      obtain ⟨a, ha, hk⟩ := h (i, .int) (by simp)
      aesop
    | .arrHole i, h => by
      obtain ⟨a, ha, hk⟩ := h (i, .exprs) (by simp)
      aesop
    | .binderRef k, _ => ⟨_, rfl⟩
    | .ident s, _ => ⟨_, rfl⟩
    | .str s, _ => ⟨_, rfl⟩
    | .int v, _ => ⟨_, rfl⟩
    | .bool b, _ => ⟨_, rfl⟩
    | .call hd args, h => by
      have ih1 := inst_of_kinds n σ hd
      have ih2 := insts_of_kinds n σ args
      aesop
    | .callSpread hd i, h => by
      have ih1 := inst_of_kinds n σ hd
      obtain ⟨a, ha, hk⟩ := h (i, .exprs) (by simp)
      aesop
    | .arr items, h => by
      have ih := insts_of_kinds n σ items
      aesop
    | .object fields, h => by
      have ih := instFields_of_kinds n σ fields
      aesop
    | .arrow b, h => by
      have ih := inst_of_kinds n σ b
      aesop
    | .lambda bs b, h => by
      have ih := inst_of_kinds n σ b
      aesop
    | .cond t a b, h => by
      have ih1 := inst_of_kinds n σ t
      have ih2 := inst_of_kinds n σ a
      have ih3 := inst_of_kinds n σ b
      aesop
    | .method target name args, h => by
      have ih1 := inst_of_kinds n σ target
      have ih2 := insts_of_kinds n σ args
      aesop
    | .arrowBlock bs body, h => by
      have ih := instStmts_of_kinds n σ body
      aesop
    | .generator body, h => by
      have ih := instStmts_of_kinds n σ body
      aesop
  theorem insts_of_kinds (n : Nat) (σ : Subst) : ∀ (ts : Tpls), Kinds σ (holeKindsTs ts) →
      ∃ es, insts n σ ts = some es
    | .nil, _ => ⟨[], rfl⟩
    | .cons hd tl, h => by
      have ih1 := inst_of_kinds n σ hd
      have ih2 := insts_of_kinds n σ tl
      aesop
  theorem instFields_of_kinds (n : Nat) (σ : Subst) : ∀ (fs : Fields),
      Kinds σ (holeKindsFields fs) → ∃ es, instFields n σ fs = some es
    | .nil, _ => ⟨[], rfl⟩
    | .cons key v tl, h => by
      have ih1 := inst_of_kinds n σ v
      have ih2 := instFields_of_kinds n σ tl
      aesop
  theorem instStmt_of_kinds (n : Nat) (σ : Subst) : ∀ (t : StmtTpl),
      Kinds σ (holeKindsStmt t) → ∃ s, instStmt n σ t = some s
    | .letInit k v ann, h => by
      have ih := inst_of_kinds n σ v
      have ih2 := instAnn_of_kinds σ ann
      aesop
    | .assign k v, h => by
      have ih := inst_of_kinds n σ v
      aesop
    | .ret v, h => by
      have ih := inst_of_kinds n σ v
      aesop
    | .exprStmt v, h => by
      have ih := inst_of_kinds n σ v
      aesop
    | .constYield k v, h => by
      have ih := inst_of_kinds n σ v
      aesop
    | .yieldDiscard v, h => by
      have ih := inst_of_kinds n σ v
      aesop
    | .ifElse t a b, h => by
      have ih1 := inst_of_kinds n σ t
      have ih2 := instStmts_of_kinds n σ a
      have ih3 := instStmts_of_kinds n σ b
      aesop
    | .whileTrue body, h => by
      have ih := instStmts_of_kinds n σ body
      aesop
    | .breakTo, _ => ⟨_, rfl⟩
  theorem instStmts_of_kinds (n : Nat) (σ : Subst) : ∀ (ts : StmtTpls),
      Kinds σ (holeKindsStmts ts) → ∃ ss, instStmts n σ ts = some ss
    | .nil, _ => ⟨[], rfl⟩
    | .cons hd tl, h => by
      have ih1 := instStmt_of_kinds n σ hd
      have ih2 := instStmts_of_kinds n σ tl
      aesop
    | .hole i, h => by
      obtain ⟨a, ha, hk⟩ := h (i, .stmts) (by simp)
      aesop
end

end Effect4.Codegen.Template

namespace Effect4.Program

open TypeScript (Expr Stmt)
open Effect4.Codegen
open Effect4.Codegen.Template
open Effect4.Codegen.Templates (RowOut ArgPat Fixed table tableLayer printAlg printArg printArgs
  argDepth argSortOf Carrier Out)

variable {Op : Type}

/-! ## What an argument prints to: its kind, and whether it prints at all -/

/-- The kind of capture an argument of a sort prints to, when it prints one. -/
def sortKind : ArgSort → Option HoleKind
  | .child .effs | .child .layers => some .exprs
  | .child .stmts => some .stmts
  | .child .stmt | .mode | .bool | .op => none
  | .child _ | .term | .optTerm | .cause | .lit | .key | .forkOptions | .path => some .expr
  | .decision => some .str
  | .nat => some .int
  | .optTy => some .type

/-- Whether an argument prints to a capture: by its sort, and for the three sorts whose
value decides it, by the value. -/
def argPrints {R : EffFam → Type} : ArgF Op R → Bool
  | .child .stmt _ | .mode _ | .bool _ | .op _ => false
  | .optTerm none | .decision .bool | .decision .option | .optTy none => false
  | _ => true

/-- A sort every value of which prints. -/
def sortPrints : ArgSort → Bool
  | .child .stmt | .mode | .bool | .op | .optTerm | .decision | .optTy => false
  | _ => true

theorem argPrints_of_sortPrints {R : EffFam → Type} (v : ArgF Op R)
    (h : sortPrints (argSortOf v) = true) : argPrints v = true := by
  cases v <;> aesop (add norm simp [sortPrints, argSortOf, argPrints])

/-- A readable leaf prints: to a capture of its sort's kind when `argPrints`, to none
otherwise. -/
theorem printArg_ok_leaf {sig : Signature Op} {d : Nat} {daemon : Bool}
    (v : ArgF Op (EffSelfCarrier Op))
    (hr : argReadable sig d daemon (ArgF.fold (readableAlg sig) v) = true)
    (hleaf : ∀ fam, argSortOf v ≠ .child fam) :
    ∃ x, printArg sig d (ArgF.fold (printAlg sig) v) = .ok x ∧
      (argPrints v = true → ∃ a, x = some a ∧ some (Arg.kind a) = sortKind (argSortOf v)) ∧
      (argPrints v = false → x = none) := by
  have hl := leafReadable_of_argReadable hleaf hr
  cases v <;> aesop (add norm simp [ArgF.fold, printArg, argPrints, sortKind, argSortOf, Arg.kind,
    leafReadable, keyReadable, printKey, bind, Except.bind, pure, Except.pure], safe cases Decision)

/-- What a printed capture's kind is, and that a readable argument prints: to a capture of
its sort's kind when `argPrints`, to none otherwise. -/
theorem printArg_ok {sig : Signature Op} {d : Nat} {daemon : Bool}
    {v : ArgF Op (EffSelfCarrier Op)}
    (hr : argReadable sig d daemon (ArgF.fold (readableAlg sig) v) = true)
    (hchild : ∀ fam' (c : EffSelfCarrier Op fam'), v = .child fam' c → ReadableAt sig fam' c d →
      ∃ y : Out fam', cataFam (printAlg sig) fam' c d = .ok y) :
    ∃ x, printArg sig d (ArgF.fold (printAlg sig) v) = .ok x ∧
      (argPrints v = true → ∃ a, x = some a ∧ some (Arg.kind a) = sortKind (argSortOf v)) ∧
      (argPrints v = false → x = none) := by
  cases v with
  | child fam c =>
    have hra := readableAt_of_argReadable hr
    obtain ⟨y, hy⟩ := hchild fam c rfl hra
    cases fam <;> aesop (add norm simp [ArgF.fold, cataFam, printArg, argPrints, sortKind,
      argSortOf, Arg.kind, bind, Except.bind, pure, Except.pure])
  | _ => exact printArg_ok_leaf _ hr (fun _ h => by cases h)


/-! ## The table: every hole is filled by a capture of its kind -/

/-- The pattern at `i` forces the argument to print (`someTerm`, `decisionTag`, `someTy`). -/
def patForcesPrint (row : Templates.Row) (i : Nat) : Bool :=
  row.fixed.any fun p => p.1 == i && match p.2 with
    | .someTerm | .decisionTag | .someTy => true
    | _ => false

def RowOut.holeKinds : RowOut → List (Nat × HoleKind)
  | .tpl t => Template.holeKinds t
  | .stmt t => holeKindsStmt t
  | _ => []

/-- Every hole of a row asks for the kind its argument's sort prints to, and the argument
prints: by its sort, or because the classifier forces it. -/
def rowHoleKinds (row : Templates.Row) : Bool :=
  match argSorts row.fam row.ctor with
  | some sorts => (RowOut.holeKinds row.out).all fun p => match sorts[p.1]? with
      | some s => sortKind s == some p.2 && (sortPrints s || patForcesPrint row p.1)
      | none => false
  | none => match row.out with
    | .tpl _ | .stmt _ => false
    | _ => true

theorem table_holeKinds : table.all rowHoleKinds = true := by decide

/-- An argument the classifier forces prints. -/
theorem argPrints_of_forced {row : Templates.Row} {fam : EffFam} {ctor : String}
    {args : List (ArgF Op (EffSelfCarrier Op))} (hsel : row.selects fam ctor args = true)
    (i : Nat) (hforce : patForcesPrint row i = true) (v : ArgF Op (EffSelfCarrier Op))
    (hv : args[i]? = some v) : argPrints v = true := by
  simp only [Templates.Row.selects, Bool.and_eq_true, List.all_eq_true] at hsel
  simp only [patForcesPrint, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hforce
  obtain ⟨⟨j, pat⟩, hmem, hj, hpat⟩ := hforce
  have := hsel.2 (j, pat) hmem
  subst hj
  cases pat <;> cases v <;> aesop (add norm simp [Templates.patternAt, Templates.ArgPat.holds,
    argPrints], safe cases Decision)

/-- All the arguments of a readable node print, and the substitution captures every hole of
the row in its kind. -/
theorem printArgs_ok {sig : Signature Op} {fam : EffFam} {n : Nat} {out : RowOut} {daemon : Bool} :
    ∀ (args : List (ArgF Op (EffSelfCarrier Op))) (i : Nat),
    argsReadable sig fam n out daemon (args.map (ArgF.fold (readableAlg sig))) i = true →
    (∀ fam' (c : EffSelfCarrier Op fam') d, ArgF.child fam' c ∈ args → ReadableAt sig fam' c d →
      ∃ y : Out fam', cataFam (printAlg sig) fam' c d = .ok y) →
    ∃ τ, printArgs sig fam n out (args.map (ArgF.fold (printAlg sig))) i = .ok τ
  | [], _, _, _ => ⟨[], rfl⟩
  | v :: rest, i, hr, hchild => by
    simp only [List.map_cons, argsReadable, Bool.and_eq_true] at hr
    obtain ⟨x, hx, _⟩ := printArg_ok (daemon := daemon) (by rw [argSortOf_fold] at hr; exact hr.1)
      (fun fam' c hv hra => hchild fam' c _ (hv ▸ List.mem_cons_self) hra)
    obtain ⟨τ, hτ⟩ := printArgs_ok rest (i + 1) hr.2
      (fun fam' c d hm hra => hchild fam' c d (List.mem_cons_of_mem _ hm) hra)
    cases x with
    | none => exact ⟨τ, by simp only [List.map_cons, printArgs, argSortOf_fold, hx, hτ, ok_bind]⟩
    | some a =>
      exact ⟨(i, a) :: τ, by simp only [List.map_cons, printArgs, argSortOf_fold, hx, hτ, ok_bind]⟩

/-- The captures of a readable node's arguments have the kinds the row's holes ask for. -/
theorem kinds_of_printArgs {sig : Signature Op} {n : Nat} {row : Templates.Row}
    (hmem : row ∈ table) {ctor : String} {args : List (ArgF Op (EffSelfCarrier Op))}
    (hsel : row.selects row.fam ctor args = true)
    (hsorts : argSorts row.fam ctor = some (args.map argSortOf)) {daemon : Bool}
    (hr : argsReadable sig row.fam n row.out daemon (args.map (ArgF.fold (readableAlg sig))) 0 = true)
    (hchild : ∀ fam' (c : EffSelfCarrier Op fam') d, ArgF.child fam' c ∈ args →
      ReadableAt sig fam' c d → ∃ y : Out fam', cataFam (printAlg sig) fam' c d = .ok y)
    {τ : Subst} (hτ : printArgs sig row.fam n row.out (args.map (ArgF.fold (printAlg sig))) 0 = .ok τ) :
    Kinds τ (RowOut.holeKinds row.out) := by
  have hk := table_fact table_holeKinds hmem
  have hctor : row.ctor = ctor := (selects_fam_ctor hsel).2
  subst hctor
  simp only [rowHoleKinds, hsorts, List.all_eq_true] at hk
  obtain ⟨hprint, _⟩ := printArgs_lookup (args.map (ArgF.fold (printAlg sig))) 0 τ hτ
  intro p hp
  have hk := hk p hp
  cases hv : (args.map argSortOf)[p.1]? with
  | none => rw [hv] at hk; cases hk
  | some s =>
    rw [hv] at hk
    simp only [Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at hk
    rw [List.getElem?_map] at hv
    cases ha : args[p.1]? with
    | none => rw [ha] at hv; cases hv
    | some v =>
      rw [ha, Option.map_some, Option.some.injEq] at hv
      subst hv
      have hpr : argPrints v = true := by
        rcases hk.2 with h | h
        · exact argPrints_of_sortPrints v h
        · exact argPrints_of_forced hsel p.1 h v ha
      have hra := argsReadable_at (args.map (ArgF.fold (readableAlg sig))) 0 p.1
        (ArgF.fold (readableAlg sig) v) hr (by simp only [List.getElem?_map, ha, Option.map_some])
      rw [argSortOf_fold, Nat.zero_add] at hra
      obtain ⟨x, hx, hsome, _⟩ := printArg_ok (daemon := daemon) hra
        (fun fam' c hv hra' => hchild fam' c _ (hv ▸ List.mem_of_getElem? ha) hra')
      obtain ⟨a, rfl, hkind⟩ := hsome hpr
      have := hprint p.1 (ArgF.fold (printAlg sig) v)
        (by simp only [List.getElem?_map, ha, Option.map_some])
      rw [argSortOf_fold, Nat.zero_add, hx] at this
      refine ⟨a, (Except.ok.inj this).symm, ?_⟩
      rw [hk.1] at hkind
      exact Option.some.inj hkind


/-! ## The row call prints -/

theorem printRow_ok {row : Row} {n : Nat} {r : Term} (h : requestReadable row n r = true) :
    ∃ x, printRow row r = .ok x := by
  unfold printRow
  unfold requestReadable at h
  cases hs : row.shape <;> rw [hs] at h <;>
    aesop (add norm simp [printRowHead, printMethod, bind, Except.bind, Option.isSome_iff_exists])

/-! ## The node steps -/

section Node

variable {sig : Signature Op}

/-- What a readable node prints to: something; a statement, with the binders the domain
counted for it (the statement spine threads them). -/
def Prints (sig : Signature Op) : (fam : EffFam) → EffSelfCarrier Op fam → Nat → Nat → Prop
  | .stmt, st, n, d => ∃ s, cata_stmt (printAlg sig) st n = .ok (s, d)
  | fam, e, n, _ => ∃ x : Out fam, cataFam (printAlg sig) fam e n = .ok x

theorem Prints.exists {fam : EffFam} {e : EffSelfCarrier Op fam} {n d : Nat}
    (h : Prints sig fam e n d) : ∃ x : Out fam, cataFam (printAlg sig) fam e n = .ok x := by
  cases fam <;> simp only [Prints, cataFam] at h ⊢ <;> aesop

/-- The recursion a node needs: every child prints at every depth it is readable at. -/
def ChildrenPrint (sig : Signature Op) (fam : EffFam) (e : EffSelfCarrier Op fam) : Prop :=
  ∀ fam' (c : EffSelfCarrier Op fam') d k, ArgF.child fam' c ∈ (view fam e).2 →
    cataFam (readableAlg sig) fam' c d = some k → Prints sig fam' c d k

theorem ChildrenPrint.exists {fam : EffFam} {e : EffSelfCarrier Op fam} (ih : ChildrenPrint sig fam e)
    {fam' : EffFam} {c : EffSelfCarrier Op fam'} {d : Nat} (hm : ArgF.child fam' c ∈ (view fam e).2)
    (hr : ReadableAt sig fam' c d) : ∃ y : Out fam', cataFam (printAlg sig) fam' c d = .ok y := by
  obtain ⟨k, hk⟩ := hr
  exact (ih fam' c d k hm hk).exists

/-- A readable node of an expression family prints. -/
theorem print_node {fam : EffFam} (hfam : fam = .eff ∨ fam = .action ∨ fam = .layer)
    {e : EffSelfCarrier Op fam} {n : Nat} (hr : ReadableAt sig fam e n)
    (ih : ChildrenPrint sig fam e) : ∃ x : Out fam, cataFam (printAlg sig) fam e n = .ok x := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view fam e = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build fam ctor args = some e := by
    have := build_view fam e; rwa [hview] at this
  have hsorts : argSorts fam ctor = some (args.map argSortOf) := by
    have := argSorts_view fam e; rwa [hview] at this
  have ih' : ∀ fam' (c : EffSelfCarrier Op fam') d, ArgF.child fam' c ∈ args →
      ReadableAt sig fam' c d → ∃ y : Out fam', cataFam (printAlg sig) fam' c d = .ok y :=
    fun fam' c d hm hra => ih.exists (by rw [hview]; exact hm) hra
  obtain ⟨d, hd⟩ := hr
  have hdom : domLayer.rowDom sig fam ctor (args.map (ArgF.fold (readableAlg sig))) n = some d := by
    have := cata_build (domLayer sig) fam ctor args e hbuild
    rw [show readableAlg sig = EffAlgebra.ofLayer (domLayer sig) from rfl, this] at hd
    rcases hfam with rfl | rfl | rfl <;> exact hd
  obtain ⟨row, hfind, hcase⟩ := rowDom_inv hdom
  have hsel : row.selects fam ctor args = true := by
    have := List.find?_some hfind; rwa [selects_fold] at this
  obtain ⟨hfamrow, hctor⟩ := selects_fam_ctor hsel
  have hmem := List.mem_of_find?_eq_some hfind
  have hfind' : (table.find? fun r => r.selects fam ctor (args.map (ArgF.fold (printAlg sig)))) =
      some row := by
    rw [find?_selects_fold (printAlg sig) (readableAlg sig)]; exact hfind
  have hcata : cataFam (printAlg sig) fam e =
      tableLayer sig fam ctor (args.map (ArgF.fold (printAlg sig))) :=
    cata_build (tableLayer sig) fam ctor args e hbuild
  rw [hcata]
  rcases hcase with ⟨t, hout, hr'⟩ | ⟨op, r, hout, hargs, hd', hreq⟩
  · -- a skeleton row: the arguments print and the skeleton instantiates
    obtain ⟨τ, hτ⟩ := printArgs_ok args 0 hr' ih'
    have hkinds : Kinds τ (RowOut.holeKinds row.out) := by
      subst hctor
      refine kinds_of_printArgs (n := n) (daemon := rowDaemon row) hmem (hfamrow ▸ hsel)
        (hfamrow ▸ hsorts) ?_ ih' ?_
      · rw [hfamrow, hout]; exact hr'
      · rw [hfamrow, hout]; exact hτ
    rw [hout] at hkinds
    obtain ⟨x, hinst⟩ := inst_of_kinds n τ t hkinds
    rcases hfam with rfl | rfl | rfl <;>
      exact ⟨x, by simp only [tableLayer, tableLayer.rowPrint, hfind', hout, hτ, ok_bind, hinst]⟩
  · -- the row call
    have hargs' := fold_eq_op_term (readableAlg sig) hargs
    subst hargs'
    obtain ⟨x, hx⟩ := printRow_ok hreq
    have hfind'' : (table.find? fun r' => r'.selects fam ctor
        ([.op op, .term r] : List (ArgF Op Carrier))) = some row := by
      simpa only [List.map_cons, List.map_nil, ArgF.fold] using hfind'
    rcases hfam with rfl | rfl | rfl <;>
      exact ⟨x, by simp only [tableLayer, tableLayer.rowPrint, List.map_cons, List.map_nil,
        ArgF.fold, hfind'', hout, hx]⟩

/-- A readable statement prints, with the binders the domain counted. -/
theorem print_stmt {st : Program.Stmt Op} {n d : Nat} (hd : cata_stmt (readableAlg sig) st n = some d)
    (ih : ChildrenPrint sig .stmt st) : ∃ s, cata_stmt (printAlg sig) st n = .ok (s, d) := by
  obtain ⟨ctor, args, hview⟩ : ∃ ctor args, view .stmt st = (ctor, args) := ⟨_, _, rfl⟩
  have hbuild : build .stmt ctor args = some st := by
    have := build_view .stmt st; rwa [hview] at this
  have hsorts : argSorts .stmt ctor = some (args.map argSortOf) := by
    have := argSorts_view .stmt st; rwa [hview] at this
  have ih' : ∀ fam' (c : EffSelfCarrier Op fam') d, ArgF.child fam' c ∈ args →
      ReadableAt sig fam' c d → ∃ y : Out fam', cataFam (printAlg sig) fam' c d = .ok y :=
    fun fam' c d hm hra => ih.exists (by rw [hview]; exact hm) hra
  have hdom : domLayer sig .stmt ctor (args.map (ArgF.fold (readableAlg sig))) n = some d := by
    have := cata_build (domLayer sig) .stmt ctor args st hbuild
    simp only [cataFam] at this
    rw [show readableAlg sig = EffAlgebra.ofLayer (domLayer sig) from rfl, this] at hd
    exact hd
  obtain ⟨row, t, hfind, hout, hr', rfl⟩ := stmtDom_inv hdom
  have hsel : row.selects .stmt ctor args = true := by
    have := List.find?_some hfind; rwa [selects_fold] at this
  obtain ⟨hfamrow, hctor⟩ := selects_fam_ctor hsel
  have hmem := List.mem_of_find?_eq_some hfind
  have hfind' : (table.find? fun r => r.selects .stmt ctor (args.map (ArgF.fold (printAlg sig)))) =
      some row := by
    rw [find?_selects_fold (printAlg sig) (readableAlg sig)]; exact hfind
  have hcata : cataFam (printAlg sig) .stmt st =
      tableLayer sig .stmt ctor (args.map (ArgF.fold (printAlg sig))) :=
    cata_build (tableLayer sig) .stmt ctor args st hbuild
  simp only [cataFam] at hcata
  rw [hcata]
  obtain ⟨τ, hτ⟩ := printArgs_ok args 0 hr' ih'
  have hkinds : Kinds τ (RowOut.holeKinds row.out) := by
    subst hctor
    refine kinds_of_printArgs (n := n) (daemon := rowDaemon row) hmem (hfamrow ▸ hsel)
      (hfamrow ▸ hsorts) ?_ ih' ?_
    · rw [hfamrow, hout]; exact hr'
    · rw [hfamrow, hout]; exact hτ
  rw [hout] at hkinds
  obtain ⟨s, hinst⟩ := instStmt_of_kinds n τ t hkinds
  refine ⟨s, ?_⟩
  obtain ⟨rfam, rctor, rfixed, rout⟩ := row
  simp only at hout hfamrow hctor
  subst hout hfamrow hctor
  simp only [tableLayer, hfind', hτ, ok_bind, hinst]


/-- The spines print item by item. -/
theorem print_effs {e : Effs Op} {n : Nat} (hr : ReadableAt sig .effs e n)
    (ih : ChildrenPrint sig .effs e) : ∃ x : Out .effs, cataFam (printAlg sig) .effs e n = .ok x := by
  cases e with
  | nil => exact ⟨[], rfl⟩
  | cons e es =>
    obtain ⟨d, hd⟩ := hr
    simp only [cataFam, dom_effs_cons, Option.bind_eq_some_iff] at hd
    obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
    obtain ⟨y, hy⟩ := ih.exists (fam' := .eff) (c := e) (d := n) List.mem_cons_self ⟨d1, hd1⟩
    obtain ⟨ys, hys⟩ := ih.exists (fam' := .effs) (c := es) (d := n)
      (List.mem_cons_of_mem _ List.mem_cons_self) ⟨d2, hd2⟩
    simp only [cataFam] at hy hys ⊢
    exact ⟨y :: ys, by rw [cata_effs_cons, hy, hys]; rfl⟩

theorem print_layers {e : LayerTerms Op} {n : Nat} (hr : ReadableAt sig .layers e n)
    (ih : ChildrenPrint sig .layers e) :
    ∃ x : Out .layers, cataFam (printAlg sig) .layers e n = .ok x := by
  cases e with
  | nil => exact ⟨[], rfl⟩
  | cons l ls =>
    obtain ⟨d, hd⟩ := hr
    simp only [cataFam, dom_layers_cons, Option.bind_eq_some_iff] at hd
    obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
    obtain ⟨y, hy⟩ := ih.exists (fam' := .layer) (c := l) (d := n) List.mem_cons_self ⟨d1, hd1⟩
    obtain ⟨ys, hys⟩ := ih.exists (fam' := .layers) (c := ls) (d := n)
      (List.mem_cons_of_mem _ List.mem_cons_self) ⟨d2, hd2⟩
    simp only [cataFam] at hy hys ⊢
    exact ⟨y :: ys, by rw [cata_layers_cons, hy, hys]; rfl⟩

theorem print_stmts {e : Stmts Op} {n : Nat} (hr : ReadableAt sig .stmts e n)
    (ih : ChildrenPrint sig .stmts e) :
    ∃ x : Out .stmts, cataFam (printAlg sig) .stmts e n = .ok x := by
  cases e with
  | nil => exact ⟨[], rfl⟩
  | cons st rest =>
    obtain ⟨d, hd⟩ := hr
    simp only [cataFam, dom_stmts_cons, Option.bind_eq_some_iff] at hd
    obtain ⟨d1, hd1, d2, hd2, _⟩ := hd
    obtain ⟨s, hs⟩ := ih .stmt st n d1 List.mem_cons_self hd1
    obtain ⟨ys, hys⟩ := ih.exists (fam' := .stmts) (c := rest) (d := n + d1)
      (List.mem_cons_of_mem _ List.mem_cons_self) ⟨d2, hd2⟩
    simp only [cataFam] at hys ⊢
    exact ⟨s :: ys, by rw [cata_stmts_cons, hs]; simp only [ok_bind]; rw [hys]; rfl⟩

end Node

/-! ## The theorem: induction on the size -/

section Theorem

variable {sig : Signature Op}

/-- Every readable node of size at most `m` prints. -/
theorem prints_upTo (m : Nat) : ∀ (fam : EffFam) (e : EffSelfCarrier Op fam) (n k : Nat),
    cataFam sizeAlg fam e ≤ m → cataFam (readableAlg sig) fam e n = some k → Prints sig fam e n k := by
  induction m using Nat.strongRecOn with
  | _ m ih =>
    intro fam e n k hsize hr
    have children : ChildrenPrint sig fam e := fun fam' c d k' hm hk =>
      ih (cataFam sizeAlg fam' c) (by have := size_child_lt fam e fam' c hm; omega) fam' c d k'
        (Nat.le_refl _) hk
    cases fam with
    | eff => exact print_node (.inl rfl) ⟨k, hr⟩ children
    | action => exact print_node (.inr (.inl rfl)) ⟨k, hr⟩ children
    | layer => exact print_node (.inr (.inr rfl)) ⟨k, hr⟩ children
    | stmt => exact print_stmt hr children
    | effs => exact print_effs ⟨k, hr⟩ children
    | layers => exact print_layers ⟨k, hr⟩ children
    | stmts => exact print_stmts ⟨k, hr⟩ children

/-- **A readable program prints.** -/
theorem print_of_readable {n : Nat} {e : Eff Op} (hr : Readable sig n e = true) :
    ∃ x, print sig n e = .ok x := by
  obtain ⟨k, hk⟩ := Option.isSome_iff_exists.mp hr
  exact prints_upTo (cataFam sizeAlg .eff e) .eff e n k (Nat.le_refl _) hk

/-- A readable layer prints. -/
theorem printLayer_of_readable {l : LayerTerm Op} (hr : ReadableAt sig .layer l 0) :
    ∃ x, printLayer sig l = .ok x := by
  obtain ⟨k, hk⟩ := hr
  exact prints_upTo (cataFam sizeAlg .layer l) .layer l 0 k (Nat.le_refl _) hk

/-- The round trip on the readable domain: a readable program prints, and what it prints
reads back to it. -/
theorem roundTrip_of_readable {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op} (hr : Readable sig n e = true) :
    roundTrip sig spell n e = .ok e := by
  obtain ⟨x, hx⟩ := print_of_readable hr
  simp only [roundTrip, hx, read_print hl hr hx]

/-- The executed check of the round trip holds on the readable domain. -/
theorem readable_of_Readable [DecidableEq Op] {spell : String → List String → Option Op}
    (hl : LawfulSpelling sig spell) {n : Nat} {e : Eff Op} (hr : Readable sig n e = true) :
    readable sig spell n e = true := by
  simp only [readable, roundTrip_of_readable hl hr, decide_true]

end Theorem

end Effect4.Program
