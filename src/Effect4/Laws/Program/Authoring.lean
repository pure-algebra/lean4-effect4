import Effect4.Program.Scoped
import Effect4.Program.Binders
import Effect4.Program.Authoring
import Effect4.Laws.Program.Authoring.Tactic
import Effect4.Laws.Auto.Inversion

/-!
# Laws.Program.Authoring — scope safety of the authoring surface

A source is *scoped* when every tree it elaborates is scoped at the depth of the scope it
was elaborated in: `Eff.scopedAt`, the binder table read as an algebra on `Nat → Bool`
(`Program/Scoped.lean`). Every lift preserves it, one lemma per lift generated from the same
table (`Laws/Program/Authoring/Lifts.lean`); the hand-written sugar's lemmas are
`Laws/Program/Authoring/Sugar.lean`. This module holds what those depend on: the predicates
(structures, so a lemma of one carrier never unifies against a goal of another), the base
(a variable resolves below the depth, a literal is closed, an atom's arguments are its
own), the spines, and the membership lemmas the lists and options need. The tactic
`authoring_scoped` (`Authoring/Tactic.lean`, meta code inside the gate's implementation
boundary) discharges the predicate for any program built from the lifts by reading the head
of each goal and applying the lemma named after it.

`Node.scopedAt_child` is the agreement between the table's two projections: a child of a
scoped node is scoped at the level `Node.childLevel` assigns it.

Consequence: a program that elaborates was scope-safe by construction, `elaborate_scoped`
(`Sugar.lean`), so a wrong lift fails a proof rather than a program.
-/

set_option autoImplicit false

namespace Effect4.Program.Authoring

open Effect4.Program

/-! ## The predicates -/

/-- Every term the source elaborates has its variables below the scope's depth. -/
structure TermSrc.Scoped (t : TermSrc) : Prop where
  holds : ∀ env p x, t env p = .ok x → Term.scoped env.names.length x = true

/-- Every program the source elaborates is scoped at the scope's depth. -/
structure Src.Scoped {Op : Type} (s : Src Op) : Prop where
  holds : ∀ env p e, s env p = .ok e → Eff.scopedAt env.names.length e = true

structure CauseSrc.Scoped (c : CauseSrc) : Prop where
  holds : ∀ env p x, c env p = .ok x → CauseTerm.scoped env.names.length x = true

structure ActionSrc.Scoped {Op : Type} (a : ActionSrc Op) : Prop where
  holds : ∀ env p x, a env p = .ok x → ActionTerm.scopedAt env.names.length x = true

/-- A layer is closed: its bodies are checked at level `0`, whatever the scope. -/
structure LayerSrc.Scoped {Op : Type} (l : LayerSrc Op) : Prop where
  holds : ∀ env p x, l env p = .ok x → LayerTerm.scoped x = true

/-! ## The two facts every lift proof uses -/

/-- A successful `do` step: the first action succeeded with some value the rest consumed. -/
theorem bind_ok {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  aesop

@[simp] theorem Env.push_length (env : Env) (xs : List String) :
    (env.push xs).names.length = env.names.length + xs.length := by
  simp [Env.push]

@[simp] theorem Env.closed_length (env : Env) : env.closed.names.length = 0 := rfl

/-! ## The base: a variable resolves below the scope's depth -/

theorem Names.resolve_go_lt (names : List String) (x : String) :
    ∀ (k : Nat) (acc : Option Nat), (∀ i, acc = some i → i < k) →
      ∀ i, Names.resolve.go x names k acc = some i → i < k + names.length := by
  induction names with
  | nil => intro k acc hacc i h; simp [Names.resolve.go] at h; simpa using hacc i h
  | cons y ys ih =>
    intro k acc hacc i h
    simp only [Names.resolve.go] at h
    have := ih (k + 1) (if y = x then some k else acc) (by
      intro j hj
      split at hj
      · cases hj; omega
      · exact Nat.lt_succ_of_lt (hacc j hj)) i h
    simp only [List.length_cons]; omega

/-- The nearest binder of a name is a level of the scope. -/
theorem Names.resolve_lt {names : List String} {x : String} {i : Nat}
    (h : Names.resolve names x = some i) : i < names.length := by
  have := Names.resolve_go_lt names x 0 none (by intro j hj; cases hj) i h
  simpa using this

/-- A name the surface minted for itself resolves below the scope's depth, like any other. -/
theorem minted_scoped (x : String) : (minted x).Scoped := by
  refine ⟨fun env p t h => ?_⟩
  unfold minted at h
  split at h
  · rename_i i hi; cases h; simpa [Term.scoped] using Names.resolve_lt hi
  · cases h

theorem var_scoped (x : String) : (var x).Scoped := by
  refine ⟨fun env p t h => ?_⟩
  unfold var at h
  split at h
  · cases h
  · exact (minted_scoped x).holds env p t h

theorem lit_scoped (v : Lit) : (lit v).Scoped := by
  refine ⟨fun env p t h => ?_⟩; cases h; rfl

theorem nat_scoped (n : Nat) : (nat n).Scoped := lit_scoped _
theorem str_scoped (s : String) : (str s).Scoped := lit_scoped _
theorem bool_scoped (b : Bool) : (bool b).Scoped := lit_scoped _
theorem unit_scoped : unit.Scoped := lit_scoped _

theorem termsOfList_scoped {n : Nat} {ts : List Term} (h : ∀ t ∈ ts, Term.scoped n t = true) :
    Terms.scoped n (termsOfList ts) = true := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    simp only [termsOfList, Terms.scoped, Bool.and_eq_true]
    exact ⟨h t (by simp), ih fun u hu => h u (by simp [hu])⟩

theorem mapM_ok_mem {α β ε : Type} {f : α → Except ε β} :
    ∀ {l : List α} {ys : List β}, l.mapM f = .ok ys → ∀ y ∈ ys, ∃ a ∈ l, f a = .ok y := by
  intro l
  induction l with
  | nil => intro ys h y hy; cases h; simp at hy
  | cons a as ih =>
    intro ys h y hy
    simp only [List.mapM_cons] at h
    obtain ⟨b, hb, h⟩ := bind_ok h
    obtain ⟨bs, hbs, h⟩ := bind_ok h
    cases h
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact ⟨a, by simp, hb⟩
    · obtain ⟨a', ha', hf⟩ := ih hbs y hy
      exact ⟨a', by simp [ha'], hf⟩

/-- An atom's arguments share its scope. -/
theorem app_scoped (atom : String) {args : List TermSrc} (h : ∀ a ∈ args, a.Scoped) :
    (app atom args).Scoped := by
  refine ⟨fun env p t hx => ?_⟩
  unfold app at hx
  obtain ⟨vs, hvs, hx⟩ := bind_ok hx
  cases hx
  simp only [Term.scoped]
  apply termsOfList_scoped
  intro v hv
  obtain ⟨a, ha, hfa⟩ := mapM_ok_mem hvs v hv
  exact (h a ha).holds env p v hfa

/-- A declared layer by name is a reference, and a reference is closed. -/
theorem Layer.ref_scoped {Op : Type} (name : String) : (Layer.ref name : LayerSrc Op).Scoped := by
  refine ⟨fun env p x h => ?_⟩
  unfold Layer.ref at h
  split at h <;> cases h
  rfl

/-! ## Spines and options -/

theorem elabEffs_scoped {Op : Type} {l : List (Src Op)} (h : ∀ s ∈ l, s.Scoped) :
    ∀ {env : Env} {spine : List Nat} {es : Effs Op}, elabEffs l env spine = .ok es →
      Effs.scopedAt env.names.length es = true := by
  induction l with
  | nil => intro env spine es hx; cases hx; rfl
  | cons s ss ih =>
    intro env spine es hx
    simp only [elabEffs] at hx
    obtain ⟨x, hx0, hx⟩ := bind_ok hx
    obtain ⟨xs, hxs, hx⟩ := bind_ok hx
    cases hx
    simp only [Effs.scopedAt_cons, Bool.and_eq_true]
    exact ⟨(h s (by simp)).holds env _ x hx0, ih (fun t ht => h t (by simp [ht])) hxs⟩

theorem elabLayers_scoped {Op : Type} {l : List (LayerSrc Op)} (h : ∀ s ∈ l, s.Scoped) :
    ∀ {env : Env} {spine : List Nat} {ls : LayerTerms Op}, elabLayers l env spine = .ok ls →
      LayerTerms.scoped ls = true := by
  induction l with
  | nil => intro env spine ls hx; cases hx; rfl
  | cons s ss ih =>
    intro env spine ls hx
    simp only [elabLayers] at hx
    obtain ⟨x, hx0, hx⟩ := bind_ok hx
    obtain ⟨xs, hxs, hx⟩ := bind_ok hx
    cases hx
    simp only [LayerTerms.scoped_cons, Bool.and_eq_true]
    exact ⟨(h s (by simp)).holds env _ x hx0, ih (fun t ht => h t (by simp [ht])) hxs⟩

theorem elabOption_scoped {o : Option TermSrc} (h : ∀ t ∈ o, t.Scoped) :
    ∀ {env : Env} {p : List Nat} {x : Option Term}, elabOption o env p = .ok x →
      x.all (·.scoped env.names.length) = true := by
  intro env p x hx
  cases o with
  | none => cases hx; rfl
  | some t =>
    simp only [elabOption] at hx
    obtain ⟨v, hv, hx⟩ := bind_ok hx
    cases hx
    simpa using (h t (by simp)).holds env p v hv

/-! ## Membership, one pair per carrier that a lift takes a list or an option of -/

theorem TermSrc.Scoped_cons {a : TermSrc} {l : List TermSrc} (h : a.Scoped)
    (hl : ∀ x ∈ l, x.Scoped) : ∀ x ∈ a :: l, x.Scoped := by
  intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact h; exact hl x hx
theorem TermSrc.Scoped_nil : ∀ x ∈ ([] : List TermSrc), x.Scoped := by
  intro x hx; simp at hx
theorem TermSrc.Scoped_some {a : TermSrc} (h : a.Scoped) : ∀ x ∈ some a, x.Scoped := by
  intro x hx; cases hx; exact h
theorem TermSrc.Scoped_none : ∀ x ∈ (none : Option TermSrc), x.Scoped := by
  intro x hx; cases hx

theorem Src.Scoped_cons {Op : Type} {a : Src Op} {l : List (Src Op)} (h : a.Scoped)
    (hl : ∀ x ∈ l, x.Scoped) : ∀ x ∈ a :: l, x.Scoped := by
  intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact h; exact hl x hx
theorem Src.Scoped_nil {Op : Type} : ∀ x ∈ ([] : List (Src Op)), x.Scoped := by
  intro x hx; simp at hx

theorem LayerSrc.Scoped_cons {Op : Type} {a : LayerSrc Op} {l : List (LayerSrc Op)}
    (h : a.Scoped) (hl : ∀ x ∈ l, x.Scoped) : ∀ x ∈ a :: l, x.Scoped := by
  intro x hx; simp only [List.mem_cons] at hx; rcases hx with rfl | hx; exact h; exact hl x hx
theorem LayerSrc.Scoped_nil {Op : Type} : ∀ x ∈ ([] : List (LayerSrc Op)), x.Scoped := by
  intro x hx; simp at hx

/-! ## The table and the algebra agree -/

/-- The one head-dependent row, as the table spells it and as the algebra spells it. -/
theorem Node.childLevel_stmts_cons {Op : Type} (n : Nat) (h : Stmt Op) (t : Stmts Op) :
    Node.childLevel n (.stmts (.cons h t)) 1 = if h.bindsNext then n + 1 else n := by
  cases h <;> rfl

/-- A child of a scoped node is scoped at the level the binder table assigns it: the two
projections of `tools/Effect4Gen/binders.json`, `Node.childLevel` and `scopedAlgebra`, agree
at every child of every constructor. -/
theorem Node.scopedAt_child {Op : Type} {n : Nat} {node c : Node Op} {i : Nat}
    (hs : Node.scopedAt n node = true) (hc : Node.child node i = some c) :
    Node.scopedAt (Node.childLevel n node i) c = true := by
  unfold Node.child at hc
  split at hc <;> cases hc <;> (try simp only [Node.childLevel_stmts_cons]) <;>
    (try cases ‹Decision›) <;>
    simp_all [Node.scopedAt, Node.childLevel, Node.binders, Node.closedChild]

end Effect4.Program.Authoring
