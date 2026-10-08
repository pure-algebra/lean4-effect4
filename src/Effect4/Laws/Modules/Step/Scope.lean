import Effect4.Modules.Step
import Effect4.Laws.Program.Authoring
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Program.Authoring.Ascribe

/-!
# Scope of module steps

These helpers serve `operation-data-scoped`, the `initial-algebras-folds` property under R4.
Their consumer is `Step.scoped`, used by module operation builders before authoring admission.
Scope alone establishes neither typing nor progress, and leaves the host boundary unchanged.
-/

namespace Effect4.Modules
open Effect4.Program Effect4.Program.Authoring

mutual
/-- Inserting one environment slot preserves the scope of a term. -/
theorem weaken_scoped (t : Term) (n cut : Nat) (h : t.scoped n = true) :
    (t.weaken cut).scoped (n + 1) = true := by
  cases t with
  | var i =>
    have hi : i < n := of_decide_eq_true h
    change decide (Var.weaken cut i < n + 1) = true
    simp only [Var.weaken]
    split
    · exact decide_eq_true (Nat.lt_succ_of_lt hi)
    · exact decide_eq_true (Nat.add_lt_add_right hi 1)
  | lit v => rfl
  | app a xs => exact weaken_terms_scoped xs n cut h
  | record fs names xs => exact weaken_terms_scoped xs n cut h
  | field m t name => exact weaken_scoped t n cut h
  | recordSet t name v =>
    simp only [Term.scoped, Bool.and_eq_true] at h
    simp only [Term.weaken, Term.scoped, weaken_scoped t n cut h.1,
      weaken_scoped v n cut h.2, Bool.and_self]
  | tupleAt t i => exact weaken_scoped t n cut h
  | fold ty xs init body =>
    simp only [Term.scoped, Bool.and_eq_true] at h
    change ((_ && _) && _) = true
    have hb := weaken_scoped body (n + 2) cut h.2
    have hn : n + 1 + 2 = n + 2 + 1 := by omega
    simp only [hn, weaken_scoped xs n cut h.1.1,
      weaken_scoped init n cut h.1.2, hb, Bool.and_self]

/-- Inserting one environment slot preserves the scope of term arguments. -/
theorem weaken_terms_scoped (ts : Terms) (n cut : Nat) (h : ts.scoped n = true) :
    (ts.weaken cut).scoped (n + 1) = true := by
  cases ts with
  | nil => rfl
  | cons t ts =>
    simp only [Terms.scoped, Bool.and_eq_true] at h
    simp only [Terms.weaken, Terms.scoped, weaken_scoped t n cut h.1,
      weaken_terms_scoped ts n cut h.2, Bool.and_self]
end

/-- Scope of one source resolution at a fixed caller scope. -/
def SourceScopedAt (s : TermSrc) (env : Env) (path : List Nat) : Prop :=
  ∀ tree, s env path = .ok tree → tree.scoped env.names.length = true

theorem app_scopedAt (atom : String) {args : List TermSrc} {env : Env} {path : List Nat}
    (h : ∀ a ∈ args, SourceScopedAt a env path) : SourceScopedAt (app atom args) env path := by
  intro tree accepted
  unfold app at accepted
  obtain ⟨vs, hvs, accepted⟩ := bind_ok accepted
  cases accepted
  apply termsOfList_scoped
  intro v member
  obtain ⟨a, member, ha⟩ := mapM_ok_mem hvs v member
  exact h a member v ha

theorem field_scopedAt {target : TermSrc} {env : Env} {path : List Nat}
    (h : SourceScopedAt target env path) (name : String) :
    SourceScopedAt (field target name) env path := by
  intro tree accepted
  unfold field at accepted
  obtain ⟨v, hv, accepted⟩ := bind_ok accepted
  cases accepted
  exact h v hv

theorem record_scopedAt (fs : List (String × Bool × Ty)) {present : List (String × TermSrc)}
    {env : Env} {path : List Nat} (h : ∀ x ∈ present, SourceScopedAt x.2 env path) :
    SourceScopedAt (record fs present) env path := by
  intro tree accepted
  unfold record at accepted
  obtain ⟨vs, hvs, accepted⟩ := bind_ok accepted
  cases accepted
  apply termsOfList_scoped
  intro v member
  obtain ⟨x, member, hx⟩ := mapM_ok_mem hvs v member
  exact h x member v hx

theorem recordSet_scopedAt {target value : TermSrc} {env : Env} {path : List Nat}
    (h : SourceScopedAt target env path) (hv : SourceScopedAt value env path) (name : String) :
    SourceScopedAt (recordSet target name value) env path := by
  intro tree accepted
  unfold recordSet at accepted
  obtain ⟨v, htarget, accepted⟩ := bind_ok accepted
  obtain ⟨w, hvalue, accepted⟩ := bind_ok accepted
  cases accepted
  simp only [Term.scoped, Bool.and_eq_true]
  exact ⟨h v htarget, hv w hvalue⟩



namespace Step
mutual
/-- Translation resolves only variables within the caller scope. -/
theorem scopedAt : ∀ {Γ : List Ty} {t : Ty} (e : Step Γ t)
    {src : {u : Ty} → Input Γ u → TermSrc} {env : Env} {path : List Nat},
    (∀ {u : Ty} (x : Input Γ u), SourceScopedAt (src x) env path) →
    SourceScopedAt (e.term src) env path
  | _, _, .tuple (ts := ts) xs, src, env, path, h => by
    change SourceScopedAt (app "tuple" (ItemResults.map (fun {_} x => x src) ts (cataItems termAlg xs))) env path
    exact app_scopedAt _ (items_scopedAt xs h)
  | _, _, .var x, _, _, _, h => h x
  | _, _, .bool b, _, env, path, _ => bool_scoped b |>.holds env path
  | _, _, .nat n, _, env, path, _ => nat_scoped n |>.holds env path
  | _, _, .unit, _, env, path, _ => unit_scoped.holds env path
  | _, _, .not a, src, env, path, h => by
    change SourceScopedAt (app "not" [a.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact scopedAt a h
  | _, _, .isZero a, src, env, path, h => by
    change SourceScopedAt (app "isZero" [a.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact scopedAt a h
  | _, _, .fst a, src, env, path, h => by
    change SourceScopedAt (app "fst" [a.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact scopedAt a h
  | _, _, .snd a, src, env, path, h => by
    change SourceScopedAt (app "snd" [a.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact scopedAt a h
  | _, _, .some a, src, env, path, h => by
    change SourceScopedAt (app "some" [a.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact scopedAt a h
  | _, _, .len a, src, env, path, h => by
    change SourceScopedAt (app "length" [a.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact scopedAt a h
  | _, _, .and a b, src, env, path, h => by
    change SourceScopedAt (app "and" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .or a b, src, env, path, h => by
    change SourceScopedAt (app "or" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .add a b, src, env, path, h => by
    change SourceScopedAt (app "add" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .sub a b, src, env, path, h => by
    change SourceScopedAt (app "sub" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .lt a b, src, env, path, h => by
    change SourceScopedAt (app "lt" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .eq a b, src, env, path, h => by
    change SourceScopedAt (app "eq" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .pair a b, src, env, path, h => by
    change SourceScopedAt (app "pair" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h

  | _, _, .append a b, src, env, path, h => by
    change SourceScopedAt (app "append" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .take a b, src, env, path, h => by
    change SourceScopedAt (app "take" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .drop a b, src, env, path, h => by
    change SourceScopedAt (app "drop" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .getOrElse a b, src, env, path, h => by
    change SourceScopedAt (app "getOrElse" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .cons a b, src, env, path, h => by
    change SourceScopedAt (app "cons" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .sameDeferred a b, src, env, path, h => by
    change SourceScopedAt (app "sameHandle" [a.term src, b.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
  | _, _, .ite a b c, src, env, path, h => by
    change SourceScopedAt (app "ite" [a.term src, b.term src, c.term src]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl
    · exact scopedAt a h
    · exact scopedAt b h
    · exact scopedAt c h

  | _, _, .get r f, src, _, _, h => field_scopedAt (scopedAt r h) f.name
  | _, _, .set r f v, src, _, _, h => recordSet_scopedAt (scopedAt r h) (scopedAt v h) f.name
  | _, _, .emptyLike a, src, env, path, h => by
    change SourceScopedAt (app "take" [a.term src, Authoring.nat 0]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact (nat_scoped 0).holds env path
  | _, _, .head a, src, env, path, h => by
    change SourceScopedAt (app "get" [a.term src, Authoring.nat 0]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · exact (nat_scoped 0).holds env path
  | _, _, .snoc a b, src, env, path, h => by
    change SourceScopedAt (app "append" [a.term src, app "cons" [b.term src, nilT]]) env path
    apply app_scopedAt
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact scopedAt a h
    · apply app_scopedAt
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl
      · exact scopedAt b h
      · exact (app_scoped "nil" (by intro a ha; cases ha)).holds env path
  | _, _, .record fields, src, _, _, h => record_scopedAt _ (fields_scopedAt fields h)
  | _, .list t, .nil, _, env, path, _ => by
    exact (Effect4.Program.Authoring.ascribe_scoped (.list _)
      (app_scoped "nil" (by intro a ha; cases ha))).holds env path
  | _, .option t, .none, _, env, path, _ => by
    exact (Effect4.Program.Authoring.ascribe_scoped (.option _)
      (app_scoped "none" (by intro a ha; cases ha))).holds env path
  | Γ, _, .fold (acc := acc) (item := item) xs init body, src, env, path, h => by
    intro tree accepted
    change (do
      let l ← xs.term src env path
      let i ← init.term src env path
      let b ← body.term (foldSources src env path)
        (env.push [env.mint "acc", env.mint "item"]) path
      Except.ok (Term.fold Option.none l i b)) = .ok tree at accepted
    obtain ⟨l, hl, accepted⟩ := bind_ok accepted
    obtain ⟨i, hi, accepted⟩ := bind_ok accepted
    obtain ⟨b, hb, accepted⟩ := bind_ok accepted
    cases accepted
    have inputs : ∀ {u : Ty} (x : Input (acc :: item :: Γ) u),
        SourceScopedAt (foldSources src env path x)
          (env.push [env.mint "acc", env.mint "item"]) path := by
      intro u x tree accepted
      cases x with
      | here =>
        cases accepted
        simp only [Term.scoped, Env.push_length, List.length_cons, List.length_nil]
        apply decide_eq_true
        exact Nat.lt_add_of_pos_right (by decide)
      | there _ x =>
        cases x with
        | here =>
          cases accepted
          simp only [Term.scoped, Env.push_length, List.length_cons, List.length_nil]
          apply decide_eq_true
          exact Nat.lt_succ_self _
        | there _ x =>
          change (do
            let t ← src x env path
            Except.ok (t.weaken env.names.length |>.weaken (env.names.length + 1))) = .ok tree at accepted
          obtain ⟨t, ht, accepted⟩ := bind_ok accepted
          cases accepted
          have hs := weaken_scoped (t.weaken env.names.length) (env.names.length + 1)
            (env.names.length + 1) (weaken_scoped t env.names.length env.names.length (h x t ht))
          simpa only [Env.push_length, List.length_cons, List.length_nil, Nat.add_assoc] using hs
    have bodyScope := scopedAt body inputs b hb
    simp only [Term.scoped, Bool.and_eq_true]
    refine ⟨⟨scopedAt xs h l hl, scopedAt init h i hi⟩, ?_⟩
    simpa only [Env.push_length, List.length_cons, List.length_nil] using bodyScope

/-- Each record child retains the original caller scope. -/
theorem fields_scopedAt : ∀ {Γ : List Ty} {fs : List (String × Bool × Ty)} (fields : StepFields Γ fs)
    {src : {u : Ty} → Input Γ u → TermSrc} {env : Env} {path : List Nat},
    (∀ {u : Ty} (x : Input Γ u), SourceScopedAt (src x) env path) →
    ∀ entry ∈ FieldResults.map (fun name {_} value => (name, value src)) fs
      (cataFields termAlg fields), SourceScopedAt entry.2 env path
  | _, _, .nil, _, _, _, _, _, member => by cases member
  | _, _, .cons name value rest, src, env, path, h, entry, member => by
    change entry ∈ (name, value.term src) :: _ at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact scopedAt value h
    · exact fields_scopedAt rest h entry member

/-- Tuple children retain the original caller scope. -/
theorem items_scopedAt : ∀ {Γ : List Ty} {ts : List Ty} (xs : StepItems Γ ts)
    {src : {u : Ty} → Input Γ u → TermSrc} {env : Env} {path : List Nat},
    (∀ {u : Ty} (x : Input Γ u), SourceScopedAt (src x) env path) →
    ∀ source ∈ ItemResults.map (fun {_} x => x src) ts (cataItems termAlg xs),
      SourceScopedAt source env path
  | _, _, .nil, _, _, _, _, _, member => by cases member
  | _, _, .cons x xs, src, env, path, h, source, member => by
    change source ∈ x.term src :: _ at member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact scopedAt x h
    · exact items_scopedAt xs h source member
end

/-- A module step elaborates only scoped terms when its inputs do. -/
theorem «scoped» {Γ : List Ty} {t : Ty} (e : Step Γ t)
    {src : {u : Ty} → Input Γ u → TermSrc} (h : ∀ {u : Ty} (x : Input Γ u), (src x).Scoped) :
    (e.term src).Scoped := ⟨fun env path => scopedAt e (fun x => (h x).holds env path)⟩

end Step
namespace Input

/-- Choosing a source from scoped terms keeps its scope, including the closed fallback. -/
theorem getD_scoped : ∀ (sources : List TermSrc) (index : Nat),
    (∀ source ∈ sources, source.Scoped) → (sources.getD index Authoring.unit).Scoped
  | [], _, _ => unit_scoped
  | a :: _rest, 0, h => h a (List.mem_cons_self)
  | a :: rest, index + 1, h => getD_scoped rest index (fun source member =>
      h source (List.mem_cons_of_mem a member))

/-- Input resolution inherits the scope of the caller's source list. -/
theorem source_scoped {Γ : List Ty} {t : Ty} {sources : List TermSrc}
    (h : ∀ source ∈ sources, source.Scoped) (x : Input Γ t) :
    (Input.source sources x).Scoped := getD_scoped sources x.index h

end Input
end Effect4.Modules
