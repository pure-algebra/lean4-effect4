import Effect4.Program.TyCache
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Folds.TyCache — accepted cache answers are the fold

`Program/TyCache.lean` keeps the entries of a type fold and accepts them by local equations.
This module proves what a caller reads from an accepted cache:

- **Local agreement.** Every answer that accepted entries hold is `cata_ty` of the same layer at
  its own source (`check_agreement`). The proof is strong induction along the entries: each
  entry reads earlier entries only, and its local equation is the fold one layer down
  (`cata_ofLayer_view`).
- **The interface.** A query of an accepted cache (`CheckedCache.query_agrees`) and the answer
  that `answer` returns (`answer_agrees`) are that fold. At the identity layer `tyBuild` the
  answer is the queried type itself (`answer_reconstructs`).
- **The building fold's success.** `check` accepts the entries that `produce` builds at every
  type and every layer (`check_produce`), so `answer` answers the fold at every type
  (`answer_eq`). The proof is an induction on a type through its generated children
  (`kids_induction`, from `cata_ofLayer_inv`).

Placement (AGENTS.md, Trust): concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7).
The claim is `fold-cache-local-agreement`, with pointer `check_agreement`. The consumer is slice
D6 of `docs/research/2026-10-09-program-graph-design.md`, memoized folds, serving R14.

What the module does not establish:

- that an accepted answer carries over to a changed type: reuse after an edit needs its own law;
- a speed bound: `answer_eq` says what `answer` returns, not what it costs;
- a typing judgment, or an equality of answers at two different types;
- an inherited input of the layer: the source type is the whole key.
-/

set_option autoImplicit false

namespace Effect4.Program.TyCache

universe u

/-- The local equations as a proposition: each entry's children stand in the earlier entries, and
its answer is the local equation's right side at its own source. A step of
`fold-cache-local-agreement`. Its consumer is `valid_agreement`. -/
def Valid {R : Type u} (layer : TyCtor → List (TyArgF R) → R) : Entries R → Prop
  | [] => True
  | (t, r) :: previous => Valid layer previous ∧
      (tyKids t).all (fun child => (lookup previous child).isSome) = true ∧
      r = localValue layer previous t

/-- Entries that `check` accepts satisfy the local equations. A step of
`fold-cache-local-agreement`. Its consumer is `check_agreement`. -/
@[semantics "initial-algebras-folds"]
theorem check_valid {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R)
    (entries : Entries R) (accepted : check layer entries = true) : Valid layer entries := by
  induction entries with
  | nil => exact True.intro
  | cons entry previous ih =>
    cases entry with
    | mk t r =>
      simp only [check, Bool.and_eq_true, decide_eq_true_eq] at accepted
      exact ⟨ih accepted.1, accepted.2.1, accepted.2.2⟩

/-- Where every stored answer is the fold, `read` is the fold at every type: a stored answer by
the premise, a missing one by its fallback. A step of `fold-cache-local-agreement`. Its consumer
is `valid_agreement`. -/
@[semantics "initial-algebras-folds"]
theorem read_agrees {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (entries : Entries R)
    (answers : ∀ t r, lookup entries t = some r → r = cata_ty (TyAlgebra.ofLayer layer) t)
    (t : Ty) : read layer entries t = cata_ty (TyAlgebra.ofLayer layer) t := by
  unfold read
  cases found : lookup entries t with
  | none => rfl
  | some r => exact answers t r found

/-- Entries that satisfy the local equations hold the fold at each source, repeated children
and payloads included. The induction runs along the entries: each entry reads the entries before
it only. A step of `fold-cache-local-agreement`. Its consumer is `check_agreement`. -/
@[semantics "initial-algebras-folds"]
theorem valid_agreement {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (entries : Entries R)
    (valid : Valid layer entries) :
    ∀ t r, lookup entries t = some r → r = cata_ty (TyAlgebra.ofLayer layer) t := by
  induction entries with
  | nil =>
    intro t r found
    cases found
  | cons entry previous ih =>
    cases entry with
    | mk s value =>
      rcases valid with ⟨prior, _covered, equation⟩
      have previousAnswers := ih prior
      have total : read layer previous = cata_ty (TyAlgebra.ofLayer layer) :=
        funext (read_agrees layer previous previousAnswers)
      have head : value = cata_ty (TyAlgebra.ofLayer layer) s := by
        rw [equation, localValue, total]
        exact (cata_ofLayer_view layer s).symm
      intro t r found
      simp only [lookup] at found
      split at found
      next same =>
        have source : t = s := Ty.key_injective same
        have stored : value = r := Option.some.inj found
        rw [← stored, source]
        exact head
      next _ => exact previousAnswers t r found

/-- **Local agreement**: every answer that accepted entries hold is `cata_ty` of the same layer at
its own source. The pointer of the claim `fold-cache-local-agreement`. Its consumers are
`CheckedCache.query_agrees`, `answer_agrees` and slice D6's memoized folds. It says nothing of a
type that no entry holds, and nothing of speed. -/
@[semantics "initial-algebras-folds"]
theorem check_agreement {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R)
    (entries : Entries R) (accepted : check layer entries = true) (t : Ty) (r : R)
    (found : lookup entries t = some r) : r = cata_ty (TyAlgebra.ofLayer layer) t :=
  valid_agreement layer entries (check_valid layer entries accepted) t r found

/-- Every answer of an accepted cache is the fold of its layer at the queried type. A consumer of
`check_agreement`, for an author who keeps a cache and queries it. -/
@[semantics "initial-algebras-folds"]
theorem CheckedCache.query_agrees {R : Type u} [DecidableEq R]
    {layer : TyCtor → List (TyArgF R) → R} (cache : CheckedCache layer) (t : Ty) (r : R)
    (answered : cache.query t = some r) : r = cata_ty (TyAlgebra.ofLayer layer) t :=
  check_agreement layer cache.entries cache.accepted t r answered

/-- Every answer that `answer` returns is the fold of its layer at the requested type. A consumer
of `check_agreement`, for an author who asks one type's answer. -/
@[semantics "initial-algebras-folds"]
theorem answer_agrees {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R)
    (t : Ty) (r : R) (answered : answer layer t = some r) :
    r = cata_ty (TyAlgebra.ofLayer layer) t := by
  unfold answer at answered
  cases prepared : prepare layer t with
  | none =>
    simp only [prepared, Option.bind_none] at answered
    cases answered
  | some cache =>
    simp only [prepared, Option.bind_some] at answered
    exact cache.query_agrees t r answered

/-- The fold of the identity layer `tyBuild` is the identity: the generated identity algebra, not a
new match. A step of `fold-cache-local-agreement`. Its consumers are `reconstructs` and
`answer_reconstructs`. -/
@[semantics "initial-algebras-folds"]
theorem reconstruction_fold (t : Ty) : cata_ty (TyAlgebra.ofLayer tyBuild) t = t := by
  change cata_ty TyAlgebra.id t = t
  exact cata_id_ty t

/-- Accepted entries of the identity layer hold each source itself. A consumer of
`check_agreement`: the identity layer keeps names, flags and child order, which a count does
not. -/
@[semantics "initial-algebras-folds"]
theorem reconstructs (entries : Entries Ty) (accepted : check tyBuild entries = true)
    (t r : Ty) (found : lookup entries t = some r) : r = t :=
  (check_agreement tyBuild entries accepted t r found).trans (reconstruction_fold t)

/-- When `answer` at the identity layer answers, it returns the requested type itself. A consumer
of `answer_agrees`. -/
@[semantics "initial-algebras-folds"]
theorem answer_reconstructs (t r : Ty) (answered : answer tyBuild t = some r) : r = t :=
  (answer_agrees tyBuild t r answered).trans (reconstruction_fold t)

/-! ## The building fold's success -/

/-- The children of a node that `tyBuild` builds are children of its arguments. A step of
`fold-cache-local-agreement`. Its consumer is `kids_induction`. The case list is `tyBuild`'s own
(`fun_cases`): a tag whose arguments do not have its sorts builds `never`, which has no child. -/
@[semantics "initial-algebras-folds"]
theorem mem_tyKids_tyBuild (c : TyCtor) (args : List (TyArgF Ty)) (k : Ty) :
    k ∈ tyKids (tyBuild c args) → k ∈ args.flatMap TyArgF.kids := by
  fun_cases tyBuild c args <;> intro member <;>
    simp only [tyKids, tyArgs, List.flatMap_nil, List.not_mem_nil] at member <;> exact member

/-- Induction on a type through its generated children: a property that holds at a type whenever
it holds at each of its children (`tyKids`) holds at every type. It is the layer invariant
`cata_ofLayer_inv` at the identity layer. A step of `fold-cache-local-agreement`. Its consumer is
`produce_covered`. -/
@[semantics "initial-algebras-folds"]
theorem kids_induction {Q : Ty → Prop} (step : ∀ t, (∀ k ∈ tyKids t, Q k) → Q t) (t : Ty) :
    Q t := by
  have held := cata_ofLayer_inv tyBuild Q (fun c args below => step _ (fun k member => by
      obtain ⟨a, inArgs, inKids⟩ := List.mem_flatMap.mp (mem_tyKids_tyBuild c args k member)
      exact below a inArgs k inKids)) t
  rwa [reconstruction_fold] at held

/-- The building fold rebuilds its type: `Built.source` commutes with the identity layer. A step
of `fold-cache-local-agreement`. Its consumer is `produce_entries`. -/
@[semantics "initial-algebras-folds"]
theorem produce_source {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    (produce layer t).source = t :=
  (cata_fusion_ty (h := Built.source) (alg := TyAlgebra.ofLayer (producerLayer layer))
    (alg' := TyAlgebra.ofLayer tyBuild) {} t).trans (reconstruction_fold t)

/-- The building fold's answer is the fold of the layer: `Built.value` commutes with the layer.
A step of `fold-cache-local-agreement`. Its consumer is `produce_entries`. -/
@[semantics "initial-algebras-folds"]
theorem produce_value {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    (produce layer t).value = cata_ty (TyAlgebra.ofLayer layer) t :=
  cata_fusion_ty (h := Built.value) (alg := TyAlgebra.ofLayer (producerLayer layer))
    (alg' := TyAlgebra.ofLayer layer) {} t

/-- The building fold one layer down: the type's own entry with the fold's answer, then its
children's entries in order. A step of `fold-cache-local-agreement`. Its consumers are
`produce_covered` and `answer_eq`. -/
@[semantics "initial-algebras-folds"]
theorem produce_entries {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    (produce layer t).entries =
      (t, cata_ty (TyAlgebra.ofLayer layer) t) ::
        (tyKids t).flatMap (fun k => (produce layer k).entries) := by
  have view : produce layer t =
      producerLayer layer (tyCtor t) ((tyArgs t).map (TyArgF.map (produce layer))) :=
    cata_ofLayer_view (producerLayer layer) t
  have head : ((produce layer t).source, (produce layer t).value) =
      (t, cata_ty (TyAlgebra.ofLayer layer) t) := by
    rw [produce_source, produce_value]
  rw [← head, view]
  simp only [producerLayer, tyKids, List.flatMap_map, TyArgF.kids_map, List.flatMap_assoc]

/-- Each entry's children stand in the entries after it, which were built before it. A step of
`fold-cache-local-agreement`. Its consumer is `check_of_covered`. -/
def Covered {R : Type u} : Entries R → Prop
  | [] => True
  | (s, _) :: rest => Covered rest ∧ ∀ k ∈ tyKids s, (lookup rest k).isSome = true

/-- An entry's source has an answer. A step of `fold-cache-local-agreement`. Its consumer is
`produce_covered`. -/
@[semantics "initial-algebras-folds"]
theorem lookup_isSome_of_mem {R : Type u} {entries : Entries R} {s : Ty} {r : R}
    (member : (s, r) ∈ entries) : (lookup entries s).isSome = true := by
  induction entries with
  | nil => cases member
  | cons entry rest ih =>
    cases entry with
    | mk s' r' =>
      simp only [lookup]
      split
      next => rfl
      next different =>
        cases List.mem_cons.mp member with
        | inl same =>
          cases same
          exact absurd rfl different
        | inr later => exact ih later

/-- An answer that `lookup` returns stands in an entry at the requested type. A step of
`fold-cache-local-agreement`. Its consumer is `check_of_covered`. -/
@[semantics "initial-algebras-folds"]
theorem lookup_mem {R : Type u} {entries : Entries R} {t : Ty} {r : R}
    (found : lookup entries t = some r) : ∃ s, (s, r) ∈ entries ∧ s = t := by
  induction entries with
  | nil => cases found
  | cons entry rest ih =>
    cases entry with
    | mk s r' =>
      simp only [lookup] at found
      split at found
      next same =>
        cases found
        exact ⟨s, List.mem_cons_self, (Ty.key_injective same).symm⟩
      next =>
        obtain ⟨s', member, same⟩ := ih found
        exact ⟨s', List.mem_cons_of_mem _ member, same⟩

/-- Later entries keep every answer that the first entries hold. A step of
`fold-cache-local-agreement`. Its consumer is `covered_append`. -/
@[semantics "initial-algebras-folds"]
theorem lookup_append_isSome {R : Type u} {first : Entries R} (second : Entries R) {t : Ty}
    (found : (lookup first t).isSome = true) : (lookup (first ++ second) t).isSome = true := by
  induction first with
  | nil => cases found
  | cons entry rest ih =>
    cases entry with
    | mk s r =>
      simp only [lookup, List.cons_append] at found ⊢
      split
      next => rfl
      next different =>
        rw [if_neg different] at found
        exact ih found

/-- Two covered lists of entries, one after the other, are covered. A step of
`fold-cache-local-agreement`. Its consumer is `covered_flatMap`. -/
@[semantics "initial-algebras-folds"]
theorem covered_append {R : Type u} {first second : Entries R} (coveredFirst : Covered first)
    (coveredSecond : Covered second) : Covered (first ++ second) := by
  induction first with
  | nil => exact coveredSecond
  | cons entry rest ih =>
    cases entry with
    | mk s r =>
      exact ⟨ih coveredFirst.1, fun k child => lookup_append_isSome second (coveredFirst.2 k child)⟩

/-- Covered lists of entries, joined in order, are covered. A step of
`fold-cache-local-agreement`. Its consumer is `produce_covered`. -/
@[semantics "initial-algebras-folds"]
theorem covered_flatMap {R : Type u} {α : Type} (f : α → Entries R) (xs : List α)
    (covered : ∀ x ∈ xs, Covered (f x)) : Covered (xs.flatMap f) := by
  induction xs with
  | nil => exact True.intro
  | cons x rest ih =>
    rw [List.flatMap_cons]
    exact covered_append (covered x List.mem_cons_self)
      (ih fun y member => covered y (List.mem_cons_of_mem _ member))

/-- `check` accepts covered entries whose answers are the fold: each local equation then reads the
fold at every child. A step of `fold-cache-local-agreement`. Its consumer is `check_produce`. -/
@[semantics "initial-algebras-folds"]
theorem check_of_covered {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R)
    (entries : Entries R) (covered : Covered entries)
    (agree : ∀ x ∈ entries, x.2 = cata_ty (TyAlgebra.ofLayer layer) x.1) :
    check layer entries = true := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    cases entry with
    | mk s r =>
      have restAgree : ∀ x ∈ rest, x.2 = cata_ty (TyAlgebra.ofLayer layer) x.1 :=
        fun x member => agree x (List.mem_cons_of_mem _ member)
      have answers : ∀ t r', lookup rest t = some r' →
          r' = cata_ty (TyAlgebra.ofLayer layer) t := by
        intro t r' found
        obtain ⟨s', member, same⟩ := lookup_mem found
        rw [← same]
        exact restAgree (s', r') member
      have total : read layer rest = cata_ty (TyAlgebra.ofLayer layer) :=
        funext (read_agrees layer rest answers)
      have equation : r = localValue layer rest s := by
        rw [localValue, total, ← cata_ofLayer_view layer s]
        exact agree (s, r) List.mem_cons_self
      simp only [check, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨ih covered.1 restAgree, List.all_eq_true.mpr covered.2, equation⟩

/-- The entries that `produce` builds are covered, and each holds the fold at its source. A step
of `fold-cache-local-agreement`. Its consumer is `check_produce`. -/
@[semantics "initial-algebras-folds"]
theorem produce_covered {R : Type u} (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    Covered (produce layer t).entries ∧
      ∀ x ∈ (produce layer t).entries, x.2 = cata_ty (TyAlgebra.ofLayer layer) x.1 := by
  induction t using kids_induction with
  | step t ih =>
    rw [produce_entries]
    refine ⟨⟨covered_flatMap _ _ fun k child => (ih k child).1, fun k child => ?_⟩, ?_⟩
    · apply lookup_isSome_of_mem (r := cata_ty (TyAlgebra.ofLayer layer) k)
      apply List.mem_flatMap.mpr
      refine ⟨k, child, ?_⟩
      rw [produce_entries]
      exact List.mem_cons_self
    · intro x member
      cases List.mem_cons.mp member with
      | inl same => rw [same]
      | inr later =>
        obtain ⟨k, child, inner⟩ := List.mem_flatMap.mp later
        exact (ih k child).2 x inner

/-- `check` accepts the entries that `produce` builds, at every type and every layer. A step of
`fold-cache-local-agreement`. Its consumer is `answer_eq`. -/
@[semantics "initial-algebras-folds"]
theorem check_produce {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R)
    (t : Ty) : check layer (produce layer t).entries = true :=
  check_of_covered layer _ (produce_covered layer t).1 (produce_covered layer t).2

/-- **`answer` answers the fold at every type**: `prepare` builds a cache at every type, and its
root entry holds `cata_ty` of the layer. A consumer of `check_agreement`'s premises, for slice
D6: a memoized fold that answers at every type. It says nothing of the cost. -/
@[semantics "initial-algebras-folds"]
theorem answer_eq {R : Type u} [DecidableEq R] (layer : TyCtor → List (TyArgF R) → R) (t : Ty) :
    answer layer t = some (cata_ty (TyAlgebra.ofLayer layer) t) := by
  unfold answer prepare admit
  rw [dif_pos (check_produce layer t)]
  simp only [Option.bind_some, CheckedCache.query]
  rw [produce_entries]
  simp only [lookup, ↓reduceIte]

end Effect4.Program.TyCache
