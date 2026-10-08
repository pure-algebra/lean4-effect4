import Effect4.Program.Bounds
import Effect4.Program.NativeAtom
import Effect4.Program.Typing.Rules
import Effect4.Program.Formation
import Effect4.Program.Native
import Effect4.Laws.Program.Template
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Bounds — the laws of the match by bounds

**What it proves.** The laws of the match of a template by bounds
(`src/Effect4/Program/Bounds.lean`, decisions rows 299 and 303), in the checker's order
`Ty.subN`.

* **Sound** (`matchB_sound`, `matchArgsB_sound`). The request is below the template's instance
  at the bindings. An argument list is below its parameters' instances at one, final list of
  bindings. The guard of the function is the law.
* **Least** (`matchB_least`, `matchArgsB_least`) and **complete** (`matchB_complete`,
  `matchArgsB_complete`). A normal request below some instance has a match, and the match's
  bindings are below every list of bindings that admits the request.
* **Monotone** (`matchArgsB_monotone`). Smaller arguments have a match with smaller bindings.
* **One normal form, one match** (`matchN_congr`, `matchArgsN_complete`, `matchArgsN_least`):
  the match read at the normal form.
* **In reach** (`TemplateOK`, `templateOKb`, `templateOK_of`). A template in the reach of the
  laws is its own normal form, is admissible, and holds no nominal reference.
  `Test/Program/BoundsControls.lean` decides it for every template of the tree.
* **The binder term** (`matchB_cell_fixed`, `matchB_modify_use`). The match keeps the cell's
  parameter and binds the reply's parameter. `bindTerm_some_ok`
  (`src/Effect4/Laws/Program/Template.lean`) exposes that match to its consumers.

**Placement** (`AGENTS.md`, Trust). Concept `subtyping-algebra` (`docs/core/semantics.md`). The
claim `template-match-complete` points at `matchB_complete`. `matchArgsB_monotone` is the
template's share of the proposed claim `checker-monotone`. Requirements R4 and R14. The consumers
are `NativeAtom.sound_of_poly` (`src/Effect4/Laws/Program/Typed.lean`), the row lemmas of
`src/Effect4/Laws/Program/Template.lean`, and the module laws of
`src/Effect4/Laws/Modules/Waiting.lean`.

**What it does not establish.**
- A match under a union head or a nominal reference of a template.
- An upper bound from a contravariant occurrence.
- That the checker is complete against `HasTy`.
- Anything of tsgo's inference. The typed printer and prelude declarations supply the target
  forms, and the truth lane tests those forms on finite programs.
- At a binder term's raw type no law is stated.
-/

open Effect4 Effect4.Program
open Effect4.Program.Bounds

namespace Effect4.Program.Bounds

open Effect4.Program.Ty
open Effect4.Constructive.List (flatMap_congr mem_zip_map_self mem_zip_middle eq_of_mem_zip_map
  lookup_of_mem_nodup)

/-! ## The variances compose -/

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem comp_co (v : Variance) : comp v .co = v := by cases v <;> rfl
/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem comp_inv (v : Variance) : comp v .inv = .inv := by cases v <;> rfl

/-! ## The join of a list of candidates is their least upper bound, in the checker's order -/

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem subN_never (u : Ty) : subN .never u = true := OrderProof.sub_never u.normalize

/-- It is a step of `matchB_least`, and `joinCands_least` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem subN_join_least {a b c : Ty} (ha : subN a c = true) (hb : subN b c = true) :
    subN (Ty.join a b) c = true := by
  show sub (Ty.join a b).normalize c.normalize = true
  rw [normalize_join]
  exact OrderProof.sub_normalize_union_le sub_trans a b c.normalize ha hb

/-- It is a step of `matchB_sound`, and `matchB_sound_step` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem joinCands_upper : ∀ (l : List Ty) (c : Ty), c ∈ l → subN c (joinCands l) = true
  | [], _, h => absurd h List.not_mem_nil
  | [x], c, h => by
    rw [List.mem_singleton] at h
    rw [h]
    exact subN_refl x
  | x :: y :: rest, c, h => by
    show subN c (Ty.join x (joinCands (y :: rest))) = true
    rcases List.mem_cons.mp h with h | h
    · rw [h]
      exact subN_join_left _ _
    · exact subN_trans (joinCands_upper (y :: rest) c h) (subN_join_right _ _)

/-- It is a step of `matchB_least`, and `solve_between` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem joinCands_least : ∀ (l : List Ty) (u : Ty), (∀ c ∈ l, subN c u = true) →
    subN (joinCands l) u = true
  | [], u, _ => subN_never u
  | [x], _, h => h x List.mem_cons_self
  | x :: y :: rest, u, h =>
    subN_join_least (h x List.mem_cons_self)
      (joinCands_least (y :: rest) u fun c hc => h c (List.mem_cons_of_mem _ hc))

/-! ## What `solve` binds -/

/-- It is a step of `matchB_least`, and `mem_lowers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem lowers_cons (c : Cand) (ds : List Cand) (i : Nat) :
    lowers (c :: ds) i = if c.1 = i ∧ c.2.1 ≠ .contra then c.2.2 :: lowers ds i else lowers ds i := by
  unfold lowers
  rw [List.filterMap_cons]
  split <;> rename_i h
  · split at h
    · exact nomatch h
    · rename_i hc
      rw [if_neg hc]
  · split at h
    · rename_i hc
      rw [if_pos hc]
      cases h
      rfl
    · exact nomatch h

/-- It is a step of `matchB_sound`, and `instantiate_solve` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem lookup_added (seed : Subst) (f : Nat → Ty) (i : Nat) (hi : seed.lookup i = none) :
    ∀ ds : List Cand,
      ((ds.filterMap fun c =>
          if c.2.1 = .contra ∨ (seed.lookup c.1).isSome then none else some (c.1, f c.1)).lookup i =
        some (f i) ∧ lowers ds i ≠ []) ∨
      ((ds.filterMap fun c =>
          if c.2.1 = .contra ∨ (seed.lookup c.1).isSome then none else some (c.1, f c.1)).lookup i =
        none ∧ lowers ds i = [])
  | [] => Or.inr ⟨rfl, rfl⟩
  | c :: ds => by
    have ih := lookup_added seed f i hi ds
    rw [List.filterMap_cons, lowers_cons]
    by_cases hc : c.2.1 = .contra ∨ (seed.lookup c.1).isSome
    · rw [if_pos hc]
      have hno : ¬ (c.1 = i ∧ c.2.1 ≠ .contra) := by
        rintro ⟨hci, hcv⟩
        rcases hc with hc | hc
        · exact hcv hc
        · rw [hci, hi] at hc
          exact Bool.noConfusion hc
      rw [if_neg hno]
      exact ih
    · rw [if_neg hc]
      have hv : c.2.1 ≠ .contra := fun h => hc (Or.inl h)
      show (((c.1, f c.1) :: _).lookup i = _ ∧ _) ∨ (((c.1, f c.1) :: _).lookup i = _ ∧ _)
      rw [List.lookup_cons]
      by_cases hci : c.1 = i
      · rw [if_pos ⟨hci, hv⟩, hci, beq_iff_eq.mpr rfl]
        exact Or.inl ⟨rfl, List.cons_ne_nil _ _⟩
      · rw [if_neg (fun h => hci h.1)]
        have hne : (i == c.1) = false := by
          cases hb : i == c.1 with
          | false => rfl
          | true => exact absurd (beq_iff_eq.mp hb).symm hci
        rw [hne]
        exact ih

/-- It is a step of `matchB_sound`, and `matchB_sound_step` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem instantiate_solve (seed : Subst) (cs : List Cand) (i : Nat) (hi : seed.lookup i = none) :
    instantiate (solve seed cs) (.var i) = joinCands (lowers cs i) := by
  rw [instantiate]
  unfold solve
  rw [List.lookup_append, hi, Option.none_or]
  rcases lookup_added seed (fun j => joinCands (lowers cs j)) i hi cs with ⟨h, -⟩ | ⟨h, hl⟩
  · rw [h]
    rfl
  · rw [h, hl]
    rfl

/-- It is a step of `matchB_sound`, and `matchB_sound_step` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem lookup_solve_seed (seed : Subst) (cs : List Cand) {i : Nat} {u : Ty}
    (hi : seed.lookup i = some u) : (solve seed cs).lookup i = some u := by
  unfold solve
  rw [List.lookup_append, hi, Option.some_or]

/-! ## Sound: the guard is the law -/

/-- Each argument below its parameter's instance at `τ`, in the checker's order. -/
def Admits (τ : Subst) (ps rs : List Ty) : Prop :=
  ∀ pr ∈ ps.zip rs, sub pr.2.normalize (instantiate τ pr.1).normalize = true

/-- **The match by bounds is sound**: the request is below the template's instance at the
bindings, both sides normalized, and the bindings keep the seed's. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_sound {seed σ : Subst} {t r : Ty} (h : matchB seed t r = some σ) :
    sub r.normalize (instantiate σ t).normalize = true ∧
      ∀ j u, seed.lookup j = some u → σ.lookup j = some u := by
  unfold matchB at h
  dsimp only at h
  split at h
  · rename_i hg
    cases h
    exact ⟨hg, fun j u hj => lookup_solve_seed seed _ hj⟩
  · exact nomatch h

/-- **The match of an argument list is sound at one instance**: every argument is below its
parameter's instance at the same, final bindings. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_sound {ps rs : List Ty} {σ : Subst} (h : matchArgsB ps rs = some σ) :
    ps.length = rs.length ∧ Admits σ ps rs := by
  unfold matchArgsB at h
  split at h
  · rename_i hl
    dsimp only at h
    split at h
    · rename_i hg
      cases h
      exact ⟨hl, fun pr hpr => List.all_eq_true.mp hg pr hpr⟩
    · exact nomatch h
  · exact nomatch h

/-! ## The templates in reach: no nominal reference -/

mutual
/-- No nominal reference anywhere in the type. -/
def noApp : Ty → Bool
  | .app _ _ => false
  | .option t | .list t | .causeOf t | .refOf t => noApp t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b
  | .map a b => noApp a && noApp b
  | .record fs => noAppFields fs
  | .tuple ts => noAppItems ts
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ | .var _
  | .null | .undefined | .number | .bytes => true
def noAppFields : List (String × Bool × Ty) → Bool
  | [] => true
  | (_, _, t) :: rest => noApp t && noAppFields rest
def noAppItems : List Ty → Bool
  | [] => true
  | t :: rest => noApp t && noAppItems rest
end

/-- It is a step of `matchB_complete`, and `noApp_args` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem noAppFields_eq_all (fs : List (String × Bool × Ty)) :
    noAppFields fs = fs.all fun p => noApp p.2.2 := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    simp only [noAppFields, List.all_cons, ih]

/-- It is a step of `matchB_complete`, and `noApp_args` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem noAppItems_eq_all (ts : List Ty) : noAppItems ts = ts.all noApp := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp only [noAppItems, List.all_cons, ih]

/-- It is a step of `matchB_complete`, and `TemplateOK.args` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem noApp_args {t : Ty} (h : noApp t = true) : ∀ p ∈ t.args, noApp p.2 = true := by
  intro p hp
  cases t
  case app n ts => exact absurd h Bool.false_ne_true
  case record fs =>
    rw [noApp, noAppFields_eq_all, List.all_eq_true] at h
    simp only [args, List.mem_map] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact h q (mem_canon hq)
  case tuple ts =>
    rw [noApp, noAppItems_eq_all, List.all_eq_true] at h
    simp only [args, List.mem_map] at hp
    obtain ⟨x, hx, rfl⟩ := hp
    exact h x hx
  all_goals simp only [args, List.mem_cons, List.not_mem_nil, or_false] at hp
  all_goals simp only [noApp, Bool.and_eq_true] at h
  all_goals aesop

/-- A template in the laws' reach. -/
structure TemplateOK (t : Ty) : Prop where
  normal : Normal t
  admissible : templateAdmissible t = true
  noApp : noApp t = true

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem TemplateOK.args {t : Ty} (h : TemplateOK t) (hm : isMember t = true) :
    ∀ p ∈ t.args, TemplateOK p.2 := fun p hp =>
  ⟨OrderProof.normal_args h.normal hm _ (List.mem_map_of_mem hp),
    templateAdmissible_args h.admissible p hp, noApp_args h.noApp p hp⟩

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem TemplateOK.head {t : Ty} (h : TemplateOK t) (hc : closed t = false) (hv : ∀ i, t ≠ .var i) :
    (∀ a b, t ≠ .union a b) ∧ (∀ n ts, t ≠ .app n ts) ∧ t.args ≠ [] ∧ isMember t = true := by
  have hu : ∀ a b, t ≠ .union a b := by
    rintro a b rfl
    have ha := h.admissible
    simp only [templateAdmissible, Bool.and_eq_true] at ha
    simp only [closed, ha.1, ha.2, Bool.and_self] at hc
    exact Bool.noConfusion hc
  have happ : ∀ n ts, t ≠ .app n ts := by
    rintro n ts rfl
    exact absurd h.noApp Bool.false_ne_true
  refine ⟨hu, happ, ?_, ?_⟩
  · intro hnil
    cases t
    case var i => exact hv i rfl
    case union a b => exact hu a b rfl
    case app n ts => exact happ n ts rfl
    case record fs =>
      have hf : fs = [] := canon_eq_nil (List.map_eq_nil_iff.mp hnil)
      rw [hf] at hc
      exact Bool.noConfusion hc
    case tuple ts =>
      have hf : ts = [] := List.map_eq_nil_iff.mp hnil
      rw [hf] at hc
      exact Bool.noConfusion hc
    case never | unknown | unit | nat | int | string | bool | handle _ | lit _
       | null | undefined | number | bytes =>
      exact Bool.noConfusion hc
    case option _ | list _ | causeOf _ | refOf _ | prod _ _ | except _ _
       | exitOf _ _ | fiberOf _ _ | deferredOf _ _ | map _ _ =>
      exact absurd hnil (List.cons_ne_nil _ _)
  · cases t
    case union a b => exact absurd rfl (hu a b)
    case never => exact Bool.noConfusion hc
    all_goals rfl

/-! ## The candidates, head by head -/

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem cands_var (v : Variance) (i : Nat) (r : Ty) : cands v (.var i) r = [(i, v, r)] := by
  rw [cands]

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem cands_union_right (v : Variance) {t : Ty} (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) (c d : Ty) :
    cands v t (.union c d) = cands v t c ++ cands v t d := by
  rw [cands]
  exacts [hv, hu]

/-- It is a step of `matchB_least`, and `cands_args` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem candsItems_eq (v : Variance) : ∀ (ts rs : List Ty),
    candsItems v ts rs = (ts.zip rs).flatMap fun p => cands v p.1 p.2
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | t :: ts, r :: rs => by
    rw [candsItems, List.zip_cons_cons, List.flatMap_cons, candsItems_eq v ts rs]

/-- It is a step of `matchB_least`, and `cands_args` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem candsFields_eq (v : Variance) (L : List (String × Bool × Ty)) :
    ∀ (fs gs : List (String × Bool × Ty)), fs.length = gs.length →
      (∀ p ∈ fs.zip gs, L.lookup p.2.1 = some p.1.2) →
      candsFields v L gs = (fs.zip gs).flatMap fun p => cands v p.1.2.2 p.2.2.2
  | [], [], _, _ => rfl
  | [], _ :: _, hl, _ => absurd hl (Nat.succ_ne_zero _).symm
  | _ :: _, [], hl, _ => absurd hl (Nat.succ_ne_zero _)
  | (m, o', ty) :: fs, (n, o, r) :: gs, hl, hk => by
    have hp := hk ((m, o', ty), (n, o, r)) List.mem_cons_self
    rw [candsFields, hp, List.zip_cons_cons, List.flatMap_cons,
      candsFields_eq v L fs gs (Nat.succ.inj hl) fun q hq => hk q (List.mem_cons_of_mem _ hq)]

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem cands_args (v : Variance) {t r : Ty} (hv : ∀ i, t ≠ .var i) (happ : ∀ n ts, t ≠ .app n ts)
    (hct : headCanon t = true) (hcr : headCanon r = true) (hh : sameHead t r = true) :
    cands v t r = (t.args.zip r.args).flatMap fun p => cands (comp v p.1.1) p.1.2 p.2.2 := by
  revert hv happ hct hcr hh
  fun_cases sameHead t r
  case case18 =>
    intro hv
    exact absurd rfl (hv _)
  case case23 =>
    intro _ happ
    exact absurd rfl (happ _ _)
  case case20 fs gs =>
    intro _ _ hct hcr hh
    have hfs : canon fs = fs := of_decide_eq_true hct
    have hgs : canon gs = gs := of_decide_eq_true hcr
    have hheads := of_decide_eq_true hh
    rw [hfs, hgs] at hheads
    have hnd : (fs.map Prod.fst).Nodup := hfs ▸ Field.canonBy_names_nodup fs
    show candsFields v fs gs = _
    have hlen : fs.length = gs.length := by
      rw [← List.length_map (f := fun p : String × Bool × Ty => (p.1, p.2.1)), hheads,
        List.length_map]
    rw [candsFields_eq v fs fs gs hlen fun p hp => by
      have hname := congrArg Prod.fst (eq_of_mem_zip_map hheads hp)
      rw [← hname]
      exact lookup_of_mem_nodup hnd (List.of_mem_zip hp).1]
    simp only [args, hfs, hgs, List.zip_map, List.flatMap_map]
    exact flatMap_congr fun a _ => by
      obtain ⟨a1, a2⟩ := a
      simp only [Prod.map, comp_co]
  case case22 xs ys =>
    intro _ _ _ _ _
    show candsItems v xs ys = _
    rw [candsItems_eq]
    simp only [args, List.zip_map, List.flatMap_map]
    exact flatMap_congr fun a _ => by
      obtain ⟨a1, a2⟩ := a
      simp only [Prod.map, comp_co]
  case case28 =>
    intro _ _ _ _ hh
    exact absurd hh Bool.false_ne_true
  all_goals
    intro _ _ _ _ _
    simp only [cands, args, List.zip_cons_cons, List.zip_nil_right, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, comp_co, comp_inv]

/-- It is a step of `matchB_complete`, and `recovers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem cands_mem_members (v : Variance) {t : Ty} (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) :
    ∀ (r : Ty) (c : Cand), c ∈ cands v t r ↔ ∃ x ∈ r.members, c ∈ cands v t x := by
  intro r
  induction r with
  | union a b iha ihb =>
    intro c
    rw [cands_union_right v hv hu, List.mem_append, iha, ihb]
    simp only [members, List.mem_append]
    constructor
    · rintro (⟨x, hx, hc⟩ | ⟨x, hx, hc⟩)
      · exact ⟨x, Or.inl hx, hc⟩
      · exact ⟨x, Or.inr hx, hc⟩
    · rintro ⟨x, hx | hx, hc⟩
      · exact Or.inl ⟨x, hx, hc⟩
      · exact Or.inr ⟨x, hx, hc⟩
  | never =>
    intro c
    have hn : cands v t .never = [] := by
      cases t
      case var i => exact absurd rfl (hv i)
      all_goals rfl
    rw [hn]
    simp only [members, List.not_mem_nil, false_and, exists_false]
  | _ =>
    intro c
    simp only [members, List.mem_singleton, exists_eq_left]

/-! ## One step of the order at a template's head -/

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem below_args (τ : Subst) {t r : Ty} (ht : Normal t) (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) (happ : ∀ n ts, t ≠ .app n ts) (hargs : t.args ≠ [])
    (hr : Normal r) (hm : isMember r = true)
    (hsub : sub r (instantiate τ t).normalize = true) :
    sameHead t r = true ∧ ∀ p ∈ t.args.zip r.args, Normal p.2.2 ∧
      (p.1.1 = .inv → p.2.2 = (instantiate τ p.1.2).normalize) ∧
      sub p.2.2 (instantiate τ p.1.2).normalize = true := by
  have hinst := (instance_members τ ht hv hu happ).2
  have hchild : ∀ p ∈ t.args.zip r.args, Normal p.2.2 := fun p hp =>
    OrderProof.normal_args hr hm _ (List.mem_map_of_mem (List.of_mem_zip hp).2)
  obtain ⟨m, hmJ, hrm⟩ := (OrderProof.sub_member_right_iff r _ hm).mp hsub
  obtain ⟨htm, hzip⟩ := hinst m hmJ
  have hmm : isMember m = true := members_isMember hmJ
  have htmLen := args_congr htm
  have hmargs : m.args ≠ [] := by
    intro hnil
    rw [hnil, List.length_nil] at htmLen
    exact hargs (List.eq_nil_of_length_eq_zero htmLen.1)
  have hleaf : leafRule r m = false := by
    cases hl : leafRule r m with
    | false => rfl
    | true => exact absurd (leafRule_args hl).2.1 hmargs
  have htop : topRule r m = false := by
    refine topRule_eq_false fun hmu => hmargs ?_
    rw [hmu]
    rfl
  rw [sub_eq_args r m hm hmm hleaf htop, Bool.and_eq_true] at hrm
  obtain ⟨hrmh, hbelow⟩ := hrm
  have hrmLen := args_congr hrmh
  refine ⟨sameHead_trans htm (sameHead_symm hrmh), fun p hp => ?_⟩
  obtain ⟨q, hpq, hrq⟩ := mem_zip_middle htmLen.1 hrmLen.1 hp
  obtain ⟨hvar, hq⟩ := hzip (p.1, q) hpq
  have hvr : p.2.1 = q.1 := eq_of_mem_zip_map hrmLen.2 hrq
  have hholds : p.2.1.holds sub p.2.2 q.2 = true :=
    List.all_eq_true.mp hbelow (p.2, q) hrq
  rcases args_co_or_inv happ p.1 (List.of_mem_zip hp).1 with hco | hinv
  · rw [hvr, ← hvar, hco] at hholds
    have hbelowJ : sub p.2.2 (instantiate τ p.1.2).normalize = true := by
      rcases hq with he | ⟨-, hf⟩
      · rw [← he]
        exact hholds
      · exact sub_trans _ _ _ hholds (sub_of_mem_factors hf)
    exact ⟨hchild p hp, fun h => absurd (h.symm.trans hco) (by decide), hbelowJ⟩
  · rw [hvr, ← hvar, hinv] at hholds
    have he : q.2 = (instantiate τ p.1.2).normalize := by
      rcases hq with he | ⟨hco, -⟩
      · exact he
      · exact absurd (hinv.symm.trans hco) (by decide)
    rw [he] at hholds
    have hboth := Bool.and_eq_true_iff.mp hholds
    have heq : p.2.2 = (instantiate τ p.1.2).normalize :=
      OrderProof.sub_antisymm_normal sub_trans _ _ (hchild p hp) (normal_normalize _)
        hboth.1 hboth.2
    exact ⟨hchild p hp, fun _ => heq, heq ▸ sub_refl _⟩

/-! ## Least: each candidate is below any bindings that admit the request -/

/-- It is a step of `matchB_least`, and `cands_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem comp_ne_contra {v w : Variance} (hv : v ≠ .contra) (hw : w = .co ∨ w = .inv) :
    comp v w ≠ .contra := by
  rcases hw with rfl | rfl
  · rw [comp_co]
    exact hv
  · rw [comp_inv]
    exact fun h => nomatch h

/-- It is a step of `matchB_least`, and `matchB_least_step` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem cands_below (τ : Subst) (n : Nat) : ∀ (r t : Ty) (v : Variance), sizeOf r < n →
    v ≠ .contra → TemplateOK t → Normal r → sub r (instantiate τ t).normalize = true →
    ∀ c ∈ cands v t r, c.2.1 ≠ .contra ∧ Normal c.2.2 ∧
      sub c.2.2 (instantiate τ (.var c.1)).normalize = true := by
  induction n with
  | zero => exact fun _ _ _ hn => absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro r t v hn hvc ht hr hsub c hc
    rcases var_or_ne t with ⟨i, rfl⟩ | hv
    · rw [cands_var, List.mem_singleton] at hc
      rw [hc]
      exact ⟨hvc, hr, hsub⟩
    cases hcl : closed t with
    | true =>
      rw [cands_closed v t r hcl] at hc
      exact absurd hc List.not_mem_nil
    | false =>
      obtain ⟨hu, happ, hargs, htm⟩ := ht.head hcl hv
      cases hrm : isMember r with
      | false =>
        rcases isMember_eq_false hrm with rfl | ⟨c1, d1, rfl⟩
        · obtain ⟨x, hx, -⟩ := (cands_mem_members v hv hu .never c).mp hc
          exact absurd hx List.not_mem_nil
        · rw [cands_union_right v hv hu] at hc
          obtain ⟨hc1, hd1, -, -⟩ := normal_union_inv hr
          have hall := (OrderProof.sub_iff_members sub_trans _ _).mp hsub
          have hsize := Ty.union.sizeOf_spec c1 d1
          rcases List.mem_append.mp hc with hc | hc
          · exact ih c1 t v (by omega) hvc ht hc1
              ((OrderProof.sub_iff_members sub_trans _ _).mpr fun x hx =>
                hall x (List.mem_append_left _ hx)) c hc
          · exact ih d1 t v (by omega) hvc ht hd1
              ((OrderProof.sub_iff_members sub_trans _ _).mpr fun x hx =>
                hall x (List.mem_append_right _ hx)) c hc
      | true =>
        obtain ⟨hh, hkids⟩ := below_args τ ht.normal hv hu happ hargs hr hrm hsub
        rw [cands_args v hv happ (OrderProof.normal_headCanon ht.normal)
          (OrderProof.normal_headCanon hr) hh] at hc
        obtain ⟨p, hp, hc⟩ := List.mem_flatMap.mp hc
        obtain ⟨hpn, -, hpsub⟩ := hkids p hp
        have hsize : sizeOf p.2.2 < sizeOf r := sizeOf_args (List.of_mem_zip hp).2
        exact ih p.2.2 p.1.2 _ (by omega)
          (comp_ne_contra hvc (args_co_or_inv happ p.1 (List.of_mem_zip hp).1))
          (ht.args htm p.1 (List.of_mem_zip hp).1) hpn hpsub c hc

/-- It is a step of `matchB_least`, and `solve_between` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem mem_lowers {cs : List Cand} {i : Nat} {x : Ty} :
    x ∈ lowers cs i ↔ ∃ c ∈ cs, c.1 = i ∧ c.2.1 ≠ .contra ∧ c.2.2 = x := by
  unfold lowers
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨c, hc, hx⟩
    split at hx
    · rename_i hcond
      cases hx
      exact ⟨c, hc, hcond.1, hcond.2, rfl⟩
    · exact nomatch hx
  · rintro ⟨c, hc, hi, hv, hx⟩
    exact ⟨c, hc, by rw [if_pos ⟨hi, hv⟩, hx]⟩

/-- It is a step of `matchB_least`, and `matchB_least_step` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem solve_between (seed : Subst) (cs : List Cand) (τ : Subst)
    (hseed : ∀ j u, seed.lookup j = some u → (instantiate τ (.var j)).normalize = u.normalize)
    (hcs : ∀ c ∈ cs, c.2.1 ≠ .contra ∧ Normal c.2.2 ∧
      sub c.2.2 (instantiate τ (.var c.1)).normalize = true) :
    (∀ i, sub (instantiate (solve seed cs) (.var i)).normalize
        (instantiate τ (.var i)).normalize = true) ∧
    (∀ c ∈ cs, sub c.2.2 (instantiate (solve seed cs) (.var c.1)).normalize = true) := by
  constructor
  · intro i
    cases hs : seed.lookup i with
    | some u =>
      rw [instantiate, lookup_solve_seed seed cs hs, hseed i u hs]
      exact sub_refl _
    | none =>
      rw [instantiate_solve seed cs i hs]
      refine joinCands_least _ (instantiate τ (.var i)) fun x hx => ?_
      obtain ⟨c, hc, hi, -, hx⟩ := mem_lowers.mp hx
      have hcc := hcs c hc
      show sub x.normalize (instantiate τ (.var i)).normalize = true
      rw [← hx, ← hi, hcc.2.1.fixed]
      exact hcc.2.2
  · intro c hc
    have hcc := hcs c hc
    cases hs : seed.lookup c.1 with
    | some u =>
      rw [instantiate, lookup_solve_seed seed cs hs]
      show sub c.2.2 u.normalize = true
      rw [← hseed c.1 u hs]
      exact hcc.2.2
    | none =>
      rw [instantiate_solve seed cs c.1 hs]
      have h := joinCands_upper _ _ (mem_lowers.mpr ⟨c, hc, rfl, hcc.1, rfl⟩)
      have h' : sub c.2.2.normalize (joinCands (lowers cs c.1)).normalize = true := h
      rw [hcc.2.1.fixed] at h'
      exact h'

/-- **The match by bounds answers the least bindings**: under any bindings that place the request
below the template's instance and agree with the seed, each binding of the match is below `τ`'s,
in the checker's order. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_least {seed σ : Subst} {t r : Ty} (h : matchB seed t r = some σ) (ht : TemplateOK t)
    (hr : Normal r) {τ : Subst}
    (hseed : ∀ j u, seed.lookup j = some u → (instantiate τ (.var j)).normalize = u.normalize)
    (hτ : sub r (instantiate τ t).normalize = true) :
    ∀ i, subN (instantiate σ (.var i)) (instantiate τ (.var i)) = true := by
  unfold matchB at h
  dsimp only at h
  split at h
  · cases h
    exact (solve_between seed _ τ hseed
      (cands_below τ (sizeOf r + 1) r t .co (Nat.lt_succ_self _) (fun h => nomatch h) ht hr hτ)).1
  · exact nomatch h

/-- It is a step of `matchArgsB_least`, and `matchArgsB_least` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem candsList_below (τ : Subst) {ps rs : List Ty} (hps : ∀ p ∈ ps, TemplateOK p)
    (hrs : ∀ r ∈ rs, Normal r) (hτ : Admits τ ps rs) :
    ∀ c ∈ candsList ps rs, c.2.1 ≠ .contra ∧ Normal c.2.2 ∧
      sub c.2.2 (instantiate τ (.var c.1)).normalize = true := by
  intro c hc
  obtain ⟨pr, hpr, hc⟩ := List.mem_flatMap.mp hc
  have hsub := hτ pr hpr
  rw [(hrs pr.2 (List.of_mem_zip hpr).2).fixed] at hsub
  exact cands_below τ (sizeOf pr.2 + 1) pr.2 pr.1 .co (Nat.lt_succ_self _) (fun h => nomatch h)
    (hps pr.1 (List.of_mem_zip hpr).1) (hrs pr.2 (List.of_mem_zip hpr).2) hsub c hc

/-- **The match of an argument list answers the least bindings.** -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_least {ps rs : List Ty} {σ : Subst} (h : matchArgsB ps rs = some σ)
    (hps : ∀ p ∈ ps, TemplateOK p) (hrs : ∀ r ∈ rs, Normal r) {τ : Subst} (hτ : Admits τ ps rs) :
    ∀ i, subN (instantiate σ (.var i)) (instantiate τ (.var i)) = true := by
  unfold matchArgsB at h
  split at h
  · dsimp only at h
    split at h
    · cases h
      exact (solve_between [] _ τ (fun _ _ hj => nomatch hj) (candsList_below τ hps hrs hτ)).1
    · exact nomatch h
  · exact nomatch h

/-! ## Complete: the solved bindings admit whatever some bindings admit -/

/-- It is a step of `matchB_complete`, and `covers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem instance_shape (τ : Subst) {t : Ty} (ht : Normal t) (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) (happ : ∀ n ts, t ≠ .app n ts) (hp : ∀ a b, t ≠ .prod a b)
    (hargs : t.args ≠ []) :
    isMember (instantiate τ t).normalize = true ∧ sameHead t (instantiate τ t).normalize = true ∧
      (instantiate τ t).normalize.args =
        t.args.map fun p => (p.1, (instantiate τ p.2).normalize) := by
  induction ht with
  | never => exact absurd rfl hargs
  | var i => exact absurd rfl (hv i)
  | prod _ _ _ _ _ _ =>
    rename_i a b _ _ _ _ _ _
    exact absurd rfl (hp a b)
  | row r _ _ _ ih =>
    obtain ⟨elems, _⟩ := r
    cases elems with
    | nil => exact absurd rfl hargs
    | cons x xs =>
      cases xs with
      | nil => exact ih x List.mem_cons_self hv hu happ hp hargs
      | cons y ys => exact absurd rfl (hu x (ofMembers (y :: ys)))
  | record _ hasc _ =>
    rename_i fs _ _
    have hc : canon fs = fs := Field.canonBy_of_ascending fs hasc
    have hJ : (instantiate τ (.record fs)).normalize =
        .record (fs.map fun q => (q.1, q.2.1, (instantiate τ q.2.2).normalize)) := by
      rw [instantiate, instantiateFields_eq_map, normalize_record, canon_map_payload, hc,
        List.map_map]
      rfl
    rw [hJ]
    have hc' : canon (fs.map fun q => (q.1, q.2.1, (instantiate τ q.2.2).normalize)) =
        fs.map fun q => (q.1, q.2.1, (instantiate τ q.2.2).normalize) :=
      (canon_map_payload fs fun x => (instantiate τ x).normalize).trans (by rw [hc])
    refine ⟨rfl, ?_, ?_⟩
    · simp only [sameHead, hc, hc', List.map_map, decide_eq_true_eq]
      rfl
    · simp only [args, hc, hc', List.map_map]
      rfl
  | tuple _ hlen _ =>
    rename_i ts _ _
    have hJ : (instantiate τ (.tuple ts)).normalize =
        .tuple (ts.map fun x => (instantiate τ x).normalize) := by
      rw [instantiate, instantiateItems_eq_map,
        normalize_tuple_of_ne _ (by rw [List.length_map]; exact hlen), normalizeItems_eq_map,
        List.map_map]
      rfl
    rw [hJ]
    refine ⟨rfl, ?_, ?_⟩
    · simp only [sameHead, List.length_map, decide_eq_true_eq]
    · simp only [args, List.map_map]
      rfl
  | app _ _ =>
    rename_i n ts _ _ _
    exact absurd rfl (happ n ts)
  | unknown | unit | nat | int | string | bool | handle _ | lit _
  | null | undefined | number | bytes =>
    exact absurd rfl hargs
  | option _ | list _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _
  | refOf _ | deferredOf _ _ | map _ _ =>
    exact ⟨rfl, rfl, rfl⟩

/-- It is a step of `matchB_complete`, and `covers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem mem_zip_map_right {α β γ : Type} (f : β → γ) :
    ∀ {xs : List α} {ys : List β} {a : α} {c : γ},
      (a, c) ∈ xs.zip (ys.map f) → ∃ b, (b, a) ∈ ys.zip xs ∧ c = f b
  | [], _, _, _, h => by
    rw [List.zip_nil_left] at h
    exact absurd h List.not_mem_nil
  | _ :: _, [], _, _, h => by
    rw [List.map_nil, List.zip_nil_right] at h
    exact absurd h List.not_mem_nil
  | x :: xs, y :: ys, a, c, h => by
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with h | h
    · rw [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨y, by rw [List.zip_cons_cons]; exact List.mem_cons_self, rfl⟩
    · obtain ⟨b, hb, hc⟩ := mem_zip_map_right f h
      exact ⟨b, by rw [List.zip_cons_cons]; exact List.mem_cons_of_mem _ hb, hc⟩

/-- It is a step of `matchB_complete`, and `covers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem mem_zip_self_map {α β : Type} (f : α → β) :
    ∀ {l : List α} {p : α}, p ∈ l → (p, f p) ∈ l.zip (l.map f)
  | [], _, h => absurd h List.not_mem_nil
  | a :: l, p, h => by
    rw [List.map_cons, List.zip_cons_cons, List.mem_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (mem_zip_self_map f h)

/-- It is a step of `matchB_complete`, and `covers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem above_args (σ : Subst) {t r : Ty} (ht : Normal t) (hv : ∀ i, t ≠ .var i)
    (hu : ∀ a b, t ≠ .union a b) (happ : ∀ n ts, t ≠ .app n ts) (hp : ∀ a b, t ≠ .prod a b)
    (hargs : t.args ≠ []) (hm : isMember r = true) (hh : sameHead t r = true)
    (hkids : ∀ p ∈ t.args.zip r.args,
      p.1.1.holds sub p.2.2 (instantiate σ p.1.2).normalize = true) :
    sub r (instantiate σ t).normalize = true := by
  obtain ⟨hmm, htm, hmargs⟩ := instance_shape σ ht hv hu happ hp hargs
  have hma : (instantiate σ t).normalize.args ≠ [] := by
    rw [hmargs]
    intro h
    exact hargs (List.map_eq_nil_iff.mp h)
  have hleaf : leafRule r (instantiate σ t).normalize = false := by
    cases hl : leafRule r (instantiate σ t).normalize with
    | false => rfl
    | true => exact absurd (leafRule_args hl).2.1 hma
  have htop : topRule r (instantiate σ t).normalize = false := by
    refine topRule_eq_false fun hmu => hma ?_
    rw [hmu]
    rfl
  rw [sub_eq_args r _ hm hmm hleaf htop, Bool.and_eq_true]
  refine ⟨sameHead_trans (sameHead_symm hh) htm, ?_⟩
  unfold argsBelow
  rw [List.all_eq_true]
  intro q hq
  rw [hmargs] at hq
  obtain ⟨b, hb, hq2⟩ := mem_zip_map_right _ hq
  have hvar : b.1 = q.1.1 := eq_of_mem_zip_map (args_congr hh).2 hb
  have hk := hkids (b, q.1) hb
  rw [hq2, ← hvar]
  exact hk

/-- It is a step of `matchB_complete`, and `covers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem above_prod (σ : Subst) {a b r1 r2 : Ty} (hr : Normal (.prod r1 r2))
    (h1 : sub r1 (instantiate σ a).normalize = true)
    (h2 : sub r2 (instantiate σ b).normalize = true) :
    sub (.prod r1 r2) (instantiate σ (.prod a b)).normalize = true := by
  have hn : Normal r1 ∧ Normal r2 := OrderProof.normal_children _ hr
  have h := OrderProof.sub_normalize_prod_mono sub_trans r1 r2 (instantiate σ a) (instantiate σ b)
    (by rw [hn.1.fixed]; exact h1) (by rw [hn.2.fixed]; exact h2)
  rw [hr.fixed] at h
  exact h

/-- It is a step of `matchB_complete`, and `prod_left_cands` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem prod_member_left (X Y : Ty) {x : Ty} (hx : x ∈ X.normalize.members) :
    ∃ y, Ty.prod x y ∈ (normalize (.prod X Y)).members := by
  obtain ⟨y0, hy0⟩ := OrderProof.normal_factors_nonempty _ (normal_normalize Y)
  have hxf : x ∈ X.normalize.factors := OrderProof.members_subset_factors hx
  have hmem : Ty.prod x y0 ∈ productMembers X.normalize Y.normalize :=
    List.mem_flatMap.mpr ⟨x, hxf, List.mem_map.mpr ⟨y0, hy0, rfl⟩⟩
  rw [OrderProof.members_normalize_prod]
  obtain ⟨z, hz, hxz⟩ := normalizeRow_coverage _ (.prod x y0) hmem
  have hz' := ((mem_normalizeRow z _).mp hz).1
  obtain ⟨x', hx', hz''⟩ := List.mem_flatMap.mp hz'
  obtain ⟨y', -, rfl⟩ := List.mem_map.mp hz''
  rw [sub_args_prod] at hxz
  simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hxz
  have hx'm : x' ∈ X.normalize.members := by
    generalize X.normalize = A at hx hx'
    cases A with
    | never => exact absurd hx List.not_mem_nil
    | _ => exact hx'
  have hXn := normal_normalize X
  have hxx' : x = x' :=
    OrderProof.sub_antisymm_normal sub_trans _ _ (hXn.members hx) (hXn.members hx'm) hxz.1
      (hXn.members_maximal x hx x' hx'm hxz.1)
  rw [hxx']
  exact ⟨y', hz⟩

/-- It is a step of `matchB_complete`, and `prod_right_cands` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem prod_member_right (X Y : Ty) {y : Ty} (hy : y ∈ Y.normalize.members) :
    ∃ x, Ty.prod x y ∈ (normalize (.prod X Y)).members := by
  obtain ⟨x0, hx0⟩ := OrderProof.normal_factors_nonempty _ (normal_normalize X)
  have hyf : y ∈ Y.normalize.factors := OrderProof.members_subset_factors hy
  have hmem : Ty.prod x0 y ∈ productMembers X.normalize Y.normalize :=
    List.mem_flatMap.mpr ⟨x0, hx0, List.mem_map.mpr ⟨y, hyf, rfl⟩⟩
  rw [OrderProof.members_normalize_prod]
  obtain ⟨z, hz, hxz⟩ := normalizeRow_coverage _ (.prod x0 y) hmem
  have hz' := ((mem_normalizeRow z _).mp hz).1
  obtain ⟨x', -, hz''⟩ := List.mem_flatMap.mp hz'
  obtain ⟨y', hy', rfl⟩ := List.mem_map.mp hz''
  rw [sub_args_prod] at hxz
  simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hxz
  have hy'm : y' ∈ Y.normalize.members := by
    generalize Y.normalize = B at hy hy'
    cases B with
    | never => exact absurd hy List.not_mem_nil
    | _ => exact hy'
  have hYn := normal_normalize Y
  have hyy' : y = y' :=
    OrderProof.sub_antisymm_normal sub_trans _ _ (hYn.members hy) (hYn.members hy'm) hxz.2
      (hYn.members_maximal y hy y' hy'm hxz.2)
  rw [hyy']
  exact ⟨x', hz⟩

/-- It is a step of `matchB_complete`, and `recovers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem mem_varsOf_args {t : Ty} (ht : Normal t) (hv : ∀ i, t ≠ .var i)
    (happ : ∀ n ts, t ≠ .app n ts) (htm : isMember t = true) {i : Nat} (hi : i ∈ varsOf t) :
    ∃ p ∈ t.args, i ∈ varsOf p.2 := by
  rw [← paramOccurrences_firsts ht, paramOccurrences_args hv happ, List.mem_map] at hi
  obtain ⟨o, ho, rfl⟩ := hi
  obtain ⟨p, hp, ho⟩ := List.mem_flatMap.mp ho
  have hpn : Normal p.2 := OrderProof.normal_args ht htm _ (List.mem_map_of_mem hp)
  have hfirsts : (childOcc (anchorsArgs t) p.2).map Prod.fst = varsOf p.2 := by
    cases anchorsArgs t
    · exact paramOccurrences_firsts hpn
    · exact (anchorOcc_firsts p.2).trans (paramOccurrences_firsts hpn)
  refine ⟨p, hp, ?_⟩
  rw [← hfirsts]
  exact List.mem_map_of_mem ho

/-- It is a step of `matchB_complete`, and `recovers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem prod_left_cands (τ σ : Subst) (v : Variance) {a b : Ty} (ht : TemplateOK (.prod a b))
    (hc : ∀ c ∈ cands v (.prod a b) (instantiate τ (.prod a b)).normalize,
      sub c.2.2 (instantiate σ (.var c.1)).normalize = true) :
    ∀ c ∈ cands v a (instantiate τ a).normalize,
      sub c.2.2 (instantiate σ (.var c.1)).normalize = true := by
  intro c hcc
  have hvP : ∀ i, Ty.prod a b ≠ .var i := fun _ h => nomatch h
  have huP : ∀ x y, Ty.prod a b ≠ .union x y := fun _ _ h => nomatch h
  have key : ∀ x ∈ (instantiate τ a).normalize.members, ∀ c' ∈ cands v a x,
      sub c'.2.2 (instantiate σ (.var c'.1)).normalize = true := by
    intro x hx c' hc'
    obtain ⟨y, hxy⟩ := prod_member_left (instantiate τ a) (instantiate τ b) hx
    refine hc c' ((cands_mem_members v hvP huP _ c').mpr ⟨.prod x y, hxy, ?_⟩)
    show c' ∈ cands v a x ++ cands v b y
    exact List.mem_append_left _ hc'
  rcases var_or_ne a with ⟨j, rfl⟩ | hva
  · rw [cands_var, List.mem_singleton] at hcc
    rw [hcc]
    show sub (instantiate τ (.var j)).normalize (instantiate σ (.var j)).normalize = true
    apply (OrderProof.sub_iff_members sub_trans _ _).mpr
    intro x hx
    have hxs := key x hx (j, v, x) (by rw [cands_var]; exact List.mem_singleton_self _)
    exact (OrderProof.sub_member_right_iff x _ (members_isMember hx)).mp hxs
  · cases hcl : closed a with
    | true =>
      rw [cands_closed v a _ hcl] at hcc
      exact absurd hcc List.not_mem_nil
    | false =>
      have haOK : TemplateOK a := ht.args rfl (.co, a) List.mem_cons_self
      obtain ⟨hua, -, -, -⟩ := haOK.head hcl hva
      obtain ⟨x, hx, hcx⟩ := (cands_mem_members v hva hua _ c).mp hcc
      exact key x hx c hcx

/-- It is a step of `matchB_complete`, and `recovers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem prod_right_cands (τ σ : Subst) (v : Variance) {a b : Ty} (ht : TemplateOK (.prod a b))
    (hc : ∀ c ∈ cands v (.prod a b) (instantiate τ (.prod a b)).normalize,
      sub c.2.2 (instantiate σ (.var c.1)).normalize = true) :
    ∀ c ∈ cands v b (instantiate τ b).normalize,
      sub c.2.2 (instantiate σ (.var c.1)).normalize = true := by
  intro c hcc
  have hvP : ∀ i, Ty.prod a b ≠ .var i := fun _ h => nomatch h
  have huP : ∀ x y, Ty.prod a b ≠ .union x y := fun _ _ h => nomatch h
  have key : ∀ y ∈ (instantiate τ b).normalize.members, ∀ c' ∈ cands v b y,
      sub c'.2.2 (instantiate σ (.var c'.1)).normalize = true := by
    intro y hy c' hc'
    obtain ⟨x, hxy⟩ := prod_member_right (instantiate τ a) (instantiate τ b) hy
    refine hc c' ((cands_mem_members v hvP huP _ c').mpr ⟨.prod x y, hxy, ?_⟩)
    show c' ∈ cands v a x ++ cands v b y
    exact List.mem_append_right _ hc'
  rcases var_or_ne b with ⟨j, rfl⟩ | hvb
  · rw [cands_var, List.mem_singleton] at hcc
    rw [hcc]
    show sub (instantiate τ (.var j)).normalize (instantiate σ (.var j)).normalize = true
    apply (OrderProof.sub_iff_members sub_trans _ _).mpr
    intro y hy
    have hys := key y hy (j, v, y) (by rw [cands_var]; exact List.mem_singleton_self _)
    exact (OrderProof.sub_member_right_iff y _ (members_isMember hy)).mp hys
  · cases hcl : closed b with
    | true =>
      rw [cands_closed v b _ hcl] at hcc
      exact absurd hcc List.not_mem_nil
    | false =>
      have hbOK : TemplateOK b :=
        ht.args rfl (.co, b) (List.mem_cons_of_mem _ List.mem_cons_self)
      obtain ⟨hub, -, -, -⟩ := hbOK.head hcl hvb
      obtain ⟨y, hy, hcy⟩ := (cands_mem_members v hvb hub _ c).mp hcc
      exact key y hy c hcy

/-- It is a step of `matchB_complete`, and `recovers` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem prod_or_not (t : Ty) : (∃ a b, t = .prod a b) ∨ ∀ a b, t ≠ .prod a b := by
  cases t
  case prod a b => exact Or.inl ⟨a, b, rfl⟩
  all_goals exact Or.inr fun _ _ h => nomatch h

/-- It is a step of `matchB_complete`, and `matchB_complete` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem recovers (τ σ : Subst) (n : Nat) : ∀ (t : Ty) (v : Variance), sizeOf t < n →
    TemplateOK t →
    (∀ c ∈ cands v t (instantiate τ t).normalize,
      sub c.2.2 (instantiate σ (.var c.1)).normalize = true) →
    ∀ i ∈ varsOf t,
      sub (instantiate τ (.var i)).normalize (instantiate σ (.var i)).normalize = true := by
  induction n with
  | zero => exact fun _ _ hn => absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro t v hn ht hc i hi
    rcases var_or_ne t with ⟨j, rfl⟩ | hv
    · rw [varsOf, List.mem_singleton] at hi
      rw [hi]
      exact hc (j, v, _) (by rw [cands_var]; exact List.mem_singleton_self _)
    cases hcl : closed t with
    | true =>
      rw [varsOf_eq_nil_of_closed t hcl] at hi
      exact absurd hi List.not_mem_nil
    | false =>
      obtain ⟨hu, happ, hargs, htm⟩ := ht.head hcl hv
      rcases prod_or_not t with ⟨a, b, rfl⟩ | hp'
      · have hsize := Ty.prod.sizeOf_spec a b
        rw [varsOf, List.mem_append] at hi
        rcases hi with hi | hi
        · exact ih a v (by omega) (ht.args rfl (.co, a) List.mem_cons_self)
            (prod_left_cands τ σ v ht hc) i hi
        · exact ih b v (by omega)
            (ht.args rfl (.co, b) (List.mem_cons_of_mem _ List.mem_cons_self))
            (prod_right_cands τ σ v ht hc) i hi
      · obtain ⟨p, hp, hip⟩ := mem_varsOf_args ht.normal hv happ htm hi
        have hsize : sizeOf p.2 < sizeOf t := sizeOf_args hp
        obtain ⟨-, htmS, hmargs⟩ := instance_shape τ ht.normal hv hu happ hp' hargs
        refine ih p.2 (comp v p.1) (by omega) (ht.args htm p hp) (fun c hcc => hc c ?_) i hip
        rw [cands_args v hv happ (OrderProof.normal_headCanon ht.normal)
          (OrderProof.normal_headCanon (normal_normalize _)) htmS, hmargs]
        exact List.mem_flatMap.mpr ⟨(p, (p.1, (instantiate τ p.2).normalize)),
          mem_zip_self_map _ hp, hcc⟩

/-- It is a step of `matchB_complete`, and `matchB_complete` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem covers (τ σ : Subst)
    (hστ : ∀ i, sub (instantiate σ (.var i)).normalize (instantiate τ (.var i)).normalize = true)
    (n : Nat) : ∀ (r t : Ty) (v : Variance), sizeOf r < n → TemplateOK t → Normal r →
      sub r (instantiate τ t).normalize = true →
      (∀ c ∈ cands v t r, sub c.2.2 (instantiate σ (.var c.1)).normalize = true) →
      sub r (instantiate σ t).normalize = true := by
  induction n with
  | zero => exact fun _ _ _ hn => absurd hn (Nat.not_lt_zero _)
  | succ n ih =>
    intro r t v hn ht hr hsub hc
    rcases var_or_ne t with ⟨i, rfl⟩ | hv
    · exact hc (i, v, r) (by rw [cands_var]; exact List.mem_singleton_self _)
    cases hcl : closed t with
    | true =>
      rw [instantiate_closed σ t hcl]
      rw [instantiate_closed τ t hcl] at hsub
      exact hsub
    | false =>
      obtain ⟨hu, happ, hargs, htm⟩ := ht.head hcl hv
      cases hrm : isMember r with
      | false =>
        rcases isMember_eq_false hrm with rfl | ⟨c1, d1, rfl⟩
        · exact OrderProof.sub_never _
        · obtain ⟨hc1, hd1, -, -⟩ := normal_union_inv hr
          have hall := (OrderProof.sub_iff_members sub_trans _ _).mp hsub
          have hsize := Ty.union.sizeOf_spec c1 d1
          rw [cands_union_right v hv hu] at hc
          have h1 := ih c1 t v (by omega) ht hc1
            ((OrderProof.sub_iff_members sub_trans _ _).mpr fun x hx =>
              hall x (List.mem_append_left _ hx))
            (fun c hcc => hc c (List.mem_append_left _ hcc))
          have h2 := ih d1 t v (by omega) ht hd1
            ((OrderProof.sub_iff_members sub_trans _ _).mpr fun x hx =>
              hall x (List.mem_append_right _ hx))
            (fun c hcc => hc c (List.mem_append_right _ hcc))
          apply (OrderProof.sub_iff_members sub_trans _ _).mpr
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact (OrderProof.sub_iff_members sub_trans _ _).mp h1 x hx
          · exact (OrderProof.sub_iff_members sub_trans _ _).mp h2 x hx
      | true =>
        obtain ⟨hh, hkids⟩ := below_args τ ht.normal hv hu happ hargs hr hrm hsub
        rw [cands_args v hv happ (OrderProof.normal_headCanon ht.normal)
          (OrderProof.normal_headCanon hr) hh] at hc
        have hchild : ∀ p ∈ t.args.zip r.args,
            sub p.2.2 (instantiate σ p.1.2).normalize = true ∧
              (p.1.1 = .inv → p.2.2 = (instantiate σ p.1.2).normalize) := by
          intro p hp
          obtain ⟨hpn, hpinv, hpsub⟩ := hkids p hp
          have hpOK := ht.args htm p.1 (List.of_mem_zip hp).1
          have hsize : sizeOf p.2.2 < sizeOf r := sizeOf_args (List.of_mem_zip hp).2
          have hcp : ∀ c ∈ cands (comp v p.1.1) p.1.2 p.2.2,
              sub c.2.2 (instantiate σ (.var c.1)).normalize = true :=
            fun c hcc => hc c (List.mem_flatMap.mpr ⟨p, hp, hcc⟩)
          refine ⟨ih p.2.2 p.1.2 _ (by omega) hpOK hpn hpsub hcp, fun hinv => ?_⟩
          have he := hpinv hinv
          rw [he] at hcp
          have hrec := recovers τ σ (sizeOf p.1.2 + 1) p.1.2 _ (Nat.lt_succ_self _) hpOK hcp
          rw [he]
          exact normalize_instantiate_congr p.1.2 fun i hi =>
            OrderProof.sub_antisymm_normal sub_trans _ _ (normal_normalize _) (normal_normalize _)
              (hrec i hi) (hστ i)
        rcases prod_or_not t with ⟨a, b, rfl⟩ | hp'
        · cases r <;> simp only [sameHead, Bool.false_eq_true] at hh
          rename_i r1 r2
          have h1 := (hchild ((.co, a), (.co, r1)) List.mem_cons_self).1
          have h2 := (hchild ((.co, b), (.co, r2)) (List.mem_cons_of_mem _ List.mem_cons_self)).1
          exact above_prod σ hr h1 h2
        · refine above_args σ ht.normal hv hu happ hp' hargs hrm hh fun p hp => ?_
          obtain ⟨hs, hi⟩ := hchild p hp
          rcases args_co_or_inv happ p.1 (List.of_mem_zip hp).1 with hco | hinv
          · rw [hco]
            exact hs
          · rw [hinv, ← hi hinv]
            show (sub p.2.2 p.2.2 && sub p.2.2 p.2.2) = true
            rw [sub_refl]
            rfl

/-- **The match by bounds is complete**: a normal request below some instance of the template has
a match. The template is normal, admissible and holds no nominal reference. No premise asks where
a parameter first occurs, and none asks where `never` stands: `Ty.anchored` and `Ty.bottomFree`
(`src/Effect4/Laws/Program/Template.lean`) are not premises. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_complete (seed : Subst) {t r : Ty} (ht : TemplateOK t) (hr : Normal r) {τ : Subst}
    (hseed : ∀ j u, seed.lookup j = some u → (instantiate τ (.var j)).normalize = u.normalize)
    (hτ : sub r (instantiate τ t).normalize = true) : ∃ σ, matchB seed t r = some σ := by
  have hb := solve_between seed (cands .co t r) τ hseed
    (cands_below τ (sizeOf r + 1) r t .co (Nat.lt_succ_self _) (fun h => nomatch h) ht hr hτ)
  refine ⟨solve seed (cands .co t r), ?_⟩
  unfold matchB
  dsimp only
  rw [hr.fixed, if_pos]
  exact covers τ _ hb.1 (sizeOf r + 1) r t .co (Nat.lt_succ_self _) ht hr hτ hb.2

/-- **The match of an argument list is complete**: normal arguments that some bindings place
below their parameters' instances have a match. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_complete {ps rs : List Ty} (hlen : ps.length = rs.length)
    (hps : ∀ p ∈ ps, TemplateOK p) (hrs : ∀ r ∈ rs, Normal r) {τ : Subst}
    (hτ : Admits τ ps rs) : ∃ σ, matchArgsB ps rs = some σ := by
  have hb := solve_between [] (candsList ps rs) τ (fun _ _ hj => nomatch hj)
    (candsList_below τ hps hrs hτ)
  refine ⟨solve [] (candsList ps rs), ?_⟩
  unfold matchArgsB
  rw [if_pos hlen]
  dsimp only
  rw [if_pos]
  rw [List.all_eq_true]
  intro pr hpr
  have hrn := hrs pr.2 (List.of_mem_zip hpr).2
  have hsub := hτ pr hpr
  rw [hrn.fixed] at hsub
  rw [hrn.fixed]
  exact covers τ _ hb.1 (sizeOf pr.2 + 1) pr.2 pr.1 .co (Nat.lt_succ_self _)
    (hps pr.1 (List.of_mem_zip hpr).1) hrn hsub
    fun c hcc => hb.2 c (List.mem_flatMap.mpr ⟨pr, hpr, hcc⟩)

/-! ## Monotone: the template's share of `checker-monotone` -/

/-- **The match of an argument list is monotone.** Smaller arguments, in the checker's order, have
a match too, and its bindings are smaller at every parameter. It follows from the complete match
and the least bindings. An answer that reads a parameter covariantly is then smaller; an answer
that reads one invariantly (`Ref.make`'s cell) is not ordered, which no rule of a template
repairs. -/
@[semantics "subtyping-algebra" (requirement := R14)]
theorem matchArgsB_monotone {ps rs rs' : List Ty} {σ : Subst} (h : matchArgsB ps rs = some σ)
    (hps : ∀ p ∈ ps, TemplateOK p) (hrs' : ∀ r ∈ rs', Normal r) (hlen : rs'.length = rs.length)
    (hle : ∀ rr ∈ rs'.zip rs, subN rr.1 rr.2 = true) :
    ∃ σ', matchArgsB ps rs' = some σ' ∧
      ∀ i, subN (instantiate σ' (.var i)) (instantiate σ (.var i)) = true := by
  obtain ⟨hl, hσ⟩ := matchArgsB_sound h
  have hσ' : Admits σ ps rs' := by
    intro pr hpr
    obtain ⟨r, hpr0, hrr⟩ := mem_zip_middle hl hlen hpr
    exact sub_trans _ _ _ (hle (pr.2, r) hrr) (hσ (pr.1, r) hpr0)
  obtain ⟨σ', hm⟩ := matchArgsB_complete (hl.trans hlen.symm) hps hrs' hσ'
  exact ⟨σ', hm, matchArgsB_least hm hps hrs' hσ'⟩

/-! ## The match reads a request up to the normal form -/

/-- The match by bounds of an argument list at the arguments' normal forms. -/
def matchArgsN (ps rs : List Ty) : Option Subst := matchArgsB ps (rs.map Ty.normalize)

/-- The match by bounds of one request at its normal form. -/
def matchN (seed : Subst) (t r : Ty) : Option Subst := matchB seed t r.normalize

/-- **Two requests with one normal form have one match.** -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchN_congr (seed : Subst) (t : Ty) {r r' : Ty} (h : r.normalize = r'.normalize) :
    matchN seed t r = matchN seed t r' := by
  unfold matchN
  rw [h]

/-- It is a step of `matchArgsN_complete`, and `matchArgsN_complete` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem admits_normalize {τ : Subst} {ps rs : List Ty} (h : Admits τ ps rs) :
    Admits τ ps (rs.map Ty.normalize) := by
  intro pr hpr
  rw [List.zip_map_right, List.mem_map] at hpr
  obtain ⟨qr, hqr, rfl⟩ := hpr
  have hq := h qr hqr
  show sub qr.2.normalize.normalize (instantiate τ qr.1).normalize = true
  rw [normalize_idem]
  exact hq

/-- **At the normal form the match is complete for every request**: arguments of any raw form
that some bindings place below their parameters' instances have a match. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsN_complete {ps rs : List Ty} (hlen : ps.length = rs.length)
    (hps : ∀ p ∈ ps, TemplateOK p) {τ : Subst} (hτ : Admits τ ps rs) :
    ∃ σ, matchArgsN ps rs = some σ :=
  matchArgsB_complete (by rw [List.length_map]; exact hlen) hps
    (fun r hr => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hr
      exact normal_normalize x)
    (admits_normalize hτ)

/-- **At the normal form the match answers the least bindings, for every request.** -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsN_least {ps rs : List Ty} {σ : Subst} (h : matchArgsN ps rs = some σ)
    (hps : ∀ p ∈ ps, TemplateOK p) {τ : Subst} (hτ : Admits τ ps rs) :
    ∀ i, subN (instantiate σ (.var i)) (instantiate τ (.var i)) = true :=
  matchArgsB_least h hps
    (fun r hr => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp hr
      exact normal_normalize x)
    (admits_normalize hτ)

/-- It is a step of `matchArgsB_least`, and `candsList_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem candsList_cons (p : Ty) (ps : List Ty) (r : Ty) (rs : List Ty) :
    candsList (p :: ps) (r :: rs) = cands .co p r ++ candsList ps rs := by
  unfold candsList
  rw [List.zip_cons_cons, List.flatMap_cons]

/-! ## The rule's first case is a consequence, not a case of the function

`solve` reads a candidate's polarity for one test: a contravariant candidate is no lower bound
(`lowers`). It has no case for an invariant occurrence. That the match still "fixes" a parameter at
an invariant occurrence is the guard's doing: below an invariant position a request's child IS
the instance's child in normal form (`below_args`, at the match's own bindings by `matchB_sound`).
The statement below is that fact at a cell. -/

/-- **At a cell the match binds the cell's own content**, up to the normal form. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_cell_fixed {seed σ : Subst} {i : Nat} {c : Ty}
    (h : matchB seed (.refOf (.var i)) (.refOf c) = some σ) :
    (instantiate σ (.var i)).normalize = c.normalize := by
  have hs := (matchB_sound h).1
  have hs' : sub (.refOf c.normalize) (.refOf (instantiate σ (.var i)).normalize) = true := hs
  rw [sub_args_refOf] at hs'
  simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons, List.all_nil,
    Bool.and_true, Bool.and_eq_true] at hs'
  exact OrderProof.sub_antisymm_normal sub_trans _ _ (normal_normalize _) (normal_normalize _)
    hs'.2 hs'.1

/-! ## Every template of the tree is in the laws' reach -/

/-- The reach as a check: the type is its own normal form, admissible, and holds no nominal
reference. -/
def templateOKb (t : Ty) : Bool := decide (t.normalize = t) && t.templateAdmissible && noApp t

@[semantics "subtyping-algebra" (requirement := R4)]
theorem templateOK_of (t : Ty) (h : templateOKb t = true) : TemplateOK t := by
  simp only [templateOKb, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1 ▸ normal_normalize t, h.1.2, h.2⟩

/-- It is a step of `TermIntro`, and `nativeAtomTy_ite_above` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem join_eq_right_of_subN {a b : Ty} (ha : sub a.normalize b.normalize = true) (hb : Normal b) :
    Ty.join a b = b := by
  have hl : subN (Ty.join a b) b = true := subN_join_least ha (subN_refl b)
  have hr : subN b (Ty.join a b) = true := subN_join_right a b
  rw [subN, normalize_join, hb.fixed] at hl hr
  exact OrderProof.sub_antisymm_normal sub_trans (Ty.join a b) b
    (normal_normalize _) hb hl hr

/-- It is a step of `TermIntro`, and `nativeAtomTy_ite_below` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem join_eq_left_of_subN {a b : Ty} (hb : sub b.normalize a.normalize = true) (ha : Normal a) :
    Ty.join a b = a := by
  rw [join_comm]
  exact join_eq_right_of_subN hb ha

/-- It is a step of `matchArgsB_one_var`, and `matchArgsB_one_var` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem candsList_nil : candsList [] [] = [] := rfl

/-- It is a step of `TermIntro`, and `Checking` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_one_var (X : Ty) : matchArgsB [.var 0] [X] = some [(0, X)] := by
  dsimp only [matchArgsB]
  rw [candsList_cons, candsList_nil, cands_var, List.append_nil]
  have hs : solve [] [(0, .co, X)] = [(0, X)] := rfl
  rw [hs]
  have hlen : [Ty.var 0].length = [X].length := rfl
  rw [if_pos hlen]
  have hsub : sub X.normalize X.normalize = true := sub_refl _
  have hcond : (([Ty.var 0].zip [X]).all fun pr =>
      pr.snd.normalize.sub (instantiate [(0, X)] pr.fst).normalize) = true := by
    change (sub X.normalize (instantiate [(0, X)] (.var 0)).normalize && true) = true
    have h0 : instantiate [(0, X)] (.var 0) = X := rfl
    rw [h0, hsub]
    rfl
  rw [hcond]
  rfl

/-- It is a step of `TermIntro`, and `Checking` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_two_vars (X Y : Ty) : matchArgsB [.var 0, .var 1] [X, Y] = some [(0, X), (1, Y)] := by
  dsimp only [matchArgsB]
  rw [candsList_cons, cands_var, candsList_cons, cands_var, candsList_nil, List.append_nil,
    List.cons_append, List.nil_append]
  have hs : solve [] [(0, .co, X), (1, .co, Y)] = [(0, X), (1, Y)] := rfl
  rw [hs]
  have hlen : [Ty.var 0, Ty.var 1].length = [X, Y].length := rfl
  rw [if_pos hlen]
  have hsubX : sub X.normalize X.normalize = true := sub_refl _
  have hsubY : sub Y.normalize Y.normalize = true := sub_refl _
  have hcond : (([Ty.var 0, Ty.var 1].zip [X, Y]).all fun pr =>
      pr.snd.normalize.sub (instantiate [(0, X), (1, Y)] pr.fst).normalize) = true := by
    change (sub X.normalize (instantiate [(0, X), (1, Y)] (.var 0)).normalize &&
      (sub Y.normalize (instantiate [(0, X), (1, Y)] (.var 1)).normalize && true)) = true
    have h0 : instantiate [(0, X), (1, Y)] (.var 0) = X := rfl
    have h1 : instantiate [(0, X), (1, Y)] (.var 1) = Y := rfl
    rw [h0, h1, hsubX, hsubY]
    rfl
  rw [hcond]
  rfl

/-- It is a step of `TermIntro`, and `Checking` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_list_var_nat (X : Ty) : matchArgsB [.list (.var 0), .nat] [.list X, .nat] = some [(0, X)] := by
  dsimp only [matchArgsB]
  rw [candsList_cons, cands, cands_var, candsList_cons, cands_closed .co .nat .nat rfl, candsList_nil, List.append_nil,
    List.cons_append, List.nil_append]
  have hs : solve [] [(0, .co, X)] = [(0, X)] := rfl
  rw [hs]
  have hlen : [Ty.list (.var 0), Ty.nat].length = [Ty.list X, Ty.nat].length := rfl
  rw [if_pos hlen]
  have hsubX : sub (Ty.list X).normalize (Ty.list X).normalize = true := sub_refl _
  have hsubN : sub Ty.nat.normalize Ty.nat.normalize = true := sub_refl _
  have hcond : (([Ty.list (.var 0), Ty.nat].zip [Ty.list X, Ty.nat]).all fun pr =>
      pr.snd.normalize.sub (instantiate [(0, X)] pr.fst).normalize) = true := by
    change (sub (Ty.list X).normalize (instantiate [(0, X)] (Ty.list (.var 0))).normalize &&
      (sub Ty.nat.normalize (instantiate [(0, X)] Ty.nat).normalize && true)) = true
    have h0 : instantiate [(0, X)] (Ty.list (.var 0)) = Ty.list X := rfl
    have h1 : instantiate [(0, X)] Ty.nat = Ty.nat := rfl
    rw [h0, h1, hsubX, hsubN]
    rfl
  rw [hcond]
  rfl

/-- It is a step of `TermIntro`, and `nativeAtomTy_append` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_append (X : Ty) (canonical : X.normalize = X) :
    matchArgsB [.list (.var 0), .list (.var 0)] [.list X, .list X] = some [(0, Ty.join X X), (0, Ty.join X X)] := by
  dsimp only [matchArgsB]
  rw [candsList_cons, cands, cands_var, candsList_cons, cands, cands_var, candsList_nil, List.append_nil,
    List.cons_append, List.nil_append]
  have hs : solve [] [(0, .co, X), (0, .co, X)] = [(0, Ty.join X X), (0, Ty.join X X)] := rfl
  rw [hs]
  have hlen : [Ty.list (.var 0), Ty.list (.var 0)].length = [Ty.list X, Ty.list X].length := rfl
  rw [if_pos hlen]
  have hj : Ty.join X X = X := by rw [join_self, canonical]
  have hinst : instantiate [(0, Ty.join X X), (0, Ty.join X X)] (Ty.list (.var 0)) = Ty.list X := by
    dsimp only [instantiate, List.lookup]
    rw [hj]
    rfl
  have hsubX : sub (Ty.list X).normalize (Ty.list X).normalize = true := sub_refl _
  have hcond : (([Ty.list (.var 0), Ty.list (.var 0)].zip [Ty.list X, Ty.list X]).all fun pr =>
      pr.snd.normalize.sub (instantiate [(0, Ty.join X X), (0, Ty.join X X)] pr.fst).normalize) = true := by
    change (sub (Ty.list X).normalize (instantiate [(0, Ty.join X X), (0, Ty.join X X)] (Ty.list (.var 0))).normalize &&
      (sub (Ty.list X).normalize (instantiate [(0, Ty.join X X), (0, Ty.join X X)] (Ty.list (.var 0))).normalize && true)) = true
    rw [hinst, hsubX]
    rfl
  rw [hcond]
  rfl

/-- It is a step of `TermIntro`, and `Checking` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_cons_nil {X : Ty} (canonical : X.normalize = X) :
    matchArgsB [.var 0, .list (.var 0)] [X, .list .never] = some [(0, Ty.join X .never), (0, Ty.join X .never)] := by
  dsimp only [matchArgsB]
  rw [candsList_cons, cands_var, candsList_cons, cands, cands_var, candsList_nil, List.append_nil,
    List.cons_append, List.nil_append]
  have hs : solve [] [(0, .co, X), (0, .co, .never)] = [(0, Ty.join X .never), (0, Ty.join X .never)] := rfl
  rw [hs]
  have hlen : [Ty.var 0, Ty.list (.var 0)].length = [X, Ty.list .never].length := rfl
  rw [if_pos hlen]
  have hj : Ty.join X .never = X := by rw [join_never_right, canonical]
  have hinst0 : instantiate [(0, Ty.join X .never), (0, Ty.join X .never)] (.var 0) = X := by
    dsimp only [instantiate, List.lookup]
    rw [hj]
    rfl
  have hinst1 : instantiate [(0, Ty.join X .never), (0, Ty.join X .never)] (Ty.list (.var 0)) = Ty.list X := by
    dsimp only [instantiate, List.lookup]
    rw [hj]
    rfl
  have hsubX : sub X.normalize X.normalize = true := sub_refl _
  have hsubN : sub (Ty.list .never).normalize (Ty.list X).normalize = true := by
    have hn1 : (Ty.list .never : Ty).normalize = Ty.list .never := rfl
    have hn2 : (Ty.list X : Ty).normalize = Ty.list X := by
      change Ty.list X.normalize = Ty.list X
      rw [canonical]
    rw [hn1, hn2, sub_args_list]
    simp only [argsBelow, args, Variance.holds, List.zip, List.zipWith, List.all_cons,
      List.all_nil, Bool.and_true, OrderProof.sub_never]
  have hcond : (([Ty.var 0, Ty.list (.var 0)].zip [X, Ty.list .never]).all fun pr =>
      pr.snd.normalize.sub (instantiate [(0, Ty.join X .never), (0, Ty.join X .never)] pr.fst).normalize) = true := by
    change (sub X.normalize (instantiate [(0, Ty.join X .never), (0, Ty.join X .never)] (.var 0)).normalize &&
      (sub (Ty.list .never).normalize (instantiate [(0, Ty.join X .never), (0, Ty.join X .never)] (Ty.list (.var 0))).normalize && true)) = true
    rw [hinst0, hinst1, hsubX, hsubN]
    rfl
  rw [hcond]
  rfl

/-- It is a step of `TermIntro`, and `nativeAtomTy_ite` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchArgsB_ite (X Y : Ty) :
    matchArgsB [.bool, .var 0, .var 0] [.bool, X, Y] = some [(0, Ty.join X Y), (0, Ty.join X Y)] := by
  dsimp only [matchArgsB]
  rw [candsList_cons, cands_closed .co .bool .bool rfl, candsList_cons, cands_var, candsList_cons, cands_var, candsList_nil, List.append_nil,
    List.nil_append, List.cons_append, List.nil_append]
  have hs : solve [] [(0, .co, X), (0, .co, Y)] = [(0, Ty.join X Y), (0, Ty.join X Y)] := rfl
  rw [hs]
  have hlen : [Ty.bool, Ty.var 0, Ty.var 0].length = [Ty.bool, X, Y].length := rfl
  rw [if_pos hlen]
  have hinst : instantiate [(0, Ty.join X Y), (0, Ty.join X Y)] (.var 0) = Ty.join X Y := by
    dsimp only [instantiate, List.lookup]
    rfl
  have hsubB : sub Ty.bool.normalize Ty.bool.normalize = true := sub_refl _
  have hsubX : sub X.normalize (Ty.join X Y).normalize = true := subN_join_left X Y
  have hsubY : sub Y.normalize (Ty.join X Y).normalize = true := subN_join_right X Y
  have hcond : (([Ty.bool, Ty.var 0, Ty.var 0].zip [Ty.bool, X, Y]).all fun pr =>
      pr.snd.normalize.sub (instantiate [(0, Ty.join X Y), (0, Ty.join X Y)] pr.fst).normalize) = true := by
    change (sub Ty.bool.normalize (instantiate [(0, Ty.join X Y), (0, Ty.join X Y)] Ty.bool).normalize &&
      (sub X.normalize (instantiate [(0, Ty.join X Y), (0, Ty.join X Y)] (.var 0)).normalize &&
      (sub Y.normalize (instantiate [(0, Ty.join X Y), (0, Ty.join X Y)] (.var 0)).normalize && true))) = true
    have hinstB : instantiate [(0, Ty.join X Y), (0, Ty.join X Y)] Ty.bool = Ty.bool := rfl
    rw [hinstB, hinst, hsubB, hsubX, hsubY]
    rfl
  rw [hcond]
  rfl

/-- It is a step of `Waiting`, and `TypedScope` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_one_var (X : Ty) : matchB [] (.var 0) X = some [(0, X)] := by
  dsimp only [matchB]
  rw [cands_var]
  have hs : solve [] [(0, .co, X)] = [(0, X)] := rfl
  rw [hs]
  have hsub : sub X.normalize X.normalize = true := sub_refl _
  have hinst : instantiate [(0, X)] (.var 0) = X := rfl
  rw [hinst, hsub]
  rfl

/-- It is a step of `Waiting`, and `TypedScope` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_refOf_var (X : Ty) : matchB [] (.refOf (.var 0)) (.refOf X) = some [(0, X)] := by
  dsimp only [matchB]
  rw [cands, comp_inv, cands_var]
  change (let σ := solve [] [(0, .inv, X)];
    if sub (Ty.refOf X).normalize (instantiate σ (Ty.refOf (.var 0))).normalize then some σ else none) = some [(0, X)]
  have hs : solve [] [(0, .inv, X)] = [(0, X)] := rfl
  rw [hs]
  dsimp only
  have hsub : sub (Ty.refOf X).normalize (Ty.refOf X).normalize = true := sub_refl _
  have hinst : instantiate [(0, X)] (Ty.refOf (.var 0)) = .refOf X := rfl
  rw [hinst, hsub]
  rfl

/-- It is a step of `Waiting`, and `answers_refModifyWith_captured` reads it. -/
@[semantics "subtyping-algebra" (requirement := R4)]
theorem matchB_modify_use (C B : Ty) :
    matchB [(0, C)] (.prod (.var 1) (.var 0)) (.prod B C) = some [(0, C), (1, B)] := by
  dsimp only [matchB]
  rw [cands, cands_var, cands_var, List.cons_append, List.nil_append]
  change (let σ := solve [(0, C)] [(1, .co, B), (0, .co, C)];
    if sub (Ty.prod B C).normalize (instantiate σ (Ty.prod (.var 1) (.var 0))).normalize then some σ else none) = some [(0, C), (1, B)]
  have hs : solve [(0, C)] [(1, .co, B), (0, .co, C)] = [(0, C), (1, B)] := rfl
  rw [hs]
  dsimp only
  have hsub : sub (Ty.prod B C).normalize (Ty.prod B C).normalize = true := sub_refl _
  have hinst : instantiate [(0, C), (1, B)] (Ty.prod (.var 1) (.var 0)) = .prod B C := rfl
  rw [hinst, hsub]
  rfl

end Effect4.Program.Bounds


