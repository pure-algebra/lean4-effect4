import Effect4.Program.TyDecls
import Effect4.Laws.Program.Admits
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Typed.Membership
import Effect4.Laws.Auto.Semantics

/-!
# Laws of the declaration table: membership as a least fixed point

The table (`Program/TyDecls.lean`, decisions rows 124, 158 and 400) is a system of type
equations, read iso-recursively. This module holds its membership judgment and its laws. The
formal note is `docs/research/2026-10-15-recursive-types/formal.md`.

- `MemberIn`: membership under a table, an inductive predicate. A union holds its sides'
  members, a declared reference holds its body's members, and a value whose shape fits a head
  holds there when every question of the step holds (`Val.obligations`). It is the least
  relation closed under these rules, so a value fits a declared name only through a finite
  derivation.
- `hasTyIn_iff`: the checker decides it, on every table, guarded or not.
- `memberIn_unfold_iff`: a reference to a declared name has exactly its body's members.
- `tyDecls_conservative`: on the empty table the checker, the predicate and inhabitance are
  `Val.hasTy`, its answer and `inhabited`.
- `memberIn_iff_cata`: the predicate is the admission fold (`Val.hasTy.alg`) with each declared
  name read from the checker (`declAlg`, `checkerOracle`). So the order's fold condition applies,
  and `memberIn_sub`: the unchanged `Ty.sub` is sound for membership under every table.
- `inhabited_of_memberIn`: the least fixed point of inhabitance is sound against membership.

Placement of the claims (`AGENTS.md`, five points), shared by every theorem below:

1. Concept `store-typing` (concept 1 of `docs/core/semantics.md`), the property that membership
   is a judgment with a decision procedure, closed under the order and invariant under
   normalization, with inhabitance as its emptiness test.
2. Questions: the registry claims `recursive-types-decided` (`hasTyIn_iff`),
   `recursive-types-unfold` (`memberIn_unfold_iff`), `recursive-types-conservative`
   (`tyDecls_conservative`), `recursive-types-sub` (`memberIn_sub`), `recursive-types-inhabited`
   (`inhabited_iff_memberIn`, modulo the goal `exists_memberIn_of_inhabited`),
   `recursive-types-normalize` (the goal `memberIn_normalize`) and `guarded-fixed-point-unique`
   (the goal `guarded_fixedPoint_unique`).
3. Reach: the shape judgment `Val.hasTy` and its allocation table, extended by a monomorphic
   table; every value, every type and every table. Decisions rows 124, 158 and 400 bound it.
4. Does not establish: anything of `Fits`, the world, or a store; formation of a table; a
   parameter; anything of a target. The checker is decided against `MemberIn`, not against a
   host's validator.
5. Unlocks: R3's open part on recursive types. The wiring slice extends `Fits` and the checker's
   callers by the same rules, and these laws are the statements it must keep.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-! ## Membership under a table, as an inductive predicate -/

/-- **Membership under a declaration table**: the least relation closed under four rules. -/
inductive MemberIn (decls : TyDecls) (allocated : List String) : Val → Ty → Prop
  /-- A member of a union's left side is a member of the union. -/
  | left {v : Val} {l r : Ty} : MemberIn decls allocated v l → MemberIn decls allocated v (.union l r)
  /-- A member of a union's right side is a member of the union. -/
  | right {v : Val} {l r : Ty} : MemberIn decls allocated v r → MemberIn decls allocated v (.union l r)
  /-- A member of a declared name's body is a member of every reference to the name. -/
  | unfold {v : Val} {t : Ty} {name : String} {body : Ty} :
      decls.unfold? t = some (name, body) → MemberIn decls allocated v body →
      MemberIn decls allocated v t
  /-- A value whose shape fits a head, with every question of the step answered. -/
  | step {v : Val} {t : Ty} {ps : List (Val × Ty)} :
      decls.unfold? t = none → Val.obligations v t allocated = some ps →
      (∀ p ∈ ps, MemberIn decls allocated p.1 p.2) → MemberIn decls allocated v t

/-! ## The heads: a union's members -/

/-- A declared reference is a union member: it is neither `never` nor a union. -/
theorem TyDecls.isMember_of_unfold? {decls : TyDecls} {t : Ty} {x : String × Ty}
    (h : decls.unfold? t = some x) : t.isMember = true := by
  cases t
  case never => cases h
  case union => cases h
  all_goals rfl

/-- A head with a step is a union member: `never` and a union have none. -/
theorem Val.isMember_of_obligations {v : Val} {t : Ty} {allocated : List String}
    {ps : List (Val × Ty)} (h : Val.obligations v t allocated = some ps) : t.isMember = true := by
  cases t
  case never => cases h
  case union => cases h
  all_goals rfl

/-- Membership at a union member is membership at the union. -/
theorem MemberIn.of_mem_members {decls : TyDecls} {allocated : List String} {v : Val} {t m : Ty}
    (hm : m ∈ t.members) (h : MemberIn decls allocated v m) : MemberIn decls allocated v t := by
  induction t with
  | union l r ihl ihr =>
    rcases List.mem_append.mp hm with hm | hm
    · exact .left (ihl hm)
    · exact .right (ihr hm)
  | never => exact absurd hm List.not_mem_nil
  | _ =>
    simp only [Ty.members, List.mem_singleton] at hm
    subst hm
    exact h

/-! ## The checker's step -/

/-- **The checker's equation**, read as a proposition: some union member either unfolds a
declared name not yet seen, or answers every question of its step. -/
theorem hasTyIn_eq_true_iff {decls : TyDecls} {seen : List String} {v : Val} {t : Ty}
    {allocated : List String} :
    Val.hasTyIn decls seen v t allocated = true ↔ ∃ m ∈ t.members,
      (∃ name body, decls.unfold? m = some (name, body) ∧ seen.contains name = false ∧
        Val.hasTyIn decls (name :: seen) v body allocated = true) ∨
      (decls.unfold? m = none ∧ ∃ ps, Val.obligations v m allocated = some ps ∧
        ∀ p ∈ ps, Val.hasTyIn decls [] p.1 p.2 allocated = true) := by
  rw [Val.hasTyIn.eq_1, List.any_eq_true]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  split
  · rename_i name body hu
    constructor
    · intro h
      split at h
      · cases h
      · rename_i hs
        exact Or.inl ⟨name, body, hu, Bool.eq_false_iff.mpr hs, h⟩
    · rintro (⟨name', body', hu', hs, h⟩ | ⟨hn, _⟩)
      · rw [hu] at hu'
        cases hu'
        rw [dif_neg (by rw [hs]; exact Bool.false_ne_true)]
        exact h
      · rw [hu] at hn
        cases hn
  · rename_i hu
    constructor
    · intro h
      split at h
      · rename_i ps hps
        refine Or.inr ⟨hu, ps, hps, fun p hp => ?_⟩
        exact List.all_eq_true.mp h ⟨p, hp⟩ (List.mem_attach _ _)
      · cases h
    · rintro (⟨name, body, hu', _, _⟩ | ⟨_, ps, hps, hall⟩)
      · rw [hu] at hu'
        cases hu'
      · split
        · rename_i qs hqs
          rw [hps] at hqs
          cases hqs
          apply List.all_eq_true.mpr
          rintro ⟨p, hp⟩ _
          exact hall p hp
        · rename_i hqs
          rw [hps] at hqs
          cases hqs

/-- A union is checked side by side. -/
theorem hasTyIn_union {decls : TyDecls} {seen : List String} {v : Val} {l r : Ty}
    {allocated : List String} :
    Val.hasTyIn decls seen v (.union l r) allocated =
      (Val.hasTyIn decls seen v l allocated || Val.hasTyIn decls seen v r allocated) := by
  rw [Val.hasTyIn.eq_1, Val.hasTyIn.eq_1, Val.hasTyIn.eq_1]
  simp only [Ty.members, List.any_append]

/-! ## The checker decides the inductive membership, on every table -/

/-- **Sound against `MemberIn`** (from any set of unfolded names): what the checker accepts is
a member. -/
theorem memberIn_of_hasTyIn {decls : TyDecls} {allocated : List String} :
    ∀ (seen : List String) (v : Val) (t : Ty),
      Val.hasTyIn decls seen v t allocated = true → MemberIn decls allocated v t := by
  intro seen v t
  induction seen, v, t using Val.hasTyIn.induct decls allocated with
  | case1 seen v t ihu ihs =>
    intro h
    obtain ⟨m, hm, hcase⟩ := hasTyIn_eq_true_iff.mp h
    refine MemberIn.of_mem_members hm ?_
    rcases hcase with ⟨name, body, hu, hs, hb⟩ | ⟨hu, ps, hps, hall⟩
    · exact .unfold hu (ihu m name body hu (by rw [hs]; exact Bool.false_ne_true) hb)
    · exact .step hu hps fun p hp => ihs m ps hps p hp (hall p hp)

/-- Fewer unfolded names accept more: the checker is antitone in `seen`. -/
theorem hasTyIn_antitone {decls : TyDecls} {allocated : List String} :
    ∀ (seen : List String) (v : Val) (t : Ty) (seen' : List String),
      (∀ x, seen'.contains x = true → seen.contains x = true) →
      Val.hasTyIn decls seen v t allocated = true → Val.hasTyIn decls seen' v t allocated = true := by
  intro seen v t
  induction seen, v, t using Val.hasTyIn.induct decls allocated with
  | case1 seen v t ihu _ =>
    intro seen' hsub h
    obtain ⟨m, hm, hcase⟩ := hasTyIn_eq_true_iff.mp h
    refine hasTyIn_eq_true_iff.mpr ⟨m, hm, ?_⟩
    rcases hcase with ⟨name, body, hu, hs, hb⟩ | ⟨hu, ps, hps, hall⟩
    · have hs' : seen'.contains name = false := by
        cases hc : seen'.contains name with
        | false => rfl
        | true =>
          rw [hsub name hc] at hs
          cases hs
      refine Or.inl ⟨name, body, hu, hs', ?_⟩
      refine ihu m name body hu (by rw [hs]; exact Bool.false_ne_true) (name :: seen')
        (fun x hx => ?_) hb
      rw [List.contains_cons] at hx ⊢
      rcases Bool.or_eq_true_iff.mp hx with hx | hx
      · rw [hx, Bool.true_or]
      · rw [hsub x hx, Bool.or_true]
    · exact Or.inr ⟨hu, ps, hps, hall⟩

/-- **The cycle cut**: a success that passes through `name` again also succeeds from its first
unfolding. Either the success avoids `name`, or its part after `name` is a success of `name`'s
body. -/
theorem hasTyIn_absorb {decls : TyDecls} {allocated : List String} {name : String} {body : Ty}
    (hb : decls.body? name = some body) :
    ∀ (seen : List String) (v : Val) (t : Ty), Val.hasTyIn decls seen v t allocated = true →
      Val.hasTyIn decls (name :: seen) v t allocated = true ∨
        Val.hasTyIn decls (name :: seen) v body allocated = true := by
  intro seen v t
  induction seen, v, t using Val.hasTyIn.induct decls allocated with
  | case1 seen v t ihu _ =>
    intro h
    obtain ⟨m, hm, hcase⟩ := hasTyIn_eq_true_iff.mp h
    rcases hcase with ⟨n, b, hu, hs, hrec⟩ | ⟨hu, ps, hps, hall⟩
    · cases hn : n == name with
      | true =>
        have heq : n = name := beq_iff_eq.mp hn
        subst heq
        have hbody : b = body := by
          have hb' := TyDecls.body?_of_unfold? hu
          rw [hb] at hb'
          exact (Option.some.inj hb').symm
        subst hbody
        exact Or.inr hrec
      | false =>
        rcases ihu m n b hu (by rw [hs]; exact Bool.false_ne_true) hrec with h1 | h2
        · refine Or.inl (hasTyIn_eq_true_iff.mpr ⟨m, hm, Or.inl ⟨n, b, hu, ?_, ?_⟩⟩)
          · rw [List.contains_cons, hs, hn, Bool.false_or]
          · refine hasTyIn_antitone _ _ _ _ (fun x hx => ?_) h1
            simp only [List.contains_cons, Bool.or_eq_true] at hx ⊢
            rcases hx with hx | hx | hx
            · exact Or.inr (Or.inl hx)
            · exact Or.inl hx
            · exact Or.inr (Or.inr hx)
        · refine Or.inr (hasTyIn_antitone _ _ _ _ (fun x hx => ?_) h2)
          simp only [List.contains_cons, Bool.or_eq_true] at hx ⊢
          rcases hx with hx | hx
          · exact Or.inl hx
          · exact Or.inr (Or.inr hx)
    · exact Or.inl (hasTyIn_eq_true_iff.mpr ⟨m, hm, Or.inr ⟨hu, ps, hps, hall⟩⟩)

/-- **Complete against `MemberIn`**: every member is accepted with no name unfolded. -/
theorem hasTyIn_of_memberIn {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (h : MemberIn decls allocated v t) : Val.hasTyIn decls [] v t allocated = true := by
  induction h with
  | left _ ih =>
    rw [hasTyIn_union, ih, Bool.true_or]
  | right _ ih =>
    rw [hasTyIn_union, ih, Bool.or_true]
  | unfold hu _ ih =>
    have hmem := Ty.members_atom (TyDecls.isMember_of_unfold? hu)
    have hrec := (hasTyIn_absorb (TyDecls.body?_of_unfold? hu) [] _ _ ih).elim id id
    exact hasTyIn_eq_true_iff.mpr ⟨_, by rw [hmem]; exact List.mem_singleton_self _,
      Or.inl ⟨_, _, hu, rfl, hrec⟩⟩
  | step hu hps _ ih =>
    have hmem := Ty.members_atom (Val.isMember_of_obligations hps)
    exact hasTyIn_eq_true_iff.mpr ⟨_, by rw [hmem]; exact List.mem_singleton_self _,
      Or.inr ⟨hu, _, hps, ih⟩⟩

/-- **The checker decides membership under the table**, on every table, guarded or not: the
least fixed point is what it computes. -/
@[semantics "store-typing" (requirement := R3)]
theorem hasTyIn_iff {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty} :
    Val.hasTyIn decls [] v t allocated = true ↔ MemberIn decls allocated v t :=
  ⟨memberIn_of_hasTyIn [] v t, hasTyIn_of_memberIn⟩

/-- **The iso-recursive unfolding**: a reference to a declared name has the body's members, and
no others. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_unfold_iff {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    {name : String} {body : Ty} (hu : decls.unfold? t = some (name, body)) :
    MemberIn decls allocated v t ↔ MemberIn decls allocated v body := by
  constructor
  · intro h
    cases h with
    | left _ => cases hu
    | right _ => cases hu
    | unfold hu' hb =>
      rw [hu] at hu'
      cases hu'
      exact hb
    | step hu' _ _ =>
      rw [hu] at hu'
      cases hu'
  · exact .unfold hu

/-! ## The step reads `Val.hasTy`'s arms -/

/-- The named read through its questions (`namedHasTy` against `namedPairs`). -/
theorem namedHasTy_eq_namedPairs (f : Val → Ty → Bool) :
    ∀ (cs : List (String × Bool × Ty)) (ns xs : List Val),
      namedHasTy (cs.map fun c => (c.1, c.2.1, fun x => f x c.2.2)) ns xs =
        match namedPairs cs ns xs with
        | some ps => ps.all fun p => f p.1 p.2
        | none => false
  | [], [], [] => rfl
  | [], [], _ :: _ => rfl
  | [], _ :: _, _ => rfl
  | (n, o, t) :: cs, [], [] => by
    simp only [List.map_cons, namedHasTy, namedPairs]
    cases o with
    | true =>
      rw [Bool.true_and, if_pos rfl]
      exact namedHasTy_eq_namedPairs f cs [] []
    | false =>
      rw [Bool.false_and, if_neg Bool.false_ne_true]
  | (_, _, _) :: _, [], _ :: _ => rfl
  | (_, _, _) :: _, _ :: _, [] => by
    rename_i nv _
    cases nv <;> rfl
  | (n, o, t) :: cs, nv :: ns, x :: xs => by
    cases nv with
    | str m =>
      simp only [List.map_cons, namedHasTy, namedPairs]
      split
      · rw [namedHasTy_eq_namedPairs f cs ns xs]
        cases namedPairs cs ns xs with
        | some qs => simp only [Option.map_some, List.all_cons]
        | none => simp only [Option.map_none, Bool.and_false]
      · cases o with
        | true =>
          rw [Bool.true_and, if_pos rfl]
          exact namedHasTy_eq_namedPairs f cs (.str m :: ns) (x :: xs)
        | false => rw [Bool.false_and, if_neg Bool.false_ne_true]
    | _ => rfl

/-- The item read through its questions (`itemsHasTy` against `itemPairs`). -/
theorem itemsHasTy_eq_itemPairs (f : Val → Ty → Bool) :
    ∀ (ts : List Ty) (xs : List Val),
      itemsHasTy (ts.map fun t x => f x t) xs =
        match itemPairs ts xs with
        | some ps => ps.all fun p => f p.1 p.2
        | none => false
  | [], [] => rfl
  | t :: ts, x :: xs => by
    simp only [List.map_cons, itemsHasTy, itemPairs]
    rw [itemsHasTy_eq_itemPairs f ts xs]
    cases itemPairs ts xs with
    | some qs => simp only [Option.map_some, List.all_cons]
    | none => simp only [Option.map_none, Bool.and_false]
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl

/-- The entry read through its questions (`entriesHasTy`'s body against `entryPairs`). -/
theorem entriesAll_eq_entryPairs (f : Val → Ty → Bool) (key value : Ty) :
    ∀ es : List Val,
      (es.all fun e => match e with
        | .pair a x => f a key && f x value
        | _ => false) =
        match entryPairs key value es with
        | some ps => ps.all fun p => f p.1 p.2
        | none => false
  | [] => rfl
  | e :: es => by
    cases e with
    | pair a x =>
      simp only [List.all_cons, entryPairs]
      rw [entriesAll_eq_entryPairs f key value es]
      cases entryPairs key value es with
      | some qs => simp only [Option.map_some, List.all_cons, Bool.and_assoc]
      | none => simp only [Option.map_none, Bool.and_false]
    | _ => rfl

/-- The cause read through its questions (`causeAdmits`'s fold against `causeObligations`).
The reading ignores the type argument, as every caller's does. -/
theorem reasonsAll_eq_causeObligations (f : Val → Ty → Bool) (error ty : Ty) :
    ∀ rs : List (Reason Err Defect FiberId Ann),
      rs.all (reasonAdmits (fun w _ => f w error) ty) =
        match causeObligations error rs with
        | some ps => ps.all fun p => f p.1 p.2
        | none => false
  | [] => rfl
  | r :: rs => by
    cases r with
    | fail e ann =>
      simp only [List.all_cons, reasonAdmits, causeObligations]
      cases valOfErr e with
      | some x =>
        dsimp only
        rw [reasonsAll_eq_causeObligations f error ty rs]
        cases causeObligations error rs with
        | some qs => simp only [Option.map_some, List.all_cons]
        | none => simp only [Option.map_none, Bool.and_false]
      | none => simp only [Bool.false_and]
    | die d ann =>
      simp only [List.all_cons, reasonAdmits, causeObligations, Bool.true_and]
      exact reasonsAll_eq_causeObligations f error ty rs
    | interrupt w ann =>
      simp only [List.all_cons, reasonAdmits, causeObligations, Bool.true_and]
      exact reasonsAll_eq_causeObligations f error ty rs

/-! ## Membership as the admission fold with the declared names read from an oracle -/

/-- **The admission fold under a table**, with each declared name read from the oracle `o`: at a
reference to a declared name the node admits what `o` admits at the name; every other node is
`Val.hasTy`'s own arm (`Val.hasTy.alg`). -/
def declAlg (decls : TyDecls) (o : String → Adm) : TyAlgebra AdmCarrier :=
  { Val.hasTy.alg with
    ty_app := fun name args =>
      match decls.body? name with
      | some _ => (.app name (args.map Prod.fst), o name)
      | none => Val.hasTy.alg.ty_app name args }

/-- On the empty table the fold reads no oracle: it is `Val.hasTy`'s. -/
theorem declAlg_nil (o : String → Adm) : declAlg [] o = Val.hasTy.alg := rfl

/-- **The fold with any oracle satisfies the order's condition**: a declared reference reads one
admission at both ends of the order, and every other arm is `Val.hasTy`'s. -/
theorem declAlg_admitsSub (decls : TyDecls) (o : String → Adm) : AdmitsSub (declAlg decls o) :=
  { Val.hasTy_admitsSub with
    app := fun name ps qs hlen hvar => by
      show Adm.le ((declAlg decls o).ty_app name ps).2 ((declAlg decls o).ty_app name qs).2
      unfold declAlg
      dsimp only
      split
      · exact Adm.le_refl _
      · exact Val.hasTy_admitsSub.app name ps qs hlen hvar }

/-- A step's verdict under a reading of its questions. -/
def obligationsAll (f : Val → Ty → Bool) (v : Val) (t : Ty) (allocated : List String) : Bool :=
  match Val.obligations v t allocated with
  | some ps => ps.all fun p => f p.1 p.2
  | none => false

/-- A leaf's verdict is its shape check. -/
theorem obligationsAll_leaf (f : Val → Ty → Bool) {v : Val} {t : Ty} {allocated : List String}
    (h : Val.obligations v t allocated = if Val.hasTy v t allocated then some [] else none) :
    obligationsAll f v t allocated = Val.hasTy v t allocated := by
  unfold obligationsAll
  rw [h]
  cases Val.hasTy v t allocated with
  | true => rfl
  | false => rfl

/-- At a leaf the fold is the shape check, and so is the step's verdict. -/
theorem cata_declAlg_leaf {decls : TyDecls} {o : String → Adm} {f : Val → Ty → Bool} {v : Val}
    {t : Ty} {allocated : List String}
    (hc : (cata_ty (declAlg decls o) t).2 v allocated = Val.hasTy v t allocated)
    (h : Val.obligations v t allocated = if Val.hasTy v t allocated then some [] else none) :
    (cata_ty (declAlg decls o) t).2 v allocated = obligationsAll f v t allocated := by
  rw [hc, obligationsAll_leaf f h]

/-- **The fold at a union member**: a declared reference is its oracle; every other member is
its step, with each question read by the fold. -/
theorem cata_declAlg_step (decls : TyDecls) (o : String → Adm) {m : Ty} (hm : m.isMember = true)
    (v : Val) (allocated : List String) :
    (cata_ty (declAlg decls o) m).2 v allocated =
      match decls.unfold? m with
      | some (name, _) => o name v allocated
      | none => obligationsAll (fun x u => (cata_ty (declAlg decls o) u).2 x allocated) v m allocated := by
  cases m
  case never => cases hm
  case union => cases hm
  case handle name => exact (obligationsAll_leaf (t := .handle name) _ rfl).symm
  case app name args =>
    show ((declAlg decls o).ty_app name _).2 v allocated = _
    unfold declAlg TyDecls.unfold?
    simp only [Ty.refName?, Option.bind_some]
    cases decls.body? name with
    | some b => rfl
    | none => exact (obligationsAll_leaf (t := .app name args) _ rfl).symm
  case option inner =>
    show (Val.hasTy.alg.ty_option (cata_ty (declAlg decls o) inner)).2 v allocated =
      obligationsAll _ v (.option inner) allocated
    unfold obligationsAll
    cases v <;> simp only [Val.hasTy.alg, Val.obligations, List.all_cons, List.all_nil, Bool.and_true]
  case list item =>
    show (Val.hasTy.alg.ty_list (cata_ty (declAlg decls o) item)).2 v allocated =
      obligationsAll _ v (.list item) allocated
    dsimp only [Val.hasTy.alg]
    split
    · rename_i head
      simp only [obligationsAll, Val.obligations]
      cases Val.snapshot? (Store.Val.ctor 3 [head]) with
      | some ids => simp only [Option.map_some, List.all_map, Function.comp_def]
      | none => rfl
    · simp only [obligationsAll, Val.obligations, List.all_map, Function.comp_def]
    · rename_i hsnap hlist
      have hnone : Val.obligations v (.list item) allocated = none := by
        simp only [Val.obligations]
      simp only [obligationsAll, hnone]
  case prod a b =>
    show (Val.hasTy.alg.ty_prod (cata_ty (declAlg decls o) a) (cata_ty (declAlg decls o) b)).2 v
      allocated = obligationsAll _ v (.prod a b) allocated
    dsimp only [Val.hasTy.alg]
    split
    · simp only [obligationsAll, Val.obligations, List.all_cons, List.all_nil, Bool.and_true]
    · rename_i hpair
      have hnone : Val.obligations v (.prod a b) allocated = none := by
        simp only [Val.obligations]
      simp only [obligationsAll, hnone]
  case except error value =>
    show (Val.hasTy.alg.ty_except (cata_ty (declAlg decls o) error)
      (cata_ty (declAlg decls o) value)).2 v allocated = obligationsAll _ v (.except error value) allocated
    dsimp only [Val.hasTy.alg]
    split
    · simp only [obligationsAll, Val.obligations, List.all_cons, List.all_nil, Bool.and_true]
    · simp only [obligationsAll, Val.obligations, List.all_cons, List.all_nil, Bool.and_true]
    · rename_i h0 h1
      have hnone : Val.obligations v (.except error value) allocated = none := by
        simp only [Val.obligations]
      simp only [obligationsAll, hnone]
  case exitOf value error =>
    show (Val.hasTy.alg.ty_exitOf (cata_ty (declAlg decls o) value)
      (cata_ty (declAlg decls o) error)).2 v allocated = obligationsAll _ v (.exitOf value error) allocated
    dsimp only [Val.hasTy.alg]
    split
    · simp only [obligationsAll, Val.obligations, List.all_cons, List.all_nil, Bool.and_true]
    · rename_i written
      simp only [obligationsAll, Val.obligations]
      cases causeImage.ofVal written with
      | some c =>
        simp only [Option.bind_some, causeAdmits]
        exact reasonsAll_eq_causeObligations
          (fun x u => (cata_ty (declAlg decls o) u).2 x allocated) error _ c.reasons
      | none => rfl
    · rename_i h0 h1
      have hnone : Val.obligations v (.exitOf value error) allocated = none := by
        simp only [Val.obligations]
      simp only [obligationsAll, hnone]
  case causeOf error =>
    show (Val.hasTy.alg.ty_causeOf (cata_ty (declAlg decls o) error)).2 v allocated =
      obligationsAll _ v (.causeOf error) allocated
    dsimp only [Val.hasTy.alg]
    simp only [obligationsAll, Val.obligations]
    cases Val.cause? v with
    | some c =>
      simp only [Option.bind_some, causeAdmits]
      exact reasonsAll_eq_causeObligations
        (fun x u => (cata_ty (declAlg decls o) u).2 x allocated) error _ c.reasons
    | none => rfl
  case map key value =>
    show (Val.hasTy.alg.ty_map (cata_ty (declAlg decls o) key)
      (cata_ty (declAlg decls o) value)).2 v allocated = obligationsAll _ v (.map key value) allocated
    dsimp only [Val.hasTy.alg]
    split
    · rename_i es
      simp only [obligationsAll, Val.obligations]
      unfold entriesHasTy
      cases sortedEntries es with
      | true =>
        rw [Bool.true_and, if_pos rfl]
        exact entriesAll_eq_entryPairs
          (fun x u => (cata_ty (declAlg decls o) u).2 x allocated) key value es
      | false => rw [Bool.false_and, if_neg Bool.false_ne_true]
    · rename_i hlist
      have hnone : Val.obligations v (.map key value) allocated = none := by
        simp only [Val.obligations]
      simp only [obligationsAll, hnone]
  case tuple ts =>
    show (Val.hasTy.alg.ty_tuple (cata_pos_list_ty (declAlg decls o) ts)).2 v allocated =
      obligationsAll _ v (.tuple ts) allocated
    dsimp only [Val.hasTy.alg]
    split
    · rename_i xs
      simp only [obligationsAll, Val.obligations]
      rw [itemCheckers_foldr, cata_pos_list_ty_eq, List.map_map]
      exact itemsHasTy_eq_itemPairs
        (fun x u => (cata_ty (declAlg decls o) u).2 x allocated) ts xs
    · rename_i hlist
      have hnone : Val.obligations v (.tuple ts) allocated = none := by
        simp only [Val.obligations]
      simp only [obligationsAll, hnone]
  case record fs =>
    show (Val.hasTy.alg.ty_record (cata_pos_list_prod_string_prod_bool_ty (declAlg decls o) fs)).2 v
      allocated = obligationsAll _ v (.record fs) allocated
    dsimp only [Val.hasTy.alg]
    simp only [obligationsAll, Val.obligations]
    cases recordParts? v with
    | some parts =>
      obtain ⟨ns, xs⟩ := parts
      simp only [Option.bind_some]
      rw [fieldCheckers_foldr, cata_pos_list_prod_string_prod_bool_ty_eq, List.map_map]
      have hmap : ((fun q => (q.1, admChecker allocated q.2)) ∘
          prodMapSnd (prodMapSnd (cata_ty (declAlg decls o)))) =
          fun c : String × Bool × Ty =>
            (c.1, c.2.1, fun x => (cata_ty (declAlg decls o) c.2.2).2 x allocated) := rfl
      rw [hmap]
      have hcanon := Field.canonBy_map (key := Field.bytesKey)
        (fun c : Bool × Ty => (c.1, fun x => (cata_ty (declAlg decls o) c.2).2 x allocated)) fs
      rw [Ty.canon, hcanon, ← Ty.canon]
      exact namedHasTy_eq_namedPairs
        (fun x u => (cata_ty (declAlg decls o) u).2 x allocated) (Ty.canon fs) ns xs
    | none => rfl
  all_goals exact cata_declAlg_leaf rfl rfl

/-- **The fold reads a union by its members**, as `Val.hasTy` does (`Ty.hasTy_members`). -/
theorem cata_declAlg_members (decls : TyDecls) (o : String → Adm) (t : Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) t).2 v allocated =
      t.members.any fun m => (cata_ty (declAlg decls o) m).2 v allocated := by
  induction t with
  | union l r ihl ihr =>
    rw [Ty.members, List.any_append, ← ihl, ← ihr]
    rfl
  | never => rfl
  | _ => simp only [Ty.members, List.any_cons, List.any_nil, Bool.or_false]

/-- The fold reads a union side by side. -/
theorem cata_declAlg_union (decls : TyDecls) (o : String → Adm) (l r : Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) (.union l r)).2 v allocated =
      ((cata_ty (declAlg decls o) l).2 v allocated || (cata_ty (declAlg decls o) r).2 v allocated) :=
  rfl

/-- The empty table declares no name. -/
theorem TyDecls.unfold?_nil (t : Ty) : TyDecls.unfold? [] t = none := by
  unfold TyDecls.unfold?
  cases t.refName? with
  | none => rfl
  | some _ => rfl

/-- **The step reads `Val.hasTy`'s arms**: at a union member, the shape check is the verdict of
its questions under the shape check. -/
theorem hasTy_eq_obligationsAll {m : Ty} (hm : m.isMember = true) (v : Val)
    (allocated : List String) :
    Val.hasTy v m allocated = obligationsAll (fun x u => Val.hasTy x u allocated) v m allocated := by
  have h := cata_declAlg_step [] (fun _ _ _ => false) hm v allocated
  rw [declAlg_nil, TyDecls.unfold?_nil] at h
  rw [Val.hasTy.eq_cata v m allocated, h]
  have hfun : (fun x u => (cata_ty Val.hasTy.alg u).snd x allocated) =
      fun x u => Val.hasTy x u allocated := by
    funext x u
    exact (Val.hasTy.eq_cata x u allocated).symm
  rw [hfun]

/-! ## Conservativity: the empty table changes nothing -/

/-- **On the empty table the checker is `Val.hasTy`**, from any set of unfolded names. -/
theorem hasTyIn_nil (seen : List String) (v : Val) (t : Ty) (allocated : List String) :
    Val.hasTyIn [] seen v t allocated = Val.hasTy v t allocated := by
  induction seen, v, t using Val.hasTyIn.induct [] allocated with
  | case1 seen v t _ ihs =>
    rw [Val.hasTyIn.eq_1, ← hasTy_members]
    apply Bool.eq_iff_iff.mpr
    rw [List.any_eq_true, List.any_eq_true]
    refine exists_congr fun m => and_congr_right fun hm => ?_
    rw [hasTy_eq_obligationsAll (Ty.members_isMember hm)]
    split
    · rename_i name body hu
      rw [TyDecls.unfold?_nil] at hu
      cases hu
    · unfold obligationsAll
      split
      · rename_i ps hps
        rw [hps]
        show (ps.attach.all _) = true ↔ (ps.all fun p => Val.hasTy p.1 p.2 allocated) = true
        rw [List.all_eq_true, List.all_eq_true]
        constructor
        · intro h p hp
          rw [← ihs m ps hps p hp]
          exact h ⟨p, hp⟩ (List.mem_attach _ _)
        · rintro h ⟨p, hp⟩ _
          show Val.hasTyIn [] [] p.1 p.2 allocated = true
          rw [ihs m ps hps p hp]
          exact h p hp
      · rename_i hps
        rw [hps]

/-- **On the empty table membership is `Val.hasTy`**: the inductive predicate holds exactly
where the existing shape check answers `true`. -/
theorem memberIn_nil {allocated : List String} {v : Val} {t : Ty} :
    MemberIn [] allocated v t ↔ Val.hasTy v t allocated = true := by
  rw [← hasTyIn_iff, hasTyIn_nil]

/-- **The decider decides membership** on every table: `Val.memberIn` is `Val.hasTy` at the
empty table (`memberIn_nil`) and the checker otherwise (`hasTyIn_iff`). The readers of reply
admission read it (decisions row 406 (2)). -/
theorem Val.memberIn_iff {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty} :
    Val.memberIn decls v t allocated = true ↔ MemberIn decls allocated v t := by
  cases decls with
  | nil => exact memberIn_nil.symm
  | cons d ds => exact hasTyIn_iff

/-! ## Membership is the admission fold at the checker's oracle -/

/-- **The checker as an oracle**: a declared name admits what the checker admits at the name's
body, with the name unfolded. -/
def checkerOracle (decls : TyDecls) (name : String) : Adm := fun v allocated =>
  match decls.body? name with
  | some body => Val.hasTyIn decls [name] v body allocated
  | none => false

/-- A member is admitted by the fold at the checker's oracle. -/
theorem cata_of_memberIn {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (h : MemberIn decls allocated v t) :
    (cata_ty (declAlg decls (checkerOracle decls)) t).2 v allocated = true := by
  induction h with
  | left _ ih => rw [cata_declAlg_union, ih, Bool.true_or]
  | right _ ih => rw [cata_declAlg_union, ih, Bool.or_true]
  | @unfold v t name body hu hb _ =>
    rw [cata_declAlg_step decls _ (TyDecls.isMember_of_unfold? hu), hu]
    show checkerOracle decls name v allocated = true
    unfold checkerOracle
    rw [TyDecls.body?_of_unfold? hu]
    exact (hasTyIn_absorb (TyDecls.body?_of_unfold? hu) [] v body (hasTyIn_of_memberIn hb)).elim
      id id
  | step hu hps _ ih =>
    rw [cata_declAlg_step decls _ (Val.isMember_of_obligations hps), hu]
    show obligationsAll _ _ _ allocated = true
    unfold obligationsAll
    rw [hps]
    exact List.all_eq_true.mpr fun p hp => ih p hp

/-- What the fold at the checker's oracle admits is a member. -/
theorem memberIn_of_cata {decls : TyDecls} {allocated : List String} (v : Val) (t : Ty)
    (h : (cata_ty (declAlg decls (checkerOracle decls)) t).2 v allocated = true) :
    MemberIn decls allocated v t := by
  rw [cata_declAlg_members] at h
  obtain ⟨m, hm, hmv⟩ := List.any_eq_true.mp h
  refine MemberIn.of_mem_members hm ?_
  rw [cata_declAlg_step decls _ (Ty.members_isMember hm)] at hmv
  split at hmv
  · rename_i name body hu
    unfold checkerOracle at hmv
    rw [TyDecls.body?_of_unfold? hu] at hmv
    exact .unfold hu (memberIn_of_hasTyIn [name] v body hmv)
  · rename_i hu
    unfold obligationsAll at hmv
    split at hmv
    · rename_i ps hps
      exact .step hu hps fun p hp => memberIn_of_cata p.1 p.2 (List.all_eq_true.mp hmv p hp)
    · cases hmv
termination_by sizeOf v
decreasing_by exact Val.sizeOf_obligation (by assumption) hp

/-- **Membership is the admission fold at the checker's oracle**: the least fixed point, read as
a fold whose declared names are read from the checker. -/
theorem memberIn_iff_cata {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty} :
    MemberIn decls allocated v t ↔
      (cata_ty (declAlg decls (checkerOracle decls)) t).2 v allocated = true :=
  ⟨cata_of_memberIn, memberIn_of_cata v t⟩

/-! ## Subtyping stays nominal, and is sound for membership under the table -/

/-- **The order is sound for membership under the table**: `Ty.sub`, unchanged, keeps the
members of every table. A declared reference is below itself by name; no rule compares two
bodies. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_sub {decls : TyDecls} {allocated : List String} {v : Val} {a b : Ty}
    (hsub : Ty.sub a b = true) (h : MemberIn decls allocated v a) : MemberIn decls allocated v b :=
  memberIn_iff_cata.mpr
    (cata_admits_sub (declAlg_admitsSub decls _) hsub v allocated (memberIn_iff_cata.mp h))

/-! ## Inhabitance: the least fixed point, sound against membership -/

/-- A record frame's questions name every required field. -/
theorem namedPairs_required (cs : List (String × Bool × Ty)) (ns xs : List Val) :
    ∀ {ps : List (Val × Ty)}, namedPairs cs ns xs = some ps →
      ∀ c ∈ cs, c.2.1 = false → ∃ x, (x, c.2.2) ∈ ps := by
  fun_induction namedPairs cs ns xs with
  | case1 =>
    intro ps _ c hc
    cases hc
  | case2 fst snd cs ih =>
    intro ps h c hc hreq
    rcases List.mem_cons.mp hc with rfl | hc
    · cases hreq
    · exact ih h c hc hreq
  | case3 =>
    intro ps h
    cases h
  | case4 o t cs m ns x xs ih =>
    intro ps h c hc hreq
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hc with rfl | hc
    · exact ⟨x, List.mem_cons_self⟩
    · obtain ⟨y, hy⟩ := ih hqs c hc hreq
      exact ⟨y, List.mem_cons_of_mem _ hy⟩
  | case5 n t cs m ns x xs _ ih =>
    intro ps h c hc hreq
    rcases List.mem_cons.mp hc with rfl | hc
    · cases hreq
    · exact ih h c hc hreq
  | case6 =>
    intro ps h
    cases h
  | case7 =>
    intro ps h
    cases h

/-- A tuple's questions name every item type. -/
theorem itemPairs_all (ts : List Ty) (xs : List Val) :
    ∀ {ps : List (Val × Ty)}, itemPairs ts xs = some ps → ∀ t ∈ ts, ∃ x, (x, t) ∈ ps := by
  fun_induction itemPairs ts xs with
  | case1 =>
    intro ps _ t ht
    cases ht
  | case2 t ts x xs ih =>
    intro ps h u hu
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hu with rfl | hu
    · exact ⟨x, List.mem_cons_self⟩
    · obtain ⟨y, hy⟩ := ih hqs u hu
      exact ⟨y, List.mem_cons_of_mem _ hy⟩
  | case3 =>
    intro ps h
    cases h

namespace TyDecls

/-- **Saturation stops at a closed set**: a declared name its test accepts there is in it. -/
theorem saturate_closed (decls : TyDecls) (holds : List String → String → Bool) :
    ∀ (known : List String) (name : String), (∃ d ∈ decls, d.1 = name) →
      holds (decls.saturate holds known) name = true → name ∈ decls.saturate holds known := by
  intro known
  induction known using TyDecls.saturate.induct decls holds with
  | case1 known hstop =>
    intro name hdecl hh
    rw [saturate, dif_pos hstop] at hh ⊢
    cases hc : known.contains name with
    | true => exact List.contains_iff_mem.mp hc
    | false =>
      obtain ⟨d, hd, rfl⟩ := hdecl
      have hround : d.1 ∈ decls.round holds known :=
        List.mem_filterMap.mpr ⟨d, hd, by rw [if_pos hh]⟩
      have hfresh : d.1 ∈ (decls.round holds known).filter fun n => !known.contains n :=
        List.mem_filter.mpr ⟨hround, by rw [hc]; rfl⟩
      rw [hstop] at hfresh
      cases hfresh
  | case2 known hmore ih =>
    intro name hdecl hh
    rw [saturate, dif_neg hmore] at hh ⊢
    exact ih name hdecl hh

/-- **Saturation keeps an invariant that each round's test establishes**: when the test's
acceptance of a name, given the invariant on the names known, gives it at the name, every name of
the saturation has it. The induction principle of both instances. -/
theorem saturate_inv (decls : TyDecls) (holds : List String → String → Bool)
    {R : String → Prop} (hstep : ∀ known, (∀ n ∈ known, R n) → ∀ n, holds known n = true → R n) :
    ∀ known, (∀ n ∈ known, R n) → ∀ n ∈ decls.saturate holds known, R n := by
  intro known
  induction known using TyDecls.saturate.induct decls holds with
  | case1 known hstop =>
    intro hk
    rw [saturate, dif_pos hstop]
    exact hk
  | case2 known hmore ih =>
    intro hk
    rw [saturate, dif_neg hmore]
    refine ih fun n hn => ?_
    rcases List.mem_append.mp hn with hold | hnew
    · exact hk n hold
    · exact hstep known hk n (mem_round (List.mem_filter.mp hnew).1).2

/-- A declared name whose body the iteration's answer calls inhabited is in the answer. -/
theorem mem_inhabitedNames {decls : TyDecls} {name : String} {body : Ty}
    (hb : decls.body? name = some body)
    (h : cata_ty (decls.inhabitedWith decls.inhabitedNames) body = true) :
    name ∈ decls.inhabitedNames := by
  refine decls.saturate_closed decls.inhabitedHolds [] name ⟨(name, body), mem_of_body? hb, rfl⟩ ?_
  unfold inhabitedHolds
  rw [hb]
  exact h

/-- At a type that names no declared name at its head, a step whose questions are inhabited is
inhabited. -/
theorem inhabitedWith_of_step {decls : TyDecls} {known : List String} {v : Val} {t : Ty}
    {allocated : List String} {ps : List (Val × Ty)} (hu : decls.unfold? t = none)
    (hps : Val.obligations v t allocated = some ps)
    (hall : ∀ p ∈ ps, cata_ty (decls.inhabitedWith known) p.2 = true) :
    cata_ty (decls.inhabitedWith known) t = true := by
  have hleaf : ∀ {u : Ty}, cata_ty (decls.inhabitedWith known) u = Effect4.Program.inhabited u →
      Val.obligations v u allocated = (if Val.hasTy v u allocated then some [] else none) →
      Val.obligations v u allocated = some ps → cata_ty (decls.inhabitedWith known) u = true := by
    intro u hcata hcatch hsome
    rw [hcatch] at hsome
    cases hh : Val.hasTy v u allocated with
    | true => rw [hcata]; exact Typed.inhabited_of_hasTy u v allocated hh
    | false =>
      rw [hh] at hsome
      cases hsome
  cases t
  case never => cases hps
  case union => cases hps
  case handle name => exact hleaf rfl rfl hps
  case app name args =>
    unfold unfold? at hu
    simp only [Ty.refName?, Option.bind_some] at hu
    refine hleaf ?_ rfl hps
    show (if (decls.body? name).isSome then _ else _) = _
    cases hb : decls.body? name with
    | some b =>
      rw [hb] at hu
      cases hu
    | none => rfl
  case option | list | exitOf | causeOf | map => rfl
  case prod a b =>
    simp only [Val.obligations] at hps
    split at hps
    · cases hps
      show (cata_ty (decls.inhabitedWith known) a && cata_ty (decls.inhabitedWith known) b) = true
      rw [hall _ (List.mem_cons_self), hall _ (List.mem_cons_of_mem _ List.mem_cons_self)]
      rfl
    · cases hps
  case except error value =>
    simp only [Val.obligations] at hps
    split at hps
    · cases hps
      show (cata_ty (decls.inhabitedWith known) error || cata_ty (decls.inhabitedWith known) value) = true
      rw [hall _ List.mem_cons_self, Bool.true_or]
    · cases hps
      show (cata_ty (decls.inhabitedWith known) error || cata_ty (decls.inhabitedWith known) value) = true
      rw [hall _ List.mem_cons_self, Bool.or_true]
    · cases hps
  case record fs =>
    simp only [Val.obligations] at hps
    obtain ⟨parts, _, hnamed⟩ := Option.bind_eq_some_iff.mp hps
    rw [cata_ty_record]
    have hpm : prodMapSnd (prodMapSnd (cata_ty (decls.inhabitedWith known))) =
        fun q : String × Bool × Ty => (q.1, prodMapSnd (cata_ty (decls.inhabitedWith known)) q.2) :=
      rfl
    rw [hpm]
    show (Ty.canon (fs.map fun q => (q.1, prodMapSnd (cata_ty (decls.inhabitedWith known)) q.2))).all
      (fun p => p.2.1 || p.2.2) = true
    unfold Ty.canon
    rw [Field.canonBy_map, List.all_map, List.all_eq_true]
    intro c hc
    show (c.2.1 || cata_ty (decls.inhabitedWith known) c.2.2) = true
    cases ho : c.2.1 with
    | true => rfl
    | false =>
      obtain ⟨x, hx⟩ := namedPairs_required _ _ _ hnamed c hc ho
      rw [Bool.false_or]
      exact hall _ hx
  case tuple ts =>
    simp only [Val.obligations] at hps
    split at hps
    · rename_i xs
      rw [cata_ty_tuple]
      show (ts.map (cata_ty (decls.inhabitedWith known))).all id = true
      rw [List.all_eq_true]
      intro b hb
      obtain ⟨u, hu', rfl⟩ := List.mem_map.mp hb
      obtain ⟨x, hx⟩ := itemPairs_all _ _ hps u hu'
      exact hall _ hx
    · cases hps
  all_goals exact hleaf rfl rfl hps

/-- Inhabitance reads a union side by side. -/
theorem inhabited_union (decls : TyDecls) (l r : Ty) :
    decls.inhabited (.union l r) = (decls.inhabited l || decls.inhabited r) := rfl

end TyDecls

/-- **Inhabitance is sound against membership under the table**: a type with a member is
inhabited, so refusing a column that `TyDecls.inhabited` calls empty never refuses one with a
member. -/
theorem inhabited_of_memberIn {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (h : MemberIn decls allocated v t) : decls.inhabited t = true := by
  induction h with
  | left _ ih => rw [TyDecls.inhabited_union, ih, Bool.true_or]
  | right _ ih => rw [TyDecls.inhabited_union, ih, Bool.or_true]
  | @unfold v t name body hu _ ih =>
    have hb := TyDecls.body?_of_unfold? hu
    have hname := List.contains_iff_mem.mpr (TyDecls.mem_inhabitedNames hb ih)
    have href : t.refName? = some name := by
      unfold TyDecls.unfold? at hu
      cases hr : t.refName? with
      | none =>
        rw [hr] at hu
        cases hu
      | some m =>
        rw [hr, Option.bind_some] at hu
        obtain ⟨b', _, he⟩ := Option.map_eq_some_iff.mp hu
        cases he
        rfl
    cases t
    case app n args =>
      cases href
      show (if (decls.body? name).isSome then _ else _) = true
      rw [hb, Option.isSome_some, if_pos rfl]
      exact hname
    all_goals cases href
  | step hu hps _ ih => exact TyDecls.inhabitedWith_of_step hu hps ih

/-! ## The claims: conservativity, inhabitance and the planned goals -/

/-- On the empty table inhabitance is `inhabited`. -/
theorem TyDecls.inhabited_nil (t : Ty) : TyDecls.inhabited [] t = Effect4.Program.inhabited t := rfl

/-- **Conservativity** (claim `recursive-types-conservative`): on the empty table the checker is
`Val.hasTy` from any set of unfolded names, membership is `Val.hasTy`'s answer, and inhabitance
is `inhabited`. So every existing statement over `Val.hasTy` and `inhabited` reads the empty
table unchanged. It says nothing of `Fits`, which takes no table yet. -/
@[semantics "store-typing" (requirement := R3)]
theorem tyDecls_conservative :
    (∀ (seen : List String) (v : Val) (t : Ty) (allocated : List String),
      Val.hasTyIn [] seen v t allocated = Val.hasTy v t allocated) ∧
    (∀ (allocated : List String) (v : Val) (t : Ty),
      MemberIn [] allocated v t ↔ Val.hasTy v t allocated = true) ∧
    (∀ t : Ty, TyDecls.inhabited [] t = inhabited t) :=
  ⟨hasTyIn_nil, fun _ _ _ => memberIn_nil, TyDecls.inhabited_nil⟩

/-! ### Completeness of inhabitance: its parts

A name's declaration is read at its first entry in both judgments (`TyDecls.inhabitedHolds`
reads `body?`). On a table with a repeated name, reading every entry made inhabitance answer
`true` at `[("A", never), ("A", unit)]`, where no value is a member of `A`. The battery keeps that
table as a control. -/

/-- A step asks the same questions at a larger allocation table: only a leaf reads the table,
through `Val.hasTy` (`hasTy_mono`). A step of `memberIn_mono`. -/
theorem Val.obligations_mono {v : Val} {t : Ty} {a b : List String} (ext : Extends a b)
    {ps : List (Val × Ty)} (h : Val.obligations v t a = some ps) :
    Val.obligations v t b = some ps := by
  have hleaf : ∀ {u : Ty}, Val.obligations v u a = (if Val.hasTy v u a then some [] else none) →
      Val.obligations v u b = (if Val.hasTy v u b then some [] else none) →
      Val.obligations v u a = some ps → Val.obligations v u b = some ps := by
    intro u ha hb h
    rw [ha] at h
    rw [hb]
    cases hv : Val.hasTy v u a with
    | true =>
      rw [hv, if_pos rfl] at h
      rw [if_pos (hasTy_mono u v a b ext hv)]
      exact h
    | false =>
      rw [hv] at h
      cases h
  cases t
  case option | list | prod | except | exitOf | causeOf | union | record | map | tuple => exact h
  all_goals exact hleaf rfl rfl h

/-- **Membership survives the growth of the allocation table.** Placement: concept
`store-typing`, R3; a step of the claim `recursive-types-inhabited`, and the shape the world order
needs when the table enters the world. Route: induct on the derivation. A step's questions read
the allocation table only at a leaf, through `Val.hasTy` (`hasTy_mono`), so `Val.obligations`
answers the same questions at the larger table. Consumer: `exists_memberIn_fresh`, to carry an
earlier part's member past a later part's allocation. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_mono {decls : TyDecls} {a b : List String} (ext : Extends a b) {v : Val}
    {t : Ty} (h : MemberIn decls a v t) : MemberIn decls b v t := by
  induction h with
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | unfold hu _ ih => exact .unfold hu ih
  | step hu hps _ ih => exact .step hu (Val.obligations_mono ext hps) ih

/-- The names of `known` whose declarations have a member at an extension of every allocation
table: the invariant of the iteration's rounds. -/
def TyDecls.Witnessed (decls : TyDecls) (known : List String) : Prop :=
  ∀ name ∈ known, ∀ body, decls.body? name = some body → ∀ allocated : List String,
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      MemberIn decls allocated' v body

/-- A value at a leaf whose shape check accepts it is a member, with no question asked. -/
theorem memberIn_of_hasTy {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (hu : decls.unfold? t = none)
    (hl : Val.obligations v t allocated = if Val.hasTy v t allocated then some [] else none)
    (hv : Val.hasTy v t allocated = true) : MemberIn decls allocated v t :=
  .step hu (by rw [hl, if_pos hv]) fun _ hp => absurd hp List.not_mem_nil

/-- A handle at a spelling some kind owns has a member at an extension of any allocation table:
an external handle at the fresh index `allocated.length`, or the scope, the context, the memo map
or the mask's saved state at its own spelling (`fits_handle_fresh`'s cases, at the shape check). -/
theorem exists_hasTy_handle_fresh {target : String}
    (hr : retiredHandleTargets.contains target = false) (allocated : List String) :
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      Val.hasTy v (.handle target) allocated' = true := by
  cases hc : internalHandleTargets.contains target with
  | false =>
    have ht : externalHandleTarget target = true := by
      unfold externalHandleTarget
      rw [hc]
      rfl
    refine ⟨Val.handle HandleKind.external.byte allocated.length, allocated ++ [target],
      extends_append allocated [target], ?_⟩
    show (externalHandleTarget target &&
      (allocated ++ [target])[allocated.length]? == some target) = true
    rw [ht, Bool.true_and, List.getElem?_concat_length]
    exact beq_iff_eq.mpr rfl
  | true =>
    have hm : target ∈ internalHandleTargets := List.contains_iff_mem.mp hc
    simp only [internalHandleTargets, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hr (by decide)
    · exact absurd hr (by decide)
    · exact ⟨Val.handle HandleKind.scope.byte 0, allocated, fun _ _ h => h, rfl⟩
    · exact ⟨Val.context emptyCtx, allocated, fun _ _ h => h, rfl⟩
    · exact ⟨Val.handle HandleKind.memoMap.byte 0, allocated, fun _ _ h => h, rfl⟩
    · exact ⟨Val.savedMask false, allocated, fun _ _ h => h, rfl⟩

/-- A record frame's questions exist only at two name and value columns of one shape. -/
theorem namedPairs_shape (cs : List (String × Bool × Ty)) (ns xs : List Val) :
    ∀ {ps : List (Val × Ty)}, namedPairs cs ns xs = some ps →
      (ns = [] ∧ xs = []) ∨ ∃ k ns' x xs', ns = .str k :: ns' ∧ xs = x :: xs' := by
  fun_induction namedPairs cs ns xs with
  | case1 => exact fun _ => .inl ⟨rfl, rfl⟩
  | case2 => exact fun _ => .inl ⟨rfl, rfl⟩
  | case3 =>
    intro ps h
    cases h
  | case4 => exact fun _ => .inr ⟨_, _, _, _, rfl, rfl⟩
  | case5 => exact fun _ => .inr ⟨_, _, _, _, rfl, rfl⟩
  | case6 =>
    intro ps h
    cases h
  | case7 =>
    intro ps h
    cases h

/-- An optional field whose name the value columns do not hold is skipped. -/
theorem namedPairs_skip {m : String} {t : Ty} {l : List (String × Bool × Ty)} {ns xs : List Val}
    {ps : List (Val × Ty)} (h : namedPairs l ns xs = some ps) (hk : ∀ k, Val.str k ∈ ns → k ≠ m) :
    namedPairs ((m, true, t) :: l) ns xs = some ps := by
  rcases namedPairs_shape l ns xs h with ⟨rfl, rfl⟩ | ⟨k, ns', x, xs', rfl, rfl⟩
  · exact h
  · show (if k = m then (namedPairs l ns' xs').map ((x, t) :: ·)
      else if true = true then namedPairs l (.str k :: ns') (x :: xs') else none) = _
    rw [if_neg (hk k List.mem_cons_self), if_pos rfl]
    exact h

/-- The record case's construction: one allocation table threaded through the canonical fields;
an optional field is left out of both columns, a required one gets a member built at the table
the previous fields left (`namedFit_fresh`'s construction, at the shape check). -/
theorem namedPairs_fresh {decls : TyDecls} :
    ∀ (l : List (String × Bool × Ty)), (l.map Prod.fst).Nodup →
      (∀ q ∈ l, q.2.1 = false → ∀ allocated : List String, ∃ (v : Val) (allocated' : List String),
        Extends allocated allocated' ∧ MemberIn decls allocated' v q.2.2) →
      ∀ allocated : List String, ∃ (ns xs : List Val) (ps : List (Val × Ty))
        (allocated' : List String), Extends allocated allocated' ∧
        (∀ k, Val.str k ∈ ns → k ∈ l.map Prod.fst) ∧ namedPairs l ns xs = some ps ∧
        ∀ p ∈ ps, MemberIn decls allocated' p.1 p.2
  | [], _, _, allocated =>
    ⟨[], [], [], allocated, fun _ _ h => h, fun _ h => absurd h List.not_mem_nil, rfl,
      fun _ hp => absurd hp List.not_mem_nil⟩
  | (m, o, t) :: l, hnd, hw, allocated => by
    rw [List.map_cons, List.nodup_cons] at hnd
    have hw' : ∀ q ∈ l, q.2.1 = false → ∀ allocated : List String, ∃ (v : Val)
        (allocated' : List String), Extends allocated allocated' ∧ MemberIn decls allocated' v q.2.2 :=
      fun q hq => hw q (List.mem_cons_of_mem _ hq)
    cases o with
    | true =>
      obtain ⟨ns, xs, ps, al', e, hnames, hps, hall⟩ := namedPairs_fresh l hnd.2 hw' allocated
      refine ⟨ns, xs, ps, al', e, fun k hk => List.mem_cons_of_mem _ (hnames k hk), ?_, hall⟩
      exact namedPairs_skip hps fun k hk hkm => hnd.1 (hkm ▸ hnames k hk)
    | false =>
      obtain ⟨x, al1, e1, hx⟩ := hw (m, false, t) List.mem_cons_self rfl allocated
      obtain ⟨ns, xs, ps, al2, e2, hnames, hps, hall⟩ := namedPairs_fresh l hnd.2 hw' al1
      refine ⟨.str m :: ns, x :: xs, (x, t) :: ps, al2, fun i s hi => e2 i s (e1 i s hi), ?_, ?_, ?_⟩
      · intro k hk
        rcases List.mem_cons.mp hk with hk | hk
        · injection hk with hk
          rw [hk]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hnames k hk)
      · show (if m = m then (namedPairs l ns xs).map ((x, t) :: ·)
          else if false = true then namedPairs l (.str m :: ns) (x :: xs) else none) = _
        rw [if_pos rfl, hps]
        rfl
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact memberIn_mono e2 hx
        · exact hall p hp

/-- The tuple case's construction: one allocation table threaded through the items. -/
theorem itemPairs_fresh {decls : TyDecls} :
    ∀ (l : List Ty), (∀ t ∈ l, ∀ allocated : List String, ∃ (v : Val) (allocated' : List String),
      Extends allocated allocated' ∧ MemberIn decls allocated' v t) →
    ∀ allocated : List String, ∃ (xs : List Val) (ps : List (Val × Ty)) (allocated' : List String),
      Extends allocated allocated' ∧ itemPairs l xs = some ps ∧
      ∀ p ∈ ps, MemberIn decls allocated' p.1 p.2
  | [], _, allocated =>
    ⟨[], [], allocated, fun _ _ h => h, rfl, fun _ hp => absurd hp List.not_mem_nil⟩
  | t :: l, hw, allocated => by
    obtain ⟨x, al1, e1, hx⟩ := hw t List.mem_cons_self allocated
    obtain ⟨xs, ps, al2, e2, hps, hall⟩ :=
      itemPairs_fresh l (fun u hu => hw u (List.mem_cons_of_mem _ hu)) al1
    refine ⟨x :: xs, (x, t) :: ps, al2, fun i s hi => e2 i s (e1 i s hi), ?_, ?_⟩
    · show (itemPairs l xs).map ((x, t) :: ·) = some ((x, t) :: ps)
      rw [hps]
      rfl
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact memberIn_mono e2 hx
      · exact hall p hp

/-- The record arm of a round's algebra. -/
theorem TyDecls.inhabitedWith_record (decls : TyDecls) (known : List String)
    (fs : List (String × Bool × Ty)) :
    cata_ty (decls.inhabitedWith known) (.record fs) =
      (Ty.canon fs).all fun q => q.2.1 || cata_ty (decls.inhabitedWith known) q.2.2 := by
  rw [cata_ty_record]
  have hpm : prodMapSnd (prodMapSnd (cata_ty (decls.inhabitedWith known))) =
      fun q : String × Bool × Ty => (q.1, prodMapSnd (cata_ty (decls.inhabitedWith known)) q.2) :=
    rfl
  rw [hpm]
  show (Ty.canon (fs.map fun q => (q.1, prodMapSnd (cata_ty (decls.inhabitedWith known)) q.2))).all
    (fun p => p.2.1 || p.2.2) = _
  rw [Ty.canon, Ty.canon, Field.canonBy_map]
  exact List.all_map

/-- A declared reference with a witnessed declaration has a member at an extension of any
allocation table. -/
theorem exists_memberIn_ref {decls : TyDecls} {known : List String} (hk : decls.Witnessed known)
    {t : Ty} {name : String} {body : Ty} (hu : decls.unfold? t = some (name, body))
    (hc : known.contains name = true) (allocated : List String) :
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      MemberIn decls allocated' v t :=
  have ⟨v, al', e, hv⟩ :=
    hk name (List.contains_iff_mem.mp hc) body (TyDecls.body?_of_unfold? hu) allocated
  ⟨v, al', e, .unfold hu hv⟩

/-- **A round's algebra is complete when its known names are witnessed**: a type that the round
calls inhabited has a member at an extension of any allocation table. Placement: concept
`store-typing`, R3, a step of the claim `recursive-types-inhabited`. Route: induct on `t`, as
`fits_of_inhabited_fresh` does. A union or an `except` takes a side that is inhabited; a product,
a tuple and a record's required fields build their parts in turn, each at the table the previous
part left, and carry the earlier parts forward (`memberIn_mono`). An external handle takes the
fresh index `allocated.length`. A declared name takes its witness from `hk`; an option, a list, a
map, an exit and a cause have a member with no question. Consumer: `witnessed_inhabitedNames`. -/
@[semantics "store-typing" (requirement := R3)]
theorem exists_memberIn_fresh {decls : TyDecls} {known : List String}
    (hk : decls.Witnessed known) (t : Ty) (h : cata_ty (decls.inhabitedWith known) t = true)
    (allocated : List String) :
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      MemberIn decls allocated' v t := by
  induction t generalizing allocated with
  | never => cases h
  | var _ => cases h
  | unit => exact ⟨.unit, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | nat => exact ⟨.nat 0, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | int => exact ⟨.nat 0, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | number => exact ⟨.nat 0, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | string => exact ⟨.str "", allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | bool => exact ⟨.bool true, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | lit s =>
    exact ⟨.str s, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl (beq_iff_eq.mpr rfl)⟩
  | null => exact ⟨.none, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | undefined => exact ⟨.unit, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | bytes => exact ⟨.bytes [], allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | unknown => exact ⟨.unit, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | fiberOf _ _ _ _ =>
    exact ⟨Val.fiber ⟨0⟩, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | refOf _ _ => exact ⟨Val.cell ⟨0⟩, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | deferredOf _ _ _ _ =>
    exact ⟨Val.promise ⟨0⟩, allocated, fun _ _ h => h, memberIn_of_hasTy rfl rfl rfl⟩
  | contextOf keys =>
    obtain ⟨services, _, hkeys⟩ := Typed.context_services_fresh
      (Typed.initialWorld (EffTy.pure .unit) fun _ => some .unit)
      (fun _ => ⟨.unit, .unit, rfl, trivial, Typed.live_of_handles_nil rfl⟩) keys.elems
    refine ⟨Val.context (Ctx.withServices services), allocated, fun _ _ h => h,
      memberIn_of_hasTy rfl rfl ?_⟩
    have hctx : Val.context? (Val.context (Ctx.withServices services)) =
        some (Ctx.withServices services) := ctxImage.ofVal_toVal _
    show (match Val.context? (Val.context (Ctx.withServices services)) with
      | some ctx => keys.elems.all fun key => (ctx.services.getV key).isSome
      | none => false) = true
    rw [hctx, List.all_eq_true]
    intro key hkey
    obtain ⟨_, value, _, hg, _⟩ := hkeys key hkey
    show (services.getV key).isSome = true
    rw [hg]
    rfl
  | option _ _ => exact ⟨.none, allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | list _ _ => exact ⟨.list [], allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | map _ _ _ _ =>
    exact ⟨.list [], allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | exitOf _ _ _ _ =>
    exact ⟨Val.exitErr ⟨[]⟩, allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | causeOf _ _ =>
    exact ⟨Val.exitErr ⟨[]⟩, allocated, fun _ _ h => h, .step rfl rfl fun _ hp => nomatch hp⟩
  | handle target =>
    obtain ⟨v, al', e, hv⟩ := exists_hasTy_handle_fresh (Typed.not_retired_of_inhabited h) allocated
    exact ⟨v, al', e, memberIn_of_hasTy rfl rfl hv⟩
  | app name args _ =>
    cases hb : decls.body? name with
    | some body =>
      have hc : known.contains name = true := by
        have h' : (if (decls.body? name).isSome then known.contains name
            else inhabitedAlg.ty_app name (args.map (cata_ty (decls.inhabitedWith known)))) =
            true := h
        rw [hb, Option.isSome_some, if_pos rfl] at h'
        exact h'
      have hu : decls.unfold? (.app name args) = some (name, body) := by
        show (decls.body? name).map (name, ·) = _
        rw [hb]
        rfl
      exact exists_memberIn_ref hk hu hc allocated
    | none =>
      have hr : retiredHandleTargets.contains name = false := by
        have h' : (if (decls.body? name).isSome then known.contains name
            else inhabitedAlg.ty_app name (args.map (cata_ty (decls.inhabitedWith known)))) =
            true := h
        rw [hb, Option.isSome_none] at h'
        exact Typed.not_retired_of_inhabited h'
      have hu : decls.unfold? (.app name args) = none := by
        show (decls.body? name).map (name, ·) = _
        rw [hb]
        rfl
      obtain ⟨v, al', e, hv⟩ := exists_hasTy_handle_fresh hr allocated
      exact ⟨v, al', e, memberIn_of_hasTy hu rfl hv⟩
  | prod a b iha ihb =>
    have h' : (cata_ty (decls.inhabitedWith known) a && cata_ty (decls.inhabitedWith known) b) =
      true := h
    obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp h'
    obtain ⟨va, al1, e1, ma⟩ := iha ha allocated
    obtain ⟨vb, al2, e2, mb⟩ := ihb hb al1
    refine ⟨.list [va, vb], al2, fun i s hi => e2 i s (e1 i s hi), .step rfl rfl ?_⟩
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact memberIn_mono e2 ma
    · rcases List.mem_singleton.mp hp with rfl
      exact mb
  | except e a ihe iha =>
    have h' : (cata_ty (decls.inhabitedWith known) e || cata_ty (decls.inhabitedWith known) a) =
      true := h
    rcases Bool.or_eq_true_iff.mp h' with he | ha
    · obtain ⟨v, al', ext, hv⟩ := ihe he allocated
      refine ⟨.ctor 0 [v], al', ext, .step rfl rfl ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      exact hv
    · obtain ⟨v, al', ext, hv⟩ := iha ha allocated
      refine ⟨.ctor 1 [v], al', ext, .step rfl rfl ?_⟩
      intro p hp
      rcases List.mem_singleton.mp hp with rfl
      exact hv
  | union l r ihl ihr =>
    have h' : (cata_ty (decls.inhabitedWith known) l || cata_ty (decls.inhabitedWith known) r) =
      true := h
    rcases Bool.or_eq_true_iff.mp h' with hl | hr
    · obtain ⟨v, al', ext, hv⟩ := ihl hl allocated
      exact ⟨v, al', ext, .left hv⟩
    · obtain ⟨v, al', ext, hv⟩ := ihr hr allocated
      exact ⟨v, al', ext, .right hv⟩
  | tuple ts ih =>
    rw [cata_ty_tuple] at h
    have h' : (ts.map (cata_ty (decls.inhabitedWith known))).all id = true := h
    rw [List.all_map, List.all_eq_true] at h'
    obtain ⟨xs, ps, al', ext, hps, hall⟩ :=
      itemPairs_fresh ts (fun u hu al => ih u hu (h' u hu) al) allocated
    exact ⟨.list xs, al', ext, .step rfl hps hall⟩
  | record fs ih =>
    rw [TyDecls.inhabitedWith_record, List.all_eq_true] at h
    obtain ⟨ns, xs, ps, al', ext, _, hps, hall⟩ :=
      namedPairs_fresh (Ty.canon fs) (Field.canonBy_names_nodup _)
        (fun q hq hreq al => ih q (Ty.mem_canon hq)
          (by
            have hq' := h q hq
            rw [hreq, Bool.false_or] at hq'
            exact hq') al)
        allocated
    exact ⟨.ctor 0 [.list ns, .list xs], al', ext, .step rfl hps hall⟩

/-- **The iteration keeps its invariant**: every name it adds has a witnessed declaration. -/
theorem witnessed_inhabitedNames (decls : TyDecls) : decls.Witnessed decls.inhabitedNames := by
  refine decls.saturate_inv decls.inhabitedHolds
    (R := fun name => ∀ body, decls.body? name = some body → ∀ allocated : List String,
      ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
        MemberIn decls allocated' v body)
    ?_ [] (fun _ hn => absurd hn List.not_mem_nil)
  intro known hk name hh body hb
  unfold TyDecls.inhabitedHolds at hh
  rw [hb] at hh
  exact exists_memberIn_fresh hk body hh

/-- **Inhabitance is complete against membership under the table**: an inhabited type has a
member at some allocation table. Placement: concept `store-typing`, R3, a step of the claim
`recursive-types-inhabited`, from `exists_memberIn_fresh` and the round invariant. Consumer: `inhabited_iff_memberIn`. It establishes nothing of a world
(`Fits`). -/
@[semantics "store-typing" (requirement := R3)]
theorem exists_memberIn_of_inhabited {decls : TyDecls} {t : Ty}
    (h : decls.inhabited t = true) :
    ∃ (v : Val) (allocated : List String), MemberIn decls allocated v t :=
  have ⟨v, allocated, _, hv⟩ := exists_memberIn_fresh (witnessed_inhabitedNames decls) t h []
  ⟨v, allocated, hv⟩

/-- **Inhabitance agrees with membership under the table** (claim `recursive-types-inhabited`):
the least fixed point over the table says `true` exactly where some value is a member. The
soundness half is proved (`inhabited_of_memberIn`); the completeness half is
`exists_memberIn_of_inhabited`. -/
@[semantics "store-typing" (requirement := R3)]
theorem inhabited_iff_memberIn {decls : TyDecls} {t : Ty} :
    decls.inhabited t = true ↔ ∃ (v : Val) (allocated : List String), MemberIn decls allocated v t :=
  ⟨exists_memberIn_of_inhabited, fun ⟨_, _, h⟩ => inhabited_of_memberIn h⟩

/-! ### Normalization: its part -/

/-- The fold reads a list of members joined by `Ty.ofMembers` as their disjunction. -/
theorem cata_declAlg_ofMembers (decls : TyDecls) (o : String → Adm) (v : Val)
    (allocated : List String) : ∀ xs : List Ty,
    (cata_ty (declAlg decls o) (Ty.ofMembers xs)).2 v allocated =
      xs.any fun t => (cata_ty (declAlg decls o) t).2 v allocated
  | [] => rfl
  | [x] => by simp only [Ty.ofMembers, List.any_cons, List.any_nil, Bool.or_false]
  | x :: y :: ys => by
    change ((cata_ty (declAlg decls o) x).2 v allocated ||
      (cata_ty (declAlg decls o) (Ty.ofMembers (y :: ys))).2 v allocated) = _
    rw [cata_declAlg_ofMembers decls o v allocated (y :: ys)]
    rfl

/-- A union row's normal form keeps a member above each one it drops (`cata_admits_sub` at
`declAlg_admitsSub`), so the fold admits the same values. -/
theorem cata_declAlg_normalizeRow (decls : TyDecls) (o : String → Adm) (v : Val)
    (allocated : List String) (xs : List Ty) :
    (Ty.normalizeRow xs).elems.any (fun t => (cata_ty (declAlg decls o) t).2 v allocated) =
      xs.any fun t => (cata_ty (declAlg decls o) t).2 v allocated := by
  rw [← any_row_normalize xs (fun t => (cata_ty (declAlg decls o) t).2 v allocated)]
  apply Bool.eq_iff_iff.mpr
  simp only [Ty.normalizeRow, List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, Effect4.Row.antichain_subset Ty.sub ht, hv⟩
  · rintro ⟨t, ht, hv⟩
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage Ty.sub Ty.sub_refl
      Ty.sub_trans (Effect4.Row.normalize xs).elems t ht
    exact ⟨u, hu, cata_admits_sub (declAlg_admitsSub decls o) htu v allocated hv⟩

/-- The fold at a product: a pair whose sides the two factors admit. -/
theorem cata_declAlg_prod (decls : TyDecls) (o : String → Adm) (a b : Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) (.prod a b)).2 v allocated =
      match v with
      | .list [x, y] =>
        (cata_ty (declAlg decls o) a).2 x allocated && (cata_ty (declAlg decls o) b).2 y allocated
      | _ => false := rfl

/-- The fold reads a type by its factors. -/
theorem cata_declAlg_factors (decls : TyDecls) (o : String → Adm) (v : Val)
    (allocated : List String) (t : Ty) :
    t.factors.any (fun u => (cata_ty (declAlg decls o) u).2 v allocated) =
      (cata_ty (declAlg decls o) t).2 v allocated := by
  cases t with
  | never => rfl
  | _ => exact (cata_declAlg_members decls o _ v allocated).symm

/-- The fold reads a product by the products of its factors. -/
theorem cata_declAlg_productMembers (decls : TyDecls) (o : String → Adm) (v : Val)
    (allocated : List String) (a b : Ty) :
    (Ty.productMembers a b).any (fun t => (cata_ty (declAlg decls o) t).2 v allocated) =
      (cata_ty (declAlg decls o) (.prod a b)).2 v allocated := by
  simp only [Ty.productMembers, List.any_flatMap, List.any_map, Function.comp_def,
    cata_declAlg_prod]
  split
  · rename_i x y
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨ta, hta, tb, htb, hx, hy⟩
      exact ⟨(Bool.eq_iff_iff.mp (cata_declAlg_factors decls o x allocated a)).mp
          (List.any_eq_true.mpr ⟨ta, hta, hx⟩),
        (Bool.eq_iff_iff.mp (cata_declAlg_factors decls o y allocated b)).mp
          (List.any_eq_true.mpr ⟨tb, htb, hy⟩)⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨ta, hta, hx⟩ := List.any_eq_true.mp
        ((Bool.eq_iff_iff.mp (cata_declAlg_factors decls o x allocated a)).mpr hx)
      obtain ⟨tb, htb, hy⟩ := List.any_eq_true.mp
        ((Bool.eq_iff_iff.mp (cata_declAlg_factors decls o y allocated b)).mpr hy)
      exact ⟨ta, hta, tb, htb, hx, hy⟩
  · apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨_, _, hx⟩ := List.any_eq_true.mp h
    obtain ⟨_, _, hy⟩ := List.any_eq_true.mp hx
    exact Bool.false_ne_true hy

/-- Normalization of a product keeps the fold's admission, given it at both factors. -/
theorem cata_declAlg_normalize_prod (decls : TyDecls) (o : String → Adm) (a b : Ty) (v : Val)
    (allocated : List String)
    (iha : ∀ v allocated, (cata_ty (declAlg decls o) a.normalize).2 v allocated =
      (cata_ty (declAlg decls o) a).2 v allocated)
    (ihb : ∀ v allocated, (cata_ty (declAlg decls o) b.normalize).2 v allocated =
      (cata_ty (declAlg decls o) b).2 v allocated) :
    (cata_ty (declAlg decls o) (Ty.prod a b).normalize).2 v allocated =
      (cata_ty (declAlg decls o) (.prod a b)).2 v allocated := by
  show (cata_ty (declAlg decls o) (Ty.ofMembers (Ty.normalizeRow
    (Ty.productMembers a.normalize b.normalize)).elems)).2 v allocated = _
  rw [cata_declAlg_ofMembers, cata_declAlg_normalizeRow, cata_declAlg_productMembers,
    cata_declAlg_prod, cata_declAlg_prod]
  split
  · rw [iha, ihb]
  · rfl

/-- The fold at a tuple: a list read item by item. -/
theorem cata_declAlg_tuple (decls : TyDecls) (o : String → Adm) (ts : List Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) (.tuple ts)).2 v allocated =
      match v with
      | .list xs => itemsHasTy (ts.map fun u x => (cata_ty (declAlg decls o) u).2 x allocated) xs
      | _ => false := by
  show (Val.hasTy.alg.ty_tuple (cata_pos_list_ty (declAlg decls o) ts)).2 v allocated = _
  dsimp only [Val.hasTy.alg]
  cases v
  case list xs =>
    rw [itemCheckers_foldr, cata_pos_list_ty_eq, List.map_map]
    rfl
  all_goals rfl

/-- A pair tuple and a product have the fold's same admission. -/
theorem cata_declAlg_tuple_pair (decls : TyDecls) (o : String → Adm) (a b : Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) (.tuple [a, b])).2 v allocated =
      (cata_ty (declAlg decls o) (.prod a b)).2 v allocated := by
  rw [cata_declAlg_tuple, cata_declAlg_prod]
  cases v
  case list xs =>
    match xs with
    | [] => rfl
    | [_] => simp only [List.map_cons, List.map_nil, itemsHasTy, Bool.and_false]
    | [_, _] => simp only [List.map_cons, List.map_nil, itemsHasTy, Bool.and_true]
    | _ :: _ :: _ :: _ => simp only [List.map_cons, List.map_nil, itemsHasTy, Bool.and_false]
  all_goals rfl

/-- The fold at a record: the canonical fields read by name. -/
theorem cata_declAlg_record (decls : TyDecls) (o : String → Adm) (fs : List (String × Bool × Ty))
    (v : Val) (allocated : List String) :
    (cata_ty (declAlg decls o) (.record fs)).2 v allocated =
      match recordParts? v with
      | some (ns, xs) => namedHasTy ((Ty.canon fs).map fun c =>
          (c.1, c.2.1, fun x => (cata_ty (declAlg decls o) c.2.2).2 x allocated)) ns xs
      | none => false := by
  show (Val.hasTy.alg.ty_record (cata_pos_list_prod_string_prod_bool_ty (declAlg decls o) fs)).2 v
    allocated = _
  dsimp only [Val.hasTy.alg]
  cases recordParts? v with
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    dsimp only
    rw [fieldCheckers_foldr, cata_pos_list_prod_string_prod_bool_ty_eq, List.map_map]
    have hmap : ((fun q => (q.1, admChecker allocated q.2)) ∘
        prodMapSnd (prodMapSnd (cata_ty (declAlg decls o)))) =
        fun c : String × Bool × Ty =>
          (c.1, c.2.1, fun x => (cata_ty (declAlg decls o) c.2.2).2 x allocated) := rfl
    rw [hmap]
    have hcanon := Field.canonBy_map (key := Field.bytesKey)
      (fun c : Bool × Ty => (c.1, fun x => (cata_ty (declAlg decls o) c.2).2 x allocated)) fs
    rw [Ty.canon, hcanon, ← Ty.canon]
  | none => rfl

/-- The fold at a reference reads its name alone: the oracle at a declared name, the handle arm at
any other. -/
theorem cata_declAlg_app (decls : TyDecls) (o : String → Adm) (name : String) (args : List Ty)
    (v : Val) (allocated : List String) :
    (cata_ty (declAlg decls o) (.app name args)).2 v allocated =
      match decls.body? name with
      | some _ => o name v allocated
      | none => Val.hasTy v (.handle name) allocated := by
  show ((declAlg decls o).ty_app name _).2 v allocated = _
  unfold declAlg
  dsimp only
  cases decls.body? name with
  | some _ => rfl
  | none => exact (Val.hasTy.eq_cata v (.app name args) allocated).symm

/-- **The fold under any oracle is invariant under normalization.** Placement: concept
`store-typing`, R3, the step of the claim `recursive-types-normalize`. Route: `hasTy_normalize`'s
induction, arm by arm, over the fold. `declAlg`'s arms are `Val.hasTy.alg`'s except at a
reference, which reads its name alone (`cata_declAlg_app`). A union's normal form keeps a member above each one it drops
(`cata_declAlg_normalizeRow`), and the congruence arms are `AdmitsNormalize`'s
(`Val.hasTy_admitsNormalize`). At the empty table it is `hasTy_normalize` (`declAlg_nil`).
Consumer: `memberIn_normalize`. -/
@[semantics "store-typing" (requirement := R3)]
theorem cata_declAlg_normalize (decls : TyDecls) (o : String → Adm) (t : Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) t.normalize).2 v allocated =
      (cata_ty (declAlg decls o) t).2 v allocated := by
  induction t generalizing v allocated with
  | never | unknown | unit | nat | int | string | bool | handle | lit | var | null | undefined
  | number | bytes | contextOf => rfl
  | fiberOf _ _ _ _ | refOf _ _ | deferredOf _ _ _ _ => rfl
  | option t ih =>
    show (Val.hasTy.alg.ty_option (cata_ty (declAlg decls o) t.normalize)).2 v allocated =
      (Val.hasTy.alg.ty_option (cata_ty (declAlg decls o) t)).2 v allocated
    rw [Val.hasTy_admitsNormalize.option _ _ (funext fun x => funext fun a => ih x a)]
  | list t ih =>
    show (Val.hasTy.alg.ty_list (cata_ty (declAlg decls o) t.normalize)).2 v allocated =
      (Val.hasTy.alg.ty_list (cata_ty (declAlg decls o) t)).2 v allocated
    rw [Val.hasTy_admitsNormalize.list _ _ (funext fun x => funext fun a => ih x a)]
  | except e a ihe iha =>
    show (Val.hasTy.alg.ty_except (cata_ty (declAlg decls o) e.normalize)
      (cata_ty (declAlg decls o) a.normalize)).2 v allocated =
      (Val.hasTy.alg.ty_except (cata_ty (declAlg decls o) e) (cata_ty (declAlg decls o) a)).2 v
        allocated
    rw [Val.hasTy_admitsNormalize.except _ _ _ _ (funext fun x => funext fun al => ihe x al)
      (funext fun x => funext fun al => iha x al)]
  | exitOf a e iha ihe =>
    show (Val.hasTy.alg.ty_exitOf (cata_ty (declAlg decls o) a.normalize)
      (cata_ty (declAlg decls o) e.normalize)).2 v allocated =
      (Val.hasTy.alg.ty_exitOf (cata_ty (declAlg decls o) a) (cata_ty (declAlg decls o) e)).2 v
        allocated
    rw [Val.hasTy_admitsNormalize.exitOf _ _ _ _ (funext fun x => funext fun al => iha x al)
      (funext fun x => funext fun al => ihe x al)]
  | causeOf e ih =>
    show (Val.hasTy.alg.ty_causeOf (cata_ty (declAlg decls o) e.normalize)).2 v allocated =
      (Val.hasTy.alg.ty_causeOf (cata_ty (declAlg decls o) e)).2 v allocated
    rw [Val.hasTy_admitsNormalize.causeOf _ _ (funext fun x => funext fun a => ih x a)]
  | map k t ihk iht =>
    have hk : (cata_ty (declAlg decls o) k.normalize).2 = (cata_ty (declAlg decls o) k).2 :=
      funext fun x => funext fun a => ihk x a
    have ht : (cata_ty (declAlg decls o) t.normalize).2 = (cata_ty (declAlg decls o) t).2 :=
      funext fun x => funext fun a => iht x a
    show (Val.hasTy.alg.ty_map (cata_ty (declAlg decls o) k.normalize)
      (cata_ty (declAlg decls o) t.normalize)).2 v allocated =
      (Val.hasTy.alg.ty_map (cata_ty (declAlg decls o) k) (cata_ty (declAlg decls o) t)).2 v
        allocated
    dsimp only [Val.hasTy.alg]
    rw [hk, ht]
  | union a b iha ihb =>
    show (cata_ty (declAlg decls o) (Ty.ofMembers (Ty.normalizeRow
      (a.normalize.members ++ b.normalize.members)).elems)).2 v allocated = _
    rw [cata_declAlg_ofMembers, cata_declAlg_normalizeRow, List.any_append,
      ← cata_declAlg_members, ← cata_declAlg_members, iha, ihb]
    rfl
  | prod a b iha ihb => exact cata_declAlg_normalize_prod decls o a b v allocated iha ihb
  | tuple ts ih =>
    cases Nat.decEq ts.length 2 with
    | isTrue h2 =>
      match ts, h2, ih with
      | [a, b], _, ih =>
        rw [cata_declAlg_tuple_pair]
        exact cata_declAlg_normalize_prod decls o a b v allocated (ih a List.mem_cons_self)
          (ih b (List.mem_cons_of_mem _ List.mem_cons_self))
    | isFalse h2 =>
      rw [Ty.normalize_tuple_of_ne ts h2, Ty.normalizeItems_eq_map, cata_declAlg_tuple,
        cata_declAlg_tuple]
      split
      · rw [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        funext x
        exact ih u hu x allocated
      · rfl
  | record fs ih =>
    rw [Ty.normalize_record, cata_declAlg_record, cata_declAlg_record]
    split
    · rename_i ns xs _
      rw [Ty.canon, Field.canonBy_of_ascending _
        (Field.ascending_map Ty.normPayload (Field.canonBy_ascending fs)), List.map_map,
        ← Ty.canon]
      congr 1
      apply List.map_congr_left
      intro q hq
      have hfun : (fun x => (cata_ty (declAlg decls o) (Ty.normPayload q.2).2).2 x allocated) =
          fun x => (cata_ty (declAlg decls o) q.2.2).2 x allocated :=
        funext fun x => ih q (Ty.mem_canon hq) x allocated
      simp only [Function.comp_apply]
      rw [← hfun]
      rfl
    · rfl
  | app name args _ => rw [Ty.normalize_app name _, cata_declAlg_app, cata_declAlg_app]

/-- **Membership under the table is invariant under normalization** (claim
`recursive-types-normalize`). It is what the checker's order needs: `Ty.subN` compares normal
forms, and a reference keeps its name in its normal form (decisions row 406 (1)).
Proved modulo its part `cata_declAlg_normalize`. Consumer: `Ty.subN` under a table, and the
world's `fits_normalize` once the table enters the world. It establishes nothing of `Fits`. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_normalize (decls : TyDecls) (allocated : List String) (v : Val) (t : Ty) :
    MemberIn decls allocated v t.normalize ↔ MemberIn decls allocated v t := by
  rw [memberIn_iff_cata, memberIn_iff_cata, cata_declAlg_normalize]

/-! ### The guarded fixed point: its parts -/

/-- An oracle is a **fixed point** of the table when each declared name admits what the fold
admits at its body, its own names read from the oracle. `MemberIn` is one on every table
(`checkerOracle_fixedPoint`), and the least one (`memberIn_iff_cata`, `cata_of_memberIn`). -/
def FixedPoint (decls : TyDecls) (o : String → Adm) : Prop :=
  ∀ (name : String) (body : Ty), decls.body? name = some body →
    o name = (cata_ty (declAlg decls o) body).2

/-- **Membership is a fixed point of every table**, guarded or not: the checker at a declared
name admits what the fold at the checker's oracle admits at the name's body. Placement: concept
`store-typing`, R3, a step of the claim `guarded-fixed-point-unique`. Consumer:
`guarded_fixedPoint_unique`. -/
theorem checkerOracle_fixedPoint (decls : TyDecls) : FixedPoint decls (checkerOracle decls) := by
  intro name body hb
  funext v allocated
  have hc : checkerOracle decls name v allocated = Val.hasTyIn decls [name] v body allocated := by
    unfold checkerOracle
    rw [hb]
  rw [hc]
  apply Bool.eq_iff_iff.mpr
  rw [← memberIn_iff_cata]
  exact ⟨memberIn_of_hasTyIn [name] v body,
    fun h => (hasTyIn_absorb hb [] v body (hasTyIn_of_memberIn h)).elim id id⟩

/-- A guarded table ranks each of its declared names. -/
theorem TyDecls.mem_rankedNames {decls : TyDecls} (hg : decls.guarded = true) {name : String}
    {body : Ty} (hb : decls.body? name = some body) : name ∈ decls.rankedNames := by
  unfold TyDecls.guarded TyDecls.unguardedAt? at hg
  cases hf : decls.find? (fun d => !decls.rankedNames.contains d.1) with
  | some d =>
    rw [hf] at hg
    cases hg
  | none =>
    have hn := List.find?_eq_none.mp hf (name, body) (TyDecls.mem_of_body? hb)
    cases hc : decls.rankedNames.contains name with
    | true => exact List.contains_iff_mem.mp hc
    | false =>
      rw [hc] at hn
      exact absurd rfl hn

/-- The fold reads a union member's verdict from the two oracles alike when they agree at the
member's name, or when the member names none and the fold agrees at every question. -/
theorem cata_declAlg_member_agree {decls : TyDecls} {o o' : String → Adm} {m : Ty}
    (hm : m.isMember = true) (v : Val) (allocated : List String)
    (href : ∀ name body, decls.unfold? m = some (name, body) → o name v allocated = o' name v allocated)
    (hq : ∀ ps, Val.obligations v m allocated = some ps → ∀ p ∈ ps,
      (cata_ty (declAlg decls o) p.2).2 p.1 allocated = (cata_ty (declAlg decls o') p.2).2 p.1 allocated) :
    (cata_ty (declAlg decls o) m).2 v allocated = (cata_ty (declAlg decls o') m).2 v allocated := by
  rw [cata_declAlg_step decls o hm, cata_declAlg_step decls o' hm]
  cases hu : decls.unfold? m with
  | some x =>
    obtain ⟨name, body⟩ := x
    exact href name body hu
  | none =>
    unfold obligationsAll
    cases hobl : Val.obligations v m allocated with
    | none => rfl
    | some ps =>
      apply Bool.eq_iff_iff.mpr
      rw [List.all_eq_true, List.all_eq_true]
      exact forall_congr' fun p => imp_congr_right fun hp => by
        dsimp only
        rw [hq ps hobl p hp]

/-- The fold reads a type's verdict from the two oracles alike when it does at every member. -/
theorem cata_declAlg_agree_of_members {decls : TyDecls} {o o' : String → Adm} (t : Ty) (v : Val)
    (allocated : List String)
    (h : ∀ m ∈ t.members,
      (cata_ty (declAlg decls o) m).2 v allocated = (cata_ty (declAlg decls o') m).2 v allocated) :
    (cata_ty (declAlg decls o) t).2 v allocated = (cata_ty (declAlg decls o') t).2 v allocated := by
  rw [cata_declAlg_members decls o, cata_declAlg_members decls o']
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, List.any_eq_true]
  exact exists_congr fun m => and_congr_right fun hm => by rw [h m hm]

/-- **At one value, two fixed points of a guarded table agree at every type**, given that they
do at smaller values, by recursion on the value's size. At the value itself the names agree
round by round of the ranking: a name's declaration has at its head only names ranked before it,
whose oracles agree, and members that ask their questions at smaller values. A step of
`fixedPoint_agree`. -/
theorem fixedPoint_agree_at {decls : TyDecls} (hg : decls.guarded = true) {o o' : String → Adm}
    (ho : FixedPoint decls o) (ho' : FixedPoint decls o') (allocated : List String) (v : Val)
    (t : Ty) :
    (cata_ty (declAlg decls o) t).2 v allocated = (cata_ty (declAlg decls o') t).2 v allocated := by
  have hsmall : ∀ ps, ∀ m, Val.obligations v m allocated = some ps → ∀ p ∈ ps,
      (cata_ty (declAlg decls o) p.2).2 p.1 allocated =
        (cata_ty (declAlg decls o') p.2).2 p.1 allocated :=
    fun ps m hobl p hp =>
      have := Val.sizeOf_obligation hobl hp
      fixedPoint_agree_at hg ho ho' allocated p.1 p.2
  have hranked : ∀ n ∈ decls.rankedNames, ∀ body, decls.body? n = some body →
      o n v allocated = o' n v allocated := by
    refine decls.saturate_inv decls.rankHolds
      (R := fun n => ∀ body, decls.body? n = some body → o n v allocated = o' n v allocated)
      ?_ [] (fun _ hn => absurd hn List.not_mem_nil)
    intro known hk n hh body hb
    unfold TyDecls.rankHolds at hh
    rw [hb, List.all_eq_true] at hh
    rw [ho n body hb, ho' n body hb]
    refine cata_declAlg_agree_of_members body v allocated fun m hm => ?_
    refine cata_declAlg_member_agree (Ty.members_isMember hm) v allocated ?_
      fun ps hobl => hsmall ps m hobl
    intro name body' hu
    have hname : name ∈ decls.headNames body :=
      List.mem_filterMap.mpr ⟨m, hm, by rw [hu]; rfl⟩
    exact hk name (List.contains_iff_mem.mp (hh name hname)) body' (TyDecls.body?_of_unfold? hu)
  refine cata_declAlg_agree_of_members t v allocated fun m hm => ?_
  refine cata_declAlg_member_agree (Ty.members_isMember hm) v allocated ?_
    fun ps hobl => hsmall ps m hobl
  intro name body hu
  have hb := TyDecls.body?_of_unfold? hu
  exact hranked name (TyDecls.mem_rankedNames hg hb) body hb
termination_by sizeOf v

/-- **Two fixed points of a guarded table agree** at every declared name. Placement: concept
`store-typing`, R3, the step of the claim `guarded-fixed-point-unique`. Route: recursion on the
value's size; at one value, induction over the rounds of the ranking (`fixedPoint_agree_at`,
`TyDecls.rankedNames`). Consumer: `guarded_fixedPoint_unique`. On an unguarded table it fails:
at `A = A` every oracle is a fixed point, the constant `true` among them (the battery's control). -/
@[semantics "store-typing" (requirement := R3)]
theorem fixedPoint_agree {decls : TyDecls} (hg : decls.guarded = true) {o o' : String → Adm}
    (ho : FixedPoint decls o) (ho' : FixedPoint decls o') {name : String} {body : Ty}
    (hb : decls.body? name = some body) : o name = o' name := by
  funext v allocated
  rw [ho name body hb, ho' name body hb]
  exact fixedPoint_agree_at hg ho ho' allocated v body

/-- **On a guarded table the fixed point is unique** (claim `guarded-fixed-point-unique`): every
fixed point admits exactly the members of each body. So the least fixed point is no choice
there: it is the greatest one too. Proved from `fixedPoint_agree`. Consumer: the
formal note's argument that guardedness fixes the meaning, and the table's admission. -/
@[semantics "store-typing" (requirement := R3)]
theorem guarded_fixedPoint_unique {decls : TyDecls} (hg : decls.guarded = true)
    {o : String → Adm} (ho : FixedPoint decls o) {name : String} {body : Ty}
    (hb : decls.body? name = some body) (v : Val) (allocated : List String) :
    o name v allocated = true ↔ MemberIn decls allocated v body := by
  rw [fixedPoint_agree hg ho (checkerOracle_fixedPoint decls) hb,
    checkerOracle_fixedPoint decls name body hb]
  exact memberIn_iff_cata.symm

end Effect4.Program
