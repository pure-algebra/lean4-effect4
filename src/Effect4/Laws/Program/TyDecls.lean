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
    ty_handle := fun name =>
      match decls.body? name with
      | some _ => (.handle name, o name)
      | none => Val.hasTy.alg.ty_handle name
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
  case handle name =>
    show ((declAlg decls o).ty_handle name).2 v allocated = _
    unfold declAlg TyDecls.unfold?
    simp only [Ty.refName?, Option.bind_some]
    cases decls.body? name with
    | some b => rfl
    | none => exact (obligationsAll_leaf (t := .handle name) _ rfl).symm
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

/-- **The iteration stops at a closed set**: every name of a round on its answer is in it. -/
theorem inhabitedFrom_closed (decls : TyDecls) : ∀ (known : List String) (name : String),
    name ∈ decls.inhabitedRound (decls.inhabitedFrom known) → name ∈ decls.inhabitedFrom known := by
  intro known
  induction known using TyDecls.inhabitedFrom.induct decls with
  | case1 known hstop =>
    intro name hname
    rw [inhabitedFrom, dif_pos hstop] at hname ⊢
    cases hc : known.contains name with
    | true => exact List.contains_iff_mem.mp hc
    | false =>
      have hfresh : name ∈ (decls.inhabitedRound known).filter fun n => !known.contains n :=
        List.mem_filter.mpr ⟨hname, by rw [hc]; rfl⟩
      rw [hstop] at hfresh
      cases hfresh
  | case2 known hmore ih =>
    intro name hname
    rw [inhabitedFrom, dif_neg hmore] at hname ⊢
    exact ih name hname

/-- A declared name whose body the iteration's answer calls inhabited is in the answer. -/
theorem mem_inhabitedNames {decls : TyDecls} {name : String} {body : Ty}
    (hb : decls.body? name = some body)
    (h : cata_ty (decls.inhabitedWith decls.inhabitedNames) body = true) :
    name ∈ decls.inhabitedNames := by
  refine inhabitedFrom_closed decls [] name (List.mem_filterMap.mpr ⟨(name, body), mem_of_body? hb, ?_⟩)
  show (decls.body? name).bind (fun body =>
    if cata_ty (decls.inhabitedWith decls.inhabitedNames) body = true then some name
    else none) = some name
  rw [hb, Option.bind_some, if_pos h]

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
  case handle name =>
    unfold unfold? at hu
    simp only [Ty.refName?, Option.bind_some] at hu
    refine hleaf ?_ rfl hps
    show (if (decls.body? name).isSome then _ else _) = _
    cases hb : decls.body? name with
    | some b =>
      rw [hb] at hu
      cases hu
    | none => rfl
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
    case handle n =>
      cases href
      show (if (decls.body? name).isSome then _ else _) = true
      rw [hb, Option.isSome_some, if_pos rfl]
      exact hname
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

A name's declaration is read at its first entry in both judgments (`TyDecls.inhabitedRound`
reads `body?`). On a table with a repeated name, reading every entry made inhabitance answer
`true` at `[("A", never), ("A", unit)]`, where no value is a member of `A`. The battery keeps that
table as a control. -/

/-- **Membership survives the growth of the allocation table.** Placement: concept
`store-typing`, R3; a step of the claim `recursive-types-inhabited`, and the shape the world order
needs when the table enters the world. Route: induct on the derivation. A step's questions read
the allocation table only at a leaf, through `Val.hasTy` (`hasTy_mono`), so `Val.obligations`
answers the same questions at the larger table. Consumer: `exists_memberIn_fresh`, to carry an
earlier part's member past a later part's allocation. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal memberIn_mono {decls : TyDecls} {a b : List String} (ext : Extends a b) {v : Val}
    {t : Ty} (h : MemberIn decls a v t) : MemberIn decls b v t

/-- The names of `known` whose declarations have a member at an extension of every allocation
table: the invariant of the iteration's rounds. -/
def TyDecls.Witnessed (decls : TyDecls) (known : List String) : Prop :=
  ∀ name ∈ known, ∀ body, decls.body? name = some body → ∀ allocated : List String,
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      MemberIn decls allocated' v body

/-- **A round's algebra is complete when its known names are witnessed**: a type that the round
calls inhabited has a member at an extension of any allocation table. Placement: concept
`store-typing`, R3, a step of the claim `recursive-types-inhabited`. Route: induct on `t`, as
`fits_of_inhabited_fresh` does. A union or an `except` takes a side that is inhabited; a product,
a tuple and a record's required fields build their parts in turn, each at the table the previous
part left, and carry the earlier parts forward (`memberIn_mono`). An external handle takes the
fresh index `allocated.length`. A declared name takes its witness from `hk`; an option, a list, a
map, an exit and a cause have a member with no question. Consumer: `witnessed_inhabitedFrom`. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal exists_memberIn_fresh {decls : TyDecls} {known : List String}
    (hk : decls.Witnessed known) (t : Ty) (h : cata_ty (decls.inhabitedWith known) t = true)
    (allocated : List String) :
    ∃ (v : Val) (allocated' : List String), Extends allocated allocated' ∧
      MemberIn decls allocated' v t

/-- **The iteration keeps its invariant**: every name it adds has a witnessed declaration. -/
theorem witnessed_inhabitedFrom (decls : TyDecls) :
    ∀ known, decls.Witnessed known → decls.Witnessed (decls.inhabitedFrom known) := by
  intro known
  induction known using TyDecls.inhabitedFrom.induct decls with
  | case1 known hstop =>
    intro hk
    rw [TyDecls.inhabitedFrom, dif_pos hstop]
    exact hk
  | case2 known hmore ih =>
    intro hk
    rw [TyDecls.inhabitedFrom, dif_neg hmore]
    refine ih fun name hname body hb => ?_
    rcases List.mem_append.mp hname with hold | hnew
    · exact hk name hold body hb
    · exact exists_memberIn_fresh hk body
        (TyDecls.inhabited_of_inhabitedRound (List.mem_filter.mp hnew).1 hb)

/-- **Inhabitance is complete against membership under the table**: an inhabited type has a
member at some allocation table. Placement: concept `store-typing`, R3, a step of the claim
`recursive-types-inhabited`. Proved modulo its parts `memberIn_mono` and
`exists_memberIn_fresh`. Consumer: `inhabited_iff_memberIn`. It establishes nothing of a world
(`Fits`). -/
@[semantics "store-typing" (requirement := R3)]
theorem exists_memberIn_of_inhabited {decls : TyDecls} {t : Ty}
    (h : decls.inhabited t = true) :
    ∃ (v : Val) (allocated : List String), MemberIn decls allocated v t :=
  have hw := witnessed_inhabitedFrom decls [] fun _ hn => absurd hn List.not_mem_nil
  have ⟨v, allocated, _, hv⟩ := exists_memberIn_fresh hw t h []
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

/-- **The fold under any oracle is invariant under normalization.** Placement: concept
`store-typing`, R3, the step of the claim `recursive-types-normalize`. Route: `hasTy_normalize`'s
induction, arm by arm, over the fold. `declAlg`'s arms are `Val.hasTy.alg`'s except at a
reference, which reads its name alone at both spellings (`Ty.normalize_app_nil`). A union's
normal form keeps a member above each one it drops (`declAlg_admitsSub`, `cata_admits_sub`), and
the congruence arms are `AdmitsNormalize`'s (`Val.hasTy_admitsNormalize`, which no theorem
consumes yet). At the empty table it is `hasTy_normalize` (`declAlg_nil`), which then becomes its
instance. Consumer: `memberIn_normalize`. -/
@[semantics "store-typing" (requirement := R3)]
proof_goal cata_declAlg_normalize (decls : TyDecls) (o : String → Adm) (t : Ty) (v : Val)
    (allocated : List String) :
    (cata_ty (declAlg decls o) t.normalize).2 v allocated = (cata_ty (declAlg decls o) t).2 v allocated

/-- **Membership under the table is invariant under normalization** (claim
`recursive-types-normalize`). It is what the checker's order needs: `Ty.subN` compares normal
forms, and `app n []` normalizes to `handle n`, which the table reads at the same declaration.
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

/-- **Two fixed points of a guarded table agree** at every declared name. Placement: concept
`store-typing`, R3, the step of the claim `guarded-fixed-point-unique`. Route: strong induction
on the value's size. At one value, induct along the table's head reach, which guardedness makes
well founded (`TyDecls.reaches`, `TyDecls.guarded`): a declared reference among a body's union
members reads the two oracles at the same value and a name nearer the value constructors, and
every other member asks its questions at smaller values (`cata_declAlg_step`,
`Val.sizeOf_obligation`). Consumer: `guarded_fixedPoint_unique`. On an unguarded table it fails:
at `A = A` every oracle is a fixed point, the constant `true` among them (the battery's control). -/
@[semantics "store-typing" (requirement := R3)]
proof_goal fixedPoint_agree {decls : TyDecls} (hg : decls.guarded = true) {o o' : String → Adm}
    (ho : FixedPoint decls o) (ho' : FixedPoint decls o') {name : String} {body : Ty}
    (hb : decls.body? name = some body) : o name = o' name

/-- **On a guarded table the fixed point is unique** (claim `guarded-fixed-point-unique`): every
fixed point admits exactly the members of each body. So the least fixed point is no choice
there: it is the greatest one too. Proved modulo its part `fixedPoint_agree`. Consumer: the
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
