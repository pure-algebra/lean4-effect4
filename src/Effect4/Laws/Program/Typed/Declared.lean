import Effect4.Laws.Program.Typed.Membership
import Effect4.Laws.Program.TyHead
import Effect4.Laws.Auto.Obligations

/-!
# Membership at a declared name: the head members, and term progress under the table

`Fits` reads the world's declaration table (the audit's D3, `Typed/Membership.lean`): a
reference to a declared name reads its body at the least fixed point (`fits_unfold`), and the
laws of `Fits` hold at every table (`fits_live`, `fits_sub`, `fits_normalize`, `fits_mono`,
`fits_memberIn`). This module holds what the term typer under a table reads.

Placement of the claims (`AGENTS.md`, five points):

1. Concept `store-typing` (concept 1 of `docs/core/semantics.md`), the property that membership
   in a world reads the application's declared names by their bodies and keeps the laws the term
   typer's readers need.
2. Questions: the claim `fits-declared`, its readers' step `fits_iff_membersIn` (R3); its term
   step is `evalTerm_progress` at a table within the world's (R9, `Typed/Denotation/Terms.lean`).
3. Reach: every table, world, value and type; native atoms for terms.
4. Does not establish: anything of a host row (F1, R6).
5. Unlocks: the term laws at the source's table, so the typed state at every table.
-/

set_option autoImplicit false

namespace Effect4.Program.Typed
open Effect4.Machine Effect4.Program.Sched

/-! ## A table within the world's

The term typer reads the program's table, and membership reads the world's. They agree when each
name the program's table declares, the world's declares at the same body (`TyDecls.Within`): the
empty table is within every table (a native signature at every world), and a table is within
itself (a source at a world tied to it). -/

/-- **A table within another**: each name it declares, the other declares at the same body. -/
def _root_.Effect4.Program.TyDecls.Within (decls outer : TyDecls) : Prop :=
  ∀ name body, decls.body? name = some body → outer.body? name = some body

/-- The empty table is within every table. -/
theorem _root_.Effect4.Program.TyDecls.within_nil (outer : TyDecls) :
    TyDecls.Within [] outer :=
  fun _ _ h => by cases h

/-- A table is within itself. -/
theorem _root_.Effect4.Program.TyDecls.within_refl (decls : TyDecls) : decls.Within decls :=
  fun _ _ h => h

/-- An empty table is within every table. -/
theorem _root_.Effect4.Program.TyDecls.within_of_nil {decls outer : TyDecls} (h : decls = []) :
    decls.Within outer :=
  h ▸ TyDecls.within_nil outer

/-- A table equal to the world's is within it. -/
theorem _root_.Effect4.Program.TyDecls.within_of_eq {decls outer : TyDecls} (h : decls = outer) :
    decls.Within outer :=
  h ▸ TyDecls.within_refl decls

/-- An unfolding under a table is an unfolding under every table it is within. -/
theorem _root_.Effect4.Program.TyDecls.Within.unfold? {decls outer : TyDecls}
    (hw : decls.Within outer) {t : Ty} {name : String} {body : Ty} (hu : decls.unfold? t = some (name, body)) :
    outer.unfold? t = some (name, body) := by
  obtain ⟨n, args, rfl⟩ := TyDecls.ref_of_unfold? hu
  have hb := TyDecls.body?_of_unfold? hu
  have hn : n = name := by
    simp only [TyDecls.unfold?, Ty.refName?, Option.bind_some, Option.map_eq_some_iff] at hu
    obtain ⟨_, _, he⟩ := hu
    exact (Prod.mk.inj he).1
  subst hn
  simp only [TyDecls.unfold?, Ty.refName?, Option.bind_some, hw _ _ hb, Option.map_some]

/-! ## Chains through members and unfoldings

A chain runs from a type through a union member, and from a reference to a declared name through
its body, to a member that is no reference. Membership at a type is membership at the end of one
of its chains (`fits_iff_reaches`), and the head members are the chains' ends (`reaches_iff`).
The second fact is combinatorial: a chain that meets a name twice shortens to one that does not
(`ReachesAvoid.shorten`), which is the head members' cut. -/

/-- **A chain avoiding `seen`**: from a type, through union members and declared names not in
`seen`, to a member that is no reference. -/
inductive ReachesAvoid (decls : TyDecls) (seen : List String) : Ty → Ty → Prop
  /-- A union member that is no reference ends a chain. -/
  | here {t m : Ty} : m ∈ t.members → decls.unfold? m = none → ReachesAvoid decls seen t m
  /-- A union member that references a declared name not in `seen` continues into its body. -/
  | step {t m b x : Ty} {n : String} : m ∈ t.members → decls.unfold? m = some (n, b) →
      seen.contains n = false → ReachesAvoid decls seen b x → ReachesAvoid decls seen t x

/-- **A chain shortens past a name**: a chain from `u` that avoids `seen` avoids `n` too, or a
chain from `n`'s body does. Its later visits to `n` are cut at the last one. -/
theorem ReachesAvoid.shorten {decls : TyDecls} {seen : List String} {n : String} {b : Ty}
    (hb : decls.body? n = some b) (hn : seen.contains n = false) {u x : Ty}
    (h : ReachesAvoid decls seen u x) :
    ReachesAvoid decls (n :: seen) u x ∨ ReachesAvoid decls (n :: seen) b x := by
  induction h with
  | here hm hu => exact Or.inl (.here hm hu)
  | @step t m b' x n' hm hu hs _ ih =>
    by_cases he : n' = n
    · subst he
      have hb' := TyDecls.body?_of_unfold? hu
      rw [hb] at hb'
      cases hb'
      exact Or.inr (ih.elim id id)
    · rcases ih with ih | ih
      · refine Or.inl (.step hm hu ?_ ih)
        rw [List.contains_cons, hs, Bool.or_false]
        exact beq_false_of_ne he
      · exact Or.inr ih

/-- **A chain's end is a head member**: the head members from `seen` hold the end of every chain
that avoids `seen`. By recursion on the declared names not yet seen, as `Ty.headMembers`
recurses. -/
theorem ReachesAvoid.mem_headMembers {decls : TyDecls} :
    ∀ (k : Nat) (seen : List String), decls.unseen seen = k → ∀ {t x : Ty},
      ReachesAvoid decls seen t x → x ∈ Ty.headMembers decls seen t := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro seen hk t x h
    cases h with
    | here hm hu => exact Ty.mem_headMembers_iff.mpr ⟨_, hm, Or.inl ⟨hu, rfl⟩⟩
    | step hm hu hs rest =>
      have hb := TyDecls.body?_of_unfold? hu
      have hshort := (rest.shorten hb hs).elim id id
      have hlt := TyDecls.unseen_cons_lt hb hs
      exact Ty.mem_headMembers_iff.mpr ⟨_, hm, Or.inr ⟨_, _, hu, hs,
        ih _ (hk ▸ hlt) _ rfl hshort⟩⟩

/-- A chain that avoids more names avoids fewer. -/
theorem ReachesAvoid.weaken {decls : TyDecls} {seen seen' : List String} {t x : Ty}
    (h : ReachesAvoid decls seen' t x)
    (hsub : ∀ n, seen.contains n = true → seen'.contains n = true) :
    ReachesAvoid decls seen t x := by
  induction h with
  | here hm hu => exact .here hm hu
  | @step t m b x n hm hu hs _ ih =>
    refine .step hm hu ?_ ih
    cases hc : seen.contains n with
    | false => rfl
    | true =>
      rw [hsub n hc] at hs
      cases hs

/-- A head member from `seen` ends a chain that avoids `seen`. -/
theorem ReachesAvoid.of_mem_headMembers {decls : TyDecls} :
    ∀ (k : Nat) (seen : List String), decls.unseen seen = k → ∀ {t x : Ty},
      x ∈ Ty.headMembers decls seen t → ReachesAvoid decls seen t x := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro seen hk t x h
    obtain ⟨m, hm, ⟨hu, rfl⟩ | ⟨n, b, hu, hs, hx⟩⟩ := Ty.mem_headMembers_iff.mp h
    · exact .here hm hu
    · have hlt := TyDecls.unseen_cons_lt (TyDecls.body?_of_unfold? hu) hs
      have hr : ReachesAvoid decls (n :: seen) b x := ih _ (hk ▸ hlt) (n :: seen) rfl hx
      exact .step hm hu hs (hr.weaken fun n' hc => by rw [List.contains_cons, hc, Bool.or_true])

/-- **The head members are the chains' ends.** -/
theorem reaches_iff {decls : TyDecls} {t x : Ty} :
    x ∈ Ty.headMembers decls [] t ↔ ReachesAvoid decls [] t x :=
  ⟨ReachesAvoid.of_mem_headMembers _ [] rfl, ReachesAvoid.mem_headMembers _ [] rfl⟩

/-- A chain's end membership is membership at its start, under a table within the world's. -/
theorem fits_of_reaches {w : World} {decls : TyDecls} (hw : decls.Within w.types)
    {seen : List String} {t x : Ty} {v : Val}
    (h : ReachesAvoid decls seen t x) (hv : Fits w v x) : Fits w v t := by
  induction h with
  | here hm _ => exact (fits_members w v _).mp ⟨_, hm, hv⟩
  | step hm hu _ _ ih =>
    exact (fits_members w v _).mp ⟨_, hm, (fits_unfold (hw.unfold? hu)).mpr (ih hv)⟩

/-- One level of membership at a type is at one of its union members. -/
theorem fitsAt_members {decls : TyDecls} {w : World} {o : String → Val → Prop} {v : Val} :
    ∀ (t : Ty), FitsAt decls w o v t → ∃ m ∈ t.members, FitsAt decls w o v m
  | .union l r, h => by
    rcases h with h | h
    · obtain ⟨m, hm, hv⟩ := fitsAt_members l h
      exact ⟨m, List.mem_append_left _ hm, hv⟩
    · obtain ⟨m, hm, hv⟩ := fitsAt_members r h
      exact ⟨m, List.mem_append_right _ hm, hv⟩
  | .never, h => h.elim
  | .unit, h | .nat, h | .int, h | .string, h | .bool, h | .handle _, h | .option _, h
  | .list _, h | .prod _ _, h | .except _ _, h | .exitOf _ _, h | .causeOf _, h
  | .fiberOf _ _, h | .lit _, h | .refOf _, h | .deferredOf _ _, h | .var _, h | .unknown, h
  | .record _, h | .map _ _, h | .tuple _, h | .app _ _, h | .null, h | .undefined, h
  | .number, h | .bytes, h | .contextOf _, h => ⟨_, List.mem_singleton_self _, h⟩

/-- **Membership at a type is membership at the end of one of its chains**, under a table within
the world's. The least fixed point lies below the reading "a member of the name, and of the end of
a chain from its body under the table", which one level of membership closes: a union member that
is no reference under the table ends a chain, and a declared one continues it. -/
theorem fits_reaches {w : World} {decls : TyDecls} (hw : decls.Within w.types) {t : Ty} {v : Val}
    (h : Fits w v t) : ∃ x, ReachesAvoid decls [] t x ∧ Fits w v x := by
  let P : String → Val → Prop := fun n u => NameFits w.types w n u ∧
    ∀ b, decls.body? n = some b → ∃ x, ReachesAvoid decls [] b x ∧ Fits w u x
  have hle : ∀ n u, P n u → NameFits w.types w n u := fun _ _ hp => hp.1
  have hc : NamesClosed w.types w P := by
    intro n b u hb hu
    refine ⟨(nameFits_iff hb).mpr (fitsAt_oracle_mono hle hu), fun b' hb' => ?_⟩
    rw [hw _ _ hb'] at hb
    cases hb
    obtain ⟨m, hm, hmv⟩ := fitsAt_members b hu
    cases hum : decls.unfold? m with
    | none => exact ⟨m, .here hm hum, fitsAt_oracle_mono hle hmv⟩
    | some nb =>
      obtain ⟨n', b''⟩ := nb
      obtain ⟨n'', args, rfl⟩ := TyDecls.ref_of_unfold? hum
      have hwu := hw.unfold? hum
      have hb'' := TyDecls.body?_of_unfold? hum
      have hn : n'' = n' := by
        simp only [TyDecls.unfold?, Ty.refName?, Option.bind_some, Option.map_eq_some_iff] at hum
        obtain ⟨_, _, he⟩ := hum
        exact (Prod.mk.inj he).1
      subst hn
      have hm' : FitsAt w.types w P u (.app n'' args) := hmv
      simp only [FitsAt, hw _ _ hb''] at hm'
      obtain ⟨x, hr, hx⟩ := hm'.2 b'' hb''
      exact ⟨x, .step hm hum rfl hr, hx⟩
  obtain ⟨m, hm, hmv⟩ := (fits_members w v t).mpr h
  cases hum : decls.unfold? m with
  | none => exact ⟨m, .here hm hum, hmv⟩
  | some nb =>
    obtain ⟨n, b⟩ := nb
    have hwu := hw.unfold? hum
    have hnf : NameFits w.types w n v :=
      (nameFits_iff (TyDecls.body?_of_unfold? hwu)).mpr ((fits_unfold hwu).mp hmv)
    obtain ⟨x, hr, hx⟩ := (hnf P hc).2 b (TyDecls.body?_of_unfold? hum)
    exact ⟨x, .step hm hum rfl hr, hx⟩

/-- **Membership reads the union members under a table within the world's**: the `Fits` form of
`memberIn_iff_membersIn`, at every such table, guarded or not; at the world's own table
(`TyDecls.within_refl`) and at the empty one (`TyDecls.within_nil`). Placement: concept
`store-typing`, R3, the readers' step of the claim `fits-declared`. Route: `fits_normalize`; a
member's membership is at the end of one of its chains (`fits_reaches`, by the least fixed point's
induction principle), and the head members are the chains' ends (`reaches_iff`, by shortening a
chain past a repeated name). Consumer: the readers of the term typer under the table (a field
read, an update, a construction, a fold and a decision). -/
@[semantics "store-typing" (requirement := R3)]
theorem fits_iff_membersIn {w : World} {decls : TyDecls} (hw : decls.Within w.types) (t : Ty)
    (v : Val) : Fits w v t ↔ ∃ x ∈ Ty.membersIn decls t, Fits w v x := by
  rw [Ty.membersIn_eq, ← fits_normalize w t v]
  constructor
  · intro h
    obtain ⟨x, hr, hx⟩ := fits_reaches hw h
    exact ⟨x, reaches_iff.mpr hr, hx⟩
  · rintro ⟨x, hx, hv⟩
    exact fits_of_reaches hw (reaches_iff.mp hx) hv

/-! ## The readers under the table

Each reader of the term typer under a table (`Program/TyHead.lean`) is sound for membership at a
world whose table holds it (`TyDecls.Within`). A lifted rule reads the head members
(`fits_liftIn_transfer`), and the fold of a written field reads the unfolding
(`fits_fieldAdmitsIn`). The `MemberIn` forms are `Laws/Program/TyHead.lean`'s; these are their
`Fits` forms, through `fits_iff_membersIn` and `fits_unfold`. -/

/-- **A lifted rule under a table within the world's carries a property of its members**: the
membership form of `UnionRule.liftIn_transfer`. A property that each member's answer gives every
member of that member, and that each join keeps, holds of the lifted answer at every member of
the target. -/
theorem fits_liftIn_transfer {α : Type} [UnionRule.Answer α] {w : World} {decls : TyDecls}
    (hw : decls.Within w.types) {P : Val → α → Prop}
    (left : ∀ {v : Val} (a b : α), P v a → P v (UnionRule.Answer.join a b))
    (right : ∀ {v : Val} (a b : α), P v b → P v (UnionRule.Answer.join a b))
    {rule : Ty → Option α} {t : Ty}
    (member : ∀ {m : Ty} {a : α} {v : Val}, m ∈ Ty.membersIn decls t → rule m = some a →
      Fits w v m → P v a)
    {a : α} {v : Val} (typed : UnionRule.liftIn decls rule t = some a) (fit : Fits w v t) :
    P v a := by
  rw [UnionRule.liftIn_eq] at typed
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  obtain ⟨m, hm, hfit⟩ := (fits_iff_membersIn hw t v).mp fit
  obtain ⟨c, hc, hrule⟩ := UnionRule.mapM_answer hanswers m hm
  exact UnionRule.joinAll_keeps (fun a b => left a b) (fun a b => right a b) hc
    (member hm hrule hfit)

/-- **The fold of a written field is sound for membership**: the membership form of
`Record.fieldAdmitsIn_sound`. Below the declared type in the order, `fits_subN` carries a member;
at a declared name, a member of the body is a member of the name (`fits_unfold`). -/
theorem fits_fieldAdmitsIn {w : World} {decls : TyDecls} (hw : decls.Within w.types) {v : Val}
    {actual declared : Ty} (h : Program.Record.fieldAdmitsIn decls actual declared = true)
    (fit : Fits w v actual) : Fits w v declared := by
  have byOrder : Ty.sub actual.normalize declared.normalize = true → Fits w v declared :=
    fun hs => fits_subN w hs v fit
  cases decls with
  | nil => exact byOrder h
  | cons d ds =>
    unfold Program.Record.fieldAdmitsIn at h
    rcases Bool.or_eq_true_iff.mp h with hs | hf
    · exact byOrder hs
    · split at hf
      · rename_i name body hu
        have hb : Fits w v body := fits_subN w hf v fit
        exact (fits_normalize w declared v).mp ((fits_unfold (hw.unfold? hu)).mpr hb)
      · cases hf

/-- **The list rule under a table within the world's bounds a member**: a member of a type the
rule reads is a member of the list of its answer. At the empty table it is `listOf_upper`. -/
theorem fits_listOfIn {w : World} {decls : TyDecls} (hw : decls.Within w.types) {t item : Ty}
    {v : Val} (typed : Checker.listOfIn decls t = some item) (fit : Fits w v t) :
    Fits w v (.list item) := by
  cases decls with
  | nil => exact fits_subN w (listOf_upper typed) v fit
  | cons d ds =>
    simp only [Checker.listOfIn, UnionRule.extendAllIn] at typed
    cases hl : Member.list t with
    | some a =>
      rw [hl] at typed
      cases typed
      obtain rfl := Member.list_eliminator.shape hl
      exact fit
    | none =>
      rw [hl] at typed
      exact fits_liftIn_transfer hw (P := fun v a => Fits w v (.list a))
        (fun a b h => fits_subN w ((Ty.subN_list_iff a _).mpr (Ty.subN_join_left a b)) _ h)
        (fun a b h => fits_subN w ((Ty.subN_list_iff b _).mpr (Ty.subN_join_right a b)) _ h)
        (fun _ hrule hfit => by
          obtain rfl := Member.list_eliminator.shape hrule
          exact hfit) typed fit

/-- **The option rule under a table within the world's bounds a member**: a member of a type the
rule reads is a member of the option of its answer. At the empty table it is `optionTy_upper`. -/
theorem fits_optionTyIn {w : World} {decls : TyDecls} (hw : decls.Within w.types) {t a : Ty}
    {v : Val} (typed : optionTyIn decls t = some a) (fit : Fits w v t) : Fits w v (.option a) :=
  fits_liftIn_transfer hw (P := fun v a => Fits w v (.option a))
    (fun a b h => fits_subN w ((Ty.subN_option_iff a _).mpr (Ty.subN_join_left a b)) _ h)
    (fun a b h => fits_subN w ((Ty.subN_option_iff b _).mpr (Ty.subN_join_right a b)) _ h)
    (fun _ hrule hfit => by
      obtain rfl := Member.option_eliminator.shape hrule
      exact hfit) typed fit

/-! ## A declared name adds members

The shape check reads no table, and a table's only arm reads a reference, which the shape check
refuses. So a member at the empty table is a member at every table (`MemberIn.of_nil`), and
`never` has a member at no table (`not_memberIn_never`). -/

/-- **A member at the empty table is a member at every table.** A step at the empty table is at
no reference: the shape check refuses a reference, so a reference's questions are refused. -/
theorem _root_.Effect4.Program.MemberIn.of_nil
    {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (h : MemberIn [] allocated v t) : MemberIn decls allocated v t := by
  induction h with
  | left _ ih => exact .left ih
  | right _ ih => exact .right ih
  | unfold hu _ _ =>
    rw [TyDecls.unfold?_nil] at hu
    cases hu
  | @step v t ps _ hobl _ ih =>
    refine .step ?_ hobl ih
    cases hd : decls.unfold? t with
    | none => rfl
    | some x =>
      obtain ⟨n, args, rfl⟩ := TyDecls.ref_of_unfold? hd
      cases hobl

/-- The shape check implies membership under every table (`MemberIn.of_nil`). -/
theorem _root_.Effect4.Program.Val.memberIn_of_hasTy
    {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty}
    (h : Val.hasTy v t allocated = true) : Val.memberIn decls v t allocated = true :=
  Val.memberIn_iff.mpr (MemberIn.of_nil (memberIn_nil.mpr h))

/-- **`never` has a member at no table.** -/
theorem _root_.Effect4.Program.not_memberIn_never
    {decls : TyDecls} {allocated : List String} {v : Val} :
    ¬ MemberIn decls allocated v .never := by
  intro h
  cases h with
  | unfold hu _ => cases hu
  | step _ hobl _ => cases hobl

/-- The decider refuses every value at `never`, at every table. -/
theorem _root_.Effect4.Program.Val.memberIn_never
    {decls : TyDecls} {allocated : List String} {v : Val} :
    Val.memberIn decls v .never allocated = false := by
  cases h : Val.memberIn decls v .never allocated
  · rfl
  · exact absurd (Val.memberIn_iff.mp h) not_memberIn_never

end Effect4.Program.Typed
