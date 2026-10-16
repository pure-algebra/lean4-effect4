import Effect4.Program.TyHead
import Effect4.Laws.Program.TyDecls
import Effect4.Laws.Program.UnionRule

/-!
# Laws of the head members under a table, and of the checker's readers on them

The readers are `Program/TyHead.lean`'s; the plan is
`docs/research/2026-10-16-usability-scope/wiring-plan.md`.

- **Conservativity** (`wiring_readers_conservative`): at the empty table each reader is its
  table-free original, by definition.
- **The head members keep membership** (`memberIn_iff_membersIn`): a value is a member of a type
  under a table exactly when it is a member of one of the type's union members under the table.
  Each such member is a union member and no declared reference (`Ty.membersIn_head`).
- **A lifted rule under a table carries a property of its members** (`UnionRule.liftIn_transfer`):
  `lift_transfer`'s statement, with membership under the table for the relation.
- **The fold is sound** (`Record.fieldAdmitsIn_sound`): a field written at a declared name, given
  a member of the name's body, holds a member of the name.
- **The tag dispatch partitions** (`Record.tagArmsIn_partition`): a member of the target is a
  member of one of the two arms.

Placement of the claims (`AGENTS.md`, five points), shared by every theorem below:

1. Concepts `store-typing` (membership under a table) and `subtyping-algebra` (the union rule's
   laws), of `docs/core/semantics.md`. Property: membership under a table is read through the
   union rule as `Val.hasTy` is, and the empty table changes no reader.
2. Questions: the proposed registry claims `wiring-readers-conservative`
   (`wiring_readers_conservative`, compatibility), `wiring-head-members`
   (`memberIn_iff_membersIn`, inversion), `wiring-lift-transfer` (`UnionRule.liftIn_transfer`,
   preservation) and `wiring-fold-sound` (`Record.fieldAdmitsIn_sound`, preservation).
3. Reach: `MemberIn` at every table, guarded or not, at every allocation table; the readers'
   answers. Decisions rows 124, 158, 400 to 402 bound it.
4. Does not establish: anything of `Fits`, of the term typer, or of the machine. A reader under a
   table is used by no caller yet. The order `Ty.sub` is unchanged and nominal.
5. Unlocks: the checker under a table (the plan's W3), whose arms these readers become; R3's open
   part on recursive types.
-/

set_option autoImplicit false

namespace Effect4.Program
open Effect4 Effect4.Machine

/-! ## The head members -/

/-- **The head members, as a proposition**: a head member is a union member that is no declared
reference, or a head member of the body of a declared name not yet unfolded. -/
theorem Ty.mem_headMembers_iff {decls : TyDecls} {seen : List String} {t x : Ty} :
    x ∈ Ty.headMembers decls seen t ↔ ∃ m ∈ t.members,
      (decls.unfold? m = none ∧ x = m) ∨
      (∃ name body, decls.unfold? m = some (name, body) ∧ seen.contains name = false ∧
        x ∈ Ty.headMembers decls (name :: seen) body) := by
  rw [Ty.headMembers.eq_1, List.mem_flatMap]
  refine exists_congr fun m => and_congr_right fun _ => ?_
  split
  · rename_i name body hu
    constructor
    · intro h
      split at h
      · exact absurd h List.not_mem_nil
      · rename_i hs
        exact Or.inr ⟨name, body, hu, Bool.eq_false_iff.mpr hs, h⟩
    · rintro (⟨hn, _⟩ | ⟨name', body', hu', hs, h⟩)
      · rw [hu] at hn
        cases hn
      · rw [hu] at hu'
        cases hu'
        rw [dif_neg (by rw [hs]; exact Bool.false_ne_true)]
        exact h
  · rename_i hu
    constructor
    · intro h
      exact Or.inl ⟨hu, List.mem_singleton.mp h⟩
    · rintro (⟨_, rfl⟩ | ⟨name, body, hu', _, _⟩)
      · exact List.mem_singleton_self _
      · rw [hu] at hu'
        cases hu'

/-- **Every head member is a union member and no declared reference.** -/
theorem Ty.headMembers_head {decls : TyDecls} :
    ∀ (seen : List String) (t : Ty) {x : Ty}, x ∈ Ty.headMembers decls seen t →
      decls.unfold? x = none ∧ x.isMember = true := by
  intro seen t
  induction seen, t using Ty.headMembers.induct decls with
  | case1 seen t ih =>
    intro x hx
    obtain ⟨m, hm, ⟨hu, rfl⟩ | ⟨name, body, hu, hs, hb⟩⟩ := Ty.mem_headMembers_iff.mp hx
    · exact ⟨hu, Ty.members_isMember hm⟩
    · exact ih m name body hu (by rw [hs]; exact Bool.false_ne_true) hb

/-- **At the empty table the head members are the union members.** -/
theorem Ty.headMembers_nil (seen : List String) (t : Ty) : Ty.headMembers [] seen t = t.members := by
  rw [Ty.headMembers.eq_1]
  generalize t.members = ms
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [List.flatMap_cons, ih]
    split
    · rename_i name body hu
      rw [TyDecls.unfold?_nil] at hu
      cases hu
    · rfl

/-- The union members under a table are the head members of the normal form, at every table. -/
theorem Ty.membersIn_eq (decls : TyDecls) (t : Ty) :
    Ty.membersIn decls t = Ty.headMembers decls [] t.normalize := by
  cases decls with
  | nil => exact (Ty.headMembers_nil [] t.normalize).symm
  | cons _ _ => rfl

/-- **Every union member under a table is a union member and no declared reference.** A member
rule that refuses a reference therefore never refuses a member under a table for being one. -/
theorem Ty.membersIn_head {decls : TyDecls} {t x : Ty} (h : x ∈ Ty.membersIn decls t) :
    decls.unfold? x = none ∧ x.isMember = true := by
  rw [Ty.membersIn_eq] at h
  exact Ty.headMembers_head [] t.normalize h

/-! ## The head members keep membership -/

/-- At a union member that is no declared reference, the checker under a table reads the step,
from any set of unfolded names. -/
theorem hasTyIn_member_iff {decls : TyDecls} {seen : List String} {v : Val} {x : Ty}
    {allocated : List String} (hu : decls.unfold? x = none) (hx : x.isMember = true) :
    Val.hasTyIn decls seen v x allocated = true ↔ ∃ ps, Val.obligations v x allocated = some ps ∧
      ∀ p ∈ ps, Val.hasTyIn decls [] p.1 p.2 allocated = true := by
  rw [hasTyIn_eq_true_iff, Ty.members_atom hx]
  constructor
  · rintro ⟨m, hm, ⟨name, body, hu', _, _⟩ | ⟨_, ps, hps, hall⟩⟩
    · rw [List.mem_singleton.mp hm, hu] at hu'
      cases hu'
    · rw [List.mem_singleton.mp hm] at hps
      exact ⟨ps, hps, hall⟩
  · rintro ⟨ps, hps, hall⟩
    exact ⟨x, List.mem_singleton_self x, Or.inr ⟨hu, ps, hps, hall⟩⟩

/-- **The checker under a table reads the head members**: from any set of unfolded names, a value
fits a type exactly when it fits one of the type's head members. -/
theorem hasTyIn_iff_headMembers {decls : TyDecls} {v : Val} {allocated : List String} :
    ∀ (seen : List String) (t : Ty), Val.hasTyIn decls seen v t allocated = true ↔
      ∃ x ∈ Ty.headMembers decls seen t, Val.hasTyIn decls [] v x allocated = true := by
  intro seen t
  induction seen, t using Ty.headMembers.induct decls with
  | case1 seen t ih =>
    rw [hasTyIn_eq_true_iff]
    constructor
    · rintro ⟨m, hm, ⟨name, body, hu, hs, hb⟩ | ⟨hu, ps, hps, hall⟩⟩
      · obtain ⟨x, hx, hxv⟩ := (ih m name body hu (by rw [hs]; exact Bool.false_ne_true)).mp hb
        exact ⟨x, Ty.mem_headMembers_iff.mpr ⟨m, hm, Or.inr ⟨name, body, hu, hs, hx⟩⟩, hxv⟩
      · exact ⟨m, Ty.mem_headMembers_iff.mpr ⟨m, hm, Or.inl ⟨hu, rfl⟩⟩,
          (hasTyIn_member_iff hu (Ty.members_isMember hm)).mpr ⟨ps, hps, hall⟩⟩
    · rintro ⟨x, hx, hxv⟩
      obtain ⟨m, hm, ⟨hu, rfl⟩ | ⟨name, body, hu, hs, hb⟩⟩ := Ty.mem_headMembers_iff.mp hx
      · obtain ⟨ps, hps, hall⟩ := (hasTyIn_member_iff hu (Ty.members_isMember hm)).mp hxv
        exact ⟨_, hm, Or.inr ⟨hu, ps, hps, hall⟩⟩
      · exact ⟨m, hm, Or.inl ⟨name, body, hu, hs,
          (ih m name body hu (by rw [hs]; exact Bool.false_ne_true)).mpr ⟨x, hb, hxv⟩⟩⟩

/-- **Membership reads the head members**: a value is a member of a type under a table exactly
when it is a member of one of the type's head members. -/
theorem memberIn_iff_headMembers {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty} :
    MemberIn decls allocated v t ↔
      ∃ x ∈ Ty.headMembers decls [] t, MemberIn decls allocated v x := by
  rw [← hasTyIn_iff, hasTyIn_iff_headMembers]
  exact exists_congr fun _ => and_congr_right fun _ => hasTyIn_iff

/-- **Membership reads the union members under a table** (the claim `wiring-head-members`): a
value is a member of a type under a table exactly when it is a member of one of the type's union
members under the table. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_iff_membersIn {decls : TyDecls} {allocated : List String} {v : Val} {t : Ty} :
    MemberIn decls allocated v t ↔
      ∃ x ∈ Ty.membersIn decls t, MemberIn decls allocated v x := by
  rw [← memberIn_normalize, Ty.membersIn_eq, memberIn_iff_headMembers]

/-! ## The readers at the empty table -/

/-- **Conservativity** (the claim `wiring-readers-conservative`): at the empty table the union
members, the lifted rules, the field read, the update, the tag dispatch and the fold are their
table-free originals, by definition. -/
@[semantics "subtyping-algebra" (requirement := R3)]
theorem wiring_readers_conservative :
    (∀ t : Ty, Ty.membersIn [] t = t.normalize.members) ∧
    (∀ (rule : Ty → Option Ty) (t : Ty), UnionRule.liftIn [] rule t = UnionRule.lift rule t) ∧
    (∀ (rule : Ty → Option Ty) (t : Ty),
      UnionRule.extendAllIn [] rule t = UnionRule.extendAll rule t) ∧
    (∀ (o : Bool) (t : Ty) (n : String), Record.fieldTypeIn [] o t n = Record.fieldType o t n) ∧
    (∀ (t : Ty) (n : String) (u : Ty), Record.setTypeIn [] t n u = Record.setType t n u) ∧
    (∀ (tag : String) (t : Ty), Record.tagArmsIn [] tag t = Record.tagArms tag t) ∧
    (∀ (fields : Record.Fields) (args : List (String × Ty)),
      Record.argumentsFitIn [] fields args = Record.argumentsFit fields args) ∧
    (∀ (fields : Record.Fields) (names : List String) (tys : List Ty),
      Record.checkIn [] fields names tys = Record.check fields names tys) :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ => rfl⟩

/-! ## A lifted rule under a table -/

/-- The lifted rule under a table reads the union members under the table, at every table. -/
theorem UnionRule.liftIn_eq {α : Type} [UnionRule.Answer α] (decls : TyDecls)
    (rule : Ty → Option α) (t : Ty) :
    UnionRule.liftIn decls rule t =
      ((Ty.membersIn decls t).mapM rule).map UnionRule.joinAll := by
  cases decls <;> rfl

/-- **A lifted rule under a table carries a property of its members** (the claim
`wiring-lift-transfer`): `UnionRule.lift_transfer` with membership under the table for the
relation. A property that each member's answer gives every member of that member, and that each
join keeps, holds of the lifted answer at every member of the target. Its consumers are the
checker's arms under a table (the plan's W3). -/
@[semantics "subtyping-algebra" (requirement := R3)]
theorem UnionRule.liftIn_transfer {α : Type} [UnionRule.Answer α] {decls : TyDecls}
    {allocated : List String} {P : Val → α → Prop}
    (left : ∀ {v : Val} (a b : α), P v a → P v (UnionRule.Answer.join a b))
    (right : ∀ {v : Val} (a b : α), P v b → P v (UnionRule.Answer.join a b))
    {rule : Ty → Option α} {t : Ty}
    (member : ∀ {m : Ty} {a : α} {v : Val}, m ∈ Ty.membersIn decls t → rule m = some a →
      MemberIn decls allocated v m → P v a)
    {a : α} {v : Val} (typed : UnionRule.liftIn decls rule t = some a)
    (fit : MemberIn decls allocated v t) : P v a := by
  rw [UnionRule.liftIn_eq] at typed
  obtain ⟨answers, hanswers, rfl⟩ := Option.map_eq_some_iff.mp typed
  obtain ⟨m, hm, hfit⟩ := memberIn_iff_membersIn.mp fit
  obtain ⟨c, hc, hrule⟩ := UnionRule.mapM_answer hanswers m hm
  exact UnionRule.joinAll_keeps (fun a b => left a b) (fun a b => right a b) hc
    (member hm hrule hfit)

/-! ## The fold of a written field, and the tag dispatch -/

/-- **The fold is sound** (the claim `wiring-fold-sound`): a field written at `declared` that
admits `actual` holds every member of `actual` under the table. Below `declared` by the order,
`memberIn_sub` carries it. At a declared name, the member is a member of the body, and the body's
members are the name's (`MemberIn.unfold`). -/
@[semantics "store-typing" (requirement := R3)]
theorem Record.fieldAdmitsIn_sound {decls : TyDecls} {allocated : List String} {v : Val}
    {actual declared : Ty} (h : Record.fieldAdmitsIn decls actual declared = true)
    (fit : MemberIn decls allocated v actual) : MemberIn decls allocated v declared := by
  have hn : MemberIn decls allocated v actual.normalize :=
    (memberIn_normalize decls allocated v actual).mpr fit
  have byOrder : Ty.sub actual.normalize declared.normalize = true →
      MemberIn decls allocated v declared :=
    fun hs => (memberIn_normalize decls allocated v declared).mp (memberIn_sub hs hn)
  cases decls with
  | nil => exact byOrder h
  | cons d ds =>
    unfold Record.fieldAdmitsIn at h
    rcases Bool.or_eq_true_iff.mp h with hs | hf
    · exact byOrder hs
    · split at hf
      · rename_i name body hu
        have hb := (memberIn_normalize (d :: ds) allocated v body).mp (memberIn_sub hf hn)
        exact (memberIn_normalize (d :: ds) allocated v declared).mp (.unfold hu hb)
      · cases hf

/-- A member of one of a list's types is a member of the union the list spells. -/
theorem memberIn_ofMembers {decls : TyDecls} {allocated : List String} {v : Val} :
    ∀ {xs : List Ty} {x : Ty}, x ∈ xs → MemberIn decls allocated v x →
      MemberIn decls allocated v (Ty.ofMembers xs)
  | [_], _, hx, h => by
    rw [List.mem_singleton.mp hx] at h
    exact h
  | y :: z :: rest, x, hx, h => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .left h
    · exact .right (memberIn_ofMembers hx h)

/-- **The tag dispatch partitions**: a member of the target under the table is a member of the
arm that carries the tag or of the arm that does not. -/
@[semantics "store-typing" (requirement := R3)]
theorem Record.tagArmsIn_partition {decls : TyDecls} {allocated : List String} {v : Val}
    {tag : String} {t hit miss : Ty} (h : Record.tagArmsIn decls tag t = some (hit, miss))
    (fit : MemberIn decls allocated v t) :
    MemberIn decls allocated v hit ∨ MemberIn decls allocated v miss := by
  simp only [Record.tagArmsIn] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨x, hx, hxv⟩ := memberIn_iff_membersIn.mp fit
    cases ht : Record.isTag tag x
    · exact Or.inr (memberIn_ofMembers (List.mem_filter.mpr ⟨hx, by rw [ht]; rfl⟩) hxv)
    · exact Or.inl (memberIn_ofMembers (List.mem_filter.mpr ⟨hx, ht⟩) hxv)
  · cases h

end Effect4.Program
