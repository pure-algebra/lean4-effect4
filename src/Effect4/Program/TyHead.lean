module

public import Effect4.Program.TyExpand
public import Effect4.Program.Record

/-!
# Program.TyHead — a type's head members under a declaration table, and the readers on them

A declared name is nominal (decisions rows 124, 158 and 401 (1)), read iso-recursively. The
checker reads a declared name by its body where it reads a type by shape. A record field written
at a declared name folds a member of the name's body into it. The order `Ty.sub` does not change.
The plan is `docs/research/2026-10-16-usability-scope/wiring-plan.md`.

* **The head members** (`Ty.headMembers`): a type's union members, with each declared reference
  replaced by its body's head members. It recurses as the checker under a table does
  (`Val.hasTyIn`, `Program/TyDecls.lean`): on the declared names not yet unfolded since the last
  value constructor. So it needs no fuel, and a name met again in one head adds no member.
* **The readers under a table**: the union members `Ty.membersIn`, the lifted rules
  `UnionRule.liftIn` and `UnionRule.extendAllIn`, the field read `Record.fieldTypeIn`, the
  update `Record.setTypeIn` and the tag dispatch `Record.tagArmsIn`.
* **The fold of a written field** (`Record.fieldAdmitsIn`, `Record.argumentsFitIn`,
  `Record.checkIn`): a field written at a declared name takes an argument below the name's
  body. One level: the fold reads the field's own head, and a nested position folds where it is
  written.

Each reader is its table-free original at the empty table by definition: it matches on the table
first, or it is the original's combinator at the table's reader. So a law of the original holds
unchanged wherever the table is empty. The laws are `Laws/Program/TyHead.lean`.
-/

@[expose] public section

namespace Effect4.Program

/-- **The head members** of a type under a table, from the names unfolded so far: each union
member of `t`, with a declared reference that `seen` does not hold replaced by its body's head
members. A reference that `seen` holds adds none: its unfolding returned to it before a value
constructor, as an unguarded table's does. Each member answered is no declared reference. -/
def Ty.headMembers (decls : TyDecls) (seen : List String) (t : Ty) : List Ty :=
  t.members.flatMap fun m =>
    match _h : decls.unfold? m with
    | some (name, body) =>
      if _hs : seen.contains name then [] else Ty.headMembers decls (name :: seen) body
    | none => [m]
termination_by decls.unseen seen
decreasing_by
  exact TyDecls.unseen_cons_lt (TyDecls.body?_of_unfold? _h) (Bool.eq_false_iff.mpr _hs)

/-- **The union members under a table**: the head members of the normal form. At the empty table
they are the normal form's union members, by definition. -/
def Ty.membersIn (decls : TyDecls) (t : Ty) : List Ty :=
  match decls with
  | [] => t.normalize.members
  | _ => Ty.headMembers decls [] t.normalize

namespace UnionRule

variable {α : Type} [Answer α]

/-- **The lifted rule under a table**: the member rule at every union member under the table,
and the join of the answers. At the empty table it is `lift`, by definition. -/
def liftIn (decls : TyDecls) (rule : Ty → Option α) (target : Ty) : Option α :=
  match decls with
  | [] => lift rule target
  | _ => ((Ty.membersIn decls target).mapM rule).map joinAll

/-- The member rule's raw answer first, and the lifted rule under the table elsewhere. At the
empty table it is `extendAll`, by definition. -/
def extendAllIn (decls : TyDecls) (rule : Ty → Option α) (target : Ty) : Option α :=
  match decls with
  | [] => extendAll rule target
  | _ => (rule target).orElse fun _ => liftIn decls rule target

end UnionRule

namespace Record

/-- Read a declared field from every record member under the table. At the empty table it is
`fieldType`. -/
def fieldTypeIn (decls : TyDecls) (optional : Bool) (target : Ty) (name : String) : Option Ty :=
  UnionRule.liftIn decls (fieldOf optional name) target

/-- Overwrite every record member under the table. At the empty table it is `setType`. -/
def setTypeIn (decls : TyDecls) (target : Ty) (name : String) (valueType : Ty) : Option Ty :=
  UnionRule.liftIn decls (setOf name valueType) target

/-- Partition a literal-tagged record column under the table. At the empty table it is
`tagArms`. -/
def tagArmsIn (decls : TyDecls) (tag : String) (target : Ty) : Option (Ty × Ty) :=
  let members := Ty.membersIn decls target
  if members.all (fun type => (tagOf type).isSome) then
    some (Ty.ofMembers (members.filter (isTag tag)),
      Ty.ofMembers (members.filter (fun type => !(isTag tag type))))
  else none

/-- **The fold of a written field**: a field written at `declared` takes an argument of type
`actual` below it in the order, or, where `declared` is a declared name, below the name's body.
At the empty table it is the order alone. -/
def fieldAdmitsIn (decls : TyDecls) (actual declared : Ty) : Bool :=
  match decls with
  | [] => Ty.sub actual.normalize declared.normalize
  | _ => Ty.sub actual.normalize declared.normalize ||
      match decls.unfold? declared.normalize with
      | some (_, body) => Ty.sub actual.normalize body.normalize
      | none => false

/-- Check supplied argument types against every declared field, each by the fold. At the empty
table it is `argumentsFit`. -/
def argumentsFitIn (decls : TyDecls) (fields : Fields) (arguments : List (String × Ty)) : Bool :=
  arguments.all (fun argument => (Field.firstOf argument.1 fields).isSome) &&
  fields.all (fun field => match Field.firstOf field.1 arguments with
    | none => field.2.1
    | some actual => fieldAdmitsIn decls actual field.2.2)

/-- Check a record's columns by the fold before returning its normalized declared type. At the
empty table it is `check`. -/
def checkIn (decls : TyDecls) (fields : Fields) (presentNames : List String)
    (argumentTypes : List Ty) : Option Ty := do
  let arguments ← Machine.Record.zipNames presentNames argumentTypes
  if (fields.map Prod.fst).Nodup ∧ presentNames.Nodup ∧
      argumentsFitIn decls fields arguments = true then
    some (Ty.normalize (.record fields))
  else none

end Record

/-! ## Where the original answers, the reader under a table answers the same

A member rule of the checker refuses a declared reference `app n args`. So where the
table-free reader answers, no union member of its target is a declared reference, the table
unfolds nothing, and the reader under any table answers the same. The checker's introduction
lemmas, stated at the originals, then hold at every table. -/

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

/-- **A property of the bodies and of a type's union members holds at its head members**: each
head member is a union member of the type or a head member of a declared body. -/
theorem Ty.headMembers_all {decls : TyDecls} {P : Ty → Prop}
    (members : ∀ t, P t → ∀ x ∈ t.members, P x)
    (bodies : ∀ d ∈ decls, P d.2) :
    ∀ (seen : List String) (t : Ty), P t → ∀ x ∈ Ty.headMembers decls seen t, P x := by
  intro seen t
  induction seen, t using Ty.headMembers.induct decls with
  | case1 seen t ih =>
    intro ht x hx
    obtain ⟨m, hm, ⟨_, rfl⟩ | ⟨name, body, hu, hs, hb⟩⟩ := Ty.mem_headMembers_iff.mp hx
    · exact members t ht _ hm
    · exact ih m name body hu (by rw [hs]; exact Bool.false_ne_true)
        (bodies _ (TyDecls.mem_of_body? (TyDecls.body?_of_unfold? hu))) x hb

/-- The lifted rule under a table reads the union members under the table, at every table. -/
theorem UnionRule.liftIn_eq {α : Type} [UnionRule.Answer α] (decls : TyDecls)
    (rule : Ty → Option α) (t : Ty) :
    UnionRule.liftIn decls rule t =
      ((Ty.membersIn decls t).mapM rule).map UnionRule.joinAll := by
  cases decls <;> rfl

/-- A type that unfolds under a table is a reference `app n args`. -/
theorem TyDecls.ref_of_unfold? {decls : TyDecls} {m : Ty} {x : String × Ty}
    (h : decls.unfold? m = some x) : ∃ n args, m = .app n args := by
  cases m
  case app n args => exact ⟨n, args, rfl⟩
  all_goals cases h

/-- With no declared reference among a type's union members, the head members are the union
members. -/
theorem Ty.headMembers_of_noRefs {decls : TyDecls} {seen : List String} {t : Ty}
    (h : ∀ m ∈ t.members, decls.unfold? m = none) : Ty.headMembers decls seen t = t.members := by
  rw [Ty.headMembers.eq_1]
  generalize t.members = ms at h ⊢
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    rw [List.flatMap_cons, ih fun x hx => h x (List.mem_cons_of_mem _ hx)]
    split
    · rename_i name body hu
      rw [h m List.mem_cons_self] at hu
      cases hu
    · rfl

/-- With no declared reference among the normal form's union members, the union members under a
table are the normal form's. -/
theorem Ty.membersIn_of_noRefs {decls : TyDecls} {t : Ty}
    (h : ∀ m ∈ t.normalize.members, decls.unfold? m = none) :
    Ty.membersIn decls t = t.normalize.members := by
  cases decls with
  | nil => rfl
  | cons _ _ => exact Ty.headMembers_of_noRefs h

/-- An answered read of a list answers at each element. -/
theorem UnionRule.mapM_isSome {β γ : Type} {f : β → Option γ} :
    ∀ {xs : List β} {ys : List γ}, xs.mapM f = some ys → ∀ x ∈ xs, (f x).isSome = true
  | [], _, _, _, hx => absurd hx List.not_mem_nil
  | x :: xs, ys, h, y, hy => by
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨a, ha, rest, hrest, _⟩ := h
    rcases List.mem_cons.mp hy with rfl | hy
    · rw [ha]
      rfl
    · exact UnionRule.mapM_isSome hrest y hy

/-- No union member that a rule answers at is a declared reference, where the rule refuses every
reference. -/
theorem UnionRule.noRefs_of_mapM {α : Type} {decls : TyDecls} {rule : Ty → Option α}
    (refuses : ∀ m x, decls.unfold? m = some x → rule m = none) {ms : List Ty} {ys : List α}
    (h : ms.mapM rule = some ys) : ∀ m ∈ ms, decls.unfold? m = none := by
  intro m hm
  cases hu : decls.unfold? m with
  | none => rfl
  | some x =>
    have hs := UnionRule.mapM_isSome h m hm
    rw [refuses m x hu] at hs
    cases hs

/-- **Where `lift` answers, `liftIn` answers the same**, for a rule that refuses every declared
reference. -/
theorem UnionRule.liftIn_of_lift {α : Type} [UnionRule.Answer α] {decls : TyDecls}
    {rule : Ty → Option α} (refuses : ∀ m x, decls.unfold? m = some x → rule m = none)
    {t : Ty} {a : α} (h : UnionRule.lift rule t = some a) : UnionRule.liftIn decls rule t = some a := by
  cases decls with
  | nil => exact h
  | cons d ds =>
    obtain ⟨ys, hys, _⟩ := Option.map_eq_some_iff.mp h
    show ((Ty.membersIn (d :: ds) t).mapM rule).map UnionRule.joinAll = some a
    rw [Ty.membersIn_of_noRefs (UnionRule.noRefs_of_mapM refuses hys)]
    exact h

/-- **Where `extendAll` answers, `extendAllIn` answers the same**, for a rule that refuses every
declared reference. -/
theorem UnionRule.extendAllIn_of_extendAll {α : Type} [UnionRule.Answer α] {decls : TyDecls}
    {rule : Ty → Option α} (refuses : ∀ m x, decls.unfold? m = some x → rule m = none)
    {t : Ty} {a : α} (h : UnionRule.extendAll rule t = some a) :
    UnionRule.extendAllIn decls rule t = some a := by
  cases decls with
  | nil => exact h
  | cons d ds =>
    show (rule t).orElse (fun _ => UnionRule.liftIn (d :: ds) rule t) = some a
    cases hr : rule t with
    | some b =>
      have hb : (rule t).orElse (fun _ => UnionRule.lift rule t) = some a := h
      rw [hr] at hb
      exact hb
    | none =>
      have hl : (rule t).orElse (fun _ => UnionRule.lift rule t) = some a := h
      rw [hr] at hl
      exact UnionRule.liftIn_of_lift refuses hl

/-- The field rule refuses a declared reference. -/
theorem Record.fieldOf_ref {decls : TyDecls} {o : Bool} {name : String} :
    ∀ m x, decls.unfold? m = some x → Record.fieldOf o name m = none := by
  intro m x h
  obtain ⟨n, args, rfl⟩ := TyDecls.ref_of_unfold? h; rfl

/-- The update rule refuses a declared reference. -/
theorem Record.setOf_ref {decls : TyDecls} {name : String} {value : Ty} :
    ∀ m x, decls.unfold? m = some x → Record.setOf name value m = none := by
  intro m x h
  obtain ⟨n, args, rfl⟩ := TyDecls.ref_of_unfold? h; rfl

/-- **Where the field read answers, the field read under a table answers the same.** -/
theorem Record.fieldTypeIn_of_fieldType {decls : TyDecls} {o : Bool} {t : Ty} {name : String}
    {a : Ty} (h : Record.fieldType o t name = some a) : Record.fieldTypeIn decls o t name = some a :=
  UnionRule.liftIn_of_lift Record.fieldOf_ref h

/-- **Where the update answers, the update under a table answers the same.** -/
theorem Record.setTypeIn_of_setType {decls : TyDecls} {t : Ty} {name : String} {value a : Ty}
    (h : Record.setType t name value = some a) : Record.setTypeIn decls t name value = some a :=
  UnionRule.liftIn_of_lift Record.setOf_ref h

/-- The order admits a field's argument at every table. -/
theorem Record.fieldAdmitsIn_of_sub {decls : TyDecls} {actual declared : Ty}
    (h : Ty.sub actual.normalize declared.normalize = true) :
    Record.fieldAdmitsIn decls actual declared = true := by
  cases decls with
  | nil => exact h
  | cons _ _ =>
    show (Ty.sub actual.normalize declared.normalize || _) = true
    rw [h, Bool.true_or]

/-- **Where the original column check admits, the fold admits.** -/
theorem Record.argumentsFitIn_of_argumentsFit {decls : TyDecls} {fields : Record.Fields}
    {arguments : List (String × Ty)} (h : Record.argumentsFit fields arguments = true) :
    Record.argumentsFitIn decls fields arguments = true := by
  unfold Record.argumentsFit at h
  unfold Record.argumentsFitIn
  obtain ⟨hargs, hfields⟩ := Bool.and_eq_true_iff.mp h
  refine Bool.and_eq_true_iff.mpr ⟨hargs, List.all_eq_true.mpr fun field hf => ?_⟩
  have hfield := List.all_eq_true.mp hfields field hf
  split
  · rename_i hn
    rw [hn] at hfield
    exact hfield
  · rename_i actual hs
    rw [hs] at hfield
    exact Record.fieldAdmitsIn_of_sub hfield

/-- **Where the record check answers, the record check under a table answers the same.** -/
theorem Record.checkIn_of_check {decls : TyDecls} {fields : Record.Fields}
    {names : List String} {tys : List Ty} {a : Ty} (h : Record.check fields names tys = some a) :
    Record.checkIn decls fields names tys = some a := by
  unfold Record.check at h
  unfold Record.checkIn
  cases hz : Machine.Record.zipNames names tys with
  | none =>
    rw [hz] at h
    cases h
  | some arguments =>
    rw [hz] at h
    change (if (fields.map Prod.fst).Nodup ∧ names.Nodup ∧
        Record.argumentsFit fields arguments = true then
      some (Ty.normalize (.record fields)) else none) = some a at h
    change (if (fields.map Prod.fst).Nodup ∧ names.Nodup ∧
        Record.argumentsFitIn decls fields arguments = true then
      some (Ty.normalize (.record fields)) else none) = some a
    split at h
    · rename_i hc
      obtain ⟨hf, hn, ha⟩ := hc
      rw [if_pos ⟨hf, hn, Record.argumentsFitIn_of_argumentsFit ha⟩]
      exact h
    · cases h

end Effect4.Program
