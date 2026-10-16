import Effect4.Program.Typed
import Effect4.Program.Columns
import Effect4.Program.TyExpand

/-!
# Program.TyDecls — the application's type declarations, and recursive types

A **declaration table** is a list of named type bodies, monomorphic (decisions rows 124, 158
and 400). A body refers to a declaration, itself included, by a nominal reference `app n args`,
which normalization keeps; a host handle `handle n` is no reference (decisions row 406 (1)). No
`Ty` constructor is added. The table
is a system of type equations `Xᵢ = Tᵢ(X₁ … Xₖ)`, read iso-recursively: a declared name unfolds
to its body only where membership asks it, and the order compares names, never bodies.

This module holds the definitions; the laws are `Effect4.Laws.Program.TyDecls`, and the formal
note is `docs/research/2026-10-15-recursive-types/formal.md`.

- `Val.obligations`: one step of `Val.hasTy`, read one level. A value's shape against a type's
  head, and the questions it leaves: each child value with the type it must fit. Every child is
  strictly smaller than the value (`Val.sizeOf_obligation`).
- `Val.hasTyIn`: the checker. A union is read by its members (`Ty.members`), a declared name by
  its body, every other head by its obligations. It recurses on the value's size, then on the
  declared names not yet unfolded since the last value constructor (`TyDecls.unseen`). No fuel:
  the measure is well founded, and a name met again before a value constructor answers `false`.
- `TyDecls.saturate`: the least set of declared names closed under a round's test, iterated
  from no name until a round adds none. Inhabitance and guardedness are its two instances.
- `TyDecls.guarded`: every declared name is ranked, its declaration's head naming only names
  ranked before it, so every cycle passes a value constructor (contractivity).
- `TyDecls.inhabited`: inhabitance, the least fixed point over the table.

At the empty table every judgment here is the existing one (`hasTyIn_nil`, `inhabited_nil` in the
laws). The module is not a Lean module (decisions row 200): it imports `Program/Typed.lean`, a
specialization site of decisions row 202, whose importers stay non-module.
-/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-! ## The table

`TyDecls`, its lookup `TyDecls.body?`, `Ty.refName?`, the unfolding `TyDecls.unfold?` and the
measure of an unfolding `TyDecls.unseen` are `Program/TyExpand.lean`'s, a Lean module that
`Modeled` and the checker's head reader (`Program/TyHead.lean`) import. -/

namespace TyDecls

/-! ## Saturation: the least set of names closed under a round -/

/-- One round: the declared names that `holds` accepts once the names of `known` are accepted. -/
def round (decls : TyDecls) (holds : List String → String → Bool) (known : List String) :
    List String :=
  decls.filterMap fun d => if holds known d.1 then some d.1 else none

/-- A name of a round is declared, and the round's test accepts it. -/
theorem mem_round {decls : TyDecls} {holds : List String → String → Bool} {known : List String}
    {name : String} (h : name ∈ decls.round holds known) :
    (∃ d ∈ decls, d.1 = name) ∧ holds known name = true := by
  obtain ⟨d, hd, hn⟩ := List.mem_filterMap.mp h
  split at hn
  · rename_i hh
    cases hn
    exact ⟨⟨d, hd, rfl⟩, hh⟩
  · cases hn

/-- **Saturation**, the least fixed point of a round by iteration: add each round's new names
until a round adds none. Well founded on the declared names not yet known: no fuel. -/
def saturate (decls : TyDecls) (holds : List String → String → Bool) (known : List String) :
    List String :=
  if _h : ((decls.round holds known).filter fun name => !known.contains name) = [] then known
  else decls.saturate holds
    (known ++ (decls.round holds known).filter fun name => !known.contains name)
termination_by decls.unseen known
decreasing_by
  obtain ⟨name, hname⟩ := List.exists_mem_of_ne_nil _ _h
  obtain ⟨hround, hfresh⟩ := List.mem_filter.mp hname
  obtain ⟨⟨d, hd, rfl⟩, _⟩ := mem_round hround
  have hknown : known.contains d.1 = false := by
    cases hc : known.contains d.1 with
    | false => rfl
    | true =>
      rw [hc] at hfresh
      cases hfresh
  refine unseen_lt (fun x hx => ?_) ⟨d, hd, ?_, hknown⟩
  · rw [List.contains_append, hx, Bool.true_or]
  · rw [List.contains_append, List.contains_iff_mem.mpr hname, Bool.or_true]

/-! ## Guardedness: a rank for every name -/

/-- The declared names a type names at its head: each union member that references one. -/
def headNames (decls : TyDecls) (t : Ty) : List String :=
  t.members.filterMap fun m => (decls.unfold? m).map Prod.fst

/-- A round's test of guardedness: every declared name at the head of the name's declaration is
ranked already. -/
def rankHolds (decls : TyDecls) (ranked : List String) (name : String) : Bool :=
  match decls.body? name with
  | some body => (decls.headNames body).all ranked.contains
  | none => false

/-- The ranked names: a topological order of the head references, by saturation. A name on a
head cycle, or one whose head reaches a cycle, is never ranked. -/
def rankedNames (decls : TyDecls) : List String := decls.saturate decls.rankHolds []

/-- The first declared name that no round ranks, if any: the name a table's admission refuses. Its
unfolding at one value can return to a name before it reaches a value constructor. -/
def unguardedAt? (decls : TyDecls) : Option String :=
  (decls.find? fun d => !decls.rankedNames.contains d.1).map Prod.fst

/-- **Guarded** (contractive): every declared name is ranked, so the head references have no
cycle and every cycle of the table passes a value constructor. -/
def guarded (decls : TyDecls) : Bool := (decls.unguardedAt?).isNone

end TyDecls

/-! ## One step of membership -/

/-- A record frame's questions (`namedHasTy`'s reading, decisions rows 157 and 165): each value
that a canonical field names, with the field's type; `none` where the names refuse. -/
def namedPairs : List (String × Bool × Ty) → List Val → List Val → Option (List (Val × Ty))
  | [], [], [] => some []
  | (_, o, _) :: cs, [], [] => if o then namedPairs cs [] [] else none
  | (n, o, t) :: cs, .str m :: ns, x :: xs =>
    if m = n then (namedPairs cs ns xs).map ((x, t) :: ·)
    else if o then namedPairs cs (.str m :: ns) (x :: xs) else none
  | _, _, _ => none

/-- A tuple's questions (`itemsHasTy`'s reading, decisions row 159): each item with its type. -/
def itemPairs : List Ty → List Val → Option (List (Val × Ty))
  | [], [] => some []
  | t :: ts, x :: xs => (itemPairs ts xs).map ((x, t) :: ·)
  | _, _ => none

/-- A map's questions (`entriesHasTy`'s reading, decisions row 125): each key at the key type and
each value at the value type; `none` at an entry that is no pair. -/
def entryPairs (key value : Ty) : List Val → Option (List (Val × Ty))
  | [] => some []
  | .pair a x :: es => (entryPairs key value es).map fun ps => (a, key) :: (x, value) :: ps
  | _ :: _ => none

/-- A cause's questions (`causeAdmits`'s reading): each typed failure's value at the error
type; `none` at a failure with no typed payload. -/
def causeObligations (error : Ty) : List (Reason Err Defect FiberId Ann) → Option (List (Val × Ty))
  | [] => some []
  | .fail e _ :: rs =>
    match valOfErr e with
    | some x => (causeObligations error rs).map ((x, error) :: ·)
    | none => none
  | _ :: rs => causeObligations error rs

/-- **One step of membership** (`Val.hasTy`'s arms, read one level): the value's shape against
the type's head, and the questions it leaves, each child value with the type it must fit.
`none` where the shape refuses, `some []` at a leaf that fits. A union has no head: the checker
reads it by its members. A reference `app n args` is a leaf here, read as a handle at its name;
the checker unfolds a declared one before it asks this step. -/
def Val.obligations (v : Val) (ty : Ty) (allocated : List String) : Option (List (Val × Ty)) :=
  match ty with
  | .option inner =>
    match v with
    | .none => some []
    | .some x => some [(x, inner)]
    | _ => none
  | .list item =>
    match v with
    | Value.fiberSnapshot _ => (Val.snapshot? v).map fun ids => ids.map fun id => (Val.fiber id, item)
    | .list values => some (values.map fun x => (x, item))
    | _ => none
  | .prod a b =>
    match v with
    | .list [x, y] => some [(x, a), (y, b)]
    | _ => none
  | .except error value =>
    match v with
    | .ctor 0 [err] => some [(err, error)]
    | .ctor 1 [val] => some [(val, value)]
    | _ => none
  | .exitOf value error =>
    match v with
    | Val.exitOk x => some [(x, value)]
    | Value.exitErr written => (causeImage.ofVal written).bind fun c => causeObligations error c.reasons
    | _ => none
  | .causeOf error => (Val.cause? v).bind fun c => causeObligations error c.reasons
  | .union _ _ => none
  | .record fs => (recordParts? v).bind fun parts => namedPairs (Ty.canon fs) parts.1 parts.2
  | .map key value =>
    match v with
    | .list es => if sortedEntries es then entryPairs key value es else none
    | _ => none
  | .tuple ts =>
    match v with
    | .list xs => itemPairs ts xs
    | _ => none
  | ty => if Val.hasTy v ty allocated then some [] else none

/-! ### Every question is about a smaller value -/

/-- A record frame's questions ask about its values. -/
theorem mem_of_namedPairs (cs : List (String × Bool × Ty)) (ns xs : List Val) :
    ∀ {ps : List (Val × Ty)}, namedPairs cs ns xs = some ps → ∀ p ∈ ps, p.1 ∈ xs := by
  fun_induction namedPairs cs ns xs with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 _ _ _ ih => exact ih
  | case3 =>
    intro ps h
    cases h
  | case4 _ _ _ _ _ x xs ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hqs p hq)
  | case5 _ _ _ _ _ _ _ _ ih => exact ih
  | case6 =>
    intro ps h
    cases h
  | case7 =>
    intro ps h
    cases h

/-- A tuple's questions ask about its items. -/
theorem mem_of_itemPairs (ts : List Ty) (xs : List Val) :
    ∀ {ps : List (Val × Ty)}, itemPairs ts xs = some ps → ∀ p ∈ ps, p.1 ∈ xs := by
  fun_induction itemPairs ts xs with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 _ _ x xs ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hq
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih hqs p hq)
  | case3 =>
    intro ps h
    cases h

/-- A map's questions ask about the two sides of its entries. -/
theorem mem_of_entryPairs (key value : Ty) (es : List Val) :
    ∀ {ps : List (Val × Ty)}, entryPairs key value es = some ps →
      ∀ p ∈ ps, ∃ a x, Store.Val.pair a x ∈ es ∧ (p.1 = a ∨ p.1 = x) := by
  fun_induction entryPairs key value es with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 a x es ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨a, x, List.mem_cons_self, Or.inl rfl⟩
    rcases List.mem_cons.mp hp with rfl | hq
    · exact ⟨a, x, List.mem_cons_self, Or.inr rfl⟩
    · obtain ⟨a', x', he, hpx⟩ := ih hqs p hq
      exact ⟨a', x', List.mem_cons_of_mem _ he, hpx⟩
  | case3 =>
    intro ps h
    cases h

/-- A cause's questions ask about the values of its typed failures. -/
theorem mem_of_causeObligations (error : Ty) (rs : List (Reason Err Defect FiberId Ann)) :
    ∀ {ps : List (Val × Ty)}, causeObligations error rs = some ps →
      ∀ p ∈ ps, ∃ e ann, Reason.fail e ann ∈ rs ∧ valOfErr e = some p.1 := by
  fun_induction causeObligations error rs with
  | case1 =>
    intro ps h p hp
    cases h
    cases hp
  | case2 e ann rs x hx ih =>
    intro ps h p hp
    obtain ⟨qs, hqs, rfl⟩ := Option.map_eq_some_iff.mp h
    rcases List.mem_cons.mp hp with rfl | hq
    · exact ⟨e, ann, List.mem_cons_self, hx⟩
    · obtain ⟨e', ann', he, hv⟩ := ih hqs p hq
      exact ⟨e', ann', List.mem_cons_of_mem _ he, hv⟩
  | case3 =>
    intro ps h
    cases h
  | case4 r rs _ ih =>
    intro ps h p hp
    obtain ⟨e', ann', he, hv⟩ := ih h p hp
    exact ⟨e', ann', List.mem_cons_of_mem _ he, hv⟩

/-- A record frame's values are smaller than the frame. -/
theorem sizeOf_lt_of_recordParts {v : Val} {ns xs : List Val} (h : recordParts? v = some (ns, xs))
    {x : Val} (hx : x ∈ xs) : sizeOf x < sizeOf v := by
  unfold recordParts? at h
  split at h
  · cases h
    have := List.sizeOf_lt_of_mem hx
    simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec, Store.Val.list.sizeOf_spec]
    omega
  · cases h

/-- A snapshot's fiber handles are smaller than the snapshot: the image is exact. -/
theorem sizeOf_fiber_lt_of_snapshot {v : Val} {ids : List FiberId} (h : Val.snapshot? v = some ids)
    {id : FiberId} (hid : id ∈ ids) : sizeOf (Val.fiber id) < sizeOf v := by
  unfold Val.snapshot? at h
  split at h
  · rename_i handles
    have hex := (Store.Image.list Value.fiberHandle).ofVal_exact h
    subst hex
    have hmem : Val.fiber id ∈ ids.map Value.fiberHandle.toVal := List.mem_map_of_mem hid
    have := List.sizeOf_lt_of_mem hmem
    show sizeOf (Val.fiber id) < sizeOf (Store.Val.ctor 3 [Store.Val.list (ids.map Value.fiberHandle.toVal)])
    simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec, Store.Val.list.sizeOf_spec]
    omega
  · cases h

/-- A typed failure's value is no larger than the error's image. -/
theorem sizeOf_valOfErr_le {e : Err} {x : Val} (h : valOfErr e = some x) :
    sizeOf x ≤ sizeOf (Err.image.toVal e) := by
  cases e with
  | boom => cases h
  | tag code =>
    cases h
    show sizeOf (Store.Val.nat code) ≤ sizeOf (Store.Val.ctor 1 [Store.Val.nat code])
    simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
    omega
  | tagged tag message =>
    cases h
    show sizeOf (Store.Val.list [.str tag, .str message]) ≤
      sizeOf (Store.Val.ctor 2 [.str tag, .str message])
    simp only [Store.Val.ctor.sizeOf_spec, Store.Val.list.sizeOf_spec]
    omega
  | text message =>
    cases h
    show sizeOf (Store.Val.str message) ≤ sizeOf (Store.Val.ctor 3 [Store.Val.str message])
    simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
    omega
  | payload p =>
    cases h
    show sizeOf p.val ≤ sizeOf (Store.Val.ctor 4 [p.val])
    simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
    omega

/-- A written cause's typed failures carry values smaller than the cause: the image is exact. -/
theorem sizeOf_lt_of_causeImage {written : Val} {c : CauseV} (h : causeImage.ofVal written = some c)
    {e : Err} {ann : ReasonAnnotations Ann} (he : Reason.fail e ann ∈ c.reasons) {x : Val} (hx : valOfErr e = some x) :
    sizeOf x < sizeOf written := by
  have hex := causeImage.ofVal_exact h
  subst hex
  have hmem : Value.toReason Err.image Defect.image Value.fiberIdentity Store.Image.unit
      (Reason.fail e ann) ∈
      c.reasons.map (Value.toReason Err.image Defect.image Value.fiberIdentity Store.Image.unit) :=
    List.mem_map_of_mem he
  have hlt := List.sizeOf_lt_of_mem hmem
  have hle := sizeOf_valOfErr_le hx
  show sizeOf x < sizeOf (Store.Val.ctor 0 [Store.Val.list
    (c.reasons.map (Value.toReason Err.image Defect.image Value.fiberIdentity Store.Image.unit))])
  have hr : Value.toReason Err.image Defect.image Value.fiberIdentity Store.Image.unit
      (Reason.fail e ann) = Store.Val.ctor 0 [Err.image.toVal e,
        (Value.annotations Store.Image.unit).toVal ann] := rfl
  rw [hr] at hlt
  simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec, Store.Val.list.sizeOf_spec] at hlt ⊢
  omega

/-- **Every question of a step is about a strictly smaller value**: the checker's well-founded
measure falls at each value constructor. -/
theorem Val.sizeOf_obligation {v : Val} {ty : Ty} {allocated : List String} {ps : List (Val × Ty)}
    (h : Val.obligations v ty allocated = some ps) {p : Val × Ty} (hp : p ∈ ps) :
    sizeOf p.1 < sizeOf v := by
  unfold Val.obligations at h
  split at h
  · split at h
    · cases h
      cases hp
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      simp only [Store.Val.some.sizeOf_spec]
      omega
    · cases h
  · split at h
    · rename_i handles
      obtain ⟨ids, hids, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hp
      exact sizeOf_fiber_lt_of_snapshot hids hid
    · cases h
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
      have := List.sizeOf_lt_of_mem hx
      simp only [Store.Val.list.sizeOf_spec]
      omega
    · cases h
  · split at h
    · cases h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;>
        simp only [Store.Val.list.sizeOf_spec, List.cons.sizeOf_spec] <;> omega
    · cases h
  · split at h
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · cases h
  · split at h
    · cases h
      rcases List.mem_singleton.mp hp with rfl
      simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · rename_i written
      obtain ⟨c, hc, hobl⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨e, ann, he, hx⟩ := mem_of_causeObligations _ _ hobl p hp
      have := sizeOf_lt_of_causeImage hc he hx
      simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · cases h
  · obtain ⟨c, hc, hobl⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨e, ann, he, hx⟩ := mem_of_causeObligations _ _ hobl p hp
    unfold Val.cause? at hc
    split at hc
    · rename_i written
      have := sizeOf_lt_of_causeImage hc he hx
      simp only [Store.Val.ctor.sizeOf_spec, List.cons.sizeOf_spec]
      omega
    · cases hc
  · cases h
  · obtain ⟨parts, hparts, hnamed⟩ := Option.bind_eq_some_iff.mp h
    exact sizeOf_lt_of_recordParts hparts (mem_of_namedPairs _ _ _ hnamed p hp)
  · split at h
    · rename_i es
      split at h
      · obtain ⟨a, x, he, hpx⟩ := mem_of_entryPairs _ _ _ h p hp
        have := List.sizeOf_lt_of_mem he
        simp only [Store.Val.list.sizeOf_spec]
        simp only [Store.Val.pair.sizeOf_spec] at this
        rcases hpx with hpx | hpx <;> rw [hpx] <;> omega
      · cases h
    · cases h
  · split at h
    · have := List.sizeOf_lt_of_mem (mem_of_itemPairs _ _ h p hp)
      simp only [Store.Val.list.sizeOf_spec]
      omega
    · cases h
  · split at h
    · cases h
      cases hp
    · cases h

/-! ## The checker -/

/-- **Membership under a declaration table** (decisions rows 124 and 400): `Val.hasTy` with
the table. A union is read by its members. A member that references a declared name unfolds to
the name's body, unless `seen`, the names unfolded since the last value constructor, already
holds it. Every other member asks its step's questions, each at a strictly smaller value and
with `seen` empty. Callers pass `seen := []`.

Well founded on the value's size, then on the declared names not yet unfolded: no fuel. On the
empty table it is `Val.hasTy` (`hasTyIn_nil`), and it decides the inductive membership on every
table (`hasTyIn_iff`, `Laws/Program/TyDecls.lean`). -/
def Val.hasTyIn (decls : TyDecls) (seen : List String) (v : Val) (t : Ty)
    (allocated : List String) : Bool :=
  t.members.any fun m =>
    match _h : decls.unfold? m with
    | some (name, body) =>
      if _hs : seen.contains name then false
      else Val.hasTyIn decls (name :: seen) v body allocated
    | none =>
      match _ho : Val.obligations v m allocated with
      | some ps => ps.attach.all fun ⟨p, _hp⟩ => Val.hasTyIn decls [] p.1 p.2 allocated
      | none => false
termination_by (sizeOf v, decls.unseen seen)
decreasing_by
  · exact Prod.Lex.right _
      (TyDecls.unseen_cons_lt (TyDecls.body?_of_unfold? _h) (Bool.eq_false_iff.mpr _hs))
  · exact Prod.Lex.left _ _ (Val.sizeOf_obligation _ho _hp)

/-! ## Inhabitance: the least fixed point over the table -/

namespace TyDecls

/-- Inhabitance (`inhabitedAlg`) with each declared name read from `known`, the names already
shown to have a member. -/
def inhabitedWith (decls : TyDecls) (known : List String) : TyAlgebra (fun _ => Bool) :=
  { inhabitedAlg with
    ty_app := fun name args =>
      if (decls.body? name).isSome then known.contains name else inhabitedAlg.ty_app name args }

/-- A round's test of inhabitance: the name's declaration, its first entry (`body?`, as the
checker reads it), has a member when `known`'s names do. A repeated name's later entries are read
nowhere. -/
def inhabitedHolds (decls : TyDecls) (known : List String) (name : String) : Bool :=
  match decls.body? name with
  | some body => cata_ty (decls.inhabitedWith known) body
  | none => false

/-- The declared names that have a member: the least fixed point by saturation. -/
def inhabitedNames (decls : TyDecls) : List String := decls.saturate decls.inhabitedHolds []

/-- **Inhabitance under the table**: `inhabited` with every declared name read as the least
fixed point says. On the empty table it is `inhabited` (`inhabited_nil`). -/
def inhabited (decls : TyDecls) (t : Ty) : Bool :=
  cata_ty (decls.inhabitedWith decls.inhabitedNames) t

end TyDecls

end Effect4.Program
