import Std

/-!
# Small lawful optics

This module provides the three pure optic shapes needed by Effect4's raw data
carriers.  They deliberately expose only ordinary functions and lists: there
is no second data representation, effectful update protocol, or profunctor
encoding hidden behind the interface.

The nested `Lawful` structures state the equations used by callers.  The
composition theorems make those equations reusable rather than requiring each
Schema dimension to prove them again.
-/

namespace Effect4

universe u v w

/-- A total view and replacement of one value inside another. -/
structure Lens (S : Type u) (A : Type v) where
  get : S → A
  replace : A → S → S

/-- A view and replacement whose focus may be absent. -/
structure Optional (S : Type u) (A : Type v) where
  preview : S → Option A
  replace : A → S → S

/-- An ordered finite collection of foci with a uniform modifier. -/
structure Traversal (S : Type u) (A : Type v) where
  collect : S → List A
  modifyAll : (A → A) → S → S

namespace Lens

/-- Modify the focus selected by a total lens. -/
def modify (optic : Lens S A) (f : A → A) (source : S) : S :=
  optic.replace (f (optic.get source)) source

/-- Compose two total lenses from outer to inner. -/
def compose (outer : Lens S A) (inner : Lens A B) : Lens S B where
  get source := inner.get (outer.get source)
  replace value source :=
    outer.replace (inner.replace value (outer.get source)) source

/-- Regard a total lens as an always-present optional. -/
def toOptional (optic : Lens S A) : Optional S A where
  preview source := some (optic.get source)
  replace := optic.replace

/-- The three standard total-lens equations. -/
structure Lawful (optic : Lens S A) : Prop where
  get_replace : ∀ source value, optic.get (optic.replace value source) = value
  replace_get : ∀ source, optic.replace (optic.get source) source = source
  replace_replace : ∀ source first second,
    optic.replace second (optic.replace first source) = optic.replace second source

namespace Lawful

/-- Composition preserves the total-lens equations. -/
theorem compose {outer : Lens S A} {inner : Lens A B}
    (outerLaw : Lawful outer) (innerLaw : Lawful inner) :
    Lawful (outer.compose inner) := by
  constructor
  · intro source value
    simp only [Lens.compose]
    rw [outerLaw.get_replace, innerLaw.get_replace]
  · intro source
    simp only [Lens.compose]
    rw [innerLaw.replace_get, outerLaw.replace_get]
  · intro source first second
    simp only [Lens.compose]
    rw [outerLaw.get_replace, innerLaw.replace_replace, outerLaw.replace_replace]

end Lawful
end Lens

namespace Optional

/-- Modify an optional focus when it is present. -/
def modify (optic : Optional S A) (f : A → A) (source : S) : S :=
  match optic.preview source with
  | none => source
  | some value => optic.replace (f value) source

/-- Compose two optional foci from outer to inner. -/
def compose (outer : Optional S A) (inner : Optional A B) : Optional S B where
  preview source := (outer.preview source).bind inner.preview
  replace value source :=
    match outer.preview source with
    | none => source
    | some focused => outer.replace (inner.replace value focused) source

/-- Regard an optional focus as a traversal with zero or one result. -/
def toTraversal (optic : Optional S A) : Traversal S A where
  collect source := (optic.preview source).toList
  modifyAll f source := optic.modify f source

/-- Stable optional equations: absent replacement is a no-op and a present
focus obeys the lens equations. -/
structure Lawful (optic : Optional S A) : Prop where
  replace_absent : ∀ source value, optic.preview source = none →
    optic.replace value source = source
  preview_replace : ∀ source current value, optic.preview source = some current →
    optic.preview (optic.replace value source) = some value
  replace_preview : ∀ source current, optic.preview source = some current →
    optic.replace current source = source
  replace_replace : ∀ source first second,
    optic.replace second (optic.replace first source) = optic.replace second source

namespace Lawful

/-- Composition preserves the stable-optional equations. -/
theorem compose {outer : Optional S A} {inner : Optional A B}
    (outerLaw : Lawful outer) (innerLaw : Lawful inner) :
    Lawful (outer.compose inner) := by
  constructor
  · intro source value absent
    change (outer.preview source).bind inner.preview = none at absent
    change (match outer.preview source with
      | none => source
      | some focused => outer.replace (inner.replace value focused) source) = source
    cases outerPreview : outer.preview source with
    | none => rfl
    | some focused =>
        rw [outerPreview] at absent
        change inner.preview focused = none at absent
        change outer.replace (inner.replace value focused) source = source
        have innerAbsent : inner.preview focused = none := absent
        rw [innerLaw.replace_absent focused value innerAbsent]
        exact outerLaw.replace_preview source focused outerPreview
  · intro source current value present
    change (outer.preview source).bind inner.preview = some current at present
    change (outer.preview (match outer.preview source with
      | none => source
      | some focused => outer.replace (inner.replace value focused) source)).bind
        inner.preview = some value
    cases outerPreview : outer.preview source with
    | none =>
        rw [outerPreview] at present
        cases present
    | some focused =>
        rw [outerPreview] at present
        change inner.preview focused = some current at present
        change (outer.preview
          (outer.replace (inner.replace value focused) source)).bind
            inner.preview = some value
        have innerPresent : inner.preview focused = some current := present
        rw [outerLaw.preview_replace source focused (inner.replace value focused)
          outerPreview]
        exact innerLaw.preview_replace focused current value innerPresent
  · intro source current present
    change (outer.preview source).bind inner.preview = some current at present
    change (match outer.preview source with
      | none => source
      | some focused => outer.replace (inner.replace current focused) source) = source
    cases outerPreview : outer.preview source with
    | none =>
        rw [outerPreview] at present
    | some focused =>
        rw [outerPreview] at present
        change inner.preview focused = some current at present
        change outer.replace (inner.replace current focused) source = source
        have innerPresent : inner.preview focused = some current := present
        rw [innerLaw.replace_preview focused current innerPresent]
        exact outerLaw.replace_preview source focused outerPreview
  · intro source first second
    change (match outer.preview (match outer.preview source with
      | none => source
      | some focused => outer.replace (inner.replace first focused) source) with
      | none => (match outer.preview source with
          | none => source
          | some focused => outer.replace (inner.replace first focused) source)
      | some focused => outer.replace (inner.replace second focused)
          (match outer.preview source with
          | none => source
          | some original => outer.replace (inner.replace first original) source)) =
      (match outer.preview source with
      | none => source
      | some focused => outer.replace (inner.replace second focused) source)
    cases outerPreview : outer.preview source with
    | none =>
        change (match outer.preview source with
          | none => source
          | some focused => outer.replace (inner.replace second focused) source) = source
        rw [outerPreview]
    | some focused =>
        change (match outer.preview
            (outer.replace (inner.replace first focused) source) with
          | none => outer.replace (inner.replace first focused) source
          | some next => outer.replace (inner.replace second next)
              (outer.replace (inner.replace first focused) source)) =
          outer.replace (inner.replace second focused) source
        have replacedPreview :
            outer.preview (outer.replace (inner.replace first focused) source) =
              some (inner.replace first focused) :=
          outerLaw.preview_replace source focused (inner.replace first focused) outerPreview
        rw [replacedPreview]
        change outer.replace (inner.replace second (inner.replace first focused))
            (outer.replace (inner.replace first focused) source) =
          outer.replace (inner.replace second focused) source
        rw [innerLaw.replace_replace, outerLaw.replace_replace]

end Lawful
end Optional

namespace Traversal

private def collectMany (collect : A → List B) : List A → List B
  | [] => []
  | head :: tail => collect head ++ collectMany collect tail

private theorem map_append_exact (f : A → B) (first second : List A) :
    (first ++ second).map f = first.map f ++ second.map f := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      change f head :: (tail ++ second).map f =
        f head :: (tail.map f ++ second.map f)
      rw [ih]

/-- Compose ordered finite traversals from outer to inner. -/
def compose (outer : Traversal S A) (inner : Traversal A B) : Traversal S B where
  collect source := collectMany inner.collect (outer.collect source)
  modifyAll f source := outer.modifyAll (inner.modifyAll f) source

/-- The finite pure traversal equations used by Effect4 data carriers. -/
structure Lawful (optic : Traversal S A) : Prop where
  modify_congr : ∀ {first second : A → A},
    (∀ value, first value = second value) → ∀ source,
      optic.modifyAll first source = optic.modifyAll second source
  modify_id : ∀ source, optic.modifyAll id source = source
  modify_comp : ∀ source first second,
    optic.modifyAll second (optic.modifyAll first source) =
      optic.modifyAll (second ∘ first) source
  collect_modify : ∀ source f,
    optic.collect (optic.modifyAll f source) = (optic.collect source).map f

namespace Lawful

/-- Composition preserves the pure finite-traversal equations. -/
theorem compose {outer : Traversal S A} {inner : Traversal A B}
    (outerLaw : Lawful outer) (innerLaw : Lawful inner) :
    Lawful (outer.compose inner) := by
  constructor
  · intro first second pointwise source
    exact outerLaw.modify_congr
      (fun value => innerLaw.modify_congr pointwise value) source
  · intro source
    change outer.modifyAll (inner.modifyAll id) source = source
    calc
      outer.modifyAll (inner.modifyAll id) source = outer.modifyAll id source :=
        outerLaw.modify_congr (fun value => innerLaw.modify_id value) source
      _ = source := outerLaw.modify_id source
  · intro source first second
    change outer.modifyAll (inner.modifyAll second)
        (outer.modifyAll (inner.modifyAll first) source) =
      outer.modifyAll (inner.modifyAll (second ∘ first)) source
    calc
      outer.modifyAll (inner.modifyAll second)
          (outer.modifyAll (inner.modifyAll first) source) =
        outer.modifyAll
          ((inner.modifyAll second) ∘ (inner.modifyAll first)) source :=
            outerLaw.modify_comp source (inner.modifyAll first)
              (inner.modifyAll second)
      _ = outer.modifyAll (inner.modifyAll (second ∘ first)) source := by
        exact outerLaw.modify_congr
          (fun value => innerLaw.modify_comp value first second) source
  · intro source f
    change collectMany inner.collect
        (outer.collect (outer.modifyAll (inner.modifyAll f) source)) =
      (collectMany inner.collect (outer.collect source)).map f
    rw [outerLaw.collect_modify]
    induction outer.collect source with
    | nil => rfl
    | cons head tail ih =>
        change inner.collect (inner.modifyAll f head) ++
            collectMany inner.collect (tail.map (inner.modifyAll f)) =
          (inner.collect head ++ collectMany inner.collect tail).map f
        rw [innerLaw.collect_modify, map_append_exact, ih]

end Lawful
end Traversal

namespace Lens.Lawful

/-- A lawful total lens remains lawful when viewed as an optional. -/
theorem toOptional {optic : Lens S A} (law : Lens.Lawful optic) :
    Optional.Lawful optic.toOptional := by
  constructor
  · intro source value absent
    change some (optic.get source) = none at absent
    cases absent
  · intro source current value _
    exact congrArg some (law.get_replace source value)
  · intro source current present
    change some (optic.get source) = some current at present
    have focused : optic.get source = current := Option.some.inj present
    rw [← focused]
    exact law.replace_get source
  · exact law.replace_replace

end Lens.Lawful

namespace Optional.Lawful

/-- A lawful optional remains lawful when viewed as a zero-or-one traversal. -/
theorem toTraversal {optic : Optional S A} (law : Optional.Lawful optic) :
    Traversal.Lawful optic.toTraversal := by
  constructor
  · intro first second pointwise source
    cases preview : optic.preview source with
    | none =>
        change optic.modify first source = optic.modify second source
        unfold Optional.modify
        rw [preview]
    | some value =>
        change optic.modify first source = optic.modify second source
        unfold Optional.modify
        rw [preview]
        exact congrArg (fun focused => optic.replace focused source)
          (pointwise value)
  · intro source
    cases preview : optic.preview source with
    | none =>
        change optic.modify id source = source
        unfold Optional.modify
        rw [preview]
    | some value =>
        change optic.modify id source = source
        unfold Optional.modify
        rw [preview]
        exact law.replace_preview source value preview
  · intro source first second
    cases preview : optic.preview source with
    | none =>
        change optic.modify second (optic.modify first source) =
          optic.modify (second ∘ first) source
        unfold Optional.modify
        rw [preview, preview]
    | some value =>
        have afterFirst :
            optic.preview (optic.replace (first value) source) = some (first value) :=
          law.preview_replace source value (first value) preview
        change optic.modify second (optic.modify first source) =
          optic.modify (second ∘ first) source
        unfold Optional.modify
        rw [preview, afterFirst]
        exact law.replace_replace source (first value) (second (first value))
  · intro source f
    cases preview : optic.preview source with
    | none =>
        change (optic.preview (optic.modify f source)).toList =
          (optic.preview source).toList.map f
        unfold Optional.modify
        rw [preview, preview]
        rfl
    | some value =>
        have after : optic.preview (optic.replace (f value) source) = some (f value) :=
          law.preview_replace source value (f value) preview
        change (optic.preview (optic.modify f source)).toList =
          (optic.preview source).toList.map f
        unfold Optional.modify
        rw [preview, after]
        rfl

end Optional.Lawful

/-! ## Identity optics and composition coherence

Each shape has an identity for `compose`, and the two forgetful views
`toOptional` and `toTraversal` commute with `compose`.  Everything below is a
corollary of the definitions and of the law records already stated above; no
new equation is assumed.

Where the total-lens definitions make a coherence square hold definitionally
it is stated as an equality of optic records, which costs no axiom.  Where it
does not, the square is stated on each face separately rather than closed with
`funext`: the packet's pointwise `modify_congr` exists precisely so that
composition reasoning never has to spend `Quot.sound` on equality of
modifiers.
-/

namespace Traversal

private theorem collectMany_append (collect : A → List B) (first second : List A) :
    collectMany collect (first ++ second) =
      collectMany collect first ++ collectMany collect second := by
  induction first with
  | nil => rfl
  | cons head tail ih =>
      change collect head ++ collectMany collect (tail ++ second) =
        (collect head ++ collectMany collect tail) ++ collectMany collect second
      rw [ih, List.append_assoc]

private theorem collectMany_collectMany (outerCollect : A → List B)
    (innerCollect : B → List C) (values : List A) :
    collectMany innerCollect (collectMany outerCollect values) =
      collectMany (fun value => collectMany innerCollect (outerCollect value)) values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change collectMany innerCollect (outerCollect head ++ collectMany outerCollect tail) =
        collectMany innerCollect (outerCollect head) ++
          collectMany (fun value => collectMany innerCollect (outerCollect value)) tail
      rw [collectMany_append, ih]

private theorem collectMany_eq_flatMap (collect : A → List B) (values : List A) :
    collectMany collect values = values.flatMap collect := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change collect head ++ collectMany collect tail =
        collect head ++ tail.flatMap collect
      rw [ih]

private theorem collectMany_singleton (values : List A) :
    collectMany (fun value => [value]) values = values := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      change head :: collectMany (fun value => [value]) tail = head :: tail
      rw [ih]

/-- The traversal whose single focus is the whole source. -/
def identity : Traversal S S where
  collect source := [source]
  modifyAll f source := f source

/-- The composite collects each inner collection in outer order.  This is the
one computation law the private accumulator hides from callers. -/
theorem compose_collect (outer : Traversal S A) (inner : Traversal A B) (source : S) :
    (outer.compose inner).collect source =
      (outer.collect source).flatMap inner.collect :=
  collectMany_eq_flatMap inner.collect (outer.collect source)

/-- The composite modifies through the nested modifier. -/
theorem compose_modifyAll (outer : Traversal S A) (inner : Traversal A B)
    (f : B → B) (source : S) :
    (outer.compose inner).modifyAll f source =
      outer.modifyAll (inner.modifyAll f) source := rfl

/-- The identity traversal is neutral on the right of composition: it collects
each focus once. -/
theorem compose_identity_collect (optic : Traversal S A) (source : S) :
    (optic.compose identity).collect source = optic.collect source :=
  collectMany_singleton (optic.collect source)

/-- The identity traversal is neutral on the right of composition: it modifies
each focus with the given function. -/
theorem compose_identity_modifyAll (optic : Traversal S A) (f : A → A) (source : S) :
    (optic.compose identity).modifyAll f source = optic.modifyAll f source := rfl

/-- The identity traversal is neutral on the left of composition on the
collecting face. -/
theorem identity_compose_collect (optic : Traversal S A) (source : S) :
    (identity.compose optic).collect source = optic.collect source :=
  List.append_nil _

/-- The identity traversal is neutral on the left of composition on the
modifying face. -/
theorem identity_compose_modifyAll (optic : Traversal S A) (f : A → A) (source : S) :
    (identity.compose optic).modifyAll f source = optic.modifyAll f source := rfl

/-- Composition is associative on the collecting face: regrouping does not
reorder the foci. -/
theorem compose_assoc_collect (outer : Traversal S A) (middle : Traversal A B)
    (inner : Traversal B C) (source : S) :
    ((outer.compose middle).compose inner).collect source =
      (outer.compose (middle.compose inner)).collect source :=
  collectMany_collectMany middle.collect inner.collect (outer.collect source)

/-- Composition is associative on the modifying face. -/
theorem compose_assoc_modifyAll (outer : Traversal S A) (middle : Traversal A B)
    (inner : Traversal B C) (f : C → C) (source : S) :
    ((outer.compose middle).compose inner).modifyAll f source =
      (outer.compose (middle.compose inner)).modifyAll f source := rfl

/-- The identity traversal satisfies the finite pure traversal equations. -/
theorem identity_lawful : Lawful (identity : Traversal S S) := by
  constructor
  · intro first second pointwise source
    exact pointwise source
  · intro _
    rfl
  · intro _ _ _
    rfl
  · intro _ _
    rfl

end Traversal

namespace Optional

/-- The optional whose always-present focus is the whole source. -/
def identity : Optional S S where
  preview source := some source
  replace value _ := value

/-- The identity optional is neutral on the left of composition. -/
theorem identity_compose (optic : Optional S A) : identity.compose optic = optic := rfl

/-- The identity optional is neutral on the right of composition on the
previewing face. -/
theorem compose_identity_preview (optic : Optional S A) (source : S) :
    (optic.compose identity).preview source = optic.preview source := by
  change (optic.preview source).bind (fun focused => some focused) = optic.preview source
  cases optic.preview source with
  | none => rfl
  | some _ => rfl

/-- The identity optional is neutral on the right of composition on the
replacing face.  Lawfulness is used exactly once: an absent focus must make
replacement a no-op, which is what the composite performs there. -/
theorem compose_identity_replace {optic : Optional S A} (law : Lawful optic)
    (value : A) (source : S) :
    (optic.compose identity).replace value source = optic.replace value source := by
  change (match optic.preview source with
    | none => source
    | some _ => optic.replace value source) = optic.replace value source
  cases present : optic.preview source with
  | none => exact (law.replace_absent source value present).symm
  | some _ => rfl

/-- The identity optional satisfies the stable-optional equations. -/
theorem identity_lawful : Lawful (identity : Optional S S) := by
  constructor
  · intro source value absent
    change some source = none at absent
    cases absent
  · intro _ _ _ _
    rfl
  · intro source current present
    change some source = some current at present
    exact (Option.some.inj present).symm
  · intro _ _ _
    rfl

/-- The identity optional is the identity traversal. -/
theorem toTraversal_identity :
    (identity : Optional S S).toTraversal = Traversal.identity := rfl

/-- `toTraversal` commutes with composition on the collecting face, with no
hypothesis: an absent outer focus collects nothing either way. -/
theorem toTraversal_compose_collect (outer : Optional S A) (inner : Optional A B)
    (source : S) :
    (outer.compose inner).toTraversal.collect source =
      (outer.toTraversal.compose inner.toTraversal).collect source := by
  change ((outer.preview source).bind inner.preview).toList =
    Traversal.collectMany (fun value => (inner.preview value).toList)
      (outer.preview source).toList
  cases outer.preview source with
  | none => rfl
  | some focused =>
      change (inner.preview focused).toList = (inner.preview focused).toList ++ []
      exact (List.append_nil _).symm

/-- `toTraversal` commutes with composition on the modifying face for a stable
outer optional.  The hypothesis is needed exactly where the outer focus is
present and the inner focus is absent: the composite leaves the source alone,
while the two-step traversal writes the unchanged focus back. -/
theorem toTraversal_compose_modifyAll {outer : Optional S A} (outerLaw : Lawful outer)
    (inner : Optional A B) (f : B → B) (source : S) :
    (outer.compose inner).toTraversal.modifyAll f source =
      (outer.toTraversal.compose inner.toTraversal).modifyAll f source := by
  show (outer.compose inner).modify f source =
    outer.modify (fun focused => inner.modify f focused) source
  cases outerPresent : outer.preview source with
  | none =>
      simp only [Optional.modify, Optional.compose, outerPresent, Option.bind]
  | some focused =>
      cases innerPresent : inner.preview focused with
      | none =>
          simp only [Optional.modify, Optional.compose, outerPresent, innerPresent,
            Option.bind]
          exact (outerLaw.replace_preview source focused outerPresent).symm
      | some value =>
          simp only [Optional.modify, Optional.compose, outerPresent, innerPresent,
            Option.bind]

end Optional

namespace Lens

/-- Regard a total lens as a traversal with exactly one focus. -/
def toTraversal (optic : Lens S A) : Traversal S A :=
  optic.toOptional.toTraversal

/-- The lens whose focus is the whole source. -/
def identity : Lens S S where
  get source := source
  replace value _ := value

/-- The identity lens is neutral on the right of composition. -/
theorem compose_identity (optic : Lens S A) : optic.compose identity = optic := rfl

/-- The identity lens is neutral on the left of composition. -/
theorem identity_compose (optic : Lens S A) : identity.compose optic = optic := rfl

/-- Lens composition is associative. -/
theorem compose_assoc (outer : Lens S A) (middle : Lens A B) (inner : Lens B C) :
    (outer.compose middle).compose inner = outer.compose (middle.compose inner) := rfl

/-- `toOptional` commutes with composition. -/
theorem toOptional_compose (outer : Lens S A) (inner : Lens A B) :
    (outer.compose inner).toOptional =
      outer.toOptional.compose inner.toOptional := rfl

/-- `toTraversal` commutes with composition.  The total case needs no
hypothesis: a lens focus is never absent, so the composite and the two-step
traversal agree on both faces definitionally. -/
theorem toTraversal_compose (outer : Lens S A) (inner : Lens A B) :
    (outer.compose inner).toTraversal =
      outer.toTraversal.compose inner.toTraversal := rfl

/-- The identity lens is the identity optional. -/
theorem toOptional_identity :
    (identity : Lens S S).toOptional = Optional.identity := rfl

/-- The identity lens is the identity traversal. -/
theorem toTraversal_identity :
    (identity : Lens S S).toTraversal = Traversal.identity := rfl

/-- The identity lens satisfies the three total-lens equations. -/
theorem identity_lawful : Lens.Lawful (identity : Lens S S) := by
  constructor
  · intro _ _
    rfl
  · intro _
    rfl
  · intro _ _ _
    rfl

end Lens

namespace Lens.Lawful

/-- A lawful total lens remains lawful when viewed as a one-focus traversal. -/
theorem toTraversal {optic : Lens S A} (law : Lens.Lawful optic) :
    Traversal.Lawful optic.toTraversal :=
  Optional.Lawful.toTraversal law.toOptional

end Lens.Lawful

end Effect4
