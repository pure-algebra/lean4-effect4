import Effects.Algebra.Handler.Composition
import Effects.Algebra.Laws
import Effect4.Data.Optic

/-!
# Effectful field semantics probe

This scratch file tests the smallest effectful interface that can be derived
from the existing `Lens`, `Signature`, `Program`, and `Handler` declarations.
It is deliberately not a persisted Schema annotation: a stored annotation
should carry first-order operation identities, while this resolved semantic
view carries actual operations and their answer-equality witnesses.

The probe establishes equations only at the structural `interpret` face.  It
does not assign a bind law to any fixed-fuel runner.
-/

namespace Effect4.Workshop.EffectfulField

universe uOp uAns uTarget

/-- Perform an operation whose dependent answer is propositionally, rather
than definitionally, the result requested by the caller. -/
def performAs {signature : Signature.{uOp, uAns}} {A : Type uAns}
    (operation : signature.Op)
    (answerEq : signature.Answer operation = A) : Program signature A :=
  Program.perform operation >>= fun answer =>
    pure (answerEq.mp answer)

/-- The corresponding normalization of a handler action.  Keeping the
transport at the returned value avoids transporting the entire target
computation through `congrArg M answerEq`. -/
def handleAs {signature : Signature.{uOp, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] {A : Type uAns}
    (handler : Handler signature M) (operation : signature.Op)
    (answerEq : signature.Answer operation = A) : M A :=
  handler.handle operation >>= fun answer =>
    pure (answerEq.mp answer)

/-- A resolved effectful field view.  `optic` is the existing pure focus.  The
operation builders are the semantic resolution of first-order annotation
identities against one known closed signature. -/
structure Access (signature : Signature.{uOp, uAns})
    (Source Focus : Type uAns) where
  optic : Lens Source Focus
  read : Source → signature.Op
  readAnswer : ∀ source, signature.Answer (read source) = Focus
  write : Source → Focus → signature.Op

namespace Access

variable {signature : Signature.{uOp, uAns}}
variable {Source Focus : Type uAns}

/-- Read the annotated field through the effect signature. -/
def get (access : Access signature Source Focus) (source : Source) :
    Program signature Focus :=
  performAs (access.read source) (access.readAnswer source)

/-- Write the annotated field, discard the operation-specific reply, and
return the source updated by the existing pure lens.  No `Unit` equality is
required, so this stays polymorphic in the signature's answer universe. -/
def set (access : Access signature Source Focus)
    (value : Focus) (source : Source) : Program signature Source :=
  Program.perform (access.write source value) >>= fun _ =>
    pure (access.optic.replace value source)

/-- Read, transform, and write an annotated field. -/
def modify (access : Access signature Source Focus)
    (f : Focus → Focus) (source : Source) : Program signature Source :=
  access.get source >>= fun current =>
    access.set (f current) source

theorem interpret_performAs {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (handler : Handler signature M) (operation : signature.Op)
    (answerEq : signature.Answer operation = Focus) :
    interpret handler (performAs operation answerEq) =
      handleAs handler operation answerEq := by
  unfold performAs handleAs
  rfl

theorem interpret_get {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (handler : Handler signature M)
    (source : Source) :
    interpret handler (access.get source) =
      handleAs handler (access.read source) (access.readAnswer source) :=
  interpret_performAs handler _ _

theorem interpret_set {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (handler : Handler signature M)
    (value : Focus) (source : Source) :
    interpret handler (access.set value source) =
      handler.handle (access.write source value) >>= fun _ =>
        pure (access.optic.replace value source) := by
  unfold set
  rfl

theorem interpret_modify {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (handler : Handler signature M)
    (f : Focus → Focus) (source : Source) :
    interpret handler (access.modify f source) =
      handleAs handler (access.read source) (access.readAnswer source) >>= fun current =>
        handler.handle (access.write source (f current)) >>= fun _ =>
          pure (access.optic.replace (f current) source) := by
  change interpret handler
      (Program.bind (access.get source) fun current => access.set (f current) source) = _
  rw [interpret_bind, interpret_get]
  apply bind_congr
  intro current
  exact interpret_set access handler (f current) source

/-- The strongest reusable local handler assumptions: normalized reads agree
with the pure focus and normalized writes acknowledge successfully. -/
structure HandlerLaw {M : Type uAns → Type uTarget} [Monad M]
    (access : Access signature Source Focus) (handler : Handler signature M) : Prop where
  read_eq : ∀ source,
    handleAs handler (access.read source) (access.readAnswer source) =
      pure (access.optic.get source)
  write_discard : ∀ source value,
    (handler.handle (access.write source value) >>= fun _ =>
      pure (access.optic.replace value source)) =
        pure (access.optic.replace value source)

theorem interpret_get_eq_pure {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (handler : Handler signature M)
    (law : HandlerLaw access handler) (source : Source) :
    interpret handler (access.get source) = pure (access.optic.get source) := by
  rw [interpret_get, law.read_eq]

theorem interpret_set_eq_pure {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (handler : Handler signature M)
    (law : HandlerLaw access handler) (value : Focus) (source : Source) :
    interpret handler (access.set value source) =
      pure (access.optic.replace value source) := by
  rw [interpret_set]
  exact law.write_discard source value

theorem interpret_modify_eq_pure {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (handler : Handler signature M)
    (law : HandlerLaw access handler) (f : Focus → Focus) (source : Source) :
    interpret handler (access.modify f source) =
      pure (access.optic.modify f source) := by
  rw [interpret_modify, law.read_eq, pure_bind, law.write_discard]
  rfl

theorem interpret_get_after_set_eq_pure {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (opticLaw : Lens.Lawful access.optic)
    (handler : Handler signature M) (law : HandlerLaw access handler)
    (source : Source) (value : Focus) :
    interpret handler (access.get (access.optic.replace value source)) = pure value := by
  rw [interpret_get_eq_pure access handler law, opticLaw.get_replace]

theorem interpret_set_current_eq_pure {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (opticLaw : Lens.Lawful access.optic)
    (handler : Handler signature M) (law : HandlerLaw access handler)
    (source : Source) :
    interpret handler (access.set (access.optic.get source) source) = pure source := by
  rw [interpret_set_eq_pure access handler law, opticLaw.replace_get]

theorem interpret_modify_id_eq_pure {M : Type uAns → Type uTarget}
    [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus) (opticLaw : Lens.Lawful access.optic)
    (handler : Handler signature M) (law : HandlerLaw access handler)
    (source : Source) :
    interpret handler (access.modify id source) = pure source := by
  rw [interpret_modify_eq_pure access handler law]
  change pure (access.optic.replace (access.optic.get source) source) = pure source
  rw [opticLaw.replace_get]

/-- Existing handler composition supplies the full collapse law; the field API
needs no special handler carrier. -/
theorem interpret_through_get {middle : Signature.{uOp, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus)
    (upper : Handler signature (Program middle)) (lower : Handler middle M)
    (source : Source) :
    interpret lower (interpret upper (access.get source)) =
      interpret (upper.through lower) (access.get source) :=
  interpret_through upper lower _

theorem interpret_through_set {middle : Signature.{uOp, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus)
    (upper : Handler signature (Program middle)) (lower : Handler middle M)
    (value : Focus) (source : Source) :
    interpret lower (interpret upper (access.set value source)) =
      interpret (upper.through lower) (access.set value source) :=
  interpret_through upper lower _

theorem interpret_through_modify {middle : Signature.{uOp, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (access : Access signature Source Focus)
    (upper : Handler signature (Program middle)) (lower : Handler middle M)
    (f : Focus → Focus) (source : Source) :
    interpret lower (interpret upper (access.modify f source)) =
      interpret (upper.through lower) (access.modify f source) :=
  interpret_through upper lower _

end Access

end Effect4.Workshop.EffectfulField
