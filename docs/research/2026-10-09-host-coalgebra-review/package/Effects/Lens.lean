import Effects.Algebra.Handler

/-!
# Lenses: signature morphisms

A signature morphism renames every operation of `S` to one of `T` and pulls each answer back: a
lens between the two signatures, read as polynomials (positions forward, directions backward).
`Program.map` renames a program's operations along it, and `Handler.pull` pulls a handler for `T`
back to one for `S`; `interpret_map` is the one law that connects them. Renaming a host
(`Effects.Coalgebra.Comodel.rename`) uses it.

Promoted from the opt-in `Effects.Experimental.Morphism` at v0.9.0, with the coalgebra layer as
its contract's consumer (`test/contracts/coalgebra.contract.md`). The sum isomorphisms stay in
the experimental module.
-/

namespace Effects

universe uOp uAns uS uT uU uTarget

/-- A signature morphism: rename every operation and pull the answer back. -/
structure Signature.Hom (S : Signature.{uS, uAns}) (T : Signature.{uT, uAns}) where
  op : S.Op → T.Op
  back : ∀ operation, T.Answer (op operation) → S.Answer operation

namespace Signature.Hom

def id (S : Signature.{uS, uAns}) : Hom S S := ⟨fun o => o, fun _ a => a⟩

def comp {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}}
    (f : Hom S T) (g : Hom T U) : Hom S U :=
  ⟨fun o => g.op (f.op o), fun o a => f.back o (g.back (f.op o) a)⟩

end Signature.Hom

/-- Rename the operations of a program along a morphism. -/
def Program.map {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}} {A : Type uAns}
    (f : Signature.Hom S T) : Program S A → Program T A
  | .pure value => .pure value
  | .vis operation next =>
      .vis (f.op operation) (fun answer => (next (f.back operation answer)).map f)

/-- Pull a handler for `T` back to a handler for `S`. -/
def Handler.pull {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M]
    (f : Signature.Hom S T) (handler : Handler T M) : Handler S M where
  handle operation := handler.handle (f.op operation) >>= fun answer => pure (f.back operation answer)

/-- The one law: interpreting a renamed program is interpreting through the
pulled-back handler. One induction, the same shape as `interpret_through`. -/
theorem interpret_map {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {M : Type uAns → Type uTarget} [Monad M] [LawfulMonad M]
    (f : Signature.Hom S T) (handler : Handler T M) {A : Type uAns}
    (program : Program S A) :
    interpret handler (program.map f) = interpret (handler.pull f) program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      show handler.handle (f.op operation) >>= _ =
        (handler.handle (f.op operation) >>= fun answer => pure (f.back operation answer)) >>= _
      rw [bind_assoc]
      simp only [pure_bind]
      exact bind_congr fun answer => ih (f.back operation answer)

theorem Program.map_id {S : Signature.{uS, uAns}} {A : Type uAns} (program : Program S A) :
    program.map (Signature.Hom.id S) = program := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      exact congrArg (Program.vis operation) (funext fun answer => ih answer)

theorem Program.map_comp {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
    {U : Signature.{uU, uAns}} {A : Type uAns}
    (f : Signature.Hom S T) (g : Signature.Hom T U) (program : Program S A) :
    (program.map f).map g = program.map (f.comp g) := by
  induction program with
  | pure value => rfl
  | vis operation next ih =>
      exact congrArg (Program.vis (g.op (f.op operation)))
        (funext fun answer => ih _)

end Effects
