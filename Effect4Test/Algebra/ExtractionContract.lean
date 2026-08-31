/-
Contract packet: `test/contracts/algebra-extraction.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until the Effect4 algebra modules and frozen declarations exist.
-/

import Effect4.Algebra.Signature
import Effect4.Algebra.Program
import Effect4.Algebra.Handler
import Effect4.Algebra.Laws
import Effect4.Algebra.MonadLaws
import Effect4.Algebra.Sum
import Effect4.Algebra.Universal
import Effect4.Algebra.Handler.Composition
import Effect4.Algebra.Handler.Category

namespace Effect4Test.Algebra.ExtractionContract

open Effect4

universe uOp uAns v

section SurfaceSnapshot

variable (S : Signature.{uOp, uAns})
variable (A B C : Type uAns)
variable (M : Type uAns → Type v)

-- The signature answer universe, program result universe, and handler input
-- universe are one parameter. These declarations reject a silently wider
-- result carrier that `M` could not consume.
def mkSignature
    (Op : Type uOp) (Answer : Op → Type uAns) : Signature.{uOp, uAns} :=
  { Op := Op, Answer := Answer }

#check @Signature.sum
#check @Program.pure
#check @Program.vis
#check @Program.bind
#check @Program.perform
#check @Program.inl
#check @Program.inr
#check @Handler.mk
#check @Handler.ext
#check @interpret
#check @Handler.sum
#check @identityHandler
#check @Handler.through

#synth Monad (Program S)
#synth LawfulMonad (Program S)

#check @Program.bind_pure_right
#check @Program.bind_assoc
#check @Program.perform_bind
#check @interpret_pure
#check @interpret_perform
#check @interpret_bind
#check @interpret_bind_of_equations
#check @interpret_identity
#check @Handler.sum_handle_inl
#check @Handler.sum_handle_inr
#check @Handler.sum_unique
#check @interpret_inl
#check @interpret_inr
#check @Program.inl_pure
#check @Program.inr_pure
#check @Program.inl_bind
#check @Program.inr_bind
#check @Program.inl_injective
#check @Program.inr_injective
#check @Program.inl_unique
#check @Program.inr_unique
#check @IsMonadMorphism
#check @interpret_isMonadMorphism
#check @interpret_of_isMonadMorphism
#check @exists_handler_of_isMonadMorphism
#check @handler_eq_of_interpret_operation_eq
#check @handler_eq_of_interpret_eq
#check @program_is_free
#check @program_is_initial_in_models
#check @interpret_pinned
#check @interpret_through
#check @Handler.through_assoc
#check @Handler.through_identity_right
#check @Handler.through_identity_left
#check @Handler.through_endomorphism_monoid

end SurfaceSnapshot

/-! The smallest concrete pair that detects a swapped or discarded sum arm. -/

inductive LeftOp where
  | tick
deriving DecidableEq

inductive RightOp where
  | jump
deriving DecidableEq

def LeftSignature : Signature.{0, 0} where
  Op := LeftOp
  Answer := fun _ => Nat

def RightSignature : Signature.{0, 0} where
  Op := RightOp
  Answer := fun _ => Nat

abbrev CounterM := StateM Nat

def leftHandler : Handler LeftSignature CounterM where
  handle
    | .tick => fun state => (state, state + 1)

def rightHandler : Handler RightSignature CounterM where
  handle
    | .jump => fun state => (state + 100, state + 10)

def oneLeft : Program LeftSignature Nat :=
  Program.perform (S := LeftSignature) .tick

def twoLeft : Program LeftSignature (Nat × Nat) := do
  let first ← Program.perform (S := LeftSignature) .tick
  let second ← Program.perform (S := LeftSignature) .tick
  pure (first, second)

def translatedLeft : Handler LeftSignature (Program RightSignature) where
  handle
    | .tick => Program.perform (S := RightSignature) .jump

-- Constructor and interpreter equations, not sampled host behavior.
example :
    Program.bind (Program.perform (S := LeftSignature) .tick)
        (fun (answer : Nat) => Program.pure (answer + 1))
      = Program.vis (signature := LeftSignature) .tick
          (fun (answer : Nat) => Program.pure (answer + 1)) :=
  Program.perform_bind _ _

example : interpret leftHandler oneLeft 0 = (0, 1) := by
  rfl

example : interpret leftHandler twoLeft 0 = ((0, 1), 2) := by
  rfl

example :
    interpret (leftHandler.sum rightHandler)
        (Program.inl (T := RightSignature) oneLeft) 0
      = interpret leftHandler oneLeft 0 := by
  rw [interpret_inl]

-- Concrete mutation for E4-ALG-CE-001. It typechecks only because both
-- operations answer Nat, and it is observably distinct on each arm.
def swappedSum : Handler (LeftSignature.sum RightSignature) CounterM where
  handle
    | .inl .tick => rightHandler.handle .jump
    | .inr .jump => leftHandler.handle .tick

example :
    -- Observe the concrete state component. The dependent answer type is
    -- intentionally opaque outside `LeftSignature` and need not expose a
    -- `DecidableEq` instance for this mutation to be executable.
    (swappedSum.handle (.inl .tick) 0).2 ≠
      ((leftHandler.sum rightHandler).handle (.inl .tick) 0).2 := by
  decide

example :
    (swappedSum.handle (.inr .jump) 0).2 ≠
      ((leftHandler.sum rightHandler).handle (.inr .jump) 0).2 := by
  decide

-- The tower collapse is checked on a nontrivial state-changing handler and
-- also through the general theorem.
example :
    interpret rightHandler (interpret translatedLeft twoLeft) 0
      = interpret (translatedLeft.through rightHandler) twoLeft 0 := by
  exact congrFun (interpret_through translatedLeft rightHandler twoLeft) 0

section LawShapes

variable {S T U : Signature.{uOp, uAns}}
variable {A B C : Type uAns}
variable {M : Type uAns → Type v}
variable [Monad M] [LawfulMonad M]
variable (handler : Handler S M)
variable (p : Program S A)
variable (f : A → Program S B)
variable (g : B → Program S C)

example : p.bind Program.pure = p := Program.bind_pure_right p

example : (p.bind f).bind g = p.bind (fun a => (f a).bind g) :=
  Program.bind_assoc p f g

example :
    interpret handler (p.bind f)
      = interpret handler p >>= fun a => interpret handler (f a) :=
  interpret_bind handler p f

example : IsMonadMorphism S (fun {_A} program => interpret handler program) :=
  interpret_isMonadMorphism handler

end LawShapes

/-! E4-ALG-CE-005: the old split-universe shape must not elaborate. -/

def SmallSignature : Signature.{0, 0} where
  Op := Unit
  Answer := fun _ => Unit

/--
error: Application type mismatch
-/
#guard_msgs(error, substring := true) in
#check (Program SmallSignature Type)

end Effect4Test.Algebra.ExtractionContract
