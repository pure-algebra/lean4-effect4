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

universe uOp uAns uS uT uU v

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

#check (@Signature.mk :
  (Op : Type uOp) → (Op → Type uAns) → Signature.{uOp, uAns})

#check (@Signature.sum :
  Signature.{uS, uAns} → Signature.{uT, uAns} →
    Signature.{max uS uT, uAns})

#check (@Program.pure :
  {S : Signature.{uS, uAns}} → {A : Type uAns} → A → Program S A)

#check (@Program.vis :
  {S : Signature.{uS, uAns}} → {A : Type uAns} →
    (operation : S.Op) →
      (S.Answer operation → Program S A) → Program S A)

#check (@Program.bind :
  {S : Signature.{uS, uAns}} → {A B : Type uAns} →
    Program S A → (A → Program S B) → Program S B)

#check (@Program.perform :
  {S : Signature.{uS, uAns}} →
    (operation : S.Op) → Program S (S.Answer operation))

#check (@Program.inl :
  {S : Signature.{uS, uAns}} → {A : Type uAns} →
    {T : Signature.{uT, uAns}} →
      Program S A → Program (S.sum T) A)

#check (@Program.inr :
  {T : Signature.{uT, uAns}} → {A : Type uAns} →
    {S : Signature.{uS, uAns}} →
      Program T A → Program (S.sum T) A)

#check (@Handler.mk :
  {S : Signature.{uS, uAns}} → {M : Type uAns → Type v} →
    ((operation : S.Op) → M (S.Answer operation)) → Handler S M)

#check (@Handler.ext :
  ∀ {S : Signature.{uS, uAns}} {M : Type uAns → Type v}
      {left right : Handler S M},
    (∀ operation : S.Op,
      left.handle operation = right.handle operation) → left = right)

#check (@interpret :
  {M : Type uAns → Type v} → {S : Signature.{uS, uAns}} →
    {A : Type uAns} → [Monad M] →
      Handler S M → Program S A → M A)

#check (@Handler.sum :
  {S : Signature.{uS, uAns}} → {M : Type uAns → Type v} →
    {T : Signature.{uT, uAns}} →
      Handler S M → Handler T M → Handler (S.sum T) M)

#check (@LeftUnit :
  (M : Type uAns → Type v) → [Monad M] → Prop)

#check (@RightUnit :
  (M : Type uAns → Type v) → [Monad M] → Prop)

#check (@BindAssoc :
  (M : Type uAns → Type v) → [Monad M] → Prop)

example (M : Type uAns → Type v) [Monad M] :
    LeftUnit M =
      (∀ {A B : Type uAns} (value : A) (next : A → M B),
        (pure value : M A) >>= next = next value) :=
  rfl

example (M : Type uAns → Type v) [Monad M] :
    RightUnit M =
      (∀ {A : Type uAns} (value : M A),
        value >>= (fun result => (pure result : M A)) = value) :=
  rfl

example (M : Type uAns → Type v) [Monad M] :
    BindAssoc M =
      (∀ {A B C : Type uAns} (value : M A)
          (next : A → M B) (last : B → M C),
        (value >>= next) >>= last =
          value >>= fun result => next result >>= last) :=
  rfl

#check (@identityHandler :
  {S : Signature.{uS, uAns}} → Handler S (Program S))

#check (@Handler.through :
  {M : Type uAns → Type v} → {S : Signature.{uS, uAns}} →
    {T : Signature.{uT, uAns}} → [Monad M] →
      Handler S (Program T) → Handler T M → Handler S M)

#synth Monad (Program S)
#synth LawfulMonad (Program S)

#check (@Program.bind_pure_right :
  ∀ {S : Signature.{uS, uAns}} {A : Type uAns}
      (program : Program S A),
    program.bind Program.pure = program)

#check (@Program.bind_assoc :
  ∀ {S : Signature.{uS, uAns}} {A B C : Type uAns}
      (program : Program S A) (next : A → Program S B)
      (last : B → Program S C),
    (program.bind next).bind last =
      program.bind fun value => (next value).bind last)

#check (@Program.perform_bind :
  ∀ {S : Signature.{uS, uAns}} {B : Type uAns}
      (operation : S.Op)
      (next : S.Answer operation → Program S B),
    (Program.perform operation).bind next = Program.vis operation next)

#check (@interpret_pure :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {A : Type uAns} [Monad M]
      (handler : Handler S M) (value : A),
    interpret handler (Program.pure value) = pure value)

#check (@interpret_perform :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      [Monad M] [LawfulMonad M]
      (handler : Handler S M) (operation : S.Op),
    interpret handler (Program.perform operation) = handler.handle operation)

#check (@interpret_bind :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {A B : Type uAns} [Monad M] [LawfulMonad M]
      (handler : Handler S M) (program : Program S A)
      (next : A → Program S B),
    interpret handler (program.bind next) =
      interpret handler program >>= fun value => interpret handler (next value))

#check (@interpret_bind_of_equations :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {A B : Type uAns} [Monad M],
    LeftUnit M → BindAssoc M →
      ∀ (handler : Handler S M) (program : Program S A)
          (next : A → Program S B),
        interpret handler (program.bind next) =
          interpret handler program >>=
            fun value => interpret handler (next value))

#check (@interpret_identity :
  ∀ {S : Signature.{uS, uAns}} {A : Type uAns}
      (program : Program S A),
    interpret identityHandler program = program)

#check (@Handler.sum_handle_inl :
  ∀ {S : Signature.{uS, uAns}} {M : Type uAns → Type v}
      {T : Signature.{uT, uAns}} (left : Handler S M)
      (right : Handler T M) (operation : S.Op),
    (left.sum right).handle (.inl operation) = left.handle operation)

#check (@Handler.sum_handle_inr :
  ∀ {S : Signature.{uS, uAns}} {M : Type uAns → Type v}
      {T : Signature.{uT, uAns}} (left : Handler S M)
      (right : Handler T M) (operation : T.Op),
    (left.sum right).handle (.inr operation) = right.handle operation)

#check (@Handler.sum_unique :
  ∀ {S : Signature.{uS, uAns}} {M : Type uAns → Type v}
      {T : Signature.{uT, uAns}} (left : Handler S M)
      (right : Handler T M) (candidate : Handler (S.sum T) M),
    (∀ operation : S.Op,
      candidate.handle (.inl operation) = left.handle operation) →
    (∀ operation : T.Op,
      candidate.handle (.inr operation) = right.handle operation) →
    candidate = left.sum right)

#check (@interpret_inl :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {T : Signature.{uT, uAns}} {A : Type uAns} [Monad M]
      (left : Handler S M) (right : Handler T M)
      (program : Program S A),
    interpret (left.sum right) (Program.inl program) = interpret left program)

#check (@interpret_inr :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {T : Signature.{uT, uAns}} {A : Type uAns} [Monad M]
      (left : Handler S M) (right : Handler T M)
      (program : Program T A),
    interpret (left.sum right) (Program.inr program) = interpret right program)

#check (@Program.inl_pure :
  ∀ {A : Type uAns} {T : Signature.{uT, uAns}}
      {S : Signature.{uS, uAns}} (value : A),
    Program.inl (T := T) (Program.pure value : Program S A) =
      Program.pure value)

#check (@Program.inr_pure :
  ∀ {A : Type uAns} {S : Signature.{uS, uAns}}
      {T : Signature.{uT, uAns}} (value : A),
    Program.inr (S := S) (Program.pure value : Program T A) =
      Program.pure value)

#check (@Program.inl_bind :
  ∀ {S : Signature.{uS, uAns}} {A B : Type uAns}
      {T : Signature.{uT, uAns}} (program : Program S A)
      (next : A → Program S B),
    Program.inl (T := T) (program.bind next) =
      (Program.inl (T := T) program).bind
        (fun value => Program.inl (T := T) (next value)))

#check (@Program.inr_bind :
  ∀ {T : Signature.{uT, uAns}} {A B : Type uAns}
      {S : Signature.{uS, uAns}} (program : Program T A)
      (next : A → Program T B),
    Program.inr (S := S) (program.bind next) =
      (Program.inr (S := S) program).bind
        (fun value => Program.inr (S := S) (next value)))

#check (@Program.inl_injective :
  ∀ {S : Signature.{uS, uAns}} {A : Type uAns}
      {T : Signature.{uT, uAns}},
    Function.Injective (Program.inl (S := S) (T := T) (A := A)))

#check (@Program.inr_injective :
  ∀ {T : Signature.{uT, uAns}} {A : Type uAns}
      {S : Signature.{uS, uAns}},
    Function.Injective (Program.inr (S := S) (T := T) (A := A)))

#check (@leftInjectionHandler :
  ∀ {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}},
    Handler S (Program (S.sum T)))

#check (@rightInjectionHandler :
  ∀ {T : Signature.{uT, uAns}} {S : Signature.{uS, uAns}},
    Handler T (Program (S.sum T)))

#check (@Program.inl_unique :
  ∀ {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      {A : Type uAns}
      (candidate : {A : Type uAns} → Program S A → Program (S.sum T) A),
    (∀ {A : Type uAns} (program : Program S A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret leftInjectionHandler program) →
    ∀ program : Program S A, candidate program = Program.inl program)

#check (@Program.inr_unique :
  ∀ {T : Signature.{uT, uAns}} {S : Signature.{uS, uAns}}
      {A : Type uAns}
      (candidate : {A : Type uAns} → Program T A → Program (S.sum T) A),
    (∀ {A : Type uAns} (program : Program T A),
      interpret (leftInjectionHandler.sum rightInjectionHandler)
          (candidate program) =
        interpret rightInjectionHandler program) →
    ∀ program : Program T A, candidate program = Program.inr program)

#check (@IsMonadMorphism :
  (S : Signature.{uS, uAns}) → {M : Type uAns → Type v} →
    [Monad M] → ({A : Type uAns} → Program S A → M A) → Prop)

#check (@IsMonadMorphism.mk :
  ∀ (S : Signature.{uS, uAns}) {M : Type uAns → Type v} [Monad M]
      (map : {A : Type uAns} → Program S A → M A),
    (∀ {A : Type uAns} (value : A),
      map (Program.pure value) = pure value) →
    (∀ {A B : Type uAns} (program : Program S A)
        (next : A → Program S B),
      map (program.bind next) = map program >>= fun value => map (next value)) →
    IsMonadMorphism S map)

#check (@interpret_isMonadMorphism :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      [Monad M] [LawfulMonad M] (handler : Handler S M),
    IsMonadMorphism S (fun {_A} program => interpret handler program))

#check (@interpret_of_isMonadMorphism :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {A : Type uAns} [Monad M]
      (map : {A : Type uAns} → Program S A → M A),
    IsMonadMorphism S map →
    ∀ program : Program S A,
      map program =
        interpret (M := M)
          ⟨fun operation => map (Program.perform operation)⟩ program)

#check (@exists_handler_of_isMonadMorphism :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}} [Monad M]
      (map : {A : Type uAns} → Program S A → M A),
    IsMonadMorphism S map →
      ∃ handler : Handler S M,
        ∀ {A : Type uAns} (program : Program S A),
          map program = interpret handler program)

#check (@handler_eq_of_interpret_operation_eq :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}} [Monad M],
    RightUnit M →
    ∀ {left right : Handler S M},
      (∀ operation : S.Op,
        interpret left (Program.perform operation) =
          interpret right (Program.perform operation)) →
      left = right)

#check (@handler_eq_of_interpret_eq :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}} [Monad M],
    RightUnit M →
    ∀ {left right : Handler S M},
      (∀ {A : Type uAns} (program : Program S A),
        interpret left program = interpret right program) →
      left = right)

#check (@program_is_free :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}} [Monad M],
    RightUnit M →
    ∀ (map : {A : Type uAns} → Program S A → M A),
      IsMonadMorphism S map →
      ∃ handler : Handler S M,
        (∀ {A : Type uAns} (program : Program S A),
          map program = interpret handler program) ∧
        ∀ other : Handler S M,
          (∀ {A : Type uAns} (program : Program S A),
            map program = interpret other program) →
          other = handler)

#check (@program_is_initial_in_models :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}} [Monad M],
    LeftUnit M → BindAssoc M → RightUnit M →
    ∀ handler : Handler S M,
      ∃ map : {A : Type uAns} → Program S A → M A,
        (IsMonadMorphism S map ∧
          ∀ operation : S.Op,
            map (Program.perform operation) = handler.handle operation) ∧
        ∀ other : {A : Type uAns} → Program S A → M A,
          IsMonadMorphism S other →
          (∀ operation : S.Op,
            other (Program.perform operation) = handler.handle operation) →
          ∀ {A : Type uAns} (program : Program S A),
            other program = map program)

#check (@interpret_pinned :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {A : Type uAns} [Monad M]
      (candidate : Handler S M → {A : Type uAns} → Program S A → M A),
    (∀ handler : Handler S M,
      IsMonadMorphism S (fun {_A} program => candidate handler program)) →
    (∀ (handler : Handler S M) (operation : S.Op),
      candidate handler (Program.perform operation) = handler.handle operation) →
    ∀ (handler : Handler S M) (program : Program S A),
      candidate handler program = interpret handler program)

#check (@interpret_through :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {T : Signature.{uT, uAns}} {A : Type uAns}
      [Monad M] [LawfulMonad M]
      (upper : Handler S (Program T)) (lower : Handler T M)
      (program : Program S A),
    interpret lower (interpret upper program) =
      interpret (upper.through lower) program)

#check (@Handler.through_assoc :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}}
      {T : Signature.{uT, uAns}} {U : Signature.{uU, uAns}} [Monad M],
    LeftUnit M → BindAssoc M →
    ∀ (first : Handler S (Program T))
        (second : Handler T (Program U)) (last : Handler U M),
      (first.through second).through last =
        first.through (second.through last))

#check (@Handler.through_identity_right :
  ∀ {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (handler : Handler S (Program T)),
    handler.through (identityHandler (S := T)) = handler)

#check (@Handler.through_identity_left :
  ∀ {M : Type uAns → Type v} {S : Signature.{uS, uAns}} [Monad M],
    RightUnit M → ∀ handler : Handler S M,
      (identityHandler (S := S)).through handler = handler)

#check (@Handler.through_endomorphism_monoid :
  ∀ {S : Signature.{uS, uAns}}
      (first second third : Handler S (Program S)),
    (first.through second).through third =
        first.through (second.through third) ∧
      first.through identityHandler = first ∧
      identityHandler.through first = first)

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

/-!
E4-ALG-CE-008: `Program` is a well-founded higher-order W-tree, not a
globally finite tree. The root below has a `Nat`-indexed continuation. Each
selected child is a structurally finite spine, while the family contains
infinitely many distinct children with no uniform depth bound.
-/

inductive InfiniteBranchOp where
  | choose

def InfiniteBranchSignature : Signature.{0, 0} where
  Op := InfiniteBranchOp
  Answer := fun _ => Nat

def finiteSpine : Nat → Program InfiniteBranchSignature Unit
  | 0 => .pure ()
  | n + 1 => .vis .choose (fun _ => finiteSpine n)

def unboundedContinuationFamily : Program InfiniteBranchSignature Unit :=
  .vis .choose finiteSpine

def selectedSpineDepth : Program InfiniteBranchSignature Unit → Nat
  | .pure _ => 0
  | .vis .choose next =>
      selectedSpineDepth
        (next (show InfiniteBranchSignature.Answer .choose from (0 : Nat))) + 1

theorem finiteSpine_depth (n : Nat) :
    selectedSpineDepth (finiteSpine n) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [finiteSpine, selectedSpineDepth, ih, InfiniteBranchSignature]

theorem finiteSpine_injective : Function.Injective finiteSpine := by
  intro left right equal
  simpa [finiteSpine_depth] using congrArg selectedSpineDepth equal

example :
    unboundedContinuationFamily =
      Program.vis (signature := InfiniteBranchSignature)
        InfiniteBranchOp.choose finiteSpine :=
  rfl

example : Function.Injective finiteSpine :=
  finiteSpine_injective

example :
    ∀ bound : Nat, ∃ answer : Nat,
      selectedSpineDepth (finiteSpine answer) > bound := by
  intro bound
  exact ⟨bound + 1, by simp [finiteSpine_depth]⟩

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
