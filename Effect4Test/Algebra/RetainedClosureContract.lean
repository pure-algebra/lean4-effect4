/-
Contract packet: `test/contracts/algebra-retained-closure.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until every retained algebra declaration has a native Effect4 API.
-/

import Effect4.Algebra.Laws
import Effect4.Algebra.Sum
import Effect4.Algebra.Universal

namespace Effect4Test.Algebra.RetainedClosureContract

open Effect4

universe uS uT uAns v

section InterpreterClosure

#check (@Program.eq_of_all_interpretations :
  forall {S : Signature.{uS, uAns}} {A : Type uAns}
      {left right : Program S A},
    (forall (M : Type uAns -> Type (max uS uAns))
        [Monad M] [LawfulMonad M] (handler : Handler S M),
      interpret handler left = interpret handler right) ->
    left = right)

#check (@interpret_vis :
  forall {M : Type uAns -> Type v} {S : Signature.{uS, uAns}}
      {A : Type uAns} [Monad M]
      (handler : Handler S M) (operation : S.Op)
      (next : S.Answer operation -> Program S A),
    interpret handler (Program.vis operation next) =
      handler.handle operation >>= fun answer => interpret handler (next answer))

#check (@interpret_perform_of_rightUnit :
  forall {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M],
    RightUnit M -> forall (handler : Handler S M) (operation : S.Op),
      interpret handler (Program.perform operation) = handler.handle operation)

#check (@interpret_isMonadMorphism_of_equations :
  forall {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M],
    LeftUnit M -> BindAssoc M -> forall handler : Handler S M,
      IsMonadMorphism S (fun {_A} program => interpret handler program))

#check (@interpret_inhabits_the_pin :
  forall {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M],
    LeftUnit M -> BindAssoc M -> RightUnit M ->
      (forall handler : Handler S M,
        IsMonadMorphism S (fun {_A} program => interpret handler program)) /\
      forall (handler : Handler S M) (operation : S.Op),
        interpret handler (Program.perform operation) = handler.handle operation)

end InterpreterClosure

section ModelMorphismClosure

variable {S : Signature.{uS, uAns}}
variable {M : Type uAns -> Type v}

#check (@ModelMorphism :
  (S : Signature.{uS, uAns}) -> (M : Type uAns -> Type v) ->
    [Monad M] -> Type (max (max (uAns + 1) uS) v))

#check (@ModelMorphism.mk :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M]
      (map : (A : Type uAns) -> Program S A -> M A),
    IsMonadMorphism S (fun {A} program => map A program) ->
    ModelMorphism S M)

#check (@ModelMorphism.map :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M],
    ModelMorphism S M -> (A : Type uAns) -> Program S A -> M A)

#check (@ModelMorphism.ofIsMonadMorphism :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M]
      (map : {A : Type uAns} -> Program S A -> M A),
    IsMonadMorphism S map -> ModelMorphism S M)

#check (@ModelMorphism.toIsMonadMorphism :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M]
      (morphism : ModelMorphism S M),
    IsMonadMorphism S
      (fun {A} program => morphism.map A program))

#check (@ModelMorphism.ext :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M]
      {left right : ModelMorphism S M},
    (forall (A : Type uAns) (program : Program S A),
      left.map A program = right.map A program) ->
    left = right)

#check (@ModelMorphism.ofIsMonadMorphism_map :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M]
      (map : {A : Type uAns} -> Program S A -> M A)
      (laws : IsMonadMorphism S map) {A : Type uAns}
      (program : Program S A),
    (ModelMorphism.ofIsMonadMorphism map laws).map A program = map program)

#check (@ModelMorphism.ofIsMonadMorphism_toIsMonadMorphism :
  forall {S : Signature.{uS, uAns}} {M : Type uAns -> Type v} [Monad M]
      (morphism : ModelMorphism S M),
    ModelMorphism.ofIsMonadMorphism
        (fun {A} program => morphism.map A program)
        morphism.toIsMonadMorphism =
      morphism)

#check (@program_is_initial_in_models_eq :
  forall {M : Type uAns -> Type v} {S : Signature.{uS, uAns}} [Monad M],
    LeftUnit M -> BindAssoc M -> RightUnit M ->
    forall handler : Handler S M,
      exists morphism : ModelMorphism S M,
        (forall operation : S.Op,
          morphism.map _ (Program.perform operation) = handler.handle operation) /\
        forall other : ModelMorphism S M,
          (forall operation : S.Op,
            other.map _ (Program.perform operation) = handler.handle operation) ->
          other = morphism)

end ModelMorphismClosure

section InjectionClosure

#check (@Program.inl_one_target_iff :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program S A -> Program (S.sum T) A)
      {A : Type uAns} (program : Program S A),
    (interpret
        ((leftInjectionHandler (S := S) (T := T)).sum
          (rightInjectionHandler (S := S) (T := T)))
        (candidate program) =
      interpret (leftInjectionHandler (S := S) (T := T)) program) <->
    candidate program = Program.inl program)

#check (@Program.inr_one_target_iff :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program T A -> Program (S.sum T) A)
      {A : Type uAns} (program : Program T A),
    (interpret
        ((leftInjectionHandler (S := S) (T := T)).sum
          (rightInjectionHandler (S := S) (T := T)))
        (candidate program) =
      interpret (rightInjectionHandler (S := S) (T := T)) program) <->
    candidate program = Program.inr program)

#check (@Program.inl_unique_one_target :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program S A -> Program (S.sum T) A),
    (forall {A : Type uAns} (program : Program S A),
      interpret
          ((leftInjectionHandler (S := S) (T := T)).sum
            (rightInjectionHandler (S := S) (T := T)))
          (candidate program) =
        interpret (leftInjectionHandler (S := S) (T := T)) program) ->
    forall {A : Type uAns} (program : Program S A),
      candidate program = Program.inl program)

#check (@Program.inr_unique_one_target :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program T A -> Program (S.sum T) A),
    (forall {A : Type uAns} (program : Program T A),
      interpret
          ((leftInjectionHandler (S := S) (T := T)).sum
            (rightInjectionHandler (S := S) (T := T)))
          (candidate program) =
        interpret (rightInjectionHandler (S := S) (T := T)) program) ->
    forall {A : Type uAns} (program : Program T A),
      candidate program = Program.inr program)

#check (@Program.inl_all_models_iff :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program S A -> Program (S.sum T) A)
      {A : Type uAns} (program : Program S A),
    (forall (M : Type uAns -> Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M),
      interpret (left.sum right) (candidate program) = interpret left program) <->
    candidate program = Program.inl program)

#check (@Program.inr_all_models_iff :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program T A -> Program (S.sum T) A)
      {A : Type uAns} (program : Program T A),
    (forall (M : Type uAns -> Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M),
      interpret (left.sum right) (candidate program) = interpret right program) <->
    candidate program = Program.inr program)

#check (@Program.inl_unique_all_models :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program S A -> Program (S.sum T) A),
    (forall (M : Type uAns -> Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M)
        {A : Type uAns} (program : Program S A),
      interpret (left.sum right) (candidate program) = interpret left program) ->
    forall {A : Type uAns} (program : Program S A),
      candidate program = Program.inl program)

#check (@Program.inr_unique_all_models :
  forall {S : Signature.{uS, uAns}} {T : Signature.{uT, uAns}}
      (candidate : {A : Type uAns} -> Program T A -> Program (S.sum T) A),
    (forall (M : Type uAns -> Type (max (max uS uT) uAns))
        [Monad M] [LawfulMonad M]
        (left : Handler S M) (right : Handler T M)
        {A : Type uAns} (program : Program T A),
      interpret (left.sum right) (candidate program) = interpret right program) ->
    forall {A : Type uAns} (program : Program T A),
      candidate program = Program.inr program)

end InjectionClosure

end Effect4Test.Algebra.RetainedClosureContract
