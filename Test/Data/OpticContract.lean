/-
Contract packet: `Test/contracts/schema-annotations.contract.md`

Breaker-owned red battery for `DATA-PG-OPTIC`. The builder must make this file
green without editing it.
-/

import Effect4.Data.Optic

namespace Test.Data.OpticContract

open Effect4

universe u v w

/-! The carriers stay universe-polymorphic and purely functional. -/

#check (@Lens.{u, v} : Type u -> Type v -> Type (max u v))
#check (@Lens.get.{u, v} : {S : Type u} -> {A : Type v} -> Lens S A -> S -> A)
#check (@Lens.replace.{u, v} :
  {S : Type u} -> {A : Type v} -> Lens S A -> A -> S -> S)
#check (@Lens.modify.{u, v} :
  {S : Type u} -> {A : Type v} -> Lens S A -> (A -> A) -> S -> S)
#check (@Lens.compose.{u, v, w} :
  {S : Type u} -> {A : Type v} -> {B : Type w} ->
    Lens S A -> Lens A B -> Lens S B)
#check (@Lens.toOptional.{u, v} :
  {S : Type u} -> {A : Type v} -> Lens S A -> Optional S A)

#check (@Optional.{u, v} : Type u -> Type v -> Type (max u v))
#check (@Optional.preview.{u, v} :
  {S : Type u} -> {A : Type v} -> Optional S A -> S -> Option A)
#check (@Optional.replace.{u, v} :
  {S : Type u} -> {A : Type v} -> Optional S A -> A -> S -> S)
#check (@Optional.modify.{u, v} :
  {S : Type u} -> {A : Type v} -> Optional S A -> (A -> A) -> S -> S)
#check (@Optional.compose.{u, v, w} :
  {S : Type u} -> {A : Type v} -> {B : Type w} ->
    Optional S A -> Optional A B -> Optional S B)
#check (@Optional.toTraversal.{u, v} :
  {S : Type u} -> {A : Type v} -> Optional S A -> Traversal S A)

#check (@Traversal.{u, v} : Type u -> Type v -> Type (max u v))
#check (@Traversal.collect.{u, v} :
  {S : Type u} -> {A : Type v} -> Traversal S A -> S -> List A)
#check (@Traversal.modifyAll.{u, v} :
  {S : Type u} -> {A : Type v} -> Traversal S A -> (A -> A) -> S -> S)
#check (@Traversal.compose.{u, v, w} :
  {S : Type u} -> {A : Type v} -> {B : Type w} ->
    Traversal S A -> Traversal A B -> Traversal S B)

/-! Law records expose exactly the reusable lens laws. -/

example {S : Type u} {A : Type v} {optic : Lens S A}
    (law : Lens.Lawful optic) (source : S) (value : A) :
    optic.get (optic.replace value source) = value :=
  law.get_replace source value

example {S : Type u} {A : Type v} {optic : Optional S A}
    (law : Optional.Lawful optic) (source : S) (value : A)
    (absent : optic.preview source = none) :
    optic.replace value source = source :=
  law.replace_absent source value absent

example {S : Type u} {A : Type v} {optic : Traversal S A}
    (law : Traversal.Lawful optic) (source : S) (f : A -> A) :
    optic.collect (optic.modifyAll f source) = (optic.collect source).map f :=
  law.collect_modify source f

example {S : Type u} {A : Type v} {optic : Traversal S A}
    (law : Traversal.Lawful optic) {first second : A -> A}
    (pointwise : forall value, first value = second value) (source : S) :
    optic.modifyAll first source = optic.modifyAll second source :=
  law.modify_congr pointwise source

#check (@Traversal.Lawful.modify_congr.{u, v} :
  forall {S : Type u} {A : Type v} {optic : Traversal S A},
    Traversal.Lawful optic -> forall {first second : A -> A},
      (forall value, first value = second value) -> forall source,
        optic.modifyAll first source = optic.modifyAll second source)

/-! Composition and kind conversion carry their laws. -/

#check (@Lens.Lawful.compose.{u, v, w} :
  {S : Type u} -> {A : Type v} -> {B : Type w} ->
  {outer : Lens S A} -> {inner : Lens A B} ->
  Lens.Lawful outer -> Lens.Lawful inner ->
  Lens.Lawful (outer.compose inner))

#check (@Lens.Lawful.toOptional.{u, v} :
  {S : Type u} -> {A : Type v} -> {optic : Lens S A} ->
  Lens.Lawful optic -> Optional.Lawful optic.toOptional)

#check (@Optional.Lawful.compose.{u, v, w} :
  {S : Type u} -> {A : Type v} -> {B : Type w} ->
  {outer : Optional S A} -> {inner : Optional A B} ->
  Optional.Lawful outer -> Optional.Lawful inner ->
  Optional.Lawful (outer.compose inner))

#check (@Optional.Lawful.toTraversal.{u, v} :
  {S : Type u} -> {A : Type v} -> {optic : Optional S A} ->
  Optional.Lawful optic -> Traversal.Lawful optic.toTraversal)

#check (@Traversal.Lawful.compose.{u, v, w} :
  {S : Type u} -> {A : Type v} -> {B : Type w} ->
  {outer : Traversal S A} -> {inner : Traversal A B} ->
  Traversal.Lawful outer -> Traversal.Lawful inner ->
  Traversal.Lawful (outer.compose inner))

end Test.Data.OpticContract
