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

/-! Composition and kind conversion carry their laws. -/

end Test.Data.OpticContract
