import Effect4.Schema.Identity
import Effect4.Laws.Step.Reading

/-!
# Laws.Schema.Identity — deferred comparison reads its key comparison

Concept: Translation Simulation. Claim: helper of `step-language-sound`, requirement R10.
Reach: an interpretation with `DeferredIdentity`, and input readings of its deferred images.
The atom law serves the reading law; the reading law serves Step's deferred comparison arm.
Module removal passes then use their existing table-injectivity premise for request numbers.
Neither law establishes allocation validity, membership, progress, or target execution.
This placement is the deferred comparison row of the module gaps plan.
-/

set_option autoImplicit false

namespace Effect4.Schema.DeferredIdentity
open Effect4.Store Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Modules Effect4.Schema.Model

variable {L : Leaves}

/-- Helper of `step-language-sound`: the native atom compares the interpretation's keys. -/
theorem atom_same (I : DeferredIdentity L) (a b : L.deferred.1) :
    nativeAtom "sameHandle" [L.deferred.2.toVal a, L.deferred.2.toVal b] =
      some (Store.Val.bool (I.equal a b)) := by
  rw [I.image_eq a, I.image_eq b]
  exact atom_sameHandle (I.key a) (I.key b)

/-- Helper of `step-language-sound`: the comparison term reads the key comparison.
The consumer is Step's deferred comparison arm, then the module removal laws. -/
theorem reads_same (I : DeferredIdentity L) {a b : TermSrc} {x y : L.deferred.1}
    {env : Env} {path : List Nat} {vals : List Store.Val}
    (ha : Reads a env path vals (L.deferred.2.toVal x))
    (hb : Reads b env path vals (L.deferred.2.toVal y)) :
    Reads (same a b) env path vals (Store.Val.bool (I.equal x y)) :=
  reads_app (.cons ha (.cons hb .nil)) (I.atom_same x y)

/-- Helper of `step-language-sound`: the total candidate agrees with key comparison
only under the interpretation capability. -/
theorem equal_eq (I : DeferredIdentity L) (a b : L.deferred.1) :
    I.equal a b = Model.deferredEqual L a b := by
  unfold Model.deferredEqual
  rw [I.image_eq a, I.image_eq b]
  rfl

/-- Helper of `step-language-sound`: the native atom reads the total candidate
on the capability's fragment. -/
theorem atom_deferredEqual (I : DeferredIdentity L) (a b : L.deferred.1) :
    nativeAtom "sameHandle" [L.deferred.2.toVal a, L.deferred.2.toVal b] =
      some (Store.Val.bool (Model.deferredEqual L a b)) := by
  rw [← I.equal_eq a b]
  exact I.atom_same a b

/-- Helper of `step-language-sound`: the term reads the total candidate
on the capability's fragment. The consumer is Step's deferred comparison arm. -/
theorem reads_deferredEqual (I : DeferredIdentity L) {a b : TermSrc} {x y : L.deferred.1}
    {env : Env} {path : List Nat} {vals : List Store.Val}
    (ha : Reads a env path vals (L.deferred.2.toVal x))
    (hb : Reads b env path vals (L.deferred.2.toVal y)) :
    Reads (same a b) env path vals (Store.Val.bool (Model.deferredEqual L x y)) := by
  rw [← I.equal_eq x y]
  exact I.reads_same ha hb

end Effect4.Schema.DeferredIdentity
