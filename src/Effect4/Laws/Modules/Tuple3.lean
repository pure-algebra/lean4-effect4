import Effect4.Modules.Step
import Effect4.Laws.Modules.Reading
import Effect4.Laws.Modules.Checking

/-!
# Flat triple step helpers

Placement: helpers of step-language-sound (translation-simulation, R10) and
step-language-typed (store-typing, R4), under the module gaps plan.
The consumers are Step.tuple3 and Queue.takeStep agreement and typing.
The carrier uses three required tuple columns and a terminal unit.
The image is flat. The checked Modeled domain still refuses tuple types.
These helpers establish no membership, allocation, or host behavior.
-/

set_option autoImplicit false

namespace Effect4.Modules
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Store

/-- The three-column carrier encodes exactly the native triple's flat value. -/
theorem tuple3_image (L : Leaves) (a b c : Ty)
    (x : CarrierAt L a) (y : CarrierAt L b) (z : CarrierAt L c) :
    (imageAt L (.tuple [a, b, c])).toVal (x, (y, (z, ()))) =
      Val.tuple [(imageAt L a).toVal x, (imageAt L b).toVal y, (imageAt L c).toVal z] := rfl

/-- The triple term reads its carrier image, using the existing native reading rule. -/
theorem reads_tuple3_image (L : Leaves) (a b c : Ty)
    (x : CarrierAt L a) (y : CarrierAt L b) (z : CarrierAt L c)
    {sx sy sz : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (hx : Reads sx env path vals ((imageAt L a).toVal x))
    (hy : Reads sy env path vals ((imageAt L b).toVal y))
    (hz : Reads sz env path vals ((imageAt L c).toVal z)) :
    Reads (tuple [sx, sy, sz]) env path vals
      ((imageAt L (.tuple [a, b, c])).toVal (x, (y, (z, ())))) :=
  reads_tuple3 hx hy hz

/-- Triple evaluation uses the same required-column carrier as its image. -/
theorem Step.eval_tuple3 {L : Leaves} {Γ : List Ty} {a b c : Ty}
    (x : Step Γ a) (y : Step Γ b) (z : Step Γ c) (vs : Inputs L Γ) :
    (Step.tuple3 x y z).eval L vs = (x.eval L vs, (y.eval L vs, (z.eval L vs, ()))) := rfl

end Effect4.Modules
