module

/-!
# Data.Located — a reason at a site

A judgment refuses with a **reason** in its own alphabet, at a **site** in its own address
space. `Located Site Reason` is that pair. A program's refusal is located at a program address
(`TypeRefusal`, `Program/Typing/Blame.lean`); another judgment names its own site and its own
reasons. Each judgment keeps its own reason alphabet and its own law that a refusal is absent
exactly when the judgment holds (`programRefusal_none_iff`, `Program/CheckedTyping.lean`). No
record of a generic judgment is shared: the owner's ruling 2 of 2026-10-18.

`mapSite` moves a refusal to another site and keeps its reason. `under` is the one prefix rule
at a call boundary: a refusal at address `q` inside a part placed at address `p` is located at
`p ++ q`. The source feed (`SourceSession.feed`), the certified checker's placement of a part
(`Check.Internal.place`) and the checker's rebase (`TypeRefusal.rebase`) all relocate by it.

Placement of `mapSite_comp`: concept `initial-algebras-folds`, the property that a path is an
inherited attribute which only locates refusals (claim `checker-base-natural`, requirement R14).
Its consumer is the layer relocation of the module check (`mapError_layer_rebase`,
`Laws/Program/CheckAgreement.lean`). It says nothing of a reason's correctness.
-/

@[expose] public section

namespace Effect4

/-- **A located refusal**: a reason, and the site it is located at. -/
structure Located (Site Reason : Type) where
  /-- where the judgment refuses -/
  site : Site
  /-- why it refuses, in the judgment's own alphabet -/
  reason : Reason
deriving DecidableEq

namespace Located

/-- Move a refusal to another site; its reason stays. -/
def mapSite {P Q R : Type} (f : P → Q) (r : Located P R) : Located Q R := ⟨f r.site, r.reason⟩

/-- **Two moves are one move**: moving by `f`, then by `g`, is moving by `g ∘ f`. -/
theorem mapSite_comp {P Q S R : Type} (f : P → Q) (g : Q → S) (r : Located P R) :
    mapSite g (mapSite f r) = mapSite (g ∘ f) r := rfl

/-- **The prefix rule** at a call boundary: a refusal at address `q` inside a part placed at `p`
is located at `p ++ q`. -/
def under {R : Type} (p : List Nat) (r : Located (List Nat) R) : Located (List Nat) R :=
  mapSite (p ++ ·) r

end Located

end Effect4
