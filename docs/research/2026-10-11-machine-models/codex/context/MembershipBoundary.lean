import Effect4.Laws.Program.Typed.Membership

/-! Readers and controls for strong typed-context membership.
The promised service carrier must remain declared in the world.
These controls serve the context reader and provider migration.
-/
namespace Test.ContextMembershipBoundary
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def keys : Effect4.Row ServiceKey := Effect4.Machine.Env.Requirement.single key

def forgetServices (w : Typed.World) : Typed.World := { w with serviceTy := fun _ => none }

-- The unchanged existential inhabitance theorem supplies a declared context member.
example : ∃ (w : Typed.World) (v : Val), Fits w v (.contextOf keys) :=
  (inhabited_iff_fits (.contextOf keys)).mp rfl

-- A missing promised service declaration prevents strong membership at every value.
example (w : Typed.World) (missing : w.serviceTy key = none) (v : Val) :
    ¬ Fits w v (.contextOf keys) := by
  intro fit
  obtain ⟨ctx, _, _, _, _, promised⟩ := fit
  obtain ⟨carrier, _, declared, _, _⟩ := promised key (by decide)
  rw [missing] at declared
  cases declared

-- The former backward-only declaration premise allows every service to disappear.
example (w : Typed.World) :
    ∀ k carrier, (forgetServices w).serviceTy k = some carrier →
      w.serviceTy k = some carrier := by
  intro k carrier absent
  cases absent

-- That backward-only premise cannot preserve a nonempty promised context row.
example (w : Typed.World) (v : Val) : ¬ Fits (forgetServices w) v (.contextOf keys) := by
  intro fit
  obtain ⟨ctx, _, _, _, _, promised⟩ := fit
  obtain ⟨carrier, _, declared, _, _⟩ := promised key (by decide)
  cases declared

-- The live native getter can return an empty context, which promises no nonempty row.
example (w : Typed.World) :
    ¬ Fits w (Val.context (.withServices Env.Context.empty)) (.contextOf keys) := by
  intro fit
  obtain ⟨ctx, decoded, _, _, _, promised⟩ := fit
  have same : ctx = Ctx.withServices Env.Context.empty :=
    (Option.some.inj ((Val.context?_context _).symm.trans decoded)).symm
  cases same
  obtain ⟨_, value, _, present, _⟩ := promised key (by decide)
  change Env.Context.empty.getV key = some value at present
  cases present
end Test.ContextMembershipBoundary
