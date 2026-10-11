import Effect4.Api

/-!
# Source identities in finalization trace events

Concept: scope-lifetime-finalization, R11, at most once per registration counted by identity.
These classifiers serve the Workers and QueueWorkers release-accounting assertions.
They read actual acquisition paths in the compiled names, on every fiber.
They introduce no execution representation or preservation claim.
They establish neither source admission, control linearity nor finalization progress.
-/

set_option autoImplicit false

namespace Effect4.Program.ReleaseTrace

open Effect4 Effect4.Machine

abbrev Event := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- `resolve.acquired` pushes this frame before registering the acquisition's foreign release. -/
def registeredAt (q : List Nat) : Event → Bool
  | .frame _ (.pushed (.onSuccess _ (.afterScopeAdd _ (.foreign c)))) => c.path == q
  | _ => false

/-- `suspendBodyAt.foreign` pushes this frame when the same acquisition's release starts. -/
def releaseAt (q : List Nat) : Event → Bool
  | .frame _ (.pushed (.onSuccess _ (.releaseUnder p _ _))) => p.path == q
  | _ => false

end Effect4.Program.ReleaseTrace
