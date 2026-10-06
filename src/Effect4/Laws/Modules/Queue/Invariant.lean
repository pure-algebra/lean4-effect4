import Effect4.Laws.Modules.Queue.Profile
import Effect4.Laws.Modules.Queue.Capacity
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# The Queue model's run invariant on the first profile (decisions rows 219, 233, 255 and 275)

`FirstRunInv` is the first profile with the three properties of the state and the run's two
flags. `first_step_inv`, the step law, is a planned goal here: one step of the model
(`src/Effect4/Laws/Modules/Queue/Model.lean`) by a first operation keeps `FirstRunInv`, from
every run that holds it. No term, no cell and no machine occurs in this file.

Placement. Concept `reactive-scheduling`: preservation of an explicit state invariant.
Requirement R12, as the model's half of the proposed claims `wait-registration-no-gap` and
`waiting-request-obligation-preserved`. Consumer: the run-level law of the Queue's wrapper
(decisions row 275, point 2). Reach: the model's `step` at `Fault.none`, for each first operation
(`firstOp`) whose request keeps `Requested`, from every run of the invariant. The statement
establishes nothing about a program or the machine, no delivery of a signal, no liveness and no
fairness. `signalled` records that a step named a request, not that the request ran again.

The invariant is Codex's, from its review of the brief:
`docs/research/2026-10-05-codex-foundation-packet/implementation-audit/heartbeat-1336-qinv-pool-maskpop/next/review.md`.
A flag is a run's history, and `FirstProfile` leaves the buffer free. So no part of the invariant
gives another. The design is `docs/research/2026-10-06-seat-QINV-design.md`.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

/-! ## The invariant -/

/-- **The run invariant of the first profile.** The state is of the profile. It has the three
properties that the flag `ok` reads: `within`, `tidy`, and `quiet` at the run's own `signalled`.
Both flags of the run hold. -/
structure FirstRunInv (r : Run) : Prop where
  profile : FirstProfile r.s
  within : within r.s = true
  tidy : tidy r.s = true
  quiet : quiet r.s r.signalled = true
  ok : r.ok = true
  named : r.named = true

/-- The invariant decides, as the conjunction of its six parts. -/
instance (r : Run) : Decidable (FirstRunInv r) :=
  decidable_of_iff
    (FirstProfile r.s ∧ within r.s = true ∧ tidy r.s = true ∧ quiet r.s r.signalled = true ∧
      r.ok = true ∧ r.named = true)
    ⟨fun ⟨profile, within, tidy, quiet, ok, named⟩ => ⟨profile, within, tidy, quiet, ok, named⟩,
      fun h => ⟨h.profile, h.within, h.tidy, h.quiet, h.ok, h.named⟩⟩

/-! ## The step law -/

/-- **One step of a first operation keeps the run invariant.** From every run of the invariant,
the model's step by a first operation whose request keeps `Requested` leaves a run of the
invariant. So the step keeps both flags. After it no taker stands ready without a signal. Each
request that waited still waits, is the step's own, or is named by a signal.

It is the model's half of `wait-registration-no-gap` and of
`waiting-request-obligation-preserved`. Consumer: the run law over a list of operations, and
then the run-level law of the Queue's wrapper. The statement is of the model alone: no program,
no delivery of a signal, no liveness and no fairness. -/
@[semantics "reactive-scheduling" (requirement := R12)]
proof_goal first_step_inv (r : Run) (op : Op) (h : FirstRunInv r)
    (first : firstOp op = true) (requested : Requested r.s op) :
    FirstRunInv (step .none r op)

end Effect4.Queue.Model
