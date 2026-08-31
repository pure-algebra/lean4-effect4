import Effects.Conformance.Schema.Homomorphism
import Effects.Replay.Interp

/-!
# CMP-001 — sequential interpretation threads replay state compositionally

HOMOMORPHISM over the reified sequential program, interpreted through the
reducer into Lean's own `EStateM`: the instance's `interp` is the
projection of `interpE` onto the schema's pair shape (`EStateM.Result` IS
that shape — ok-with-state or error-with-state), and the laws are the
monad-morphism theorems. The fail channel is the interpretation halt —
the program's own typed failure, the session's typed rejection, or a leaf
under an already-aborted session; it mirrors what the session boundary
observes and never widens a wrapped method's error union.

The kit runs both branches through a leaf: the fixture history records a
typed failure, the positive program's continuation recovers from it (the
envelope reaches the continuation on both channels), and the failing
program re-raises it.
-/

namespace Effects.Conformance

open Effects.Replay (Prog ReplayState Halt interpE Invocation
  CMP_001_interp_bind)

private abbrev PS := Prog String String String String

private abbrev RS := ReplayState String String String String

/-- Project the built-in carrier's result onto the schema's pair shape. -/
private def toOutcome {α : Type} :
    EStateM.Result (Halt String) RS α → BindOutcome (Halt String) α × RS
  | .ok a s => (.ok a, s)
  | .error e s => (.fail e, s)

private def call : Invocation String String := ⟨"acme/Rates/get", 1, "req-0"⟩

/-- One entry recording a typed failure — both kit branches run through
it. -/
private def start : RS :=
  ⟨⟨.replay, .active, [⟨"acme/Rates/get", 1, "req-0", .failure "err-0"⟩], 0, none⟩,
    rfl⟩

/-- CMP-001: sequential interpretation threads replay state
compositionally across success and typed-failure outcomes. -/
def cmp001 : Homomorphism PS RS (Halt String) where
  id := "CMP-001"
  sentence := "Interpretation respects return and sequential bind across both outcome cases — sequential interpretation threads the replay session state compositionally: a returned value consumes nothing, a nested program continues from exactly the state its prefix reached, and both halting cases — the program's own typed failure and the session's typed rejection — short-circuit carrying the state they stopped at, so the cursor neither resets nor forks across composition; the recorded outcome envelope reaches the leaf continuation on both channels, so recovery fires exactly as it did live."
  pureP := fun a => Prog.pure a
  bindP := fun p k => p.bind k
  interp := fun p s => toOutcome (interpE p s)
  law_pure := fun _ _ => rfl
  law_bind := fun p k s => by
    simp only [CMP_001_interp_bind]
    cases interpE p s <;> rfl
  posState := start
  posOk := Prog.invoke call fun _ => Prog.pure ()
  pos_ok := ⟨_, rfl⟩
  posFail := Prog.invoke call fun out =>
    match out with
    | .success _ => Prog.pure ()
    | .failure e => Prog.fail e
  pos_fail := ⟨_, _, rfl⟩

end Effects.Conformance
