/-!
# Terminals, outcome envelopes, and session outcomes

Three distinct result carriers, deliberately not identified:

- `Terminal` is a program terminal — success or declared typed failure —
  the thing a completed session carries.
- `Outcome` is the channel-preserving recorded outcome envelope of ONE
  operation occurrence: success of the declared success type or failure of
  the declared typed-failure type. Substitution re-injects it through the
  native channels, so recovery combinators fire exactly as they did live.
- `SessionOutcome` is the tagged session result: `completed` with the
  terminal; `rejected` with category, position, and — for the
  unconsumed-suffix case only — the program's terminal so far; or
  `violated` with the ambient-service violation. `violated` is produced by
  the runtime tripwires, never by the pure reducer in this slice; the
  constructor is present because the outcome taxonomy is ratified
  caller-visible API.
-/

namespace Effects.Replay

/-- A program terminal: success or declared typed failure. -/
inductive Terminal (Val Err : Type) where
  | succeeded (value : Val)
  | failed (error : Err)
  deriving DecidableEq

/-- The channel-preserving recorded outcome envelope of one occurrence. -/
inductive Outcome (Val Err : Type) where
  | success (value : Val)
  | failure (error : Err)
  deriving DecidableEq

/-- The ambient services the replay-mode tripwires guard. -/
inductive AmbientService where
  | clock
  | random
  deriving DecidableEq

end Effects.Replay
