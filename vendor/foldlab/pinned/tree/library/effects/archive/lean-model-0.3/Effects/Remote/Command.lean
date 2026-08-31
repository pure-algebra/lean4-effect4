import Effects.Remote.Event

/-!
# Wire commands

What the machine emits toward the Effect shell. Commands are data — the
shell owns their transport realization — and command sequences are part
of the compared conformance surface alongside decisions. No command
carries credentials or ambient state.
-/

namespace Effects.Remote

/-- The command vocabulary the shell realizes over a transport. -/
inductive Command (K B : Type) where
  | probeCapabilities
  | load (key : K)
  | findMissing (keys : List K)
  | upload (key : K) (bytes : B)
  | queryCommitted (key : K)
  | publishRoot (key : K)
  deriving DecidableEq

end Effects.Remote
