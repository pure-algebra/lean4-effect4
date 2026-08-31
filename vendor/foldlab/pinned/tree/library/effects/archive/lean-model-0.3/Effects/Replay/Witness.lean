import Effects.Replay.Session

/-!
# The replay witness

The immutable evidence a finished session leaves: mode, execution
identity, the consumed history, the ordered decision trace, and the
session outcome. It carries EXECUTION identity, never program identity —
compatibility is behavioral, emitted stream against recorded stream — and
nothing in it implies the recording program is unchanged or that the
external world would answer the same today. No obligation attaches to the
carrier in this slice; the session assembly that produces it is the M4
service work, and the interface re-freeze happens after this
representation passes review.
-/

namespace Effects.Replay

/-- The immutable session witness. `execId` is execution identity — an
opaque name for one run, never a program identity. -/
structure Witness (Op Req Val Err : Type) where
  mode : Mode
  execId : String
  consumed : List (Entry Op Req Val Err)
  trace : List (Decision Op)
  outcome : SessionOutcome Val Err
  deriving DecidableEq

end Effects.Replay
