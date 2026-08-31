import Effects.Cas.Value

/-!
# The remote exchange alphabet

The abstract server-event vocabulary the remote client machine consumes —
the model's entire view of the wire. Every member is data: no HTTP
vocabulary, no wall-clock, no host detail, no credentials. Absence
(`absent`, per-key `missing`) and corruption (`integrityMismatch`, and
locally detected verification failure) never share a member — the
convergence every surveyed production system encodes.

`integrityMismatch` is an R1 amendment to the Pass A member list: a
server-side integrity rejection of an upload is neither absence nor a
transport fault, and folding it into either would violate the ratified
separation principle. Flagged for the R1 ratification point.
-/

namespace Effects.Remote

/-- Declared client-side budgets the machine enforces before any hashing
or decoding. -/
structure Budgets where
  maxBytes : Nat
  maxKeys : Nat
  deriving DecidableEq, Repr

/-- Server-declared limits carried by a capabilities event. -/
structure Limits where
  maxBatchKeys : Nat
  maxBlobBytes : Nat
  deriving DecidableEq, Repr

/-- One key's outcome inside a batch result. -/
inductive KeyStatus (K B : Type) where
  | found (key : K) (bytes : B)
  | missing (key : K)
  | failed (key : K)
  deriving DecidableEq

/-- The exchange alphabet: everything a server (or the transport) can say
to the client machine. `ok` carries the declared length separately from
the bytes so budget checks precede any inspection of the body. -/
inductive Event (K B : Type) where
  | ok (declared : Nat) (bytes : B)
  | absent
  | truncated
  | reset
  | silence
  | unauthenticated
  | denied
  | rateLimited (retryAfter : Nat)
  | capacity
  | redirected
  | integrityMismatch
  | batchResult (results : List (KeyStatus K B))
  | capabilities (limits : Limits)
  | interrupted
  deriving DecidableEq

end Effects.Remote
