import Effects.Cas.Value
import Effects.Cas.Node
import Effects.Cas.Codec
import Effects.Cas.Separation
import Effects.Cas.Address
import Effects.Cas.Store
import Effects.Cas.Admission
import Effects.Replay.Outcome
import Effects.Replay.History
import Effects.Replay.Decision
import Effects.Replay.Session
import Effects.Replay.Reducer
import Effects.Replay.Relation
import Effects.Replay.Laws
import Effects.Replay.Run
import Effects.Replay.Witness
import Effects.Replay.Program
import Effects.Replay.Interp
import Effects.Remote.Event
import Effects.Remote.Command
import Effects.Remote.Machine
import Effects.Remote.Laws
import Effects.Remote.ControlCodec
import Effects.Wire.Nat32
import Effects.Server.Free
import Effects.Server.Model
import Effects.Server.Laws
import Effects.Merkle.Chunk
import Effects.Merkle.Tree
import Effects.Merkle.Verify
import Effects.Merkle.Decoder
import Effects.Merkle.Laws
import Effects.Merkle.Consistency
import Effects.Merkle.ProofCodec
import Effects.Merkle.Blob
import Effects.Merkle.Manifest
import Effects.Merkle.Parser
import Effects.Conformance

/-!
# Effects

Root module for the Foldlab effects library.

The domain model arrives with the M2/M3 slices under the ratified contract.
`Effects.Conformance` carries the ratified workflow's schema-bundle
structures: obligation families as structures whose laws and anti-vacuity
kits are fields, with the ledger projection over typed instances.
-/
