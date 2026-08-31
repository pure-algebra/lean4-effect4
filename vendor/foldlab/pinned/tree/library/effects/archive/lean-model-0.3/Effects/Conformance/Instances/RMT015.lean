import Effects.Conformance.Schema.Agreement
import Effects.Conformance.RemoteVectors

/-!
# RMT-015 — a successful remote load implements the logical load

The first relational AGREEMENT instance: the two computations produce
different types — the machine run delivers bytes, the logical store
load produces a node — and the relation states that the delivered bytes
are exactly the canonical encoding of the node the store holds. The
domain is leaf admitted nodes within the declared byte budget: the R2
single-key slice covers reference-free nodes, and closure ordering for
graphs arrives at R3. The observation on the machine side is the
delivered payload of the completed run — commands need no separate
observation here because a load that delivers anything else fails the
byte relation itself. The negative kit is the substitution defect: a
mutated computation delivering altered bytes as success, which the
relation refuses; the wire-level mirror is the declared
`RMT015_SubstitutedDelivery` mutant killed by the vectors.
-/

namespace Effects.Conformance

open Effects.Remote Effects.Cas Manifest

private abbrev RunOut :=
  MachineState Addr32 Bytes × List (MResult Addr32 Bytes) ×
    List (OpId × RDecision Addr32 Bytes) × List (OpId × Command Addr32 Bytes)

/-- The bytes the run delivered to the caller, if any. -/
private def deliveredOf (r : RunOut) : Option Bytes :=
  r.2.1.findSome? fun
    | .delivered _ b => some b
    | _ => none

/-- The remote load run: request the node's address, then the server
answers with its canonical bytes. -/
private def loadRun (x : AdmittedNode) : RunOut :=
  run vecParams vecEmpty
    [ .request 1 (.load (toyAddr (encodeAdmitted x)))
    , .fromWire 1 (.ok (encodeAdmitted x).length (encodeAdmitted x)) ]

/-- The mutated computation for the falsification kit: a client that
delivers substituted bytes as a successful load. -/
private def substitutedRun (x : AdmittedNode) : RunOut :=
  (vecEmpty,
    [.delivered (toyAddr (encodeAdmitted x)) (encodeAdmitted x ++ [0])],
    [], [])

/-- RMT-015: a successful remote load implements the logical
admitted-node load. -/
def rmt015 : Agreement AdmittedNode RunOut (Option Node)
    (Option Bytes) (Option Node) where
  id := "RMT-015"
  sentence := "On leaf admitted nodes within the declared byte budget, the remote client's completed load run and the logical admitted-node store load agree at the delivered bytes under exact canonical encoding — a successful remote load implements the logical admitted-node load: what the machine delivers is precisely the canonical encoding of the node the store holds at that address, so remote success can never produce a node the logical load would not."
  hyp := fun x => x.val.refs = [] ∧ (encodeAdmitted x).length ≤ 40
  observeF := deliveredOf
  observeG := id
  rel := fun ob on => ob = on.map encodeNode
  f := loadRun
  g := fun x =>
    (Store.empty.set (toyAddr (encodeAdmitted x)) x.val)
      (toyAddr (encodeAdmitted x))
  law := fun x hx => by
    have hnotover : ¬ (encodeNode x.val).length > 40 := by
      have hle := hx.2
      simp [encodeAdmitted] at hle
      omega
    simp [loadRun, run, step, loadEvent, deliveredOf, vecEmpty,
      vecParams, encodeAdmitted, hnotover, Store.set_same,
      List.findSome?]
  posX := payloadNode
  pos_hyp := ⟨rfl, by decide⟩
  negF := substitutedRun
  negX := payloadNode
  neg_hyp := ⟨rfl, by decide⟩
  neg_diverges := by
    intro h
    simp [substitutedRun, deliveredOf, Store.set_same,
      encodeAdmitted] at h

end Effects.Conformance
