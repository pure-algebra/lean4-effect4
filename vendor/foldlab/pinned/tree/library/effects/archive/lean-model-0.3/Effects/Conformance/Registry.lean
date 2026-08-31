import Effects.Conformance.Schema.WfPreserve
import Effects.Conformance.Schema.TraceExcludes
import Effects.Conformance.Schema.ExactStep
import Effects.Conformance.Schema.FailClosed
import Effects.Conformance.Schema.Distinctness
import Effects.Conformance.Schema.Homomorphism
import Effects.Conformance.Schema.Codec
import Effects.Conformance.Schema.RejectionClause
import Effects.Conformance.Instances.CAS001
import Effects.Conformance.Instances.CAS002
import Effects.Conformance.Instances.CMP001
import Effects.Conformance.Instances.RPL002
import Effects.Conformance.Instances.RPL003
import Effects.Conformance.Instances.RPL004
import Effects.Conformance.Instances.RPL005
import Effects.Conformance.Instances.SES001
import Effects.Conformance.Instances.SES002
import Effects.Conformance.Instances.SES003
import Effects.Conformance.Instances.CMP002
import Effects.Conformance.Instances.RMT001
import Effects.Conformance.Instances.RMT002
import Effects.Conformance.Instances.RMT003
import Effects.Conformance.Instances.RMT004
import Effects.Conformance.Instances.RMT005
import Effects.Conformance.Instances.RMT006
import Effects.Conformance.Instances.RMT007
import Effects.Conformance.Instances.RMT008
import Effects.Conformance.Instances.RMT014
import Effects.Conformance.Instances.RMT015
import Effects.Conformance.Instances.RMT017
import Effects.Conformance.Instances.MRK001
import Effects.Conformance.Instances.MRK002
import Effects.Conformance.Instances.MRK003
import Effects.Conformance.Instances.MRK005
import Effects.Conformance.Instances.MRK006
import Effects.Conformance.Instances.MRK007
import Effects.Conformance.Instances.MRK011
import Effects.Conformance.Instances.MRK012
import Effects.Conformance.Instances.MRK018

/-!
# The instance registry

The registry lists every instantiated (therefore proved-with-kit)
obligation, via each family's `entry` projection. Pending obligations are
exactly those in the plan's obligation ledger that are absent here; the
phase-1 ledger generator merges the two with the TypeScript suite and
mutation results.
-/

namespace Effects.Conformance

def registry : List LedgerEntry :=
  [ cas001.entry, cas002.entry
  , rpl002.entry, rpl003.entry, rpl004.entry, rpl005.entry
  , ses001.entry, ses002.entry, ses003.entry, cmp001.entry, cmp002.entry
  , rmt001.entry, rmt002.entry, rmt003.entry
  , rmt004.entry, rmt005.entry, rmt006.entry, rmt007.entry
  , rmt008.entry, rmt014.entry, rmt015.entry, rmt017.entry
  , mrk001.entry, mrk002.entry, mrk003.entry
  , mrk005.entry, mrk006.entry, mrk007.entry
  , mrk011.entry, mrk012.entry, mrk018.entry ]

#guard registry.map (·.id) ==
  ["CAS-001", "CAS-002", "RPL-002", "RPL-003", "RPL-004", "RPL-005",
   "SES-001", "SES-002", "SES-003", "CMP-001", "CMP-002", "RMT-001",
   "RMT-002", "RMT-003", "RMT-004", "RMT-005", "RMT-006", "RMT-007",
   "RMT-008", "RMT-014", "RMT-015", "RMT-017", "MRK-001", "MRK-002",
   "MRK-003", "MRK-005", "MRK-006", "MRK-007", "MRK-011", "MRK-012",
   "MRK-018"]
#guard registry.map (·.family) ==
  ["CODEC", "REJECTION-CLAUSE", "TRACE-EXCLUDES", "EXACT-STEP",
   "FAIL-CLOSED", "FAIL-CLOSED", "TRACE-EXCLUDES", "WF-PRESERVE",
   "FAIL-CLOSED", "HOMOMORPHISM", "DISTINCTNESS", "TRACE-EXCLUDES",
   "FAIL-CLOSED", "TRACE-EXCLUDES", "EXACT-STEP", "TRACE-EXCLUDES",
   "FAIL-CLOSED", "TRACE-EXCLUDES", "FAIL-CLOSED", "FAIL-CLOSED",
   "AGREEMENT", "FAIL-CLOSED", "CODEC", "TRACE-EXCLUDES",
   "TRACE-EXCLUDES", "AGREEMENT", "AGREEMENT", "AGREEMENT", "CODEC",
   "CODEC", "CODEC"]
#guard (emitLedger registry).take 20 == "# Conformance ledger"

/-- Every declared sentence rider: the conjuncts of ratified sentences
discharged by named theorems rather than schema law fields, carried
structurally so the citations are load-bearing. -/
def sentenceRiders : List SentenceRider :=
  [ rmt001ReturnRider
  , rmt003MonotoneRider
  , rmt003RunRider
  , rmt017ConfirmsRider
  , rmt017CacheRider
  , ses003OrderRider ]

#guard sentenceRiders.map (·.id) ==
  ["RMT-001", "RMT-003", "RMT-003", "RMT-017", "RMT-017", "SES-003"]
#guard (sentenceRiders.map (·.id)).all
  (fun id => (registry.map (·.id)).contains id)

end Effects.Conformance
