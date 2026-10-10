import Tools.Session.Snapshot
import ProofGraph.AxiomAudit

set_option autoImplicit false
namespace SnapshotControls
open Effect4.Program Effect4.Store Tools.Session Tools.Session.Snapshot

def one : Sketch := { program := .succeed (.lit (.nat 1)) }
def two : Sketch := { program := .succeed (.lit (.nat 2)) }
def holes : Sketch := { program := one.program, holes := [Row.hole "h" .nat .never []] }

#guard (fresh one.encode).isSome
#guard (fresh two.encode).isSome
#guard (fresh ([], [])).isNone
#guard (resolve one.encode (prepare one.encode)).isSome
#guard (resolve two.encode (prepare one.encode)).isSome
#guard (resolve holes.encode (prepare one.encode)).isSome
#guard (resolve ([], []) (prepare one.encode)).isNone
#guard (match resolve one.encode (prepare two.encode) with
  | some s => Wire.encodeProgram s.sketch.program == one.encode.1
  | none => false)
#guard (match resolve holes.encode (prepare one.encode) with
  | some s => Wire.encodeHoles s.sketch.holes == holes.encode.2
  | none => false)

-- Reader: the actual prepared cache satisfies the generic agreement law.
example (bytes : Bytes × Bytes) : resolve bytes (prepare one.encode) = fresh bytes :=
  resolve_agrees _ _ (prepare_valid _)

#eval hexString (Wire.encodeHoles [])
end SnapshotControls
#axiom_audit Tools.Session.Snapshot
