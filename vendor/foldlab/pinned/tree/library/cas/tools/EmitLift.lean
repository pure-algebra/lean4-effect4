import Cas.Lift.Manifest
import Gate

/-!
# The lift-manifest emitter — `lake exe emitlift`

Emits both projections of the effect-lift manifest (the R11
interchange document of the lift lane) from `Cas.Lift.manifestV0`:
the JSON the engines consume, through the house manifest printer, and
the human Markdown rendering (P4) beside it at the same path with the
`md` extension. `--check` is the byte-identity gate over both.
-/

namespace EmitLiftMain

/-- Where the manifest lives in the effects package — the lane's own
knowledge of its artifact. A positional argument overrides it, and the
Markdown projection follows the JSON's path either way. -/
def defaultTarget : System.FilePath :=
  "../effects/src/cas/generated/lift/manifest.json"

/-- The manifest's emitted header. `schemaVersion` opens at the
`manifestVersion` the document already declares, and that field stays
for one release beside the header that now carries it.

The Markdown projection is not headed: it is a rendering FOR PEOPLE of
the same value, and the JSON beside it is where a machine reads the
provenance. -/
def emitted : Gate.Emitted where
  schemaVersion := Cas.Lift.manifestV0.manifestVersion
  emitter := "emitlift"
  module := "library/cas/tools/EmitLift.lean"

-- The manifest's projection is an OBJECT, which is where the header
-- goes; this is what makes `Emitted.onto`'s pass-through arm
-- unreachable here.
#guard match Cas.Lift.manifestV0.toValue with | .obj _ => true | _ => false

/-- The manifest, headed. -/
def document : String :=
  Cas.Json.document (emitted.onto Cas.Lift.manifestV0.toValue)

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  let json := target.getD defaultTarget
  let rules := s!"{Cas.Lift.manifestV0.rules.length} rules"
  return [
    ⟨json, document, rules⟩,
    ⟨json.withExtension "md", Cas.Lift.markdown, s!"{rules}, Markdown"⟩]

end EmitLiftMain

def main := Gate.mainAt "lake exe emitlift" EmitLiftMain.fixtures
