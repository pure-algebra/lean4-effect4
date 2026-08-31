import Cas.Backend.Admission
import Cas.Backend.Ts
import Gate

/-!
# The admission-table emitter — `lake exe emitgate`

R11 applied to the DOOR. The TypeScript admitted-subset gate used to be
a 330-line hand copy of `Ast.ofRepresentationJson` and `Ast.wf`, with
the check spelling, the safe-integer bound, the union modes, the
declaration columns and the refusal prose all retyped. This tool prints
`Cas.Backend.Admission`'s table into the effects package, where a small
interpreter walks it; `--check` is the byte-identity gate.
-/

namespace EmitGateMain

/-- Where the table lives in the effects package — the tool's own
knowledge of its artifact, so no caller carries the path. A positional
argument overrides it. -/
def defaultTarget : System.FilePath :=
  "../effects/src/cas/generated/SchemaAdmission.ts"

/-- The table's emitted header. The module declared no version before
this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "emitgate"
  module := "library/cas/tools/EmitGate.lean"

/-- The table, headed. The module is `Cas.Backend.Admission`'s, so the
header is appended to its doc block rather than spelled in this tool —
the table's prose belongs to the value, the provenance to the run that
printed it. -/
def rendered : String :=
  Cas.Backend.Ts.Render.module Cas.Backend.Ts.house0
    { Cas.Backend.Admission.module with
      header := Cas.Backend.Admission.module.header ++ emitted.headerLines }

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  return [⟨target.getD defaultTarget, rendered,
    s!"{Cas.Backend.Admission.nodes.length} nodes, \
{Cas.Backend.Admission.clauses.length} clauses"⟩]

end EmitGateMain

def main := Gate.mainAt "lake exe emitgate" EmitGateMain.fixtures
