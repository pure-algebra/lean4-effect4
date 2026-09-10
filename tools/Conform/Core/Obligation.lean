import Lean.Data.Json
import Conform.Core.Report

/-!
# Conform.Core.Obligation — what remains to be shown, as data

**What it is.** An *obligation* is a proof or check that a certificate would need and that the
tool did not itself establish: a leaf specification a verification-condition generator lacked,
a representation law a container model needs from its element, a translation relation a
generated function assumes, a host action no model covers. The design packet
(`docs/research/2026-09-09-type-tooling-design.md` §7) asks for a bounded schema of *kinds*,
each with a subject, its dependencies, the profile and the pins it was stated under — never a
serialised Lean proposition, never a "proved" string standing in for a proof.

An obligation report can therefore say "this is what would make the certificate complete"
without ever confusing a receipt with a theorem. The propositions the kinds stand for live with
the check that emits them (in Lean, as the statement the check reconstructs and compares a
supplied theorem's type against — `Conform.Spec`); this module holds only the data.

**Depends on.** `Conform.Core.Report`, `Lean.Json`.

**Properties.**
* **Kinds are registered, not free.** `Obligation.kind` is validated against a `Registry` the
  driver supplies; an unregistered kind is a refusal of the *report*, so a check cannot invent
  an obligation vocabulary of its own without documenting it — *by construction*
  (`Obligation.validate`).
* **An obligation is not a failure.** A report may carry open obligations and still pass its
  check; what it may not do is claim a certificate that depends on them. `Report.withObligations`
  attaches them under their own key and leaves the rows' outcomes alone — *by construction*.
* **Remaining does not mean false.** The five statuses distinguish an unproved theorem from
  failed automation, an unsupported extraction, malformed input and a counterexample — *by
  construction* (`Status`).
-/

namespace Conform

open Lean (Json)

/-- Why an obligation is open. -/
inductive Obligation.Status
  /-- Stated, nobody has proved it. -/
  | unproved
  /-- Automation was tried and did not close it; a hand proof may. -/
  | automationFailed
  /-- The tool cannot even state it for this input (unsupported form). -/
  | unsupported
  /-- The input was malformed; the obligation is moot until the input is repaired. -/
  | malformedInput
  /-- A witness refutes it as stated. -/
  | refuted
deriving DecidableEq, Repr, Inhabited

namespace Obligation.Status

protected def toString : Obligation.Status → String
  | .unproved => "unproved"
  | .automationFailed => "automation-failed"
  | .unsupported => "unsupported"
  | .malformedInput => "malformed-input"
  | .refuted => "refuted"

instance : ToString Obligation.Status := ⟨Obligation.Status.toString⟩
instance : Lean.ToJson Obligation.Status := ⟨fun s => Json.str (toString s)⟩

end Obligation.Status

/-- One registered kind of obligation: its stable id and one sentence a reader can act on. -/
structure Obligation.Kind where
  id : String
  description : String
deriving Repr, Inhabited

/-- The kinds a driver admits. -/
abbrev Obligation.Registry := List Obligation.Kind

/-- What remains. -/
structure Obligation where
  kind : String
  subject : Subject
  status : Obligation.Status
  /-- What this obligation would need first (other subjects, rendered). -/
  dependsOn : List String := []
  /-- The profile or configuration it is stated under. -/
  profile : String := ""
  /-- The exact statement as the check rendered it, for a human; not a proof term. -/
  statement : String
  detail : Json := Json.null
deriving Inhabited, Lean.ToJson

namespace Obligation

/-- The derived encoder, under the name the rest of the library calls; the keys are the field
names, sorted by `Json.obj`. -/
def toJson (o : Obligation) : Json := Lean.toJson o

/-- Every obligation's kind is registered; the first offender is named. -/
def validate (registry : Registry) (os : Array Obligation) : Except String Unit := do
  for o in os do
    unless registry.any (·.id == o.kind) do
      throw s!"obligation kind `{o.kind}` on {o.subject.render} is not registered (known: {", ".intercalate (registry.map (·.id))})"

end Obligation

namespace Report

/-- The report with its open obligations attached under `obligations`, kinds validated. -/
def withObligations (r : Report) (registry : Obligation.Registry) (os : Array Obligation) :
    Except String Json := do
  Obligation.validate registry os
  pure (r.toJson.setObjVal! "obligations" (Json.arr (os.map Obligation.toJson)))

end Report

end Conform
