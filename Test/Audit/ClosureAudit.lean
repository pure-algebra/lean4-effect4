import Effect4
import Tools.Semantics
import ProofGraph.ClosureAudit

/-!
# No table bound before a returned closure (`#closure_audit`)

The audit over the code that runs: the core (`Effect4`), the report tools and the proof-graph
tools. Then the control: a table bound before the closure is refused, and the same table passed
as data is not (`tools/ProofGraph/ClosureAudit.lean`).
-/

#guard_msgs (drop info) in
#closure_audit Effect4 Tools ProofGraph

namespace Test.Audit.ClosureAudit

/-- A table bound before the closure: built again at every application. -/
def rebuilt (n : Nat) : Nat → Bool := let table := List.range n; fun k => table.contains k

/-- The same table passed as data: the caller builds it once. -/
def asData (table : List Nat) (k : Nat) : Bool := table.contains k

open Lean in
/-- A module name read through `moduleNames`, which maps every module per call. -/
def moduleByNames (env : Environment) (i : Nat) : Option Name := env.header.moduleNames[i]?

open Lean in
/-- The same name read from the header's entry: one lookup. -/
def moduleByEntry (env : Environment) (i : Nat) : Option Name :=
  (env.header.modules[i]?).map (·.module)

end Test.Audit.ClosureAudit

-- control: the audit of this module refuses `rebuilt` and `moduleByNames`, and only them
/--
error: #closure_audit: 2 definitions build a table per use; build it once and pass it as data:
  Test.Audit.ClosureAudit.moduleByNames indexes `EnvironmentHeader.moduleNames`, which builds an array per call
  Test.Audit.ClosureAudit.rebuilt binds [table] before the closure it returns
-/
#guard_msgs in
#closure_audit Test.Audit.ClosureAudit
