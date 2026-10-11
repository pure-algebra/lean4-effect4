import Effect4.Laws.Program.NativeCallbacks
import Effect4.Laws.Program.HeapSites.Core

/-!
# Source-owned reference writers

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The source witness supplies the checked site law to an actual native store operation.
Administrative operations retain the reference heap.
The history closure consumes these command facts.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program HeapSites

/-- The checked source site applies to the actual operation produced at that site. -/
theorem origin_keeps (root : NativeEff) (P : Val → Prop) (sites : SitesKeep root P)
    (op : SyncOp) (origin : OpOrigin root op) : OpKeeps P op := by
  obtain ⟨p, row, request, value, found, scope, evaluated, operation⟩ := origin
  exact sites p.path row request p.env value op found scope evaluated operation

/-- An operation with retained source scope keeps the site's cell predicate. -/
theorem op_at_keeps (root : NativeEff) (P : Val → Prop) (sites : SitesKeep root P)
    (op : SyncOp) (owned : OpAt root op) : OpKeeps P op := by
  cases op
  case refMake | refSet | refGetAndSet | refSetAndGet | refUpdate | refGetAndUpdate
    | refUpdateAndGet | refUpdateSome | refGetAndUpdateSome | refUpdateSomeAndGet
    | refModify | refModifySome => exact origin_keeps root P sites _ owned
  all_goals unfold OpKeeps
  all_goals intro before after answer operation heap
  all_goals unfold syncOpStep at operation
  all_goals repeat' split at operation
  all_goals aesop (add norm unfold [refStep])

end Effect4.Program.SourceScope
