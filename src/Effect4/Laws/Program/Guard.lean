import Effect4.Laws.Program.Guard.NativeQueueAssembly
import Effect4.Laws.Program.Guard.Race
import Effect4.Laws.Program.Guard.Continuation
import Effect4.Laws.Program.Guard.Single
import Effect4.Laws.Program.Guard.Decision

/-! Guard-key ownership and preservation through machine commands.
The proof components track stored keys, active command owners, and interruption
separately. Native evaluation, returned-fiber settlement, observer callbacks,
and continuation steps connect through these shared invariants. Driver and raw
decision induction establish them for every explicit prefix from Api.load. -/
