import Test.Machine.Environment.ContextKeyAssurance

/-!
`ServiceName` exists, but the mutant assigns it to the empty Environment
module instead of its frozen owner `Effect4.Context.Key`.
-/

#effect4_check_context_declaration_owners Effect4.Context.Environment [
  Effect4.ServiceName]
