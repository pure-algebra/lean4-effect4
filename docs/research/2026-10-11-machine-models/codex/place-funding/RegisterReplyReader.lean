import Effect4.Laws.Program.SourceOpportunityPrimitive
import Test.Dogfood.Scenario.Atomic.WriterMachine
set_option autoImplicit false
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope
-- Both scalar observations read the one actual register producer.
example (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (callback : EffName) (owner : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (produced : ((interpAt root view table).registerAsync callback owner token state).2 = some code)
    (id : Nat) : Test.Dogfood.Scenario.Atomic.WriterPhase.current id code = 0 := by
  have reply := register_reply root view table callback owner token state code produced
  cases reply <;> rfl

example (root : NativeEff) (view : List (FiberId × ExitV)) (table : RowTable)
    (callback : EffName) (owner : FiberId) (token : Nat) (state : Stores) (code : NCode)
    (produced : ((interpAt root view table).registerAsync callback owner token state).2 = some code)
    (q : List Nat) : Opportunities.current root q code = 0 :=
  Opportunities.terminal_reply_zero root q code
    (register_reply root view table callback owner token state code produced)
