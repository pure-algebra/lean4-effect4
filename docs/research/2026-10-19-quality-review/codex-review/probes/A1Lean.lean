import Effect4.Machine.Integers
import Effect4.Store.Carrier.Val

-- Finite controls for A1. No new theorem or proof claim.
#eval Effect4.Program.intSub (.negInt 0) (.negInt 4611686018427387903)
#guard Effect4.Program.intSub (.negInt 0) (.negInt 4611686018427387903) =
  some (.nat 4611686018427387903)
#eval (Effect4.Store.Val.floatFrame 0x3FE0000000000000,
  Effect4.Store.Val.floatFrame 0xBFE0000000000000,
  Effect4.Store.Val.floatFrame 0x4004000000000000,
  Effect4.Store.Val.floatFrame 0x8000000000000000)
#guard Effect4.Store.Val.encode (.float 0x3FE0000000000000) !=
  Effect4.Store.Val.encode (.float 0xBFE0000000000000)
