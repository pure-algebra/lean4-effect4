import Effect4.Laws.Program.Typed.TypedStateDecl
import Effect4.Store.Carrier.Val
open Effect4.Program.Typed
namespace Test.MetadataDuplicateRed
inductive Expect | root
structure Sample where
  value : Effect4.Store.Val
  token : Nat
def sources : List Row := [
  ("Test.MetadataDuplicateRed.Sample", .owner "Whole"),
  ("Test.MetadataDuplicateRed.Sample.token", .custom "Token")]
/-- error: typed state: duplicate owner coverage at Test.MetadataDuplicateRed.Sample.token -/
#guard_msgs in
#typed_state Test.MetadataDuplicateRed.Sample using sources
end Test.MetadataDuplicateRed
