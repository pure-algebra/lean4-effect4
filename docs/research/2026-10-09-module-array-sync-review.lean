import Test.Program.SynchronizedRef
import Test.Program.StreamArray

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.ModuleArraySyncReview
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules
open Test.Program.SynchronizedRef

-- The captured fold has its own two binders and reads an original caller variable.
def outerCapture : Src NativeOp :=
  bindName "current" (succeed (nat 3)) fun delta =>
    bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
      bindWith (Effect4.SynchronizedRef.modify self body
        (capture (foldWith (listOf [nat 2, nat 4]) (nat 0) fun acc item =>
          app "add" [acc, app "add" [item, delta]]))) fun reply =>
        inspect self reply
#guard observation outerCapture == some (numericExpected 17)
#guard observation outerCapture != some (numericExpected 11)

-- A nested captured fold must retain both its outer item and the original caller input.
def nestedCapture : Src NativeOp :=
  bindName "item" (succeed (nat 3)) fun delta =>
    bindWith (Effect4.SynchronizedRef.make .nat (nat 5)) fun self =>
      bindWith (Effect4.SynchronizedRef.modify self body
        (capture (foldWith (listOf [nat 1, nat 2]) (nat 0) fun outerAcc outerItem =>
          app "add" [outerAcc,
            foldWith (listOf [outerItem, delta]) (nat 0) fun innerAcc item =>
              app "add" [innerAcc, item]]))) fun reply =>
        inspect self reply
#guard observation nestedCapture == some (numericExpected 14)
#guard observation nestedCapture != some (numericExpected 8)

-- Array input resolution sees the original caller slot; open introduces no prior local slot.
def callerLast : TermSrc := fun env _ => .ok (.var (env.names.length - 1))
def arrayCaller : Src NativeOp :=
  bindName "items" (succeed (listOf [nat 6, nat 8])) fun _ =>
    Stream.runCollect (Stream.fromArray .nat callerLast)
#guard Test.Program.StreamArray.runModule {main := arrayCaller} =
  some (.success (.list [.nat 6, .nat 8]))
#guard Test.Program.StreamArray.runModule {main := arrayCaller} !=
  some (.success (.list []))
end Test.ModuleArraySyncReview
