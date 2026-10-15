import Effect4.Library.Queue.Ops
import Effect4.Program.Authoring.Mask

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.QueueTraces

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The variants of the Queue's part

A variant changes the Queue's part of `take` and of `offer`, and nothing of the wrapper. The
library's operation is the variant with no change. -/

/-- The knobs of a variant. Each default is the library's. -/
structure Variant where
  /-- How a step's signals are delivered. -/
  post : TermSrc → TermSrc → Src NativeOp := postAll
  /-- Whether a withdrawal posts the wake that its step names. -/
  withdrawalPosts : Bool := true
  /-- Whether an interrupted wait withdraws its request. -/
  withdraws : Bool := true
  /-- The wrapper of `take`. -/
  retry : Ty → String → Waiter → Src NativeOp := waitRetry
  /-- The term of an offer's withdrawal. -/
  withdrawOffer : Ty → TermSrc → TermSrc → TermSrc := Queue.withdrawOffer

/-- A withdrawal under a variant: its step, and its posts. -/
def withdrawalOf (v : Variant) (q : TermSrc) (step : TermSrc → TermSrc) : Src NativeOp :=
  if v.withdraws then
    bindWith (Ref.modifyWith q step) fun woken =>
      if v.withdrawalPosts then v.post woken unit else succeed (nat 0)
  else succeed (nat 0)

/-- `take` under a variant. -/
def takeOf (v : Variant) (A : Ty) (q : TermSrc) : Src NativeOp :=
  v.retry A "queue: the loop ended without a message"
    { hint := .unit
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (Queue.takeStep A id hint)) fun reply =>
          andThen (v.post (tupleAt reply 1) (bool true))
            (andThen (v.post (tupleAt reply 2) unit)
              (selectOptionWith (tupleAt reply 0) wait done))
      withdraw := fun id => withdrawalOf v q (Queue.withdrawTake A id) }

/-- `offer` under a variant. -/
def offerOf (v : Variant) (A : Ty) (q message : TermSrc) : Src NativeOp :=
  waitAnswer
    { hint := .bool
      attempt := fun id hint wait done =>
        bindWith (Ref.modifyWith q (Queue.offerStep A id hint message)) fun reply =>
          andThen (v.post (tupleAt reply 1) unit)
            (selectOptionWith (tupleAt reply 0) wait done)
      withdraw := fun id => withdrawalOf v q (v.withdrawOffer A id) }

/-- **A withdrawal that takes a message back**: the offer's withdrawal, which also drops the
newest buffered message. -/
def takesBack (_A : Ty) (id s : TermSrc) : TermSrc :=
  app "pair" [Queue.wake (field s "takers") (field s "msgs"),
    recordSet (recordSet s "offers" (Queue.removeOffer (field s "offers") id)) "msgs"
      (app "take" [field s "msgs", app "sub" [len (field s "msgs"), nat 1]])]

end Test.Program.QueueTraces
