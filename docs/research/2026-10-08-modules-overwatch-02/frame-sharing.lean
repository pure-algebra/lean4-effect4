import Test.Program.StepLanguage

set_option autoImplicit false
open Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Test.Program.StepLanguage

namespace Overwatch02.FrameSharing

-- A reply/state pair does not expose a record update spine through its projection.
#guard (Step.snd release).spine == none
#guard releaseNext.spine == some 0

-- Share the update itself, keeping the existing emitted term unchanged.
def clearWaiters : Step [cellTy] cellTy :=
  .set (.var cell) waitersF (.emptyLike (.get (.var cell) waitersF))

def next : Step [cellTy] cellTy :=
  .ite (.get (.var cell) openF) (.var cell) clearWaiters

def releaseShared : Step [cellTy] (.prod (.prod .bool (.list waiterTy)) cellTy) :=
  .ite (.get (.var cell) openF)
    (.pair (.pair (.bool false) (.emptyLike (.get (.var cell) waitersF))) (.var cell))
    (.pair (.pair (.bool true) (.get (.var cell) waitersF)) clearWaiters)

example : next = releaseNext := rfl
example : releaseShared = release := rfl

example (L : Leaves) (vs : Inputs L [cellTy]) :
    openF.get (next.eval L vs) = openF.get (cell.get vs) :=
  Step.frame L vs cell openF next rfl (by decide)

end Overwatch02.FrameSharing
