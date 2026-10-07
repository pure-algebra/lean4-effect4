module

public import Effect4.Modules.Stream.Source
public import Effect4.Modules.Stream.Steps
public import Effect4.Program.Authoring.Loops
public import Effect4.Program.Authoring.Sugar
public import Effect4.Program.Authoring.Lifts
public import Effect4.Modules.Words

@[expose] public section

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **The loop of one opened stream**: pull until the end. `gain acc chunk` is the program that
answers the next accumulator. The loop's cursor is the pair of the accumulator and the leftover
once the end arrived. It answers the pair at the end. -/
def drain (src : Source) (accTy : Ty) (zero : TermSrc) (h : TermSrc)
    (gain : TermSrc → TermSrc → Src NativeOp) : Src NativeOp :=
  iterateWith (app "pair" [zero, noneT])
    { cursorTy := some (Ty.prod accTy (.option src.done)).normalize
      while_ := fun c => notT (app "isSome" [app "snd" [c]])
      body := fun c =>
        bindWith (src.pull h) fun answer =>
          selectTagWith answer "End"
            (fun leftover => succeed (endStep (app "fst" [c]) leftover))
            (fun chunk =>
              bindWith (gain (app "fst" [c]) (app "snd" [chunk])) fun next =>
                succeed (chunkStep next))
      step := fun _ next => next }

/-- **Open, drain, close**: the stream is opened inside a scope of its own, and its close is the
scope's finalizer. So the close runs at every exit of the loop. -/
def runWith (src : Source) (accTy : Ty) (zero : TermSrc)
    (gain : TermSrc → TermSrc → Src NativeOp) : Src NativeOp :=
  scope (bindWith (acquireWith src.opened src.close) fun h => drain src accTy zero h gain)

/-- **`Stream.runCollect`**: every element, in the order of the pulls
(`vendor/effect-4.0.0-rc.112/src/Stream.ts`, `runCollect`). -/
def runCollect (src : Source) : Src NativeOp :=
  bindWith (runWith src (.list src.elem) nilT fun acc chunk => succeed (app "append" [acc, chunk]))
    fun last => succeed (app "fst" [last])

/-- **`Stream.runForEach`**: `body` once for each element, in the order of the pulls
(`vendor/effect-4.0.0-rc.112/src/Stream.ts`, `runForEach`). It answers nothing. -/
def runForEach (src : Source) (body : TermSrc → Src NativeOp) : Src NativeOp :=
  andThen
    (runWith src .unit unit fun _ chunk => andThen (forEachOf chunk body) (succeed unit))
    (succeed unit)

end Effect4.Stream
