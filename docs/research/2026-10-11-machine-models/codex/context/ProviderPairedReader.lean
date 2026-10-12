import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Auto.KernelRfl

set_option autoImplicit false
namespace ProviderPairedReader
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

-- Readers consume the paired provider producers and the actual shared Region fold.
example (update : Env.ContextUpdate) (body : Region) :
    updateContextAt update body =
      .onSuccess (.withFiber .captureMask) (.provideMask update body) := rfl

example (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (flag : Bool) :
    (interpOf root).withFiberOf (.provideMasked update body flag) =
      some (.setInterruptible
        (.onSuccess (.withFiber .getCtx) (.updateThen update body flag)) false) := rfl

example (root : NativeEff) (body : Region) (flag : Bool) :
    (interpOf root).withFiberOf (.restoreRegion body flag) =
      some (.setInterruptible (regionCode root body) flag) := rfl

example (update : Env.ContextUpdate) (body : Region) :
    updateContextR update body =
      (guardR .onSuccess (fiberValR .getInterruptible rfl)).bind (seqR fun value =>
        match Val.savedMask? value with
        | some flag => .vis (.inr (.mask false (.contextEntry update body flag))) Effects.Program.pure
        | none => .pure badShapeExit) := rfl

example (root : NativeEff) (body : Region) :
    denoteBody root (.region body) =
      regionBodyR (denoteAt root) (layerBuildR root) body := rfl

example (root : NativeEff) (update : Env.ContextUpdate) (body : Region) (flag : Bool) :
    denoteBody root (.contextEntry update body flag) = contextEntryR update body flag := rfl

example (interp : RInterp) (body : Region) :
    bodyR interp (.region body) =
      regionBodyR (fun point => interp.suspendBody (.body point))
        (fun point memo scope => interp.suspendBody (.forkLayer point memo scope)) body := rfl

example (interp : RInterp) (update : Env.ContextUpdate) (body : Region) (flag : Bool) :
    bodyR interp (.contextEntry update body flag) = contextEntryR update body flag := rfl

end ProviderPairedReader
