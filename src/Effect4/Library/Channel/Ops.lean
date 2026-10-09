module

public import Effect4.Library.Pull.Ops

/-!
# Channel transformations over stored upstream definitions

Decisions rows 331 and 335 keep the upstream as a stored definition and its state request.
Every builder authors ordinary Eff data; no runtime function or Channel syntax is stored.
The first profile transforms each whole list-valued batch and ignores the output index.
The producer supplies nonempty input and mapped batches.
Clean completion remains an End value; no native Done-cause correspondence is claimed.
The Stream consumer owns opening, stopping after End and finalization.
These builders invoke the upstream once and acquire no resource.
-/

@[expose] public section
set_option autoImplicit false

namespace Effect4.Channel
open Effect4.Program Effect4.Program.Authoring

/-- The implemented Channel operations use latest's Effect and Pull building blocks. -/
def buildingBlocks : List String := ["Effect", "Pull"]

namespace Internal

/-- Shared batch dispatcher over an authored input.
Input failures bypass the transform; selected-transform failures escape with their stores.
The completion payload passes through unchanged.
Latest `Channel.ts:2328-2346`, `mapEffectSequential`, maps one successful pull value. -/
def mapEffectOf (self : Src NativeOp) (transform : TermSrc → Src NativeOp) : Src NativeOp :=
  bindWith self fun answer =>
    Pull.matchAnswer answer
      (fun batch => bindWith (transform batch) fun mapped => succeed (Pull.chunkValue mapped))
      (fun leftover => succeed (Pull.endValue leftover))

end Internal

/-- Transform one whole batch from a stored upstream at its captured state request.
The callback authors Eff syntax and ignores latest's index argument. -/
def mapEffect (upstream : DefSrc NativeOp) (state : TermSrc)
    (transform : TermSrc → Src NativeOp) : Src NativeOp :=
  Internal.mapEffectOf (Def.invoke upstream.name [state]) transform

/-- Pure whole-batch mapping, through the effectful dispatcher.
Latest `Channel.ts:2100-2104`, `map`, maps one successful pull value. -/
def map (upstream : DefSrc NativeOp) (state : TermSrc)
    (transform : TermSrc → TermSrc) : Src NativeOp :=
  mapEffect upstream state fun batch => succeed (transform batch)

namespace Internal

/-- Shared completion dispatcher over an authored input.
Batches pass through unchanged; only the End payload enters the transform.
Latest `Channel.ts:2188-2192`, `mapDoneEffect`, transforms completion through Pull.catchDone. -/
def mapDoneEffectOf (self : Src NativeOp) (transform : TermSrc → Src NativeOp) : Src NativeOp :=
  bindWith self fun answer =>
    Pull.matchAnswer answer
      (fun batch => succeed (Pull.chunkValue batch))
      (fun leftover => bindWith (transform leftover) fun mapped => succeed (Pull.endValue mapped))

end Internal

/-- Transform the completion payload from a stored upstream at its captured state request.
Input and selected-transform failures escape through the existing bind semantics. -/
def mapDoneEffect (upstream : DefSrc NativeOp) (state : TermSrc)
    (transform : TermSrc → Src NativeOp) : Src NativeOp :=
  Internal.mapDoneEffectOf (Def.invoke upstream.name [state]) transform

/-- Pure completion mapping, through the effectful completion dispatcher.
Latest `Channel.ts:2138`, `mapDone`, lifts its callback into mapDoneEffect. -/
def mapDone (upstream : DefSrc NativeOp) (state : TermSrc)
    (transform : TermSrc → TermSrc) : Src NativeOp :=
  mapDoneEffect upstream state fun leftover => succeed (transform leftover)

end Effect4.Channel
