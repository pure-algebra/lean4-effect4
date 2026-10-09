module

public import Effect4.Program.Stream
public import Effect4.Program.Authoring.Sugar

/-!
# Pull consumers over the existing chunk protocol

The answer type remains `Program.Stream.pulledTy`, with its `Chunk` and `End` values.
This profile produces lists of elements, rather than latest's arbitrary success values.
A producer or binding supplies the nonempty chunk premise; these builders do not check it.
Decisions row 331 represents clean completion as an `End` value with its leftover.
Latest represents completion as a `Cause.Done` failure (`Pull.ts:40-42`).
The consumers transcribe `catchDone` (`Pull.ts:215-219`) and `matchEffect` (`Pull.ts:488-500`).
Their building block is Effect, through the existing bind, selection and cause match.
They establish no correspondence for latest's mixed Done causes (`Pull.ts:277-295`).
Authoring handlers elaborate to ordinary Eff data; the module stores no runtime closure.
-/

@[expose] public section
set_option autoImplicit false

namespace Effect4.Pull

open Effect4.Program Effect4.Program.Authoring

/-- Pull's implemented building block, under decisions row 335. -/
def buildingBlocks : List String := ["Effect"]

/-- The existing protocol's chunk value, from a list source term. -/
def chunkValue (items : TermSrc) : TermSrc := app "pair" [str "Chunk", items]

/-- The existing protocol's end value, with its leftover source term. -/
def endValue (leftover : TermSrc) : TermSrc := app "pair" [str "End", leftover]

/-- Handle one chunk answer or clean end, passing only the payload to its handler.
The caller supplies a value of `Program.Stream.pulledTy`.
Ordinary failures remain outside this value selection. -/
def matchAnswer (answer : TermSrc) (onSuccess onDone : TermSrc → Src NativeOp) :
    Src NativeOp :=
  selectTagWith answer "End" onDone fun chunk => onSuccess (app "snd" [chunk])

/-- Recover from clean end; a normal chunk answers its list unchanged.
The body's failures and the end handler's failures propagate through the existing bind.
This is latest's `catchDone`, under the signed value representation of row 331. -/
def catchDone (self : Src NativeOp) (onDone : TermSrc → Src NativeOp) : Src NativeOp :=
  bindWith self fun answer => matchAnswer answer (fun chunk => succeed chunk) onDone

/-- The three handlers of latest's `Pull.matchEffect`, in the chunk profile.
The failure handler receives the whole cause value.
These functions build source syntax and are not stored program content. -/
structure Handlers where
  onSuccess : TermSrc → Src NativeOp
  onFailure : TermSrc → Src NativeOp
  onDone : TermSrc → Src NativeOp

/-- Select the chunk, failure or clean-end handler after the pull body finishes.
The cause match surrounds only the body, so selected-handler failures escape unchanged.
The selected handler receives the body's resulting state through the existing Eff semantics. -/
def matchEffect (self : Src NativeOp) (options : Handlers) : Src NativeOp :=
  minting "value" fun value => minting "cause" fun cause =>
    Effect4.Program.Authoring.matchCause value cause self
      (matchAnswer (minted value) options.onSuccess options.onDone)
      (options.onFailure (minted cause))

end Effect4.Pull
