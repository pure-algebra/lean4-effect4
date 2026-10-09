import Effect4.Library.Pull.Ops
import Effect4.Laws.Program.Authoring.Sugar

/-!
# Pull builders keep source scope

Placement: helpers of proposed `pull-protocol-selection`, concept `translation-simulation`, R10.
The plan is `docs/research/2026-10-09-pull-protocol-plan.md`.
These helpers also serve the existing `elaborate_scoped` consequence.
The reach requires scoped caller terms, programs and handlers.
The consumers are the public Pull operations and `Stream.drain_scoped`.
The statements establish scope alone, with no typing, evaluation or outside-runtime correspondence.
-/

set_option autoImplicit false

namespace Effect4.Pull

open Effect4.Program Effect4.Program.Authoring

/-- A chunk constructor keeps its payload's source scope. -/
theorem chunkValue_scoped {items : TermSrc} (h : items.Scoped) :
    (chunkValue items).Scoped :=
  app_scoped "pair" (TermSrc.Scoped_cons (str_scoped "Chunk")
    (TermSrc.Scoped_cons h TermSrc.Scoped_nil))

/-- An end constructor keeps its leftover's source scope. -/
theorem endValue_scoped {leftover : TermSrc} (h : leftover.Scoped) :
    (endValue leftover).Scoped :=
  app_scoped "pair" (TermSrc.Scoped_cons (str_scoped "End")
    (TermSrc.Scoped_cons h TermSrc.Scoped_nil))

/-- Answer selection keeps scope where the answer and both payload handlers do. -/
theorem matchAnswer_scoped {answer : TermSrc}
    {onSuccess onDone : TermSrc → Src NativeOp} (ha : answer.Scoped)
    (hs : ∀ chunk : TermSrc, chunk.Scoped → (onSuccess chunk).Scoped)
    (hd : ∀ leftover : TermSrc, leftover.Scoped → (onDone leftover).Scoped) :
    (matchAnswer answer onSuccess onDone).Scoped :=
  selectTagWith_scoped "End" ha hd fun _ hc =>
    hs _ (app_scoped "snd" (TermSrc.Scoped_cons hc TermSrc.Scoped_nil))

/-- Completion recovery keeps scope where the input and leftover handler do. -/
theorem catchDone_scoped {self : Src NativeOp} {onDone : TermSrc → Src NativeOp}
    (hself : self.Scoped)
    (hd : ∀ leftover : TermSrc, leftover.Scoped → (onDone leftover).Scoped) :
    (catchDone self onDone).Scoped :=
  bindWith_scoped hself fun _ ha =>
    matchAnswer_scoped ha (fun _ hc => succeed_scoped hc) hd

/-- Each handler builds a scoped program from a scoped payload reader. -/
structure Handlers.Scoped (options : Handlers) : Prop where
  onSuccess : ∀ chunk : TermSrc, chunk.Scoped → (options.onSuccess chunk).Scoped
  onFailure : ∀ cause : TermSrc, cause.Scoped → (options.onFailure cause).Scoped
  onDone : ∀ leftover : TermSrc, leftover.Scoped → (options.onDone leftover).Scoped

/-- Three-outcome selection keeps scope where the input and each handler do. -/
theorem matchEffect_scoped {self : Src NativeOp} {options : Handlers}
    (hself : self.Scoped) (ho : options.Scoped) : (matchEffect self options).Scoped :=
  minting_scoped "value" fun value => minting_scoped "cause" fun cause =>
    Effect4.Program.Authoring.matchCause_scoped value cause hself
      (matchAnswer_scoped (minted_scoped value) ho.onSuccess ho.onDone)
      (ho.onFailure _ (minted_scoped cause))

end Effect4.Pull
