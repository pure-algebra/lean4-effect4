import Effect4.Program.Authoring.Lifts
import Effect4.Program.Authoring.Sugar
import Effect4.Codegen.Forms
import Effect4.Laws.Program.Authoring.Lifts
import Effect4.Laws.Program.Authoring.Sugar

/-! Seat J, step 2: the regenerated forms (scratch) with their generated scope lemmas, in one
module, so `authoring_scoped` is tested on `Authoring.minting` before the group is cut. -/

set_option autoImplicit false

namespace Effect4.Program.Authoring.Forms


open Effect4.Program Effect4.Program.Authoring

/-- `Effect.void` (`internal/effect.ts:1024-1026`). -/
def void : Src NativeOp :=
  Authoring.succeed Authoring.unit

/-- `Effect.die` (`internal/effect.ts:1018`). -/
def die (value : TermSrc) : Src NativeOp :=
  Authoring.failCause (Authoring.Cause.die value)

/-- `yield* Key` (`internal/effect.ts:2059`). -/
def yieldKey (key : Effect4.ServiceKey) : Src NativeOp :=
  Authoring.service key

/-- `Effect.andThen` (`internal/effect.ts:1417-1439`). -/
def andThenEffect (effect : Src NativeOp) (effect1 : Src NativeOp) : Src NativeOp :=
  Authoring.minting "answer" fun mintedAnswer0 => Authoring.bind mintedAnswer0 (effect) (effect1)

/-- `Effect.andThen` (`internal/effect.ts:1417-1439`). -/
def andThenContinuation (answer : String) (effect : Src NativeOp) (continuation : Src NativeOp) : Src NativeOp :=
  Authoring.bind answer (effect) (continuation)

/-- `Effect.andThen` (`internal/effect.ts:1417-1439`). -/
def andThenThunk (effect : Src NativeOp) (thunk : Src NativeOp) : Src NativeOp :=
  Authoring.minting "answer" fun mintedAnswer0 => Authoring.bind mintedAnswer0 (effect) (thunk)

/-- `Effect.as` (`internal/effect.ts:1386-1414`). -/
def as (answer : String) (effect : Src NativeOp) (value : TermSrc) : Src NativeOp :=
  Authoring.bind answer (effect) (Authoring.succeed value)

/-- `Effect.asVoid` (`internal/effect.ts:1467`). -/
def asVoid (effect : Src NativeOp) : Src NativeOp :=
  Authoring.minting "answer" fun mintedAnswer0 => Authoring.bind mintedAnswer0 (effect) (Authoring.succeed Authoring.unit)

/-- `Effect.tap` (`internal/effect.ts:1442-1464`). -/
def tapContinuation (answer : String) (effect : Src NativeOp) (continuation : Src NativeOp) : Src NativeOp :=
  Authoring.bind answer (effect) (Authoring.minting "answer" fun mintedAnswer1 => Authoring.bind mintedAnswer1 (continuation) (Authoring.succeed (Authoring.var answer)))

/-- `Effect.tap` (`internal/effect.ts:1442-1464`). -/
def tapEffect (effect : Src NativeOp) (effect1 : Src NativeOp) : Src NativeOp :=
  Authoring.minting "answer" fun mintedAnswer0 => Authoring.bind mintedAnswer0 (effect) (Authoring.minting "answer" fun mintedAnswer1 => Authoring.bind mintedAnswer1 (effect1) (Authoring.succeed (Authoring.minted mintedAnswer0)))

/-- `Effect.ensuring` (`internal/effect.ts:4043-4057`). -/
def ensuring (effect : Src NativeOp) (effect1 : Src NativeOp) : Src NativeOp :=
  Authoring.minting "exit" fun mintedExit0 => Authoring.onExit mintedExit0 (effect) (effect1)

/-- `Effect.matchCause` (`internal/effect.ts:3468-3495`). -/
def matchCause (value : String) (cause : String) (effect : Src NativeOp) (onValue : TermSrc) (onCause : TermSrc) : Src NativeOp :=
  Authoring.matchCause value cause (effect) (Authoring.succeed onValue) (Authoring.succeed onCause)

/-- `Effect.matchCauseEffect` (`internal/effect.ts:3427-3460`). -/
def matchCauseEffect (value : String) (cause : String) (effect : Src NativeOp) (onValue : Src NativeOp) (onCause : Src NativeOp) : Src NativeOp :=
  Authoring.matchCause value cause (effect) (onValue) (onCause)

/-- `Effect.yieldNow` (`internal/effect.ts:997`). -/
def yieldNow : Src NativeOp :=
  Authoring.yieldNow 0

/-- `Effect.forkChild` (`internal/effect.ts:5228-5284`). -/
def forkChildDefault (effect : Src NativeOp) : Src NativeOp :=
  Authoring.withFiber (Authoring.Action.fork (effect) (Effect4.Codegen.Forms.defaults false))

/-- `Effect.forkDetach` (`internal/effect.ts:5287-5334`). -/
def forkDetachDefault (effect : Src NativeOp) : Src NativeOp :=
  Authoring.withFiber (Authoring.Action.fork (effect) (Effect4.Codegen.Forms.defaults true))

/-- `Effect.forkIn` (`internal/effect.ts:5337-5379`). -/
def forkInDefault (effect : Src NativeOp) (scope : TermSrc) : Src NativeOp :=
  Authoring.withFiber (Authoring.Action.forkIn (effect) (Effect4.Codegen.Forms.defaults true) scope)

/-- `Effect.forkScoped` (`internal/effect.ts:5382-5406`). -/
def forkScopedDefault (effect : Src NativeOp) : Src NativeOp :=
  Authoring.withFiber (Authoring.Action.forkScoped (effect) (Effect4.Codegen.Forms.defaults true))

/-- `Effect.acquireRelease` (`internal/effect.ts:3971-4000`). -/
def releaseOne (resource : String) (effect : Src NativeOp) (release : Src NativeOp) : Src NativeOp :=
  Authoring.minting "exit" fun mintedExit1 => Authoring.acquireRelease resource mintedExit1 (effect) (release)

/-! ## Each form read on the reader is its printed expansion -/

#guard (elaborate (void)).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "void")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (die (nat 7))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "die")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (yieldKey ⟨⟨4⟩, ⟨4⟩⟩)).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "yieldKey")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (andThenEffect (succeed (nat 11)) (bind "x" (succeed (nat 22)) (succeed (var "x"))))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "andThenEffect")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (andThenContinuation "b0" (succeed (nat 11)) (succeed (var "b0")))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "andThenContinuation")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (andThenThunk (succeed (nat 11)) (bind "x" (succeed (nat 22)) (succeed (var "x"))))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "andThenThunk")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (as "b0" (succeed (nat 11)) (nat 7))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "as")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (asVoid (succeed (nat 11)))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "asVoid")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (tapContinuation "b0" (succeed (nat 11)) (succeed (var "b0")))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "tapContinuation")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (tapEffect (succeed (nat 11)) (bind "x" (succeed (nat 22)) (succeed (var "x"))))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "tapEffect")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (ensuring (succeed (nat 11)) (bind "x" (succeed (nat 22)) (succeed (var "x"))))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "ensuring")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (matchCause "b0" "b1" (succeed (nat 11)) (var "b0") (var "b1"))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "matchCause")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (matchCauseEffect "b0" "b1" (succeed (nat 11)) (succeed (var "b0")) (succeed (var "b1")))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "matchCauseEffect")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (yieldNow)).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "yieldNow")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (forkChildDefault (succeed (nat 11)))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "forkChildDefault")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (forkDetachDefault (succeed (nat 11)))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "forkDetachDefault")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (forkInDefault (succeed (nat 11)) (nat 7))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "forkInDefault")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (forkScopedDefault (succeed (nat 11)))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "forkScopedDefault")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

#guard (elaborate (releaseOne "b0" (succeed (nat 11)) (succeed (var "b0")))).toOption =
  (Effect4.Codegen.Forms.all.find? (·.id == "releaseOne")).bind fun f => f.expansion.expand 0 (f.exampleArgs 0)

/-! ## Receipts -/




theorem void_scoped  :
    ((void) : Src NativeOp).Scoped := by
  unfold void; authoring_scoped

theorem die_scoped {value : TermSrc} (h0 : value.Scoped) :
    ((die value) : Src NativeOp).Scoped := by
  unfold die; authoring_scoped

theorem yieldKey_scoped (key : Effect4.ServiceKey) :
    ((yieldKey key) : Src NativeOp).Scoped := by
  unfold yieldKey; authoring_scoped

theorem andThenEffect_scoped {effect : Src NativeOp} {effect1 : Src NativeOp} (h0 : effect.Scoped) (h1 : effect1.Scoped) :
    ((andThenEffect effect effect1) : Src NativeOp).Scoped := by
  unfold andThenEffect; authoring_scoped

theorem andThenContinuation_scoped (answer : String) {effect : Src NativeOp} {continuation : Src NativeOp} (h0 : effect.Scoped) (h1 : continuation.Scoped) :
    ((andThenContinuation answer effect continuation) : Src NativeOp).Scoped := by
  unfold andThenContinuation; authoring_scoped

theorem andThenThunk_scoped {effect : Src NativeOp} {thunk : Src NativeOp} (h0 : effect.Scoped) (h1 : thunk.Scoped) :
    ((andThenThunk effect thunk) : Src NativeOp).Scoped := by
  unfold andThenThunk; authoring_scoped

theorem as_scoped (answer : String) {effect : Src NativeOp} {value : TermSrc} (h0 : effect.Scoped) (h1 : value.Scoped) :
    ((as answer effect value) : Src NativeOp).Scoped := by
  unfold as; authoring_scoped

theorem asVoid_scoped {effect : Src NativeOp} (h0 : effect.Scoped) :
    ((asVoid effect) : Src NativeOp).Scoped := by
  unfold asVoid; authoring_scoped

theorem tapContinuation_scoped (answer : String) {effect : Src NativeOp} {continuation : Src NativeOp} (h0 : effect.Scoped) (h1 : continuation.Scoped) :
    ((tapContinuation answer effect continuation) : Src NativeOp).Scoped := by
  unfold tapContinuation; authoring_scoped

theorem tapEffect_scoped {effect : Src NativeOp} {effect1 : Src NativeOp} (h0 : effect.Scoped) (h1 : effect1.Scoped) :
    ((tapEffect effect effect1) : Src NativeOp).Scoped := by
  unfold tapEffect; authoring_scoped

theorem ensuring_scoped {effect : Src NativeOp} {effect1 : Src NativeOp} (h0 : effect.Scoped) (h1 : effect1.Scoped) :
    ((ensuring effect effect1) : Src NativeOp).Scoped := by
  unfold ensuring; authoring_scoped

theorem matchCause_scoped (value : String) (cause : String) {effect : Src NativeOp} {onValue : TermSrc} {onCause : TermSrc} (h0 : effect.Scoped) (h1 : onValue.Scoped) (h2 : onCause.Scoped) :
    ((matchCause value cause effect onValue onCause) : Src NativeOp).Scoped := by
  unfold matchCause; authoring_scoped

theorem matchCauseEffect_scoped (value : String) (cause : String) {effect : Src NativeOp} {onValue : Src NativeOp} {onCause : Src NativeOp} (h0 : effect.Scoped) (h1 : onValue.Scoped) (h2 : onCause.Scoped) :
    ((matchCauseEffect value cause effect onValue onCause) : Src NativeOp).Scoped := by
  unfold matchCauseEffect; authoring_scoped

theorem yieldNow_scoped  :
    ((yieldNow) : Src NativeOp).Scoped := by
  unfold yieldNow; authoring_scoped

theorem forkChildDefault_scoped {effect : Src NativeOp} (h0 : effect.Scoped) :
    ((forkChildDefault effect) : Src NativeOp).Scoped := by
  unfold forkChildDefault; authoring_scoped

theorem forkDetachDefault_scoped {effect : Src NativeOp} (h0 : effect.Scoped) :
    ((forkDetachDefault effect) : Src NativeOp).Scoped := by
  unfold forkDetachDefault; authoring_scoped

theorem forkInDefault_scoped {effect : Src NativeOp} {scope : TermSrc} (h0 : effect.Scoped) (h1 : scope.Scoped) :
    ((forkInDefault effect scope) : Src NativeOp).Scoped := by
  unfold forkInDefault; authoring_scoped

theorem forkScopedDefault_scoped {effect : Src NativeOp} (h0 : effect.Scoped) :
    ((forkScopedDefault effect) : Src NativeOp).Scoped := by
  unfold forkScopedDefault; authoring_scoped

theorem releaseOne_scoped (resource : String) {effect : Src NativeOp} {release : Src NativeOp} (h0 : effect.Scoped) (h1 : release.Scoped) :
    ((releaseOne resource effect release) : Src NativeOp).Scoped := by
  unfold releaseOne; authoring_scoped

/-! ## Receipts -/



#print axioms tapEffect_scoped
#print axioms tapContinuation_scoped
#print axioms releaseOne_scoped
#print axioms ensuring_scoped

end Effect4.Program.Authoring.Forms
