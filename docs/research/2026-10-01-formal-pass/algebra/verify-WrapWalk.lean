import Effect4.Laws.Program.Typed.Stack

/-!
# verify-WrapWalk — ALG-01's amendment: wrapping the hook premises does not survive the walk

Adversarial verifier of seat ALGEBRA, formal pass, 2026-10-01. ALG-01's amendment says the hook
protocols may be "closed the same way, or wrapped as in P2", and that `popR_typed` is reused
"at the current world by reflexivity". Red control, over an abstract interpreter and hooks that
satisfy `HookLaws` (`hookLawsX`): the input stack `[.iter n1]` is accepted in P2's wrapped Kripke
form (`input_kripke`), today's one-world walk types the output (`walk_typed_one_world`), but the
output stack `[.iter n2]` admits no wrapped Kripke typing (`output_not_kripke`): the pushed
protocol's intermediate type is chosen per world by `HookLaws` (`Stack.lean:253-274`; the loop arm `:276-289`), `A` at the
initial world and `B` once cell 0 is declared. So the walk must be restated over Kripke stacks,
and the hook protocols themselves (`IteratorProtocol`, `LoopProtocol`, the async clause) closed
under later worlds in their definitions, so that `HookLaws` hands back a protocol that holds at
every later world with one intermediate type.
-/

set_option autoImplicit false

namespace FormalPass.AlgebraVerify.WrapWalk

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Program.Typed.Contracts

abbrev TW := Effect4.Program.Typed.World

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))

abbrev A : EffTy := EffTy.pure .unit
abbrev B : EffTy := EffTy.pure (.union .unit .unit)
abbrev T : EffTy := EffTy.pure .unit

/-- The resumed protocol's input type reads the world: `A` while cell 0 is undeclared, `B` after. -/
def midOf (w : TW) : EffTy :=
  match w.Ρ ⟨0⟩ with
  | none => A
  | some _ => B

def n1 : EffName := .abort
def n2 : EffName := .restore (.success Val.unit)

/-- An interpreter whose generator `n1` resumes with `unit` code under the name `n2`, and whose
`n2` is done with `unit`. -/
def interpX : RInterp :=
  { interpR refProg with
    iterNext := fun name _ => match name with
      | .abort => ([], .resume (.pure (.success Val.unit)) n2)
      | _ => ([], .done Val.unit) }

/-- Hooks: `n1` at `A → T` at every world; `n2` at `midOf w → T`. -/
def hooksX : FrameProtocols where
  asyncFinalizer _ _ _ _ := False
  iterator w tin tout name := match name with
    | .abort => tin = A ∧ tout = T
    | .restore _ => tin = midOf w ∧ tout = T
    | _ => False
  loop _ _ _ _ _ := False

theorem unit_fits_mid (w : TW) : FitsExit w (midOf w) (.success Val.unit) := by
  unfold midOf
  split
  · rw [fitsExit_success_iff]
    exact trivial
  · rw [fitsExit_success_iff]
    change Typed.Fits w Val.unit (.union .unit .unit)
    exact Or.inl trivial

/-- `popR_typed`'s hook premise holds for this interpreter and these hooks. -/
theorem hookLawsX : HookLaws (refProg : ProgramSource) interpX hooksX where
  asyncFinalizer _ _ _ _ h := h.elim
  iterator w tin tout name h := by
    cases name with
    | abort =>
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun v _ => ?_⟩
      exact ⟨midOf w, TypedProg.pure (unit_fits_mid w), rfl, rfl⟩
    | restore e =>
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun v _ => ?_⟩
      · unfold midOf
        split <;> rfl
      · show FitsExit w T (.success Val.unit)
        rw [fitsExit_success_iff]
        exact trivial
    | _ => exact h.elim
  loop _ _ _ _ _ h := h.elim

/-! ## P2's wrapped Kripke frame judgment (copied; probe files cannot import each other) -/

section Kripke

variable (TP : TW → EffTy → RProgram → Prop) (Ex : TW → EffTy → ExitV → Prop)
  (hooks : FrameProtocols)

inductive FrameAcceptsK (w : TW) : EffTy → EffTy → ScopeFrame → Prop
  | resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → kind.hasExitArm ex = true →
        TP w' tout (next ex))
      (skip : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → kind.hasExitArm ex = false →
        Ex w' tout ex) :
      FrameAcceptsK w tin tout (.resume kind next)
  | answer {tin tout : EffTy} (next : ExitV → RProgram)
      (run : ∀ w', w.leHost w' → ∀ ex, Ex w' tin ex → TP w' tout (next ex)) :
      FrameAcceptsK w tin tout (.answer next)
  | restoreMask (ty : EffTy) (flag : Bool) : FrameAcceptsK w ty ty (.restoreMask flag)
  | asyncFinalizer {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.asyncFinalizer w' tin tout name) :
      FrameAcceptsK w tin tout (.asyncFinalizer name)
  | finalizerMask (ty : EffTy) (flag : Bool) : FrameAcceptsK w ty ty (.finalizerMask flag)
  | iter {tin tout : EffTy} (name : EffName)
      (protocol : ∀ w', w.leHost w' → hooks.iterator w' tin tout name) :
      FrameAcceptsK w tin tout (.iter name)
  | loop {tin tout : EffTy} (name : EffName) (cursor : Val)
      (protocol : ∀ w', w.leHost w' → hooks.loop w' tin tout name cursor) :
      FrameAcceptsK w tin tout (.loop name cursor)

inductive StackAcceptsK (w : TW) : EffTy → EffTy → List ScopeFrame → Prop
  | nil (ty : EffTy) : StackAcceptsK w ty ty []
  | cons {tin middle tout : EffTy} {frame : ScopeFrame} {rest : List ScopeFrame}
      (head : FrameAcceptsK TP Ex hooks w tin middle frame)
      (tail : StackAcceptsK w middle tout rest) : StackAcceptsK w tin tout (frame :: rest)

end Kripke

/-! ## Two worlds: cell 0 undeclared, then declared -/

abbrev w0 : TW := initialWorld T

def s1 : Stores := { Stores.empty with refs := [Val.nat 0] }

def w1 : TW := { w0 with state := s1, Ρ := fun k => if k = ⟨0⟩ then some .nat else none }

theorem w0_le_w1 : w0.leHost w1 := by
  have hst : Stores.le w0.state w1.state :=
    ⟨Nat.zero_le _, Nat.le_refl _, fun _ h => h, Nat.le_refl _, fun _ h => h, Nat.le_refl _⟩
  have hrho : TableExtends w0.Ρ w1.Ρ := fun _ _ h => by cases h
  have hcells : CellCompatible w0 w1 := by
    unfold CellCompatible
    refine ⟨fun _ _ h => ?_, fun _ _ h => ?_⟩
    · unfold HeapTypedAt at h
      cases h.1
    · unfold PromiseTypedAt at h
      cases h.1
  exact ⟨⟨⟨fun _ h => h, hst⟩, fun _ _ h => h, fun _ _ h => h, hrho, hcells,
    fun _ _ _ h => h⟩, fun _ _ h => h⟩

theorem mid_w0 : midOf w0 = A := rfl

theorem mid_w1 : midOf w1 = B := by
  unfold midOf
  rw [show w1.Ρ ⟨0⟩ = some .nat by simp only [w1, if_pos]]

/-! ## The walk -/

def frame0 : RSaved :=
  { current := .pure (.success Val.unit), stack := [.iter n1], interruptible := true,
    interruptedCause := none, deferredInterrupt := false }

/-- The input frame is accepted in the wrapped Kripke form: its hook premise holds at every
later world (`n1`'s protocol does not read the world). -/
theorem input_kripke :
    StackAcceptsK (TypedProg (refProg : ProgramSource)) FitsExit hooksX w0 A T [.iter n1] :=
  .cons (.iter n1 (fun _ _ => ⟨rfl, rfl⟩)) (.nil T)

theorem input_exit : FitsExit w0 A (.success Val.unit) := by
  rw [fitsExit_success_iff]
  exact trivial

/-- The walk pushes `n2`'s frame over the resumed code. -/
theorem walk_output :
    popR interpX (.success Val.unit) [.iter n1] frame0 =
      ({ frame0 with current := .pure (.success Val.unit), stack := [.iter n2] }, none) := rfl

/-- Today's one-world walk lemma types the output (contrast). -/
theorem walk_typed_one_world :
    WalkTyped (refProg : ProgramSource) hooksX w0 T
      (popR interpX (.success Val.unit) [.iter n1] frame0) :=
  popR_typed (refProg : ProgramSource) interpX hooksX hookLawsX w0 [.iter n1] A T _ frame0
    (.cons (.iter n1 ⟨rfl, rfl⟩) (.nil T)) input_exit ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩

/-- **Red control: the walk's output has no wrapped Kripke typing.** Whatever intermediate type
the resumed code is given, `n2`'s frame would need it to be `midOf w'` at every later world,
which is `A` at `w0` and `B` at `w1`. So reusing `popR_typed` with wrapped hook premises does not
re-establish a Kripke stack after an iterator resume; the walk must be restated, and the hook
protocols themselves closed under later worlds (`HookLaws` then states the pushed protocol at
every later world with one intermediate type). -/
theorem output_not_kripke :
    ¬ ∃ tin', StackAcceptsK (TypedProg (refProg : ProgramSource)) FitsExit hooksX w0 tin' T
      [.iter n2] := by
  rintro ⟨tin', h⟩
  cases h with
  | cons head tail =>
    cases tail
    cases head with
    | iter name protocol =>
      have h0 : tin' = midOf w0 ∧ T = T := protocol w0 (leHost_refl w0)
      have h1 : tin' = midOf w1 ∧ T = T := protocol w1 w0_le_w1
      rw [mid_w0] at h0
      rw [mid_w1, h0.1] at h1
      cases h1.1

end FormalPass.AlgebraVerify.WrapWalk

#print axioms FormalPass.AlgebraVerify.WrapWalk.hookLawsX
#print axioms FormalPass.AlgebraVerify.WrapWalk.w0_le_w1
#print axioms FormalPass.AlgebraVerify.WrapWalk.input_kripke
#print axioms FormalPass.AlgebraVerify.WrapWalk.walk_output
#print axioms FormalPass.AlgebraVerify.WrapWalk.walk_typed_one_world
#print axioms FormalPass.AlgebraVerify.WrapWalk.output_not_kripke
