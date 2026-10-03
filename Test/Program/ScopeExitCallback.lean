import Effect4.Laws.Program.Typed.Assembly

/-!
# Test.Program.ScopeExitCallback — the scope-exit marker at its run position only

Placement: semantics Concept 4 (the configuration invariant `I`), question `deliver_preserves`
and `loop_preserves`; decisions row 188 (a), `E4-TYPED-CE-034`. The historical refutation is
pinned unchanged at `docs/research/2026-10-02-claude-lead/witnesses/RawScopeExit.lean` (checked at
`53caad0f`): `TypedProg`'s general `scopeExit` constructor typed a raw marker of a present scope as
current code, and the counted step answers it `badShapeExit`. Row 188 (a) types the scope's exit
callback only at the run position of the guard the `scoped` arm installs (`TypedProg.scopedGuard`)
and of the slot that guard saves (`FrameAccepts.scopedResume`).

Controls:
1. `marker_untyped`, `input_refused`: the witness's raw marker is no typed code at any world and
   type, so its input (a running fiber on the marker, a queued `deliver`) is no typed
   configuration at any world. The same refusal holds with scope 0 present (`live`): it is the
   position, not presence, that is refused.
2. `scoped_code_typed`: the code the real producer installs, the `onExit false` guard over a body
   bound to the scope's exit callback, is typed at the same world (`scopedGuardBind_typed`), and
   its saved slot is the `scopedResume` arrow (`scoped_slot_accepted`).
3. `absent_scope_refused`: the same well-shaped code is not typed where scope 0 is absent (row
   156's presence, now read at the run position): an ordinary guard would have to type the raw
   callback, and the `scopedGuard` reading needs the scope.

These are constructed-configuration controls, not reachability claims; they prove neither
`step_deliver` nor `step_loop`.
-/

set_option autoImplicit false

namespace Test.Program.ScopeExitCallback
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Effect4.Program.Denote Effect4.Laws.Effects Contracts
abbrev W := Effect4.Program.Typed.World

def rootProgram : NativeEff := .succeed (.lit .unit)
def unitTy : EffTy := EffTy.pure .unit

/-- The witness's raw scope-exit marker of scope 0, as current code. -/
def marker : RProgram :=
  .vis (.inr (.scopeExit emptyCtx 0 (.success .unit))) (fun _ => .pure (.success .unit))

/-- A store holding one sequential scope, 0. -/
def scopeStore : Stores :=
  { Stores.empty with scopes := Stores.empty.scopes.make 0 .sequential, nextName := 1 }

def rootFiber : RFiber :=
  { RunFiber.make Api.root marker true (stores.budgetOf emptyCtx) emptyCtx with running := true }

def machine : RState :=
  { loadR rootProgram 20 20 with fibers := [rootFiber], nextId := 1, state := scopeStore }

def world : W :=
  { initialWorld unitTy with
    Γ := fun id => if id = Api.root then some unitTy else none
    state := scopeStore }

def commands : List RCmd := [.deliver Api.root false]

theorem live : ScopeLive world 0 := by decide

/-- Row 188 (a): the raw marker is no typed code, at any world and type. -/
theorem marker_untyped (w : W) (ty : EffTy) :
    ¬ TypedProg (rootProgram : ProgramSource) w ty marker := by
  intro typed
  cases typed with
  | fiber _ _ _ notScopeExit _ _ _ => exact absurd rfl (notScopeExit _ _ _)

/-- **The repaired red control**: the witness's input is no typed configuration at any world.
The queued `deliver` reads the running root's code (`ReadCode`), which would have to type the
raw marker. -/
theorem input_refused (w : W) :
    ¬ ConfigTyped (rootProgram : ProgramSource) unitTy w machine commands := by
  intro config
  have valid := config.machine.typed.1
  have member : rootFiber ∈ machine.fibers := List.mem_singleton_self _
  obtain ⟨ty, declared⟩ := Option.isSome_iff_exists.mp
    ((valid.fibers Api.root).mpr (List.mem_map_of_mem member))
  have reads : ReadsCode Api.root commands := ⟨false, Or.inr List.mem_cons_self⟩
  obtain ⟨tin, code, _, _⟩ :=
    (config.code rootFiber member rfl reads rfl ty declared).code_of_deliver List.mem_cons_self
  exact marker_untyped w tin code

/-- The producer's code: the `onExit false` guard over a unit body, bound to scope 0's exit
callback restoring the empty context (`evaluateFiberR`'s `.scoped` arm, `EvaluateR.lean`). -/
def scopedCode : RProgram :=
  (guardR (.onExit false) (.pure (.success .unit))).bind
    fun ex => .vis (.inr (.scopeExit emptyCtx 0 ex)) Effects.Program.pure

theorem empty_services (w : W) : ServicesFit w emptyCtx.services := servicesFit_empty w

/-- **The positive control**: at the witness's world, where scope 0 is present, the code the
`scoped` arm installs is typed. -/
theorem scoped_code_typed :
    TypedProg (rootProgram : ProgramSource) world unitTy scopedCode :=
  scopedGuardBind_typed (rootProgram : ProgramSource) (mid := unitTy) (j := Effects.Program.pure)
    (TypedProg.pure (ty := unitTy) (ex := .success .unit) ⟨trivial, trivial⟩) live
    (empty_services world) (fun _ _ _ hex => hex)

/-- The guard's saved slot is the `scopedResume` arrow from the body's type to the guard's. -/
theorem scoped_slot_accepted : ∃ mid : EffTy,
    FrameAccepts (TypedProg (rootProgram : ProgramSource)) ExitOk
      (frameProtocols (rootProgram : ProgramSource)) world mid unitTy
      (.resume (.onExit false) fun ex => .vis (.inr (.scopeExit emptyCtx 0 ex)) Effects.Program.pure) := by
  obtain ⟨mid, _, slot⟩ := TypedProg.guard_frame scoped_code_typed
  exact ⟨mid, slot⟩

/-- A world whose store holds no scope. -/
def absentWorld : W := initialWorld unitTy

/-- **The presence control** (rows 156 and 188 (a)): where scope 0 is absent the producer's
well-shaped code is not typed at any type. -/
theorem absent_scope_refused (ty : EffTy) :
    ¬ TypedProg (rootProgram : ProgramSource) absentWorld ty scopedCode := by
  intro typed
  rcases TypedProg.guard_inv typed with ⟨mid, body, run, _⟩ | ⟨_, mid, prev, sc, _, callback, live, _⟩
  · have payload : ExitOk absentWorld mid (.success .unit) :=
      unguard_payload_inv _ _ _ _ _ body
    have raw := run absentWorld (leHost_refl _) (.success .unit) ⟨rfl, payload⟩
    cases raw with
    | fiber _ _ _ notScopeExit _ _ _ => exact absurd rfl (notScopeExit _ _ _)
  · have same := callback (.success .unit)
    change some (emptyCtx, 0, Exit.success Val.unit) = some (prev, sc, Exit.success Val.unit) at same
    cases same
    exact absurd live (by decide)

end Test.Program.ScopeExitCallback
