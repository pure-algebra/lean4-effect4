import Effect4.Laws.Program.Typed.Residual
import Test.Api.ExternalContract
/-!
E4-SCHED-CE-013: a protocol row whose postcondition is `True` refuses every program that
feeds that row's answer into its result. The judgment demands a typed continuation for every
admitted answer, including answers of the wrong type. `denoteR` emits exactly that shape for
`async` (sleep, deferred await, external calls), the join-all waits, child snapshots, races,
generators, loops, scopes, the fuel frontier, and every performed store operation; the rows
are listed in `docs/research/2026-09-23-typed-state-admission-audit.md`. The witnesses below
are four of them, at every world and root.

E4-SCHED-CE-014: source admission (`PointTyped`) checks a body against the empty host-row
table, so a forked, scoped or masked body that performs a host row is refused although the
checker admits it under the program's table.

Finite controls tie the witnesses to generated code: the loaded code of a checker-typed
`sleep(1)` has the refused shape.
-/
set_option autoImplicit false
namespace Test.Counterexamples.TrivialPosts
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-! ## CE-013 -/

/-- The code `denoteR` gives `sleep(1)`: an async registration whose answer is the leaf. -/
def sleepCode : RProgram :=
  .vis (.inr (.async (.store (.registerSleep (ClockMillis.ofNat 1))) (Val.nat 1))) Effects.Program.pure

def sleeping : NativeEff := .perform .sleep (.lit (.nat 1))
#guard typeOf nativeSignature sleeping = some (EffTy.pure .unit)

/-- The loaded root code of `sleep(1)` is an async registration answering into the leaf. -/
def loadedIsAsyncLeaf : Bool :=
  match (loadR sleeping 20 20).fiber? Api.root with
  | some f => match f.frame.current with
    | .vis (.inr (.async (.store (.registerSleep _)) _)) _ => true
    | _ => false
  | none => false
#guard loadedIsAsyncLeaf

theorem sleep_code_untypable (root : NativeEff) (w : W) :
    ¬ TypedProg root w (EffTy.pure .unit) sleepCode := by
  intro h
  cases h with
  | fiber _ _ _ _ _ _ next =>
    exact Bool.noConfusion (TypedProg.pure_inv (next w (leHost_refl w) (.success (.nat 5)) trivial)).1

/-- The join-all park code `interpR` installs. -/
def joinAll (targets : List FiberId) : RProgram :=
  .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)

theorem joinAll_untypable (root : NativeEff) (w : W) (targets : List FiberId) :
    ¬ TypedProg root w (EffTy.pure .nat) (joinAll targets) := by
  intro h
  cases h with
  | fiber _ _ _ _ _ _ next =>
    exact Bool.noConfusion (TypedProg.pure_inv (next w (leHost_refl w) (Val.bool true) trivial)).1

/-- A performed store operation, in the shape `denoteR`'s `.perform` arm emits for a sync row. -/
def modifyCode (cell : RefKey) (f : FnName) : RProgram :=
  .vis (.inl (.refModify cell f)) fun v => .pure (.success v)

theorem modify_untypable (root : NativeEff) (w : W) (cell : RefKey) (f : FnName) :
    ¬ TypedProg root w (EffTy.pure .unit) (modifyCode cell f) := by
  intro h
  obtain ⟨_, _, next⟩ := TypedProg.store_inv h
  exact Bool.noConfusion (TypedProg.pure_inv (next w (leHost_refl w) (.nat 5) trivial)).1

/-- The fuel frontier `denoteR` emits: a live frontier is never answered, yet its `True` post
demands a typed leaf for every exit. -/
theorem frontier_untypable (root : NativeEff) (w : W) (reason : PendingReason) (at_ : Point) :
    ¬ TypedProg root w (EffTy.pure .unit) (.vis (.inr (.frontier reason at_)) Effects.Program.pure) := by
  intro h
  cases h with
  | fiber _ _ _ _ _ _ next =>
    exact Bool.noConfusion (TypedProg.pure_inv (next w (leHost_refl w) (.success (.nat 5)) trivial)).1

/-- A construction whose continuation returns a completed fiber's exit, as `inlineYield`'s
`awaitFiber` arm does for a join after a bind (`DenoteR.lean:511-512`): the `True` post admits
any completed list, so the join's result is untyped (audit A9). A continuation that ignores the
list, as a bind without a join does, is not refused. -/
def joinsCompleted : RProgram :=
  .vis (.inr .construction) fun completed => .pure (match completed with
    | (_, ex) :: _ => ex
    | [] => .success (.nat 0))

theorem construction_read_untypable (root : NativeEff) (w : W) :
    ¬ TypedProg root w (EffTy.pure .nat) joinsCompleted := by
  intro h
  cases h with
  | fiber _ _ _ _ _ _ next =>
    exact Bool.noConfusion
      (TypedProg.pure_inv (next w (leHost_refl w) [(⟨1⟩, .success (.bool true))] trivial)).1

/-! ## CE-014 -/

/-- A body performing host row 0 (`query`, answering `nat`) of the external-row battery. -/
def hostBody : NativeEff := .perform (.external 0) (.lit (.nat 1))
def checks (r : Except TypeRefusal EffTy) : Bool := match r with | .ok _ => true | .error _ => false
-- The checker admits the body under its table and refuses it under the empty table that
-- `PointTyped` uses.
#guard checks (Checker.check (nativeSignature Test.Api.ExternalContract.table) [] [] hostBody)
#guard !checks (Checker.check (nativeSignature []) [] [] hostBody)

#print axioms sleep_code_untypable
#print axioms joinAll_untypable
#print axioms modify_untypable
#print axioms frontier_untypable
#print axioms construction_read_untypable
end Test.Counterexamples.TrivialPosts
