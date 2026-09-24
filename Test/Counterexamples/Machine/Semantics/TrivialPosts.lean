import Effect4.Laws.Program.Typed.Residual
import Test.Api.ExternalContract
/-!
E4-SCHED-CE-013 and E4-SCHED-CE-014, repaired (typed-state admission audit §6, 2026-09-23).

CE-013: a protocol row whose postcondition was `True` refused every program feeding the row's
answer into its result. The original witnesses (`sleep_code_untypable`, `joinAll_untypable`,
`modify_untypable`, `frontier_untypable`, `construction_read_untypable`) are retained at
`7401afc6`; after the repair each row certifies its answer's type, so the same shapes are the
positive controls below. The loaded code of a checker-typed `sleep(1)` still has the shape
`sleepCode` has (`loadedIsAsyncLeaf`).

CE-014: source admission checked a body under the empty host-row table. It now reads the
source's table (`ProgramSource`); the empty-table refusal below is the checker's, retained as
the historical attack, and `hostBody_admitted` is its repair.
-/
set_option autoImplicit false
namespace Test.Counterexamples.TrivialPosts
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-! ## CE-013, repaired -/

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

/-- The timer's answer is certified at `unit`. -/
theorem sleep_code_typed (root : ProgramSource) (w : W) :
    TypedProg root w (EffTy.pure .unit) sleepCode :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .unit) (Ty.sub_refl _)
    (fun _ _ _ hpost => TypedProg.pure hpost)

/-- The join-all park code `interpR` installs. -/
def joinAll (targets : List FiberId) : RProgram :=
  .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)

/-- Certified at the list of the targets' exits, read through the fiber table. -/
theorem joinAll_typed (root : ProgramSource) (w : W) (targets : List FiberId) (a e : Ty)
    (declared : ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧ fty.answer.sub a = true ∧
      fty.error.sub e = true) :
    TypedProg root w (EffTy.pure (.list (.exitOf a e))) (joinAll targets) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (Ty.list (.exitOf a e)) ⟨a, e, rfl, declared⟩
    (fun w' _ ans hpost => TypedProg.pure (strongExit_success w' _ ans hpost))

/-- A performed store operation, in the shape `denoteR`'s `.perform` arm emits for a sync row. -/
def modifyCode (cell : RefKey) (f : FnName) : RProgram :=
  .vis (.inl (.refModify cell f)) fun v => .pure (.success v)

/-- `Ref.modify` answers a `nat`, the row's answer column. -/
theorem modify_typed (root : ProgramSource) (w : W) (cell : RefKey) (f : FnName)
    (declared : ∃ ty, w.Ρ cell = some ty) :
    TypedProg root w (EffTy.pure .nat) (modifyCode cell f) := by
  refine TypedProg.store () declared ?_
  intro w' _ ans hpost
  obtain ⟨n, rfl⟩ := hpost
  exact TypedProg.pure (strongExit_success w' _ _ ⟨rfl, trivial, fun _ mem => by cases mem⟩)

/-- The fuel frontier is never answered, so its continuation owes nothing. -/
theorem frontier_typed (root : ProgramSource) (w : W) (ty : EffTy) (reason : PendingReason)
    (at_ : Point) :
    TypedProg root w ty (.vis (.inr (.frontier reason at_)) Effects.Program.pure) :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial (fun _ _ _ hpost => nomatch hpost)

/-- A callback that reads one fiber's completed exit, as `inlineYield`'s `awaitFiber` arm does
for a join after a bind (`DenoteR.lean:511-512`); an absent fiber answers an interruption. -/
def joinsFiber (target : FiberId) : RProgram :=
  .vis (.inr .construction) fun completed =>
    match completed.find? (·.1 == target) with
    | some (_, ex) => .pure ex
    | none => .pure (.failure (Cause.interrupt none))

/-- The completed exits are typed at their fibers' declared types. -/
theorem joinsFiber_typed (root : ProgramSource) (w : W) (target : FiberId) (ty : EffTy)
    (declared : ∀ w', w.leHost w' → w'.Γ target = some ty) :
    TypedProg root w ty (joinsFiber target) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial ?_
  intro w' hle ans hpost
  cases hfind : ans.find? (·.1 == target) with
  | none => exact TypedProg.pure (strongExit_of_clean w' ty _ rfl)
  | some entry =>
    obtain ⟨id, ex⟩ := entry
    have mem := List.mem_of_find?_eq_some hfind
    have hit := List.find?_some hfind
    have same : id = target := beq_iff_eq.mp hit
    obtain ⟨ty', hΓ, typed⟩ := hpost (id, ex) mem
    rw [same, declared w' hle] at hΓ
    cases hΓ
    exact TypedProg.pure typed

/-! ## CE-014, repaired -/

/-- A body performing host row 0 (`query`, answering `nat`) of the external-row battery. -/
def hostBody : NativeEff := .perform (.external 0) (.lit (.nat 1))
def checks (r : Except TypeRefusal EffTy) : Bool := match r with | .ok _ => true | .error _ => false
-- The attack: the checker admits the body under its table and refuses it under the empty one.
#guard checks (Checker.check (nativeSignature Test.Api.ExternalContract.table) [] [] hostBody)
#guard !checks (Checker.check (nativeSignature []) [] [] hostBody)

/-- The repair: source admission reads the source's own table. -/
theorem hostBody_checks :
    Checker.check (nativeSignature Test.Api.ExternalContract.table) [] [] hostBody =
      .ok (EffTy.pure .nat) := by decide +kernel

theorem hostBody_admitted (w : W) :
    PointTyped ⟨hostBody, Test.Api.ExternalContract.table⟩ w (rootPoint 20) (EffTy.pure .nat) :=
  ⟨hostBody, [], rfl, hostBody_checks, rfl, fun _ _ _ h => nomatch h⟩

#print axioms sleep_code_typed
#print axioms joinAll_typed
#print axioms modify_typed
#print axioms frontier_typed
#print axioms joinsFiber_typed
#print axioms hostBody_admitted
end Test.Counterexamples.TrivialPosts
