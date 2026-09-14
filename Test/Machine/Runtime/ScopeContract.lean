/-
Contract packet: `Test/contracts/scope.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until `src/Effect4/Machine/Scope.lean` declares the frozen surface.

Until 2026-09-13 every public declaration was also frozen here by a hand-typed
`#check (@name : proposition)` copy of its statement; those copies were retired, since a
statement lives in its theorem and its change is that file's diff. What remains is what
only this battery says: the guards over named programs and the counterexample theorems. Names are written
fully qualified; this module deliberately does not `open Effect4`.

Pinned source: `effect@4.0.0-rc.112` under `vendor/effect-4.0.0-rc.112/src/`.
Reading: `docs/effect-rc112-fiber-runtime.html` section 6.
-/

import Effect4.Machine.Exit
import Effect4.Machine.Scope

set_option autoImplicit false

namespace Test.Runtime.ScopeContract

universe u v

section StrategySurface

/-! S0: the two-value finalizer strategy label (census: scope.make,
scope.close-sequential, scope.close-parallel).

The strategy is a passive label. rc.112 does not attach a scheduler policy to
it: "parallel" is immediate daemon forks that inherit the closing fiber's mask.
This packet models no fiber, so it states only the alphabet. -/

#synth DecidableEq Effect4.FinalizerStrategy
#synth Repr Effect4.FinalizerStrategy

end StrategySurface

section StateSurface

/-! S1: the scope state machine (census: scope.states).

`κ` is the externally admitted finalizer-key alphabet — rc.112's `{}` object
identity. `φ` is the externally admitted finalizer-name alphabet: a finalizer
is a nominal key, never a stored Lean closure (DB-02). The three `open*`
constructors are exactly the three inhabited shapes of rc.112's `Open` record
under its own XOR invariant. -/

example {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ] [DecidableEq φ]
    [DecidableEq β] [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    DecidableEq (Effect4.ScopeState κ φ β ε δ ι α) :=
  inferInstance

/-! The materialised registration order of each state. -/

/-! `Empty` and `Closed` are not `Open`. -/

/-! The cleared inline slot is not the empty map: the next add lands in the
inline slot in the first case and in the map in the second. -/

end StateSurface

section ScopeSurface

/-! S2: the scope carrier and its observations (census: scope.states,
scope.make). -/

example {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ] [DecidableEq φ]
    [DecidableEq β] [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] :
    DecidableEq (Effect4.Scope κ φ β ε δ ι α) :=
  inferInstance

/-! A new scope starts Empty; the default strategy is sequential. -/

/-! rc.112 `scopeFinalizerCountUnsafe` answers zero for every non-Open scope. -/

/-! The rc.112 `{}` key freshness is refused, not modelled: an Effect4 key is a
value, so no minting function can distinguish two structurally equal keys. -/

end ScopeSurface

section TableSurface

/-! S3: the keyed insertion-ordered finalizer table (census:
scope.add-finalizer, scope.remove-finalizer).

`tableInsert` is JavaScript `Map.prototype.set`: an existing key keeps its slot
and only its value changes; a new key is appended. `tableRemove` is
`Map.prototype.delete`. -/

end TableSurface

section AddSurface

/-! S4: registration (census: scope.add-finalizer, scope.add-after-closed). -/

/-! The first add stores an inline finalizer and its key. -/
/-! A cleared inline slot takes the next add inline again, not into a map. -/
/-! The second add promotes both into a map. -/
/-! `scopeAddFinalizerUnsafe` has no `Closed` arm at all. -/
/-! The promotion preserves insertion order. -/
/-! Registration appends, in every open shape. -/

/-! `scopeAddFinalizerExit`: register when open, run now when closed. -/

end AddSurface

section RemoveSurface

/-! S5: removal (census: scope.remove-finalizer). -/

/-! The inline slot is cleared when the key matches. -/
/-! An inline slot under a different key is untouched: there is no map to
delete from. -/
/-! A non-Open scope is left untouched. -/

end RemoveSurface

section CloseSurface

/-! S6: closing (census: scope.close-state-first, scope.close-lifo,
scope.close-sequential, scope.close-parallel, scope.close-merge,
rule.scope-close-lifo-state-first).

`run` is the externally supplied finalizer interpretation: it maps a nominal
finalizer and the closing exit to the finalizer's own exit. It is an argument,
never stored in the scope, so no Lean closure enters canonical scope data. -/

/-! Close is exactly the state flip paired with the finalizer result. -/
/-! State first: the resulting state cannot depend on what any finalizer does. -/
/-! Closing an already-Closed scope returns without running a finalizer. -/
/-! The sharp form of "state before finalizers": a finalizer that re-enters the
scope while it closes sees a Closed scope, so its own registration runs
immediately with the closing exit rather than being recorded. -/

/-! LIFO: finalizers are materialised in insertion order and iterated backwards. -/
/-! Every registered finalizer runs: a failing one does not abort the close. -/

/-! The three arms of `scopeCloseUnsafe`: nothing, the single finalizer's own
effect, and the `exitAsVoidAll` merge. -/
/-! Every failure reason of every finalizer reaches the closing cause, in close
order. -/
/-! The strategy label selects no observation this model exposes. The temporal
difference between "sequential" and "parallel" belongs to the fiber machine,
which this packet does not model; `docs/research/SCOPE-DAG.md` records the two rows that
stay `partial` because of it. -/

end CloseSurface

section ForkSurface

/-! S7: scope fork linkage (census: scope.fork-linkage).

The two linked finalizers are nominal: `closeChild` is the parent-side name of
`(exit) => scopeClose(child, exit)` and `detachFromParent` is the child-side
name of `(_) => scopeRemoveFinalizerUnsafe(parent, key)`. Interpreting those
two names needs a scope store, which this packet does not model; what is frozen
here is the linkage shape and the removal law that makes the detach work. -/

/-! A child of a Closed parent is born Closed with the parent's exit. -/
/-! One key, registered on both sides. -/
/-! Removing the shared key restores the parent's registration list exactly:
the child's own finalizer can detach it. -/

end ForkSurface

section BracketSurface

/-! S8: the two brackets, scope side only (census: scope.scoped,
scope.acquire-release).

`Scope.runScoped` carries rc.112's `scoped` name; `scoped` is a Lean keyword.
Neither bracket models the fiber context, the OnExit frame, or
`uninterruptibleMask`. -/

/-! `scoped` installs a fresh default-strategy scope and closes it with the
body's exit. -/

/-! `acquireRelease` registers the release only after a successful acquire. -/
/-! Acquiring against an already-closed ambient scope runs the release now. -/

end BracketSurface

section GroundChecks

/-! S9: small executable checks over closed alphabets. They are finite probes,
not laws; every law above is separately frozen. -/

abbrev Key := Nat
abbrev Finalizer := Nat
abbrev Err := Nat
abbrev Defect := Bool
abbrev Interruptor := Nat
abbrev Ann := Nat

abbrev GroundScope := Effect4.Scope Key Finalizer Unit Err Defect Interruptor Ann
abbrev GroundExit := Effect4.Exit Unit Err Defect Interruptor Ann

def failWith (error : Nat) : GroundExit :=
  Effect4.Exit.failure
    (Effect4.Cause.mk [Effect4.Reason.fail error Effect4.ReasonAnnotations.empty])

/-- Finalizer `0` succeeds, `1` and `2` fail with their error, `3` fails with
the empty cause. -/
def run : Finalizer -> GroundExit -> GroundExit
  | 0, _ => Effect4.Exit.void
  | 1, _ => failWith 1
  | 2, _ => failWith 2
  | 3, _ => Effect4.Exit.failure Effect4.Cause.empty
  | _, _ => Effect4.Exit.void

def emptyScope : GroundScope := Effect4.Scope.make Effect4.FinalizerStrategy.sequential
def oneScope : GroundScope := emptyScope.addUnsafe 10 0
def twoScope : GroundScope := oneScope.addUnsafe 20 1
def threeScope : GroundScope := twoScope.addUnsafe 30 2

/-! The first add is inline; the second promotes both into an ordered map. -/
example : oneScope.state = Effect4.ScopeState.openInline 10 0 := by decide
example : twoScope.state = Effect4.ScopeState.openMap [(10, 0), (20, 1)] := by decide
example : threeScope.finalizers = [(10, 0), (20, 1), (30, 2)] := by decide

/-! The last registered finalizer runs first. -/
example : threeScope.closeOrder = [2, 1, 0] := by decide

/-! A failing finalizer does not stop the ones that follow it. -/
example : (Effect4.Scope.closeExits run threeScope Effect4.Exit.void).length = 3 := by decide

/-! Every failure reason reaches one flat closing cause, in close order. -/
example :
    (Effect4.Scope.close run threeScope Effect4.Exit.void).snd =
      Effect4.Exit.failure
        (Effect4.Cause.mk
          [Effect4.Reason.fail 2 Effect4.ReasonAnnotations.empty,
            Effect4.Reason.fail 1 Effect4.ReasonAnnotations.empty]) := by
  decide

/-! Close writes the state and drops the registration list. -/
example :
    (Effect4.Scope.close run threeScope Effect4.Exit.void).fst.state =
      Effect4.ScopeState.closed Effect4.Exit.void := by
  decide
example : (Effect4.Scope.close run threeScope Effect4.Exit.void).fst.finalizers = [] := by
  decide

/-! A second close runs nothing. -/
example :
    Effect4.Scope.close run (Effect4.Scope.close run threeScope Effect4.Exit.void).fst
        (failWith 9) =
      ((Effect4.Scope.close run threeScope Effect4.Exit.void).fst, Effect4.Exit.void) := by
  decide

/-! The single-finalizer arm returns the finalizer's own exit, so an empty-cause
failure survives where `exitAsVoidAll` would have erased it. -/
example :
    Effect4.Scope.closeResult run (emptyScope.addUnsafe 10 3) Effect4.Exit.void =
      Effect4.Exit.failure Effect4.Cause.empty := by
  decide
example :
    Effect4.Exit.asVoidAll
        (Effect4.Scope.closeExits run (emptyScope.addUnsafe 10 3) Effect4.Exit.void) =
      Effect4.Exit.success () := by
  decide

/-! Adding to a closed scope runs the finalizer now, with the stored exit. -/
example :
    Effect4.Scope.addExit run (Effect4.Scope.close run oneScope (failWith 7)).fst 40 1 =
      ((Effect4.Scope.close run oneScope (failWith 7)).fst, failWith 1) := by
  decide

/-! Removing the inline slot leaves `openEmpty`: neither `empty` nor `openMap []`. -/
example : (oneScope.removeUnsafe 10).state = Effect4.ScopeState.openEmpty := by decide
example :
    (oneScope.removeUnsafe 10).state ≠
      (Effect4.ScopeState.empty :
        Effect4.ScopeState Key Finalizer Unit Err Defect Interruptor Ann) := by
  decide
example : (oneScope.removeUnsafe 10).state ≠ Effect4.ScopeState.openMap [] := by decide
example :
    ((oneScope.removeUnsafe 10).addUnsafe 50 0).state =
      Effect4.ScopeState.openInline 50 0 := by
  decide
example :
    (((twoScope.removeUnsafe 10).removeUnsafe 20).addUnsafe 50 0).state =
      Effect4.ScopeState.openMap [(50, 0)] := by
  decide

/-! Removal leaves an Empty or Closed scope untouched. -/
example : emptyScope.removeUnsafe 10 = emptyScope := by decide
example :
    (Effect4.Scope.close run oneScope Effect4.Exit.void).fst.removeUnsafe 10 =
      (Effect4.Scope.close run oneScope Effect4.Exit.void).fst := by
  decide

/-! A child of a Closed parent is born Closed with the parent's exit. -/
example :
    (Effect4.Scope.fork (Effect4.Scope.close run oneScope (failWith 7)).fst
        Effect4.FinalizerStrategy.parallel 99 1 2).snd =
      ({ strategy := Effect4.FinalizerStrategy.parallel,
          state := Effect4.ScopeState.closed (failWith 7) } : GroundScope) := by
  decide

/-! One shared key links the two scopes, and only that key detaches the parent. -/
example :
    (Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1 2).fst.finalizers =
      [(10, 0), (20, 1), (99, 1)] := by
  decide
example :
    (Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1 2).snd.finalizers =
      [(99, 2)] := by
  decide
example :
    ((Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1
        2).fst.removeUnsafe 99).finalizers = twoScope.finalizers := by
  decide
example :
    ((Effect4.Scope.fork twoScope Effect4.FinalizerStrategy.sequential 99 1
        2).fst.removeUnsafe 77).finalizers ≠ twoScope.finalizers := by
  decide

/-! `runScoped` and `acquireRelease`. -/
example :
    (Effect4.Scope.runScoped run ([] : List (Key × Finalizer)) (failWith 5) :
        GroundScope × GroundExit) =
      ({ strategy := Effect4.FinalizerStrategy.sequential,
          state := Effect4.ScopeState.closed (failWith 5) },
        Effect4.Exit.void) := by
  decide
example :
    (Effect4.Scope.runScoped run [(10, 0), (20, 1)] Effect4.Exit.void :
      GroundScope × GroundExit).snd = failWith 1 := by
  decide
example :
    Effect4.Scope.acquireRelease run oneScope 20 1 (Effect4.Exit.failure Effect4.Cause.empty) =
      (oneScope, Effect4.Exit.void) := by
  decide
example :
    (Effect4.Scope.acquireRelease run oneScope 20 1
      (Effect4.Exit.success ())).fst.finalizers = [(10, 0), (20, 1)] := by
  decide

/-! The strategy label changes no exit in this model. -/
example :
    (Effect4.Scope.close run
        { strategy := Effect4.FinalizerStrategy.parallel, state := threeScope.state }
        Effect4.Exit.void).snd =
      (Effect4.Scope.close run threeScope Effect4.Exit.void).snd := by
  decide

end GroundChecks

section AxiomReceipts

#print axioms Effect4.Scope.make_state
#print axioms Effect4.Scope.addUnsafe_finalizers
#print axioms Effect4.Scope.addExit_closed
#print axioms Effect4.Scope.removeUnsafe_inline_hit
#print axioms Effect4.Scope.close_state_independent_of_run
#print axioms Effect4.Scope.close_reentrant_add
#print axioms Effect4.Scope.close_idempotent
#print axioms Effect4.Scope.closeOrder_last_first
#print axioms Effect4.Scope.closeResult_single
#print axioms Effect4.Scope.closeResult_reasons
#print axioms Effect4.Scope.fork_closed_parent
#print axioms Effect4.Scope.fork_detach
#print axioms Effect4.Scope.runScoped_lifo
#print axioms Effect4.Scope.acquireRelease_registers

end AxiomReceipts

end Test.Runtime.ScopeContract
