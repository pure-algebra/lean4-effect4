import Effect4.Laws.Program.Handles.Term
import Effect4.Laws.Program.Typed.Edits

/-!
Controls for the raw-frame term preservation helper; definitions pinned in the receipt.
Concept 4; helper of M7.exitHandles_valid's registered-frame producer invariant.
These exercise the actual evaluator and raw Store.Val.handles. They do not prove
machine-wide registration or reachable exit validity. The retained receipt distinguishes compilation from complete machine preservation.
-/
set_option autoImplicit false
namespace RawHandleControls
open Effect4 Effect4.Machine Effect4.Program

-- Byte 6 is deliberately unregistered; byte 7 is the external-handle kind.
#guard HandleKind.ofByte? 6 = none
#guard HandleKind.ofByte? 7 = some .external
#guard evalTerm [.handle 6 9] (.var 0) = some (.handle 6 9)
#guard Store.Val.handles (.handle 6 9) = [(6, 9)]
#guard Val.keys (.handle 6 9) = []
#guard evalTerm [.handle 7 9] (.app "some" (.cons (.var 0) .nil)) =
  some (.some (.handle 7 9))
#guard Store.Val.handles (.some (.handle 7 9)) = [(7, 9)]

-- Repetition is allowed: the proposed relation is membership subset, not multiplicity.
#guard evalTerms [.handle 6 9] (.cons (.var 0) (.cons (.var 0) .nil)) =
  some [.handle 6 9, .handle 6 9]

-- Actual snapshots reconstruct exactly the stored fiber handles; malformed ones refuse.
#guard nativeAtom "get" [Val.fibers [⟨2⟩], .nat 0] = some (.some (Val.fiber ⟨2⟩))
#guard nativeAtom "get" [Value.fiberSnapshot (.list [.handle 6 9]), .nat 0] = none
#guard nativeAtom "get" [.list [.handle 6 9], .nat 0] = some (.some (.handle 6 9))

-- A successful option-none is different from an invalid operation's refusal.
#guard nativeAtom "get" [.list [.handle 6 9], .nat 1] = some .none
#guard nativeAtom "strings" [.handle 6 9] = none
#guard nativeAtom "__unknown_raw_handle_atom__" [.handle 6 9] = none
#guard nativeAtom "fst" [.pair (.handle 6 9) .unit] = none

-- Cause queries either return handle-free error data or refuse a malformed cause.
#guard nativeAtom "causeError" [Val.exitErr (Cause.fail (.tag 9))] = some (.some (.nat 9))
#guard nativeAtom "causeError" [Val.exitOk (.handle 6 9)] = some .none
#guard nativeAtom "causeError" [Value.exitErr (.handle 6 9)] = none

/-- Reject the overstrong claim: a term can copy an unregistered raw handle from its
input environment. This proves no defect in the intended conditional subset law. -/
theorem not_every_term_output_registered :
    ¬ (∀ (env : List Val) (t : Term) (v : Val), evalTerm env t = some v →
      ∀ h ∈ Store.Val.handles v, (HandleKind.ofByte? h.1).isSome = true) := by
  intro all
  have impossible := all [.handle 6 9] (.var 0) (.handle 6 9) rfl
    (6, 9) List.mem_cons_self
  change false = true at impossible
  cases impossible

/-- The ordinary external kind is retained exactly by the same variable evaluator. -/
theorem external_handle_variable :
    evalTerm [.handle 7 9] (.var 0) = some (.handle 7 9) ∧
      ∀ h ∈ Store.Val.handles (.handle 7 9), (HandleKind.ofByte? h.1).isSome = true := by
  refine ⟨rfl, ?_⟩
  intro h member
  cases member with
  | head => rfl
  | tail _ member => cases member

end RawHandleControls

/-- The exported helper supplies the existing predicate without a new invariant definition. -/
example (t : Effect4.Program.Term) (env : List Effect4.Machine.Val) (v : Effect4.Machine.Val)
    (registered : ∀ x ∈ env, Effect4.Program.Typed.HandlesRegistered x)
    (evaluates : Effect4.Program.evalTerm env t = some v) :
    Effect4.Program.Typed.HandlesRegistered v :=
  Effect4.Program.RawHandles.evalTerm_registered t env v registered evaluates
