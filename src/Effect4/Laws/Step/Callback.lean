import Effect4.Step.Callback
import Effect4.Laws.Step
import Effect4.Laws.Step.Scope
import Effect4.Laws.Step.Waiting

/-!
# Reading and typing a captured step callback

Placement: helpers of step-language-sound under R10 and step-language-typed under R4.
Consumers are Ref callback agreement and the typing of Ref and SynchronizedRef callers.
Reading retains one inserted binder, aligned caller scope, and successful captured source readings.
Typing also covers appended wrapper slots under the existing typed-scope reach premise.
The callback term additionally requires Step.canonical or Step.Facts and its identity facts.
These laws establish no source admission, allocation, scheduling, host callback, or whole run.
-/

set_option autoImplicit false
namespace Effect4.Modules.Step
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model

/-- Relocation preserves typing after arbitrary appended slots.
Helper of freeze_kept and callback_capture_types.
Consumers: Ref callback typing and SynchronizedRef.modify_answers. -/
theorem relocate_types {Op : Type} (sig : Signature Op) (before more : List Ty)
    (const : Bool) (term : Term) :
    argTy sig (before ++ more) const (relocate before.length more.length term) =
      argTy sig before const term := by
  induction more with
  | nil => simp only [List.append_nil, List.length_nil, relocate]
  | cons X more ih =>
    simp only [List.length_cons, relocate]
    rw [argTy_weaken, ih]

/-- Reached scopes append exactly their newly introduced slots.
Helper of freeze_kept, consumed by SynchronizedRef.modify_answers. -/
theorem reached_slots {s t : TypedScope} (reach : s.Reaches t) :
    ∃ more, t.types = s.types ++ more ∧ t.env.names.length = s.env.names.length + more.length := by
  induction reach with
  | here => exact ⟨[], (List.append_nil _).symm, (Nat.add_zero _).symm⟩
  | @push t stem X _ ih =>
    obtain ⟨more, types, names⟩ := ih
    refine ⟨more ++ [X], ?_, ?_⟩
    · change t.types ++ [X] = _
      rw [types, List.append_assoc]
    · change (t.env.push [_]).names.length = _
      simp only [Env.push_length, List.length_append, List.length_cons, List.length_nil, names,
        Nat.add_assoc]
  | @push2 t first second X Y _ ih =>
    obtain ⟨more, types, names⟩ := ih
    refine ⟨more ++ [X, Y], ?_, ?_⟩
    · change t.types ++ [X, Y] = _
      rw [types, List.append_assoc]
    · change (t.env.push [_, _]).names.length = _
      simp only [Env.push_length, List.length_append, List.length_cons, List.length_nil, names,
        Nat.add_assoc]

/-- A caller's typed source remains typed after freezing at its original path.
Consumer: SynchronizedRef.modify_answers under R4.
No capture stability premise is required. -/
theorem freeze_kept {sig : Signature NativeOp} {source : TermSrc} {s : TypedScope}
    {path : List Nat} {T : Ty} (typed : TypesEach sig source s.env path s.types T) :
    Kept sig (freeze source s.env path) s T := by
  intro t reach innerPath const
  obtain ⟨more, types, names⟩ := reached_slots reach
  obtain ⟨term, tree, checked⟩ := typed const
  refine ⟨relocate s.types.length more.length term, ?_, ?_⟩
  · simp only [freeze, tree, names, Nat.add_sub_cancel_left, Except.map, s.depth]
  · rw [types, relocate_types]
    exact checked

/-- Freezing and one-slot relocation retain the original capture's reading.
Helper of callback_term_reads, serving step-language-sound and Ref callback agreement. -/
theorem callback_capture_reads {source : TermSrc} {env : Env} {path : List Nat}
    {vals : List Store.Val} {v : Store.Val}
    (depth : vals.length = env.names.length) (reads : Reads source env path vals v)
    (name : String) (current : Store.Val) :
    Reads (callbackCapture source env path) (env.push [name]) path (vals ++ [current]) v := by
  obtain ⟨term, tree, value⟩ := reads
  refine ⟨term.weaken env.names.length, ?_, ?_⟩
  · simp only [callbackCapture, relocate, tree, Except.map]
  · rw [← depth]
    have lifted := evalTerm_weaken vals [] current term
    simp only [List.append_nil] at lifted
    rw [lifted]
    exact value

/-- Freezing and one-slot relocation retain the original capture's type.
Helper of callback_term_types, serving step-language-typed and checked Ref callers. -/
theorem callback_capture_types {Op : Type} {sig : Signature Op} {source : TermSrc}
    {env : Env} {path : List Nat} {types : List Ty} {T : Ty}
    (depth : types.length = env.names.length)
    (typed : TypesEach sig source env path types T) (name : String) (C : Ty) :
    TypesEach sig (callbackCapture source env path) (env.push [name]) path (types ++ [C]) T := by
  intro const
  obtain ⟨term, tree, checked⟩ := typed const
  refine ⟨term.weaken env.names.length, ?_, ?_⟩
  · simp only [callbackCapture, relocate, tree, Except.map]
  · rw [← depth]
    have lifted := relocate_types sig types [C] const term
    simp only [List.length_cons, List.length_nil, relocate] at lifted
    rw [lifted]
    exact checked

/-- The callback inputs read the current value and the caller's original captures.
Helper of callback_term_reads; no capture stability under the new binder is assumed. -/
theorem callback_sources_reads {L : Leaves} {C : Ty} {Γ : List Ty} {vs : Inputs L Γ}
    {captures : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat}
    {vals : List Store.Val} (depth : vals.length = env.names.length)
    (inputs : ∀ {t : Ty} (x : Input Γ t),
      Reads (captures x) env path vals ((imageAt L t).toVal (x.get vs)))
    (name : String) (cell : CarrierAt L C) {current : TermSrc}
    (cellReads : Reads current (env.push [name]) path
      (vals ++ [(imageAt L C).toVal cell]) ((imageAt L C).toVal cell)) :
    ∀ {t : Ty} (x : Input (C :: Γ) t),
      Reads (callbackSources captures env path current x) (env.push [name]) path
        (vals ++ [(imageAt L C).toVal cell]) ((imageAt L t).toVal (x.get (cell, vs)))
  | _, .here _ _ => cellReads
  | _, .there _ x => callback_capture_reads depth (inputs x) name _

/-- The callback inputs type at the current value and the caller's original capture types.
Helper of callback_term_types; capture stability is obtained by relocation. -/
theorem callback_sources_types {Op : Type} {sig : Signature Op} {C : Ty} {Γ : List Ty}
    {captures : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (inputs : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (captures x) env path types t)
    (name : String) {current : TermSrc}
    (cellTyped : TypesEach sig current (env.push [name]) path (types ++ [C]) C) :
    ∀ {t : Ty} (x : Input (C :: Γ) t),
      TypesEach sig (callbackSources captures env path current x) (env.push [name]) path
        (types ++ [C]) t
  | _, .here _ _ => cellTyped
  | _, .there _ x => callback_capture_types depth (inputs x) name C

/-- A callback term reads its step's carrier value with the original captures.
Consumer: Ref callback agreement, a helper of step-language-sound under R10. -/
theorem callback_term_reads {L : Leaves} {C R : Ty} {Γ : List Ty}
    (body : Step (C :: Γ) R) {vs : Inputs L Γ}
    {captures : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat}
    {vals : List Store.Val} (depth : vals.length = env.names.length)
    (inputs : ∀ {t : Ty} (x : Input Γ t),
      Reads (captures x) env path vals ((imageAt L t).toVal (x.get vs)))
    (name : String) (cell : CarrierAt L C) {current : TermSrc}
    (cellReads : Reads current (env.push [name]) path
      (vals ++ [(imageAt L C).toVal cell]) ((imageAt L C).toVal cell))
    (canonical : body.canonical = true) (identity : body.IdentityFacts L := by trivial) :
    Reads (body.term (callbackSources captures env path current)) (env.push [name]) path
      (vals ++ [(imageAt L C).toVal cell]) ((imageAt L R).toVal (body.eval (Γ := C :: Γ) L (cell, vs))) := by
  exact sound L (Γ := C :: Γ) (cell, vs) (callback_sources_reads depth inputs name cell cellReads) body canonical
    (scope_of_alignment body (by
      simp only [List.length_append, List.length_cons, List.length_nil, Env.push_length, depth])) identity

/-- A callback term has its step's indexed type with typed caller captures.
Consumer: checked Ref callers, a helper of step-language-typed under R4. -/
theorem callback_term_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {C R : Ty} {Γ : List Ty} (body : Step (C :: Γ) R)
    {captures : {t : Ty} → Input Γ t → TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (inputs : ∀ {t : Ty} (x : Input Γ t), TypesEach sig (captures x) env path types t)
    (name : String) {current : TermSrc}
    (cellTyped : TypesEach sig current (env.push [name]) path (types ++ [C]) C)
    (facts : body.Facts) :
    TypesEach sig (body.term (callbackSources captures env path current)) (env.push [name]) path
      (types ++ [C]) R := by
  exact typed sig atoms (callback_sources_types depth inputs name cellTyped) body facts
    (scope_of_alignment body (by
      simp only [List.length_append, List.length_cons, List.length_nil, Env.push_length, depth]))

end Effect4.Modules.Step
