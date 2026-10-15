import Effect4.Laws.Program.CodeClosure.Slots
import Effect4.Laws.Program.AnswerSlots.Points

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: stable native syntax retains the root bindings used by the crew log proofs.
Reach: existing code, continuation names, operations, program names and finalizer captures.
Limit: this annotation supplies no allocation, acquired identity or history proof.
Consumer: the answer-flow stable code class for Workers and QueueWorkers.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The leading-binding instance of the shared slot annotation. -/
abbrev FinAt (bindings : List Val) :=
  CodeClosure.Slots.FinAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev OpAt (bindings : List Val) :=
  CodeClosure.Slots.OpAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev ProgAt (bindings : List Val) :=
  CodeClosure.Slots.ProgAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev StoreNameAt (bindings : List Val) :=
  CodeClosure.Slots.StoreNameAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev StoreActionAt (bindings : List Val) :=
  CodeClosure.Slots.StoreActionAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev StoreThunkAt (bindings : List Val) :=
  CodeClosure.Slots.StoreThunkAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev RegionAt (bindings : List Val) :=
  CodeClosure.Slots.RegionAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev NameAt (bindings : List Val) :=
  CodeClosure.Slots.NameAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The leading-binding instance of the shared slot annotation. -/
abbrev ThunkAt (bindings : List Val) :=
  CodeClosure.Slots.ThunkAt (fun p => Prefix bindings p.env) (Prefix bindings)

/-- The native code graph retains leading bindings in every delayed source-bearing field. -/
def CodeAt (bindings : List Val) : NCode → Prop
  | .sync thunk | .suspend thunk | .withFiber thunk => ThunkAt bindings thunk
  | .iterator name _ | .whileLoop name _ | .asyncFinalizer name => NameAt bindings name
  | .onSuccess body name | .onFailure body name | .onExit body name _ =>
    CodeAt bindings body ∧ NameAt bindings name
  | .onSuccessConst body next => CodeAt bindings body ∧ CodeAt bindings next
  | .onSuccessAndFailure body success failure =>
    CodeAt bindings body ∧ NameAt bindings success ∧ NameAt bindings failure
  | .exitFrame body => CodeAt bindings body
  | .async register _ cancel => NameAt bindings register ∧ ∀ name ∈ cancel, NameAt bindings name
  | _ => True
/-- The existing leading-binding predicate is the shared generated runtime-code fold.
Consumer: the common compiler and callback closure. -/
theorem codeAt_fold (bindings : List Val) (code : NCode) :
    CodeAt bindings code =
      cata_prim (CodeClosure.codeAlg (NameAt bindings) (ThunkAt bindings)) code := by
  let hom : PrimHom (CodeClosure.codeAlg (NameAt bindings) (ThunkAt bindings)) := by
    refine ⟨CodeAt bindings, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; rfl
  exact hom_eq_cata_prim hom code

end Effect4.Program.AnswerSlots
