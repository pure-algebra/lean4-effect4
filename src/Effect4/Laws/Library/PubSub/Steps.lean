import Effect4.Library.PubSub.Steps
import Effect4.Laws.Library.PubSub.Data
import Effect4.Laws.Step

/-! Placement: pubsub-single-steps-agree, Translation Simulation, simulation, R10.
Six source readings connect stored pure steps to the independent natural-message model.
The equations cover arbitrary model states. Latest-source interpretation needs Model.Live.
Fresh names model source allocation without claiming runtime identity correspondence.
Typing readers serve step-language-typed, Store Typing, compatibility, R4.
No theorem here establishes waiting, delivery, backpressure, scopes, or whole-source agreement. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Effect4.PubSub
open Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Model (State)

namespace Model
section Reading
variable {env : Env} {path : List Nat} {vals : List Effect4.Store.Val}

/-- The empty source reads the independent model's initial image. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem initial_reads : Reads initialStep env path vals ((Modeled.image State).toVal initial) := by
  have reading := Step.sound (Γ := []) (env := env) (path := path) (vals := vals)
    (src := fun {t} (x : Input [] t) => nomatch x) Leaves.refused ()
    (fun {t} (x : Input [] t) => nomatch x) Data.initial rfl
  rw [initial_eval] at reading
  exact reading

/-- Helper of pubsub-single-steps-agree: observe the subscribe reply and next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem subscribe_reads (s : State) (id : Nat) {idSrc cellSrc : TermSrc}
    (ha : Reads idSrc env path vals (.nat id))
    (hs : Reads cellSrc env path vals ((Modeled.image State).toVal s))
    (fresh : Fresh s id) :
    Reads (subscribeStep idSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.unit (Modeled.image State)).toVal (subscribe s id)) := by
  have reading := Step.sound (Γ := Data.NamedInputs.types) Leaves.refused (named s id)
    (Input.reads_cons ha (Input.reads_cons hs Input.reads_nil)) Data.subscribe rfl
  rw [subscribe_eval s id fresh] at reading
  exact reading

/-- Helper of pubsub-single-steps-agree: observe the tryPublish reply and next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem tryPublish_reads (s : State) (message : Nat) {messageSrc cellSrc : TermSrc}
    (ha : Reads messageSrc env path vals (.nat message))
    (hs : Reads cellSrc env path vals ((Modeled.image State).toVal s)) :
    Reads (tryPublishStep messageSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.bool (Modeled.image State)).toVal (tryPublish s message)) := by
  have reading := Step.sound (Γ := Data.PublishInputs.types) Leaves.refused (publishing s message)
    (Input.reads_cons ha (Input.reads_cons hs Input.reads_nil)) Data.tryPublish rfl
  rw [tryPublish_eval] at reading
  exact reading

/-- Helper of pubsub-single-steps-agree: observe the poll reply and next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem poll_reads (s : State) (id : Nat) {idSrc cellSrc : TermSrc}
    (aligned : vals.length = env.names.length)
    (ha : Reads idSrc env path vals (.nat id))
    (hs : Reads cellSrc env path vals ((Modeled.image State).toVal s)) :
    Reads (pollStep idSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 (Effect4.Store.Image.option Effect4.Store.Image.nat) (Modeled.image State)).toVal (poll s id)) := by
  have reading := Step.sound (Γ := Data.NamedInputs.types) Leaves.refused (named s id)
    (Input.reads_cons ha (Input.reads_cons hs Input.reads_nil)) Data.poll rfl (Step.scope_of_alignment _ aligned)
  rw [poll_eval] at reading
  exact reading

/-- Helper of pubsub-single-steps-agree: observe the unsubscribe reply and next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem unsubscribe_reads (s : State) (id : Nat) {idSrc cellSrc : TermSrc}
    (aligned : vals.length = env.names.length)
    (ha : Reads idSrc env path vals (.nat id))
    (hs : Reads cellSrc env path vals ((Modeled.image State).toVal s)) :
    Reads (unsubscribeStep idSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.unit (Modeled.image State)).toVal (unsubscribe s id)) := by
  have reading := Step.sound (Γ := Data.NamedInputs.types) Leaves.refused (named s id)
    (Input.reads_cons ha (Input.reads_cons hs Input.reads_nil)) Data.unsubscribe rfl (Step.scope_of_alignment _ aligned)
  rw [unsubscribe_eval] at reading
  exact reading

/-- Helper of pubsub-single-steps-agree: observe the slide reply and next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem slide_reads (s : State) {cellSrc : TermSrc}
    (hs : Reads cellSrc env path vals ((Modeled.image State).toVal s)) :
    Reads (slideStep cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.unit (Modeled.image State)).toVal (slide s)) := by
  have reading := Step.sound (Γ := Data.CellInputs.types) Leaves.refused (input_values% (Data.CellInputs) (Leaves.refused) {cell := encoded s})
    (Input.reads_cons hs Input.reads_nil) Data.slide rfl
  rw [slide_eval] at reading
  exact reading

end Reading

/-- The six pure source observations agree with the independent model images.
This claim retains fresh subscribe names and aligned fold scopes.
Model.Live bounds its source interpretation; the formal equations do not require it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem single_steps_agree :
    (∀ (env : Env) (path : List Nat) (vals : List Effect4.Store.Val),
      Reads initialStep env path vals ((Modeled.image State).toVal initial)) ∧
    (∀ (s : State) (id : Nat) (idSrc cellSrc : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads idSrc env path vals (.nat id) →
      Reads cellSrc env path vals ((Modeled.image State).toVal s) →
      Fresh s id →
      Reads (subscribeStep idSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.unit (Modeled.image State)).toVal (subscribe s id))) ∧
    (∀ (s : State) (message : Nat) (messageSrc cellSrc : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads messageSrc env path vals (.nat message) →
      Reads cellSrc env path vals ((Modeled.image State).toVal s) →
      Reads (tryPublishStep messageSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.bool (Modeled.image State)).toVal (tryPublish s message))) ∧
    (∀ (s : State) (id : Nat) (idSrc cellSrc : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), vals.length = env.names.length →
      Reads idSrc env path vals (.nat id) →
      Reads cellSrc env path vals ((Modeled.image State).toVal s) →
      Reads (pollStep idSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 (Effect4.Store.Image.option Effect4.Store.Image.nat) (Modeled.image State)).toVal (poll s id))) ∧
    (∀ (s : State) (id : Nat) (idSrc cellSrc : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), vals.length = env.names.length →
      Reads idSrc env path vals (.nat id) →
      Reads cellSrc env path vals ((Modeled.image State).toVal s) →
      Reads (unsubscribeStep idSrc cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.unit (Modeled.image State)).toVal (unsubscribe s id))) ∧
    (∀ (s : State) (cellSrc : TermSrc) (env : Env) (path : List Nat)
      (vals : List Effect4.Store.Val), Reads cellSrc env path vals ((Modeled.image State).toVal s) →
      Reads (slideStep cellSrc) env path vals ((Effect4.Store.Image.tuple2 Effect4.Store.Image.unit (Modeled.image State)).toVal (slide s))) :=
  ⟨fun _ _ _ => initial_reads,
   fun s id _ _ _ _ _ ha hs fresh => subscribe_reads s id ha hs fresh,
   fun s message _ _ _ _ _ ha hs => tryPublish_reads s message ha hs,
   fun s id _ _ _ _ _ aligned ha hs => poll_reads s id aligned ha hs,
   fun s id _ _ _ _ _ aligned ha hs => unsubscribe_reads s id aligned ha hs,
   fun s _ _ _ _ hs => slide_reads s hs⟩

end Model

section Typing
variable {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
  {env : Env} {path : List Nat} {types : List Ty}
include atoms

/-- Consumer of step-language-typed, R4, at the empty construction. -/
@[semantics "store-typing" (requirement := R4)]
theorem initial_types : TypesEach sig initialStep env path types cellTy :=
  Step.typed_of_normal (Γ := []) sig atoms Input.types_nil Data.initial rfl

/-- Consumer of step-language-typed, R4, at the subscribe source. -/
@[semantics "store-typing" (requirement := R4)]
theorem subscribe_types {idSrc cellSrc : TermSrc}
    (ha : TypesEach sig idSrc env path types .nat)
    (hs : TypesEach sig cellSrc env path types cellTy) :
    TypesEach sig (subscribeStep idSrc cellSrc) env path types (.prod .unit cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons ha (Input.types_cons hs Input.types_nil)) Data.subscribe rfl

/-- Consumer of step-language-typed, R4, at the tryPublish source. -/
@[semantics "store-typing" (requirement := R4)]
theorem tryPublish_types {messageSrc cellSrc : TermSrc}
    (ha : TypesEach sig messageSrc env path types .nat)
    (hs : TypesEach sig cellSrc env path types cellTy) :
    TypesEach sig (tryPublishStep messageSrc cellSrc) env path types (.prod .bool cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons ha (Input.types_cons hs Input.types_nil)) Data.tryPublish rfl

/-- Consumer of step-language-typed, R4, at the poll source. -/
@[semantics "store-typing" (requirement := R4)]
theorem poll_types {idSrc cellSrc : TermSrc}
    (aligned : types.length = env.names.length)
    (ha : TypesEach sig idSrc env path types .nat)
    (hs : TypesEach sig cellSrc env path types cellTy) :
    TypesEach sig (pollStep idSrc cellSrc) env path types (.prod (.option .nat) cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons ha (Input.types_cons hs Input.types_nil)) Data.poll rfl (Step.scope_of_alignment _ aligned)

/-- Consumer of step-language-typed, R4, at the unsubscribe source. -/
@[semantics "store-typing" (requirement := R4)]
theorem unsubscribe_types {idSrc cellSrc : TermSrc}
    (aligned : types.length = env.names.length)
    (ha : TypesEach sig idSrc env path types .nat)
    (hs : TypesEach sig cellSrc env path types cellTy) :
    TypesEach sig (unsubscribeStep idSrc cellSrc) env path types (.prod .unit cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons ha (Input.types_cons hs Input.types_nil)) Data.unsubscribe rfl (Step.scope_of_alignment _ aligned)

/-- Consumer of step-language-typed, R4, at the slide source. -/
@[semantics "store-typing" (requirement := R4)]
theorem slide_types {cellSrc : TermSrc}
    (hs : TypesEach sig cellSrc env path types cellTy) :
    TypesEach sig (slideStep cellSrc) env path types (.prod .unit cellTy) :=
  Step.typed_of_normal sig atoms (Input.types_cons hs Input.types_nil) Data.slide rfl

end Typing
end Effect4.PubSub
