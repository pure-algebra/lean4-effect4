import Effect4.Library.Ref.Model
import Effect4.Laws.Machine.RefKernel
import Effect4.Laws.Auto.Semantics

/-!
# Ref's native operations agree with its independent model

Placement: concept `translation-simulation`, proposed claim `ref-steps-agree`, role simulation,
requirement R10. The placement precedes these obligations in the Ref catalogue plan.
Reach: one allocated cell, arbitrary exact images, and successful callback evaluation at the
encoded current value. Each operation observes its reply and final stores.
The model records optional writes. The kernel premise retains that distinction.
Final store equality does not observe writing an unchanged value.
The consumers are typed Step callbacks, Ref callers, SynchronizedRef and keyed cells.
The callback's type is not an allocation proof. These laws establish no scheduling, whole-run
agreement, host object identity, callback exceptions or arbitrary JavaScript semantics.

The native kernel connector handles every operation except allocation.
The independent model distinguishes no write from writing the old value.
-/

set_option autoImplicit false
namespace Effect4.Ref
open Effect4.Machine Effect4.Program
open Effect4.Store (Image)

/-- Apply the model's optional write through the chosen value image. -/
def resultStores {A B : Type} (I : Image A) (r : Model.Result A B) (q : RefKey)
    (stores : Stores) : Stores :=
  { stores with refs := refWriteBack stores.refs q (r.write.map I.toVal) }

/-- Helper of ref-steps-agree; the nonallocating agreement laws consume this connector. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem kernel_agrees {A B : Type} (I : Image A) (reply : B → Val) (a : A)
    (r : Model.Result A B) {stores : Stores} {q : RefKey} {op : SyncOp} {kernel : RefKernel}
    (held : refPeek stores.refs q = some (I.toVal a))
    (row : op.refKernel = some (q, kernel))
    (value : kernel (I.toVal a) = some (reply r.reply, r.write.map I.toVal)) :
    syncOpStep op stores = some (resultStores I r q stores, reply r.reply) := by
  rw [syncOpStep_eq_refStepOf row]
  simp only [refStepOf, held, value, Option.bind_some, Option.map_some]
  rfl

/-- Helper of ref-steps-agree; optional callback laws consume its exact option decoding. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem decode_option {A : Type} (I : Image A) (o : Option A) :
    Image.ofOption Image.ident (Image.toOption I o) = some (o.map I.toVal) := by
  cases o <;> rfl

/-- Helper of ref-steps-agree; the optional reply laws consume this value equation. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem encode_getD {A : Type} (I : Image A) (o : Option A) (a : A) :
    (o.map I.toVal).getD (I.toVal a) = I.toVal (o.getD a) := by
  cases o <;> rfl

/-- Helper of ref-steps-agree; modifySome consumes the callback pair's option decoding. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem decode_modifySome {A B : Type} (I : Image A) (J : Image B) (p : B × Option A) :
    Image.ofTuple2 Image.ident (Image.option Image.ident)
      ((Image.tuple2 J (Image.option I)).toVal p) =
        some (J.toVal p.1, p.2.map I.toVal) := by
  obtain ⟨b, o⟩ := p
  cases o <;> rfl

/-- Ref.make allocates the model's initial value and answers its fresh cell identity. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem make_agrees {A : Type} (I : Image A) (a : A) (stores : Stores) :
    syncOpStep (.refMake (I.toVal a)) stores =
      some ({ stores with refs := stores.refs ++ [I.toVal (Model.make a)] },
        Val.cell ⟨stores.refs.length⟩) := rfl

section Operations
variable {A B : Type} (I : Image A) (J : Image B) (a : A)
  {stores : Stores} {q : RefKey}
  (held : refPeek stores.refs q = some (I.toVal a))
include held

/-- Ref.get observes the model's reply and performs no write. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem get_agrees : syncOpStep (.refGet q) stores =
    some (resultStores I (Model.get a) q stores, I.toVal (Model.get a).reply) :=
  kernel_agrees I I.toVal a (Model.get a) held rfl rfl

/-- Ref.set answers the backing-cell identity, retaining the declaration's signed exception. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem set_agrees (value : A) : syncOpStep (.refSet q (I.toVal value)) stores =
    some (resultStores I (Model.set q a value) q stores, Val.cell (Model.set q a value).reply) :=
  kernel_agrees I Val.cell a (Model.set q a value) held rfl rfl

/-- Ref.getAndSet answers the old value and stores the replacement. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem getAndSet_agrees (value : A) : syncOpStep (.refGetAndSet q (I.toVal value)) stores =
    some (resultStores I (Model.getAndSet a value) q stores,
      I.toVal (Model.getAndSet a value).reply) :=
  kernel_agrees I I.toVal a (Model.getAndSet a value) held rfl rfl

/-- Ref.setAndGet answers and stores the replacement. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem setAndGet_agrees (value : A) : syncOpStep (.refSetAndGet q (I.toVal value)) stores =
    some (resultStores I (Model.setAndGet a value) q stores,
      I.toVal (Model.setAndGet a value).reply) :=
  kernel_agrees I I.toVal a (Model.setAndGet a value) held rfl rfl

/-- Ref.update agrees when its callback evaluates to the model's next value. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem update_agrees (fn : A → A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f = some (I.toVal (fn a))) :
    syncOpStep (.refUpdate q f captured) stores =
      some (resultStores I (Model.update fn a) q stores,
        (fun _ => Val.unit) (Model.update fn a).reply) := by
  apply kernel_agrees I (fun _ => Val.unit) a (Model.update fn a) held rfl
  simp only [termKernel, value, Option.bind_some, Option.map_some]
  rfl

/-- Ref.getAndUpdate agrees when its callback evaluates to the model's next value. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem getAndUpdate_agrees (fn : A → A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f = some (I.toVal (fn a))) :
    syncOpStep (.refGetAndUpdate q f captured) stores =
      some (resultStores I (Model.getAndUpdate fn a) q stores,
        (I.toVal) (Model.getAndUpdate fn a).reply) := by
  apply kernel_agrees I (I.toVal) a (Model.getAndUpdate fn a) held rfl
  simp only [termKernel, value, Option.bind_some, Option.map_some]
  rfl

/-- Ref.updateAndGet agrees when its callback evaluates to the model's next value. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem updateAndGet_agrees (fn : A → A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f = some (I.toVal (fn a))) :
    syncOpStep (.refUpdateAndGet q f captured) stores =
      some (resultStores I (Model.updateAndGet fn a) q stores,
        (I.toVal) (Model.updateAndGet fn a).reply) := by
  apply kernel_agrees I (I.toVal) a (Model.updateAndGet fn a) held rfl
  simp only [termKernel, value, Option.bind_some, Option.map_some]
  rfl

/-- Ref.updateSome agrees with both optional branches, retaining the optional write. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem updateSome_agrees (fn : A → Option A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f = some (Image.toOption I (fn a))) :
    syncOpStep (.refUpdateSome q f captured) stores =
      some (resultStores I (Model.updateSome fn a) q stores,
        (fun _ => Val.unit) (Model.updateSome fn a).reply) := by
  apply kernel_agrees I (fun _ => Val.unit) a (Model.updateSome fn a) held rfl
  simp only [termKernel, value, Option.bind_some, decode_option, Option.map_some]
  rfl

/-- Ref.getAndUpdateSome agrees with both optional branches, retaining the optional write. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem getAndUpdateSome_agrees (fn : A → Option A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f = some (Image.toOption I (fn a))) :
    syncOpStep (.refGetAndUpdateSome q f captured) stores =
      some (resultStores I (Model.getAndUpdateSome fn a) q stores,
        (I.toVal) (Model.getAndUpdateSome fn a).reply) := by
  apply kernel_agrees I (I.toVal) a (Model.getAndUpdateSome fn a) held rfl
  simp only [termKernel, value, Option.bind_some, decode_option, Option.map_some]
  rfl

/-- Ref.updateSomeAndGet agrees with both optional branches, retaining the optional write. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem updateSomeAndGet_agrees (fn : A → Option A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f = some (Image.toOption I (fn a))) :
    syncOpStep (.refUpdateSomeAndGet q f captured) stores =
      some (resultStores I (Model.updateSomeAndGet fn a) q stores,
        (I.toVal) (Model.updateSomeAndGet fn a).reply) := by
  apply kernel_agrees I (I.toVal) a (Model.updateSomeAndGet fn a) held rfl
  simp only [termKernel, value, Option.bind_some, decode_option, Option.map_some]
  rw [encode_getD]
  rfl

/-- Ref.modify returns the callback's first value and stores its second value. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem modify_agrees (fn : A → B × A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f =
      some ((Image.tuple2 J I).toVal (fn a))) :
    syncOpStep (.refModify q f captured) stores =
      some (resultStores I (Model.modify fn a) q stores, J.toVal (Model.modify fn a).reply) := by
  apply kernel_agrees I J.toVal a (Model.modify fn a) held rfl
  simp only [termKernel, value, Option.bind_some, Image.tuple2, Image.ofTuple2,
    Image.ident, Option.map_some]
  rfl

/-- Ref.modifySome writes the old value on None, through latest's call to modify. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem modifySome_agrees (fn : A → B × Option A) (f : Term) (captured : List Val)
    (value : evalTerm (captured ++ [I.toVal a]) f =
      some ((Image.tuple2 J (Image.option I)).toVal (fn a))) :
    syncOpStep (.refModifySome q f captured) stores =
      some (resultStores I (Model.modifySome fn a) q stores,
        J.toVal (Model.modifySome fn a).reply) := by
  apply kernel_agrees I J.toVal a (Model.modifySome fn a) held rfl
  simp only [termKernel, value, Option.bind_some, decode_modifySome, Option.map_some]
  rw [encode_getD]
  rfl

end Operations

/-- **Ref's thirteen effectful operations agree with the independent model**: one field for each
operation of latest (Effect 4.0.1), at the statement of its law above. Each field's type is the
law's own (`type_of%`), so no statement is written twice. -/
structure StepsAgree : Prop where
  /-- `Ref.make`: `make_agrees`. -/
  make : type_of% @make_agrees
  /-- `Ref.get`: `get_agrees`. -/
  get : type_of% @get_agrees
  /-- `Ref.set`: `set_agrees`. -/
  set : type_of% @set_agrees
  /-- `Ref.getAndSet`: `getAndSet_agrees`. -/
  getAndSet : type_of% @getAndSet_agrees
  /-- `Ref.setAndGet`: `setAndGet_agrees`. -/
  setAndGet : type_of% @setAndGet_agrees
  /-- `Ref.update`: `update_agrees`. -/
  update : type_of% @update_agrees
  /-- `Ref.getAndUpdate`: `getAndUpdate_agrees`. -/
  getAndUpdate : type_of% @getAndUpdate_agrees
  /-- `Ref.updateAndGet`: `updateAndGet_agrees`. -/
  updateAndGet : type_of% @updateAndGet_agrees
  /-- `Ref.updateSome`: `updateSome_agrees`. -/
  updateSome : type_of% @updateSome_agrees
  /-- `Ref.getAndUpdateSome`: `getAndUpdateSome_agrees`. -/
  getAndUpdateSome : type_of% @getAndUpdateSome_agrees
  /-- `Ref.updateSomeAndGet`: `updateSomeAndGet_agrees`. -/
  updateSomeAndGet : type_of% @updateSomeAndGet_agrees
  /-- `Ref.modify`: `modify_agrees`. -/
  modify : type_of% @modify_agrees
  /-- `Ref.modifySome`: `modifySome_agrees`. -/
  modifySome : type_of% @modifySome_agrees

/-- **The thirteen operation laws hold** (the claim `ref-steps-agree`, role simulation).
Placement: concept `translation-simulation`, requirement R10. Reach: allocation for any exact
image; every other operation on one allocated cell holding the encoded value, with a callback
that evaluates to the encoded next value. Each law observes the reply and the final stores. Not
established: the laws compare replies and final stores, not write events; no scheduling,
whole run, host object identity, callback exception or reentrant mutation. Consumers: the typed
callback connector (`src/Effect4/Laws/Library/Ref/Callback.lean`), then SynchronizedRef and the
keyed cells (decisions row 335). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem ref_steps_agree : StepsAgree := ⟨@make_agrees, @get_agrees, @set_agrees, @getAndSet_agrees, @setAndGet_agrees, @update_agrees, @getAndUpdate_agrees, @updateAndGet_agrees, @updateSome_agrees, @getAndUpdateSome_agrees, @updateSomeAndGet_agrees, @modify_agrees, @modifySome_agrees⟩

end Effect4.Ref
