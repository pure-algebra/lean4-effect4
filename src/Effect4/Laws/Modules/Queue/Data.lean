import Effect4.Modules.Queue.Data
import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Step.ErasedCompiler
import Effect4.Laws.Modules.Queue.Relation

/-!
# Laws.Modules.Queue.Data — the Queue's model on the step language's carriers

The connector between the Queue's model and its step written as data
(`src/Effect4/Modules/Queue/Data.lean`; decisions row 330, slice L3). It has the three parts of
Semaphore's (`src/Effect4/Laws/Modules/Semaphore/Data.lean`): the reading law, once; the
encoding, once for the module (`cellVal_image`); and the step's value (`size_eval`).

**The message type is a parameter.** The reading is taken with the type variable `P` in
place of the message type, whose carrier at the opaque context is the value itself, so a message's value is the
model's `msg` of its name, as in `cellVal`.

Placement: concept `translation-simulation`, requirement R10, a helper of `sizeStep_agrees`
(`src/Effect4/Laws/Modules/Queue/Steps.lean`). Nothing here covers a step that folds.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.Queue (cellRecord)

/-- The type variable that stands for the message type. -/
abbrev P : Ty := .var 0

/-- A message list on the carrier of the opaque context: each message through the message map. -/
theorem messages_image (msg : Nat → Val) (ms : List Nat) :
    (imageAt Leaves.opaque (.list P)).toVal (ms.map msg) = .list (ms.map msg) := by
  show Val.list ((ms.map msg).map id) = _
  rw [List.map_id]

/-- A pending offer on the carrier of the opaque context. -/
def offerC (tb : Table) (msg : Nat → Val) (o : Offer) : CarrierAt Leaves.opaque (offerTy P) :=
  (o.batch, (Val.promise (tb.hint o.id), (Val.promise (tb.handle o.id), (o.rest.map msg, ()))))

/-- A waiting taker on the carrier of the opaque context. -/
def takerC (tb : Table) (t : Taker) : CarrierAt Leaves.opaque takerTy :=
  (Val.promise (tb.hint t.id), (Val.promise (tb.handle t.id), ()))

/-- **A model state on the carrier of the opaque context.** -/
def cellC (tb : Table) (msg : Nat → Val) (s : State) :
    CarrierAt Leaves.opaque (.record (cellRecord P)) :=
  (s.capacity.getD 0, (s.messages.map msg, (s.offers.map (offerC tb msg),
    (s.takers.map (takerC tb), ()))))

theorem offerVal_image (tb : Table) (msg : Nat → Val) (o : Offer) :
    (imageAt Leaves.opaque (offerTy P)).toVal (offerC tb msg o) = offerVal tb msg o := by
  show offerOf (.bool o.batch) (Val.promise (tb.hint o.id)) (Val.promise (tb.handle o.id))
    ((imageAt Leaves.opaque (.list P)).toVal (o.rest.map msg)) = _
  rw [messages_image]
  rfl

/-- **The encoding**: a model state's carrier has the cell's value as its image. -/
theorem cellVal_image (tb : Table) (msg : Nat → Val) (s : State) :
    (imageAt Leaves.opaque (.record (cellRecord P))).toVal (cellC tb msg s) = cellVal tb msg s := by
  show cellOf (.nat (s.capacity.getD 0)) ((imageAt Leaves.opaque (.list P)).toVal (s.messages.map msg))
      (.list ((s.offers.map (offerC tb msg)).map (imageAt Leaves.opaque (offerTy P)).toVal))
      (.list ((s.takers.map (takerC tb)).map (imageAt Leaves.opaque takerTy).toVal)) = _
  rw [messages_image, List.map_map, List.map_map]
  have offers : (imageAt Leaves.opaque (offerTy P)).toVal ∘ offerC tb msg = offerVal tb msg :=
    funext (offerVal_image tb msg)
  rw [offers]
  rfl

/-- The size step's input at a model state. -/
abbrev cellInputs (tb : Table) (msg : Nat → Val) (s : State) :
    Inputs Leaves.opaque [.record (cellRecord P)] :=
  (cellC tb msg s, ())

/-- **The size step's value is the buffer's length.** -/
theorem size_eval (tb : Table) (msg : Nat → Val) (s : State) :
    (Data.size P).eval Leaves.opaque (cellInputs tb msg s) =
      s.messages.length :=
  List.length_map _

/-- Request records on the deferred-key carrier retain the existing model encoding. -/
def takerK (tb : Table) (t : Taker) : CarrierAt Leaves.deferredKeys takerTy :=
  (tb.hint t.id, (tb.handle t.id, ()))
def offerK (tb : Table) (msg : Nat → Val) (o : Offer) : CarrierAt Leaves.deferredKeys (offerTy P) :=
  (o.batch, (tb.hint o.id, (tb.handle o.id, (o.rest.map msg, ()))))
def cellK (tb : Table) (msg : Nat → Val) (s : State) : CarrierAt Leaves.deferredKeys (cellTy P) :=
  (s.capacity.getD 0, (s.messages.map msg, (s.offers.map (offerK tb msg), (s.takers.map (takerK tb), ()))))

theorem takerK_image (tb : Table) (t : Taker) :
    (imageAt Leaves.deferredKeys takerTy).toVal (takerK tb t) = takerVal tb t := rfl
theorem offerK_image (tb : Table) (msg : Nat → Val) (o : Offer) :
    (imageAt Leaves.deferredKeys (offerTy P)).toVal (offerK tb msg o) = offerVal tb msg o :=
  offerVal_image tb msg o
theorem cellK_image (tb : Table) (msg : Nat → Val) (s : State) :
    (imageAt Leaves.deferredKeys (cellTy P)).toVal (cellK tb msg s) = cellVal tb msg s := by
  show cellOf (.nat (s.capacity.getD 0)) ((imageAt Leaves.opaque (.list P)).toVal (s.messages.map msg))
      (.list ((s.offers.map (offerK tb msg)).map (imageAt Leaves.deferredKeys (offerTy P)).toVal))
      (.list ((s.takers.map (takerK tb)).map (imageAt Leaves.deferredKeys takerTy).toVal)) = _
  rw [messages_image, List.map_map, List.map_map]
  have offers : (imageAt Leaves.deferredKeys (offerTy P)).toVal ∘ offerK tb msg = offerVal tb msg :=
    funext (offerK_image tb msg)
  rw [offers]
  rfl

abbrev takeInputs (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : Machine.DeferredKey) :
    Inputs Leaves.deferredKeys (Data.takeΓ P) := (tb.handle id, (hint, (cellK tb msg s, ())))
abbrev offerInputs (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat) (hint : Machine.DeferredKey) :
    Inputs Leaves.deferredKeys (Data.offerΓ P) := (tb.handle id, (hint, (msg a, (cellK tb msg s, ()))))
abbrev withdrawInputs (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) :
    Inputs Leaves.deferredKeys (Data.withdrawΓ P) := (tb.handle id, (cellK tb msg s, ()))

end Effect4.Queue.Model

namespace Effect4.Queue.Data
open Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The runtime reading is independent of the message declaration, including arbitrary values. -/
theorem take_parameter (A : Ty) (id hint s : TermSrc) :
    eraseSource (Queue.takeStep A id hint s) = eraseSource (Queue.takeStep (.var 0) id hint s) := by
  change eraseSource ((take A).term (Input.source [id, hint, s])) =
    eraseSource ((take (.var 0)).term (Input.source [id, hint, s]))
  rw [Step.term_erase, Step.term_erase]
  rfl

/-- The runtime reading is independent of the message declaration, including arbitrary values. -/
theorem offer_parameter (A : Ty) (id hint a s : TermSrc) :
    eraseSource (Queue.offerStep A id hint a s) = eraseSource (Queue.offerStep (.var 0) id hint a s) := by
  change eraseSource ((offer A).term (Input.source [id, hint, a, s])) =
    eraseSource ((offer (.var 0)).term (Input.source [id, hint, a, s]))
  rw [Step.term_erase, Step.term_erase]
  rfl

/-- The runtime reading is independent of the message declaration, including arbitrary values. -/
theorem poll_parameter (A : Ty) (s : TermSrc) :
    eraseSource (Queue.pollStep A s) = eraseSource (Queue.pollStep (.var 0) s) := by
  change eraseSource ((poll A).term (Input.source [s])) =
    eraseSource ((poll (.var 0)).term (Input.source [s]))
  rw [Step.term_erase, Step.term_erase]
  rfl

/-- The runtime reading is independent of the message declaration, including arbitrary values. -/
theorem size_parameter (A : Ty) (s : TermSrc) :
    eraseSource (Queue.sizeStep A s) = eraseSource (Queue.sizeStep (.var 0) s) := by
  change eraseSource ((size A).term (Input.source [s])) =
    eraseSource ((size (.var 0)).term (Input.source [s]))
  rw [Step.term_erase, Step.term_erase]
  rfl

/-- The runtime reading is independent of the message declaration, including arbitrary values. -/
theorem withdrawTake_parameter (A : Ty) (id s : TermSrc) :
    eraseSource (Queue.withdrawTake A id s) = eraseSource (Queue.withdrawTake (.var 0) id s) := by
  change eraseSource ((withdrawTake A).term (Input.source [id, s])) =
    eraseSource ((withdrawTake (.var 0)).term (Input.source [id, s]))
  rw [Step.term_erase, Step.term_erase]
  rfl

/-- The runtime reading is independent of the message declaration, including arbitrary values. -/
theorem withdrawOffer_parameter (A : Ty) (id s : TermSrc) :
    eraseSource (Queue.withdrawOffer A id s) = eraseSource (Queue.withdrawOffer (.var 0) id s) := by
  change eraseSource ((withdrawOffer A).term (Input.source [id, s])) =
    eraseSource ((withdrawOffer (.var 0)).term (Input.source [id, s]))
  rw [Step.term_erase, Step.term_erase]
  rfl

end Effect4.Queue.Data
