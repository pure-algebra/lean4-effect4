import Effect4.Modules.Queue.Data
import Effect4.Laws.Modules.Queue.Passes
import Effect4.Laws.Modules.Step
import Effect4.Laws.Modules.Step.ErasedCompiler
import Effect4.Laws.Modules.Queue.Relation

/-!
# Queue model carriers and operation data connectors

These helpers serve the existing Queue operation agreement claims under translation-simulation and R10.
Queue Steps consumes the exact encodings, identity passes, and source annotation equalities.
The message carrier uses the type variable P, so the message map may contain arbitrary values.
The input and table hypotheses stay explicit. These helpers establish neither progress nor host delivery.
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

/-- Injective model identities agree with deferred-key comparison. -/
theorem tableEqual (tb : Table) (injective : tb.Injective) (a b : Nat) :
    Model.deferredEqual Leaves.deferredKeys (tb.handle a) (tb.handle b) = decide (a = b) :=
  (DeferredIdentity.deferredKeys.equal_eq _ _).symm.trans (injective.decides a b)

/-- Model filtering negates exactly the compared request identity. -/
theorem tableNotEqual (tb : Table) (injective : tb.Injective) (a b : Nat) :
    (!Model.deferredEqual Leaves.deferredKeys (tb.handle a) (tb.handle b)) = (a != b) :=
  (congrArg Bool.not (tableEqual tb injective a b)).trans
    (congrArg Bool.not (Lean.Grind.beq_eq_decide_eq a b).symm)

/-- Taker removal computes the independent model's identity filter. -/
theorem removeTaker_value {Γ : List Ty} (tb : Table) (injective : tb.Injective)
    (ts : Step Γ (.list takerTy)) (request : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) (takers : List Taker) (id : Nat)
    (hts : ts.eval Leaves.deferredKeys vs = takers.map (takerK tb))
    (hid : request.eval Leaves.deferredKeys vs = tb.handle id) :
    (Data.removeTaker ts request).eval Leaves.deferredKeys vs =
      (takers.filter (fun t => t.id != id)).map (takerK tb) := by
  rw [Data.removeTaker_eval, hts, hid]
  change (takers.map (takerK tb)).filter
    (fun (t : DeferredKey × (DeferredKey × Unit)) => !Model.deferredEqual Leaves.deferredKeys t.2.1 (tb.handle id)) = _
  refine (List.filter_map (f := takerK tb)
    (p := fun (t : DeferredKey × (DeferredKey × Unit)) => !Model.deferredEqual Leaves.deferredKeys t.2.1 (tb.handle id))
    (l := takers)).trans ?_
  apply congrArg (List.map (takerK tb))
  apply congrArg (fun predicate => takers.filter predicate)
  funext t
  exact tableNotEqual tb injective t.id id

/-- Offer removal computes the independent model's identity filter. -/
theorem removeOffer_value {Γ : List Ty} (tb : Table) (injective : tb.Injective)
    (msg : Nat → Val) (ts : Step Γ (.list (offerTy P))) (request : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) (takers : List Offer) (id : Nat)
    (hts : ts.eval Leaves.deferredKeys vs = takers.map (offerK tb msg))
    (hid : request.eval Leaves.deferredKeys vs = tb.handle id) :
    (Data.removeOffer P ts request).eval Leaves.deferredKeys vs =
      (takers.filter (fun t => t.id != id)).map (offerK tb msg) := by
  rw [Data.removeOffer_eval, hts, hid]
  change (takers.map (offerK tb msg)).filter
    (fun (t : Bool × (DeferredKey × (DeferredKey × (List Val × Unit)))) => !Model.deferredEqual Leaves.deferredKeys t.2.2.1 (tb.handle id)) = _
  refine (List.filter_map (f := offerK tb msg)
    (p := fun (t : Bool × (DeferredKey × (DeferredKey × (List Val × Unit)))) => !Model.deferredEqual Leaves.deferredKeys t.2.2.1 (tb.handle id))
    (l := takers)).trans ?_
  apply congrArg (List.map (offerK tb msg))
  apply congrArg (fun predicate => takers.filter predicate)
  funext t
  exact tableNotEqual tb injective t.id id

/-- Enrolment tests exactly the independent model's request identity. -/
theorem enrolled_value {Γ : List Ty} (tb : Table) (injective : tb.Injective)
    (ts : Step Γ (.list takerTy)) (request : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) (takers : List Taker) (id : Nat)
    (hts : ts.eval Leaves.deferredKeys vs = takers.map (takerK tb))
    (hid : request.eval Leaves.deferredKeys vs = tb.handle id) :
    (Data.enrolled ts request).eval Leaves.deferredKeys vs =
      takers.any (fun t => decide (t.id = id)) := by
  rw [Data.enrolled_eval, hts, hid]
  refine (List.any_map (f := takerK tb)
    (p := fun (t : DeferredKey × (DeferredKey × Unit)) => Model.deferredEqual Leaves.deferredKeys t.2.1 (tb.handle id))
    (l := takers)).trans ?_
  apply congrArg (fun predicate => takers.any predicate)
  funext t
  exact tableEqual tb injective t.id id

/-- Head selection compares exactly the first independent model taker. -/
theorem isHead_value {Γ : List Ty} (tb : Table) (injective : tb.Injective)
    (ts : Step Γ (.list takerTy)) (request : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) (takers : List Taker) (id : Nat)
    (hts : ts.eval Leaves.deferredKeys vs = takers.map (takerK tb))
    (hid : request.eval Leaves.deferredKeys vs = tb.handle id) :
    (Data.isHead ts request).eval Leaves.deferredKeys vs =
      (takers.take 1).any (fun t => decide (t.id = id)) :=
  enrolled_value tb injective (.take ts (.nat 1)) request vs (takers.take 1) id
    ((congrArg (fun xs => xs.take 1) hts).trans List.map_take.symm) hid

/-- Renewal changes the matching taker's hint and keeps its request identity. -/
theorem takerK_renewed (tb : Table) (injective : tb.Injective) (id : Nat)
    (hint : DeferredKey) (t : Taker) :
    (if Model.deferredEqual Leaves.deferredKeys (tb.handle t.id) (tb.handle id)
      then (hint, (tb.handle id, ())) else takerK tb t) = takerK (tb.renew id hint) t := by
  rw [tableEqual tb injective t.id id]
  change (if decide (t.id = id) then (hint, (tb.handle id, ())) else
    (tb.hint t.id, (tb.handle t.id, ()))) =
    ((if t.id = id then hint else tb.hint t.id), (tb.handle t.id, ()))
  by_cases same : t.id = id
  · have yes : decide (t.id = id) = true := decide_eq_true same
    rw [yes, if_pos rfl, if_pos same, same]
  · rw [if_neg same]
    have no : decide (t.id = id) = false := decide_eq_false same
    rw [no, if_neg (by decide)]

/-- Hint renewal maps to the independent model's renewed table. -/
theorem renewHint_value {Γ : List Ty} (tb : Table) (injective : tb.Injective)
    (ts : Step Γ (.list takerTy)) (request fresh : Step Γ idTy)
    (vs : Inputs Leaves.deferredKeys Γ) (takers : List Taker) (id : Nat) (hint : DeferredKey)
    (hts : ts.eval Leaves.deferredKeys vs = takers.map (takerK tb))
    (hid : request.eval Leaves.deferredKeys vs = tb.handle id)
    (hhint : fresh.eval Leaves.deferredKeys vs = hint) :
    (Data.renewHint ts request fresh).eval Leaves.deferredKeys vs =
      takers.map (takerK (tb.renew id hint)) := by
  rw [Data.renewHint_eval, hts, hid, hhint]
  refine (List.map_map (f := takerK tb)
    (g := fun (t : DeferredKey × (DeferredKey × Unit)) =>
      if Model.deferredEqual Leaves.deferredKeys t.2.1 (tb.handle id)
      then (hint, (tb.handle id, ())) else t) (l := takers)).trans ?_
  apply congrArg (fun f => takers.map f)
  funext t
  exact takerK_renewed tb injective id hint t

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
