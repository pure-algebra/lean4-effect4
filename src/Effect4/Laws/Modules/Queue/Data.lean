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

/-- Entering offers are the model prefix bounded by available room. -/
theorem entering_value {Γ : List Ty} (tb : Table) (msg : Nat → Val)
    (room : Step Γ .nat) (os : Step Γ (.list (offerTy P))) (vs : Inputs Leaves.deferredKeys Γ)
    (r : Nat) (offers : List Offer)
    (hr : room.eval Leaves.deferredKeys vs = r)
    (ho : os.eval Leaves.deferredKeys vs = offers.map (offerK tb msg)) :
    (Data.entering P room os).eval Leaves.deferredKeys vs =
      (offers.take (Nat.min r offers.length)).map (offerK tb msg) := by
  change (os.eval Leaves.deferredKeys vs).take ((Data.fitting P room os).eval Leaves.deferredKeys vs) = _
  rw [Data.fitting_eval, hr, ho]
  exact (congrArg (fun n => (offers.map (offerK tb msg)).take (Nat.min r n))
    (List.length_map (f := offerK tb msg) (as := offers))).trans List.map_take.symm

/-- Staying offers are the model suffix after the entering prefix. -/
theorem staying_value {Γ : List Ty} (tb : Table) (msg : Nat → Val)
    (room : Step Γ .nat) (os : Step Γ (.list (offerTy P))) (vs : Inputs Leaves.deferredKeys Γ)
    (r : Nat) (offers : List Offer)
    (hr : room.eval Leaves.deferredKeys vs = r)
    (ho : os.eval Leaves.deferredKeys vs = offers.map (offerK tb msg)) :
    (Data.staying P room os).eval Leaves.deferredKeys vs =
      (offers.drop (Nat.min r offers.length)).map (offerK tb msg) := by
  change (os.eval Leaves.deferredKeys vs).drop ((Data.fitting P room os).eval Leaves.deferredKeys vs) = _
  rw [Data.fitting_eval, hr, ho]
  exact (congrArg (fun n => (offers.map (offerK tb msg)).drop (Nat.min r n))
    (List.length_map (f := offerK tb msg) (as := offers))).trans List.map_drop.symm

/-- Entering offers append their model messages in arrival order. -/
theorem gained_value {Γ : List Ty} (tb : Table) (msg : Nat → Val)
    (room : Step Γ .nat) (ms : Step Γ (.list P)) (os : Step Γ (.list (offerTy P)))
    (vs : Inputs Leaves.deferredKeys Γ) (r : Nat) (messages : List Nat) (offers : List Offer)
    (hr : room.eval Leaves.deferredKeys vs = r)
    (hm : ms.eval Leaves.deferredKeys vs = messages.map msg)
    (ho : os.eval Leaves.deferredKeys vs = offers.map (offerK tb msg)) :
    (Data.gained P room ms os).eval Leaves.deferredKeys vs =
      (messages ++ (offers.take (Nat.min r offers.length)).flatMap (·.rest)).map msg := by
  rw [Data.gained_eval, entering_value tb msg room os vs r offers hr ho, hm]
  let selected := offers.take (Nat.min r offers.length)
  let rests : (Bool × (DeferredKey × (DeferredKey × (List Val × Unit)))) → List Val := fun entry => entry.2.2.2.1
  refine (Effect4.Constructive.List.foldl_append_flatMap rests (selected.map (offerK tb msg)) (messages.map msg)).trans ?_
  have flat : (selected.map (offerK tb msg)).flatMap rests = (selected.flatMap (·.rest)).map msg :=
    (List.flatMap_map (offerK tb msg) rests selected).trans List.map_flatMap.symm
  exact (congrArg (fun tails => messages.map msg ++ tails) flat).trans List.map_append.symm

/-- A list of pending offer carriers has exactly the existing offer encoding. -/
theorem offersK_image (tb : Table) (msg : Nat → Val) (offers : List Offer) :
    (imageAt Leaves.deferredKeys (.list (offerTy P))).toVal (offers.map (offerK tb msg)) =
      Val.list (offers.map (offerVal tb msg)) := by
  change Val.list ((offers.map (offerK tb msg)).map ((imageAt Leaves.deferredKeys (offerTy P)).toVal)) = _
  rw [List.map_map]
  exact congrArg Val.list (List.map_congr_left (fun o _ => offerK_image tb msg o))

/-- The optional message head retains the arbitrary message map. -/
theorem headK_image (msg : Nat → Val) (messages : List Nat) :
    (imageAt Leaves.deferredKeys (.option P)).toVal ((messages.map msg).head?) =
      pollReplyVal msg messages.head? := by
  cases messages with
  | nil => rfl
  | cons m ms => rfl

abbrev takeInputs (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : Machine.DeferredKey) :
    Inputs Leaves.deferredKeys (Data.takeΓ P) := (tb.handle id, (hint, (cellK tb msg s, ())))
abbrev offerInputs (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat) (hint : Machine.DeferredKey) :
    Inputs Leaves.deferredKeys (Data.offerΓ P) := (tb.handle id, (hint, (msg a, (cellK tb msg s, ()))))
abbrev withdrawInputs (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) :
    Inputs Leaves.deferredKeys (Data.withdrawΓ P) := (tb.handle id, (cellK tb msg s, ()))

/-- Withdrawal computes the model taker filter and its ordered wake list. -/
theorem withdrawTake_value (tb : Table) (injective : tb.Injective) (msg : Nat → Val) (s : State) (id : Nat) :
    (Data.withdrawTake P).eval Leaves.deferredKeys (withdrawInputs tb msg s id) =
      ((if s.messages.length = 0 then [] else (s.takers.filter (fun t => t.id != id)).take 1).map (takerK tb),
        cellK tb msg (removeTaker s id)) := by
  let request : Step (Data.withdrawΓ P) idTy := .var (.here _ _)
  let state : Step (Data.withdrawΓ P) (cellTy P) := .var (.there _ (.here _ _))
  let removed := Data.removeTaker (.get state (Data.takersF P)) request
  have hr := removeTaker_value tb injective (.get state (Data.takersF P)) request
    (withdrawInputs tb msg s id) s.takers id rfl rfl
  change ((if (s.messages.map msg).length == 0 then [] else
    (removed.eval Leaves.deferredKeys (withdrawInputs tb msg s id)).take 1),
    (s.capacity.getD 0, (s.messages.map msg, (s.offers.map (offerK tb msg),
      (removed.eval Leaves.deferredKeys (withdrawInputs tb msg s id), ()))))) = _
  rw [hr, List.length_map]
  by_cases empty : s.messages.length = 0
  · rw [if_pos empty]
    have yes : (s.messages.length == 0) = true := by exact beq_iff_eq.mpr empty
    rw [yes]
    rfl
  · rw [if_neg empty]
    have no : (s.messages.length == 0) = false := beq_eq_false_iff_ne.mpr empty
    rw [no]
    exact congrArg (fun first => (first, cellK tb msg (removeTaker s id))) List.map_take.symm

/-- Offer withdrawal computes the filtered model cell and ordered wake list. -/
theorem withdrawOffer_value (tb : Table) (injective : tb.Injective) (msg : Nat → Val) (s : State) (id : Nat) :
    (Data.withdrawOffer P).eval Leaves.deferredKeys (withdrawInputs tb msg s id) =
      ((if s.messages.length = 0 then [] else s.takers.take 1).map (takerK tb),
        cellK tb msg {s with offers := s.offers.filter (fun o => o.id != id)}) := by
  let request : Step (Data.withdrawΓ P) idTy := .var (.here _ _)
  let state : Step (Data.withdrawΓ P) (cellTy P) := .var (.there _ (.here _ _))
  let removed := Data.removeOffer P (.get state (Data.offersF P)) request
  have hr := removeOffer_value tb injective msg (.get state (Data.offersF P)) request
    (withdrawInputs tb msg s id) s.offers id rfl rfl
  change ((if (s.messages.map msg).length == 0 then [] else (s.takers.map (takerK tb)).take 1),
    (s.capacity.getD 0, (s.messages.map msg,
      (removed.eval Leaves.deferredKeys (withdrawInputs tb msg s id), (s.takers.map (takerK tb), ()))))) = _
  rw [hr, List.length_map]
  by_cases empty : s.messages.length = 0
  · rw [if_pos empty]
    have yes : (s.messages.length == 0) = true := beq_iff_eq.mpr empty
    rw [yes]
    rfl
  · rw [if_neg empty]
    have no : (s.messages.length == 0) = false := beq_eq_false_iff_ne.mpr empty
    rw [no]
    exact congrArg (fun first => (first, cellK tb msg {s with offers := s.offers.filter (fun o => o.id != id)})) List.map_take.symm

/-- Poll computes the exact pending-prefix transition at the original caller inputs. -/
theorem poll_value (tb : Table) (msg : Nat → Val) (s : State) :
    (Data.poll P).eval (Γ := (Data.CellInputs P).types) Leaves.deferredKeys (cellK tb msg s, ()) =
      if (!decide (s.messages.length = 0) && decide (s.takers.length = 0)) then
        (((s.messages.map msg).head?, (s.offers.take (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)).map (offerK tb msg)),
          cellK tb msg { s with messages := s.messages.drop 1 ++ (s.offers.take (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)).flatMap (·.rest), offers := s.offers.drop (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length) })
      else ((none, []), cellK tb msg s) := by
  let vs : Inputs Leaves.deferredKeys (Data.CellInputs P).types := (cellK tb msg s, ())
  let state : Step (Data.CellInputs P).types (cellTy P) := .var (Data.cell P)
  let ms := Step.get state (Data.msgsF P)
  let os := Step.get state (Data.offersF P)
  let rest := Step.drop ms (.nat 1)
  let room := Step.sub (.get state (Data.capF P)) (.len rest)
  have hrest : rest.eval Leaves.deferredKeys vs = (s.messages.drop 1).map msg := List.map_drop.symm
  have hr : room.eval Leaves.deferredKeys vs = s.capacity.getD 0 - (s.messages.drop 1).length := by
    change s.capacity.getD 0 - (rest.eval Leaves.deferredKeys vs).length = _
    rw [hrest]
    exact congrArg (fun n => s.capacity.getD 0 - n) (List.length_map (f := msg) (as := s.messages.drop 1))
  have hg := gained_value tb msg room rest os vs _ (s.messages.drop 1) s.offers hr hrest rfl
  have he := entering_value tb msg room os vs _ s.offers hr rfl
  have hs := staying_value tb msg room os vs _ s.offers hr rfl
  change (if (!decide ((s.messages.map msg).length = 0) && decide ((s.takers.map (takerK tb)).length = 0))
    then (((s.messages.map msg).head?, (Data.entering P room os).eval Leaves.deferredKeys vs),
      (s.capacity.getD 0, ((Data.gained P room rest os).eval Leaves.deferredKeys vs,
        ((Data.staying P room os).eval Leaves.deferredKeys vs, (s.takers.map (takerK tb), ())))))
    else ((none, []), cellK tb msg s)) = _
  rw [List.length_map, List.length_map, hg, he, hs]
  rfl

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

namespace Effect4.Queue.Model
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules
/-- Shared step reading transports to every message declaration through annotation erasure. -/
theorem withdrawTake_reads (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.withdrawTake A idSrc cellSrc) env path vals
      ((imageAt Leaves.deferredKeys (.prod (.list takerTy) (cellTy P))).toVal
        ((Data.withdrawTake P).eval Leaves.deferredKeys (withdrawInputs tb msg s id))) := by
  apply Reads.of_annotations (source := Queue.withdrawTake P idSrc cellSrc)
    (same := congrFun (congrFun (Data.withdrawTake_parameter A idSrc cellSrc) env) path)
  exact Step.sound Leaves.deferredKeys (withdrawInputs tb msg s id)
    (Input.reads_cons readsId (Input.reads_cons (readsCell.to (cellK_image tb msg s).symm) Input.reads_nil))
    (Data.withdrawTake P) (by decide) (Step.scope_of_alignment _ depth)
    (by exact ⟨DeferredIdentity.deferredKeys⟩)

/-- The withdrawal reading observes the model cell and ordered encoded takers. -/
theorem withdrawTake_encoded (A : Ty) (tb : Table) (injective : tb.Injective) (msg : Nat → Val) (s : State) (id : Nat)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.withdrawTake A idSrc cellSrc) env path vals
      (Val.tuple [Val.list ((if s.messages.length = 0 then [] else (s.takers.filter (fun t => t.id != id)).take 1).map (takerVal tb)),
        cellVal tb msg (removeTaker s id)]) := by
  apply (withdrawTake_reads A tb msg s id depth readsId readsCell).to
  rw [withdrawTake_value tb injective]
  let w := if s.messages.length = 0 then [] else (s.takers.filter (fun t => t.id != id)).take 1
  change Val.tuple [Val.list ((w.map (takerK tb)).map ((imageAt Leaves.deferredKeys takerTy).toVal)),
    (imageAt Leaves.deferredKeys (cellTy P)).toVal (cellK tb msg (removeTaker s id))] = _
  rw [List.map_map, cellK_image]
  have encoded : w.map (fun t => (imageAt Leaves.deferredKeys takerTy).toVal (takerK tb t)) = w.map (takerVal tb) :=
    List.map_congr_left (fun t _ => takerK_image tb t)
  exact congrArg (fun values => Val.tuple [Val.list values, cellVal tb msg (removeTaker s id)]) encoded

/-- Shared step reading transports to every message declaration through annotation erasure. -/
theorem withdrawOffer_reads (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.withdrawOffer A idSrc cellSrc) env path vals
      ((imageAt Leaves.deferredKeys (.prod (.list takerTy) (cellTy P))).toVal
        ((Data.withdrawOffer P).eval Leaves.deferredKeys (withdrawInputs tb msg s id))) := by
  apply Reads.of_annotations (source := Queue.withdrawOffer P idSrc cellSrc)
    (same := congrFun (congrFun (Data.withdrawOffer_parameter A idSrc cellSrc) env) path)
  exact Step.sound Leaves.deferredKeys (withdrawInputs tb msg s id)
    (Input.reads_cons readsId (Input.reads_cons (readsCell.to (cellK_image tb msg s).symm) Input.reads_nil))
    (Data.withdrawOffer P) (by decide) (Step.scope_of_alignment _ depth)
    (by exact ⟨DeferredIdentity.deferredKeys⟩)


/-- The withdrawal reading observes the model cell and ordered encoded takers. -/
theorem withdrawOffer_encoded (A : Ty) (tb : Table) (injective : tb.Injective) (msg : Nat → Val) (s : State) (id : Nat)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.withdrawOffer A idSrc cellSrc) env path vals
      (Val.tuple [Val.list ((if s.messages.length = 0 then [] else s.takers.take 1).map (takerVal tb)),
        cellVal tb msg {s with offers := s.offers.filter (fun o => o.id != id)}]) := by
  apply (withdrawOffer_reads A tb msg s id depth readsId readsCell).to
  rw [withdrawOffer_value tb injective]
  let w := if s.messages.length = 0 then [] else s.takers.take 1
  change Val.tuple [Val.list ((w.map (takerK tb)).map ((imageAt Leaves.deferredKeys takerTy).toVal)),
    (imageAt Leaves.deferredKeys (cellTy P)).toVal (cellK tb msg {s with offers := s.offers.filter (fun o => o.id != id)})] = _
  rw [List.map_map, cellK_image]
  have encoded : w.map (fun t => (imageAt Leaves.deferredKeys takerTy).toVal (takerK tb t)) = w.map (takerVal tb) :=
    List.map_congr_left (fun t _ => takerK_image tb t)
  exact congrArg (fun values => Val.tuple [Val.list values, cellVal tb msg {s with offers := s.offers.filter (fun o => o.id != id)}]) encoded


/-- Take reading uses only the original caller scope and exact input images. -/
theorem take_reads (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    {idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.takeStep A idSrc hintSrc cellSrc) env path vals
      ((imageAt Leaves.deferredKeys (.prod (.tuple [.option P, .list (offerTy P), .list takerTy]) (cellTy P))).toVal
        ((Data.take P).eval Leaves.deferredKeys (takeInputs tb msg s id hint))) := by
  apply Reads.of_annotations (source := Queue.takeStep P idSrc hintSrc cellSrc)
    (same := congrFun (congrFun (Data.take_parameter A idSrc hintSrc cellSrc) env) path)
  exact Step.sound Leaves.deferredKeys (takeInputs tb msg s id hint)
    (Input.reads_cons readsId (Input.reads_cons readsHint
      (Input.reads_cons (readsCell.to (cellK_image tb msg s).symm) Input.reads_nil)))
    (Data.take P) (by decide) (Step.scope_of_alignment _ depth)
    (by exact ⟨DeferredIdentity.deferredKeys⟩)

/-- Offer reading keeps arbitrary message values at the exact variable carrier. -/
theorem offer_reads (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat) (hint : DeferredKey)
    {idSrc hintSrc messageSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsMessage : Reads messageSrc env path vals (msg a))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.offerStep A idSrc hintSrc messageSrc cellSrc) env path vals
      ((imageAt Leaves.deferredKeys (.prod (.prod (.option .bool) (.list takerTy)) (cellTy P))).toVal
        ((Data.offer P).eval Leaves.deferredKeys (offerInputs tb msg s id a hint))) := by
  apply Reads.of_annotations (source := Queue.offerStep P idSrc hintSrc messageSrc cellSrc)
    (same := congrFun (congrFun (Data.offer_parameter A idSrc hintSrc messageSrc cellSrc) env) path)
  exact Step.sound Leaves.deferredKeys (offerInputs tb msg s id a hint)
    (Input.reads_cons readsId (Input.reads_cons readsHint (Input.reads_cons readsMessage
      (Input.reads_cons (readsCell.to (cellK_image tb msg s).symm) Input.reads_nil))))
    (Data.offer P) (by decide)

/-- Poll reading freezes the cell before its ordered collection fold. -/
theorem poll_reads (A : Ty) (tb : Table) (msg : Nat → Val) (s : State)
    {cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.pollStep A cellSrc) env path vals
      ((imageAt Leaves.deferredKeys (.prod (.prod (.option P) (.list (offerTy P))) (cellTy P))).toVal
        ((Data.poll P).eval (Γ := (Data.CellInputs P).types) Leaves.deferredKeys (cellK tb msg s, ()))) := by
  apply Reads.of_annotations (source := Queue.pollStep P cellSrc)
    (same := congrFun (congrFun (Data.poll_parameter A cellSrc) env) path)
  exact Step.sound (Γ := (Data.CellInputs P).types) Leaves.deferredKeys (cellK tb msg s, ())
    (Input.reads_cons (readsCell.to (cellK_image tb msg s).symm) Input.reads_nil)
    (Data.poll P) (by decide) (Step.scope_of_alignment _ depth)

/-- Poll reading observes the exact conditional reply, entering offers, and model cell. -/
theorem poll_encoded (A : Ty) (tb : Table) (msg : Nat → Val) (s : State)
    {cellSrc : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    (depth : vals.length = env.names.length)
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.pollStep A cellSrc) env path vals
      (if (!decide (s.messages.length = 0) && decide (s.takers.length = 0)) then
        Val.tuple [Val.tuple [pollReplyVal msg s.messages.head?,
          Val.list ((s.offers.take (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)).map (offerVal tb msg))],
          cellVal tb msg {s with messages := s.messages.drop 1 ++ (s.offers.take (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)).flatMap (·.rest), offers := s.offers.drop (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)}]
      else Val.tuple [Val.tuple [Store.Val.none, Val.list []], cellVal tb msg s]) := by
  apply (poll_reads A tb msg s depth readsCell).to
  rw [poll_value]
  by_cases accepted : (!decide (s.messages.length = 0) && decide (s.takers.length = 0)) = true
  · rw [if_pos accepted, if_pos accepted]
    change Val.tuple [Val.tuple [(imageAt Leaves.deferredKeys (.option P)).toVal ((s.messages.map msg).head?),
      (imageAt Leaves.deferredKeys (.list (offerTy P))).toVal ((s.offers.take (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)).map (offerK tb msg))],
      (imageAt Leaves.deferredKeys (cellTy P)).toVal (cellK tb msg {s with messages := s.messages.drop 1 ++ (s.offers.take (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)).flatMap (·.rest), offers := s.offers.drop (Nat.min (s.capacity.getD 0 - (s.messages.drop 1).length) s.offers.length)})] = _
    rw [headK_image, offersK_image, cellK_image]
  · rw [if_neg accepted, if_neg accepted]
    change Val.tuple [Val.tuple [Store.Val.none, Val.list []], (imageAt Leaves.deferredKeys (cellTy P)).toVal (cellK tb msg s)] = _
    rw [cellK_image]

end Effect4.Queue.Model
