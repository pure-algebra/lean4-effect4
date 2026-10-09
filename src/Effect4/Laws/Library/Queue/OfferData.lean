import Effect4.Laws.Library.Queue.Data

/-!
# Queue offer data encoding

Placement: helper of queue-steps-agree, translation-simulation, R10.
The consumer is the existing public Queue.offerStep_agrees theorem.
The observation is the raw reply and next cell encoded by the offer step.
Caller sources read the supplied table, message map, and current model state.
This helper requires no new model premise. The consumer retains its profile, request, and freshness premises.
The helper establishes no notification model equation, allocation, progress, or host behavior.
-/

set_option autoImplicit false
namespace Effect4.Queue.Model
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Schema Effect4.Schema.Model Effect4.Modules

/-- The offer data's encoded branches, before the independent model chooses a transition. -/
theorem offer_encoded (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat)
    (hint : DeferredKey) {idSrc hintSrc messageSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val}
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsMessage : Reads messageSrc env path vals (msg a))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    let pending := cellOf (.nat (s.capacity.getD 0)) (.list (s.messages.map msg))
      (.list (s.offers.map (offerVal tb msg) ++
        [offerOf (.bool false) (.promise hint) (.promise (tb.handle id)) (.list [msg a])]))
      (.list (s.takers.map (takerVal tb)))
    let accepted := cellOf (.nat (s.capacity.getD 0)) (.list ((s.messages ++ [a]).map msg))
      (.list (s.offers.map (offerVal tb msg))) (.list (s.takers.map (takerVal tb)))
    Reads (Queue.offerStep A idSrc hintSrc messageSrc cellSrc) env path vals
      (if !decide (s.offers.length = 0) then
        Val.tuple [Val.tuple [Store.Val.none, .list []], pending]
      else if decide (s.messages.length < s.capacity.getD 0) then
        Val.tuple [Val.tuple [Store.Val.some (.bool true), .list ((s.takers.take 1).map (takerVal tb))], accepted]
      else
        Val.tuple [Val.tuple [Store.Val.none,
          .list ((if s.messages.length = 0 then [] else s.takers.take 1).map (takerVal tb))], pending]) := by
  have reads := offer_reads A tb msg s id a hint readsId readsHint readsMessage readsCell
  refine reads.to ?_
  change (imageAt Leaves.deferredKeys (.prod (.prod (.option .bool) (.list takerTy)) (cellTy P))).toVal
    ((Data.offer P).eval Leaves.deferredKeys (offerInputs tb msg s id a hint)) = _
  let pendingCarrier : CarrierAt Leaves.deferredKeys (cellTy P) :=
    (s.capacity.getD 0, (s.messages.map msg,
      (s.offers.map (offerK tb msg) ++ ([(false, (hint, (tb.handle id, ([msg a], ()))))] : List (CarrierAt Leaves.deferredKeys (offerTy P))),
        (s.takers.map (takerK tb), ()))))
  let acceptedCarrier : CarrierAt Leaves.deferredKeys (cellTy P) :=
    (s.capacity.getD 0, (s.messages.map msg ++ [msg a],
      (s.offers.map (offerK tb msg), (s.takers.map (takerK tb), ()))))
  change (imageAt Leaves.deferredKeys (.prod (.prod (.option .bool) (.list takerTy)) (cellTy P))).toVal
    (if !decide ((s.offers.map (offerK tb msg)).length = 0) then ((Option.none, []), pendingCarrier)
    else if decide ((s.messages.map msg).length < s.capacity.getD 0) then
      ((Option.some true, if decide ((s.messages.map msg ++ [msg a]).length = 0) then []
        else (s.takers.map (takerK tb)).take 1), acceptedCarrier)
    else ((Option.none, if decide ((s.messages.map msg).length = 0) then []
        else (s.takers.map (takerK tb)).take 1), pendingCarrier)) = _
  have offers : (imageAt Leaves.deferredKeys (offerTy P)).toVal ∘ offerK tb msg = offerVal tb msg :=
    funext (offerK_image tb msg)
  have takers : (imageAt Leaves.deferredKeys takerTy).toVal ∘ takerK tb = takerVal tb :=
    funext (takerK_image tb)
  have pendingImage : (imageAt Leaves.deferredKeys (cellTy P)).toVal pendingCarrier =
      cellOf (.nat (s.capacity.getD 0)) (.list (s.messages.map msg))
        (.list (s.offers.map (offerVal tb msg) ++
          [offerOf (.bool false) (.promise hint) (.promise (tb.handle id)) (.list [msg a])]))
        (.list (s.takers.map (takerVal tb))) := by
    change cellOf _ (.list ((s.messages.map msg).map _root_.id))
      (.list (((s.offers.map (offerK tb msg)) ++ _).map (imageAt Leaves.deferredKeys (offerTy P)).toVal))
      (.list ((s.takers.map (takerK tb)).map (imageAt Leaves.deferredKeys takerTy).toVal)) = _
    rw [List.map_id, List.map_append, List.map_map, List.map_map, offers, takers]
    rfl
  have acceptedImage : (imageAt Leaves.deferredKeys (cellTy P)).toVal acceptedCarrier =
      cellOf (.nat (s.capacity.getD 0)) (.list ((s.messages ++ [a]).map msg))
        (.list (s.offers.map (offerVal tb msg))) (.list (s.takers.map (takerVal tb))) := by
    change cellOf _ (.list ((s.messages.map msg ++ [msg a]).map _root_.id))
      (.list ((s.offers.map (offerK tb msg)).map (imageAt Leaves.deferredKeys (offerTy P)).toVal))
      (.list ((s.takers.map (takerK tb)).map (imageAt Leaves.deferredKeys takerTy).toVal)) = _
    rw [List.map_id, List.map_map, List.map_map, offers, takers, List.map_append]
    rfl
  simp only [List.length_map]
  by_cases pending : s.offers.length = 0
  · rw [decide_eq_true pending]
    by_cases room : s.messages.length < s.capacity.getD 0
    · rw [decide_eq_true room]
      have nonempty : (s.messages.map msg ++ [msg a]).length ≠ 0 := by
        rw [List.length_append, List.length_singleton]
        omega
      rw [decide_eq_false nonempty]
      change Val.tuple [Val.tuple [Store.Val.some (.bool true),
        .list (((s.takers.map (takerK tb)).take 1).map (imageAt Leaves.deferredKeys takerTy).toVal)],
        (imageAt Leaves.deferredKeys (cellTy P)).toVal acceptedCarrier] = _
      rw [acceptedImage, ← List.map_take, List.map_map, takers]
      rfl
    · rw [decide_eq_false room]
      by_cases empty : s.messages.length = 0
      · rw [decide_eq_true empty]
        change Val.tuple [Val.tuple [Store.Val.none, .list []],
          (imageAt Leaves.deferredKeys (cellTy P)).toVal pendingCarrier] = _
        rw [pendingImage]
        simp only [empty, ↓reduceIte, List.map_nil]
        rfl
      · rw [decide_eq_false empty]
        change Val.tuple [Val.tuple [Store.Val.none,
          .list (((s.takers.map (takerK tb)).take 1).map (imageAt Leaves.deferredKeys takerTy).toVal)],
          (imageAt Leaves.deferredKeys (cellTy P)).toVal pendingCarrier] = _
        rw [pendingImage, ← List.map_take, List.map_map, takers]
        simp only [empty, ↓reduceIte]
        rfl
  · rw [decide_eq_false pending]
    change Val.tuple [Val.tuple [Store.Val.none, .list []],
      (imageAt Leaves.deferredKeys (cellTy P)).toVal pendingCarrier] = _
    rw [pendingImage]
    rfl

end Effect4.Queue.Model
