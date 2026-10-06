import Effect4.Laws.Modules.Queue.Relation
import Effect4.Laws.Modules.Reading

/-!
# Reading the Queue's step terms: the cell's records and the Queue's passes (decisions row 255)

A step goal says that a step's source term reads a value (`Reads`,
`src/Effect4/Laws/Modules/Reading.lean`). The shared reading rules give what each authoring
builder and each word of a step term reads. This file adds what the Queue's steps need beside
them.

- **The cell's records**: what a read answers and what an overwrite stores, one `rfl` for each
  field of the cell, of a taker and of an offer.
- **The passes** of `src/Effect4/Modules/Queue/Steps.lean` on the encoding of a model's lists:
  the two records, the wake, the identity tests, the two removals and the accept pass.
- **Two facts of lists** serve those passes: a fold that keeps is a filter (`foldl_keep`), and
  a fold that appends each element's gift is `flatMap` (`foldl_append_flatMap`). They are in
  `Effect4.Constructive.List` (`src/Effect4/Data/Constructive.lean`).

Placement. Concept `translation-simulation`, requirement R10. Every lemma here is a helper of
the six step goals (`src/Effect4/Laws/Modules/Queue/Steps.lean`), parts of the proposed claim
`queue-expansion-agrees`. Its consumer is the proof of a step goal. The lemmas establish
nothing of a model's step by themselves.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Constructive.List (foldl_keep foldl_append_flatMap)

/-! ## The cell's records: what a read answers and what an overwrite stores -/

theorem cell_cap (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "cap" = some c := rfl
theorem cell_msgs (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "msgs" = some m := rfl
theorem cell_offers (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "offers" = some o := rfl
theorem cell_takers (c m o t : Val) :
    Machine.Record.read false (cellOf c m o t) "takers" = some t := rfl
theorem cell_setMsgs (c m o t v : Val) :
    Machine.Record.set (cellOf c m o t) "msgs" v = some (cellOf c v o t) := rfl
theorem cell_setOffers (c m o t v : Val) :
    Machine.Record.set (cellOf c m o t) "offers" v = some (cellOf c m v t) := rfl
theorem cell_setTakers (c m o t v : Val) :
    Machine.Record.set (cellOf c m o t) "takers" v = some (cellOf c m o v) := rfl
theorem taker_id (h i : Val) : Machine.Record.read false (takerOf h i) "id" = some i := rfl
theorem offer_id (b h i r : Val) :
    Machine.Record.read false (offerOf b h i r) "id" = some i := rfl
theorem offer_rest (b h i r : Val) :
    Machine.Record.read false (offerOf b h i r) "rest" = some r := rfl
theorem taker_build (i h : Val) :
    Machine.Record.build ["id", "hint"] [i, h] = some (takerOf h i) := rfl
theorem offer_build (i h b r : Val) :
    Machine.Record.build ["id", "hint", "batch", "rest"] [i, h, b, r] = some (offerOf b h i r) :=
  rfl


/-! ## The passes, on the encoding of a model's lists -/

section Passes

variable {env : Env} {path : List Nat} {vals : List Val}

/-- A waiting taker's record, built from an identity and a hint. -/
theorem reads_mkTaker {id hint : TermSrc} {i h : Val} (hid : Reads id env path vals i)
    (hhint : Reads hint env path vals h) :
    Reads (Queue.mkTaker id hint) env path vals (takerOf h i) :=
  reads_record (.cons hid (.cons hhint .nil)) (taker_build i h)

/-- A pending offer's record. -/
theorem reads_mkOffer (A : Ty) {id hint batch rest : TermSrc} {i h b r : Val}
    (hid : Reads id env path vals i) (hhint : Reads hint env path vals h)
    (hbatch : Reads batch env path vals b) (hrest : Reads rest env path vals r) :
    Reads (Queue.mkOffer A id hint batch rest) env path vals (offerOf b h i r) :=
  reads_record (.cons hid (.cons hhint (.cons hbatch (.cons hrest .nil)))) (offer_build i h b r)

/-- The wake's pass: the earliest stored taker, where a message is buffered. -/
theorem reads_wake {takers msgs : TermSrc} {ts ms : List Val}
    (htakers : Reads takers env path vals (Val.list ts))
    (hmsgs : Reads msgs env path vals (Val.list ms)) :
    Reads (Queue.wake takers msgs) env path vals
      (Val.list (if ms.length = 0 then [] else ts.take 1)) := by
  refine (reads_ifT (reads_isEmpty hmsgs) (reads_noneOf htakers)
    (reads_take htakers (reads_nat 1 env path vals))).to ?_
  by_cases empty : ms.length = 0
  · rw [decide_eq_true empty, if_pos rfl, if_pos empty]
  · rw [decide_eq_false empty, if_neg Bool.false_ne_true, if_neg empty]

/-- The identity of a folded taker against the request's, under the fold's binders. -/
theorem reads_sameTaker {id : TermSrc} (tb : Table) (injective : tb.Injective) (i : Nat)
    (depth : vals.length = env.names.length)
    (hid : Captured id env path vals (Val.promise (tb.handle i))) (acc : Val) (t : Taker) :
    Reads (same (field (minted (env.mint "item")) "id") id)
      (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc, takerVal tb t])
      (Val.bool (decide (t.id = i))) :=
  (reads_same (reads_field (reads_minted_item depth path acc (takerVal tb t)) (taker_id _ _))
    (hid.underFold acc (takerVal tb t))).to (by rw [injective.decides])

/-- `enrolled`: whether the request waits among the takers. -/
theorem reads_enrolled {takers id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.enrolled takers id) env path vals
      (Val.bool (ts.foldl (fun found t => found || decide (t.id = i)) false)) :=
  reads_foldWith_model (takerVal tb) Val.bool (fun found t => found || decide (t.id = i)) ts
    false ⟨0, 1, 1⟩ htakers (reads_bool false env path vals) fun found t =>
      reads_orT (reads_minted_acc depth path (Val.bool found) (takerVal tb t))
        (reads_sameTaker tb injective i depth hid (Val.bool found) t)

/-- `isHead`: whether the request is the earliest taker. -/
theorem reads_isHead {takers id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.isHead takers id) env path vals
      (Val.bool ((ts.take 1).foldl (fun _ t => decide (t.id = i)) false)) :=
  reads_foldWith_model (takerVal tb) Val.bool (fun _ t => decide (t.id = i)) (ts.take 1) false
    ⟨0, 1, 1⟩ ((reads_take htakers (reads_nat 1 env path vals)).to (by rw [List.map_take]))
    (reads_bool false env path vals) fun found t =>
      reads_sameTaker tb injective i depth hid (Val.bool found) t

/-- `removeTaker`: the takers without the request. -/
theorem reads_removeTaker {takers id : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.removeTaker takers id) env path vals
      (Val.list ((ts.filter (fun t => t.id != i)).map (takerVal tb))) := by
  have folded : Reads (Queue.removeTaker takers id) env path vals
      (Val.list ((ts.foldl (fun kept t => if t.id = i then kept else kept ++ [t]) []).map
        (takerVal tb))) :=
    reads_foldWith_model (takerVal tb)
    (fun kept : List Taker => Val.list (kept.map (takerVal tb)))
    (fun kept t => if t.id = i then kept else kept ++ [t]) ts [] ⟨0, 1, 1⟩ htakers
    (reads_noneOf htakers) fun kept t => by
      refine (reads_ifT (reads_sameTaker tb injective i depth hid _ t)
        (reads_minted_acc depth path _ (takerVal tb t))
        (reads_snoc (reads_minted_acc depth path _ (takerVal tb t))
          (reads_minted_item depth path _ (takerVal tb t)))).to ?_
      by_cases same : t.id = i
      · rw [decide_eq_true same, if_pos rfl, if_pos same]
      · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.map_append]
        rfl
  exact folded.to (by rw [foldl_keep, List.nil_append]; rfl)

/-- The identity of a folded offer against the request's, under the fold's binders. -/
theorem reads_sameOffer {id : TermSrc} (tb : Table) (msg : Nat → Val) (injective : tb.Injective)
    (i : Nat) (depth : vals.length = env.names.length)
    (hid : Captured id env path vals (Val.promise (tb.handle i))) (acc : Val) (o : Offer) :
    Reads (same (field (minted (env.mint "item")) "id") id)
      (env.push [env.mint "acc", env.mint "item"]) path (vals ++ [acc, offerVal tb msg o])
      (Val.bool (decide (o.id = i))) :=
  (reads_same
    (reads_field (reads_minted_item depth path acc (offerVal tb msg o)) (offer_id _ _ _ _))
    (hid.underFold acc (offerVal tb msg o))).to (by rw [injective.decides])

/-- `removeOffer`: the pending offers without the request. -/
theorem reads_removeOffer {offers id : TermSrc} (tb : Table) (msg : Nat → Val)
    (injective : tb.Injective) (os : List Offer) (i : Nat)
    (depth : vals.length = env.names.length)
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg))))
    (hid : Captured id env path vals (Val.promise (tb.handle i))) :
    Reads (Queue.removeOffer offers id) env path vals
      (Val.list ((os.filter (fun o => o.id != i)).map (offerVal tb msg))) := by
  have folded : Reads (Queue.removeOffer offers id) env path vals
      (Val.list ((os.foldl (fun kept o => if o.id = i then kept else kept ++ [o]) []).map
        (offerVal tb msg))) :=
    reads_foldWith_model (offerVal tb msg)
      (fun kept : List Offer => Val.list (kept.map (offerVal tb msg)))
      (fun kept o => if o.id = i then kept else kept ++ [o]) os [] ⟨0, false, []⟩ hoffers
      (reads_noneOf hoffers) fun kept o => by
        refine (reads_ifT (reads_sameOffer tb msg injective i depth hid _ o)
          (reads_minted_acc depth path _ (offerVal tb msg o))
          (reads_snoc (reads_minted_acc depth path _ (offerVal tb msg o))
            (reads_minted_item depth path _ (offerVal tb msg o)))).to ?_
        by_cases same : o.id = i
        · rw [decide_eq_true same, if_pos rfl, if_pos same]
        · rw [decide_eq_false same, if_neg Bool.false_ne_true, if_neg same, List.map_append]
          rfl
  exact folded.to (by rw [foldl_keep, List.nil_append]; rfl)

/-- `fitting`: how many pending offers enter the room. -/
theorem reads_fitting {room offers : TermSrc} {r : Nat} {os : List Val}
    (hroom : Reads room env path vals (Val.nat r))
    (hoffers : Reads offers env path vals (Val.list os)) :
    Reads (Queue.fitting room offers) env path vals (Val.nat (Nat.min r os.length)) :=
  reads_minT hroom (reads_len hoffers)

/-- `entering`: the offers that enter, on the encoding of the pending offers. -/
theorem reads_entering {room offers : TermSrc} (tb : Table) (msg : Nat → Val) (r : Nat)
    (os : List Offer) (hroom : Reads room env path vals (Val.nat r))
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg)))) :
    Reads (Queue.entering room offers) env path vals
      (Val.list ((os.take (Nat.min r os.length)).map (offerVal tb msg))) :=
  (reads_take hoffers (reads_fitting hroom hoffers)).to
    (by rw [List.length_map, List.map_take])

/-- `staying`: the offers that stay pending. -/
theorem reads_staying {room offers : TermSrc} (tb : Table) (msg : Nat → Val) (r : Nat)
    (os : List Offer) (hroom : Reads room env path vals (Val.nat r))
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg)))) :
    Reads (Queue.staying room offers) env path vals
      (Val.list ((os.drop (Nat.min r os.length)).map (offerVal tb msg))) :=
  (reads_drop hoffers (reads_fitting hroom hoffers)).to
    (by rw [List.length_map, List.map_drop])

/-- `gained`: the buffer with the messages of the offers that enter. -/
theorem reads_gained {room msgs offers : TermSrc} (tb : Table) (msg : Nat → Val) (r : Nat)
    (ms : List Nat) (os : List Offer) (depth : vals.length = env.names.length)
    (hroom : Reads room env path vals (Val.nat r))
    (hmsgs : Reads msgs env path vals (Val.list (ms.map msg)))
    (hoffers : Reads offers env path vals (Val.list (os.map (offerVal tb msg)))) :
    Reads (Queue.gained room msgs offers) env path vals
      (Val.list ((ms ++ (os.take (Nat.min r os.length)).flatMap (·.rest)).map msg)) := by
  have folded : Reads (Queue.gained room msgs offers) env path vals
      (Val.list (((os.take (Nat.min r os.length)).foldl (fun buffer o => buffer ++ o.rest)
        ms).map msg)) :=
    reads_foldWith_model (offerVal tb msg) (fun buffer : List Nat => Val.list (buffer.map msg))
      (fun buffer o => buffer ++ o.rest) (os.take (Nat.min r os.length)) ms ⟨0, false, []⟩
      (reads_entering tb msg r os hroom hoffers) hmsgs fun buffer o =>
        (reads_append (reads_minted_acc depth path _ (offerVal tb msg o))
          (reads_field (reads_minted_item depth path _ (offerVal tb msg o))
            (offer_rest _ _ _ _))).to (by rw [List.map_append])
  exact folded.to (by rw [foldl_append_flatMap])

end Passes

end Effect4.Queue.Model
