import Effect4.Laws.Modules.Queue.Relation
import Effect4.Laws.Modules.Queue.Reading
import Effect4.Laws.Program.Typed.ListFold
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# The Queue's six steps agree with the abstract model: the step goals (decisions row 255)

Each step term of `src/Effect4/Modules/Queue/Steps.lean` has one statement here: from a cell
that holds a state of the first profile, the step's answer and stored value are the encoding of
the model's step, and its lists are the model's signals in order (the design's F3,
`docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`). The relation is
in `src/Effect4/Laws/Modules/Queue/Relation.lean`.

Placement. Concept `translation-simulation`. Requirement R10, as parts of the proposed claim
`queue-expansion-agrees`. The consumer of each step goal is the wrapper's law, in the public
path's slice. Reach, for each goal:

- the domain is `FirstProfile`, with the request's premise `Requested`
  (`src/Effect4/Laws/Modules/Queue/Profile.lean`);
- the table's injectivity is a written premise, and the hint that the step sets is written in
  the conclusion's table (`Table.afterTake`, `Table.afterOffer`);
- the observation is the reply, the stored value and the ordered notifications: every signal
  of the model, and no other (`Notified`);
- the statement holds at every scope, for every caller's term that reads the step's arguments
  (`Reads`, `Captured`).

`step_updates` joins a goal to the store: a step term that reads the pair of a reply and a next
value is one atomic update of the cell (`refStep_modify`). `step_keeps_cell` gives the typed
half (`ListFoldRules.step`). `sizeStep` is a term over a read, and `cell_read` is its store law
(`refStep_get`).

The six statements are proved, each in place of its planned goal (decisions row 203). The
proofs read each builder of a step through `src/Effect4/Laws/Modules/Queue/Reading.lean`, and
they put the model's step in closed form on the profile: `acceptLoop_single` and
`wake_profile` give the offers that enter and the taker to wake.

The statements establish no delivery, no cancellation law, no liveness and nothing of a
wrapper. An equal value in the model says nothing of a host. The finite controls are
`Test/Program/QueueAgreement.lean` and `Test/Program/QueueRelation.lean`: each statement's
conclusion on every state of a universe of 200 states, and each statement's pinned axioms.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Typed

/-! ## The connector to the store -/

/-- **One atomic update.** A step term that reads the pair of a reply and a next value, under
the cell's current value as its last binder, is one `Ref.modify`: the store step reads the cell
once, answers the reply and writes the next value. Stated once, for the five steps of a
`Ref.modify`. Consumer: the wrapper's law, which runs each step so. It is the census clause
`refStep_modify`, and it needs no typing. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem step_updates {step : TermSrc} {env : Env} {path : List Nat} {current : String}
    {captured : List Val} {stores : Stores} {q : RefKey} {cell reply next : Val}
    (held : refPeek stores.refs q = some cell)
    (reads : Reads step (env.push [current]) path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    ∃ f, step (env.push [current]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q next }, reply) := by
  obtain ⟨f, elaborated, value⟩ := reads
  refine ⟨f, elaborated, ?_⟩
  show (refStep (.refModify q f captured) stores.refs).map
    (fun step => ({ stores with refs := step.2 }, step.1)) = _
  rw [refStep_modify stores.refs q f captured cell reply next held value]
  rfl

/-- **The typed half of the connector.** A step term that the checker types at the pair of a
reply type and the cell's type keeps the cell a member of its type, and its reply is a member
of the reply type. It is `ListFoldRules.step`, read at the value that the step answers.
Consumer: the wrapper's law, with a step's typing statement
(`src/Effect4/Laws/Modules/Queue/Typing.lean`). -/
@[semantics "store-typing" (requirement := R4)]
theorem step_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {w : Typed.World} {tys : TyEnv} {captured : List Val} (typedEnv : EnvTyped w tys captured)
    {f : Term} {C B : Ty} (typed : termTy sig (tys ++ [C]) f = some (.prod B C))
    {stores : Stores} {q : RefKey} {cell reply next : Val}
    (held : refPeek stores.refs q = some cell) (member : Fits w cell C)
    (value : evalTerm (captured ++ [cell]) f = some (Val.tuple [reply, next])) :
    Fits w reply B ∧ Fits w next C := by
  obtain ⟨b, a, answered, -, fitsReply, fitsNext⟩ :=
    (fold_typed_atomic_update sig).step atoms w tys captured typedEnv f C B typed stores q cell
      held member
  rw [value] at answered
  have same : Val.tuple [reply, next] = Val.tuple [b, a] := Option.some.inj answered
  have parts : [reply, next] = [b, a] := Store.Val.list.inj same
  obtain ⟨rfl, rest⟩ := List.cons.inj parts
  obtain ⟨rfl, -⟩ := List.cons.inj rest
  exact ⟨fitsReply, fitsNext⟩

/-- **The read law of `size`.** A `Ref.get` of the cell answers its value and leaves the
stores: the size step is a term over that value, and it writes nothing. It is the census clause
`refStep_get`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cell_read {stores : Stores} {q : RefKey} {cell : Val}
    (held : refPeek stores.refs q = some cell) :
    syncOpStep (.refGet q) stores = some (stores, cell) := by
  show (refStep (.refGet q) stores.refs).map
    (fun step => ({ stores with refs := step.2 }, step.1)) = _
  rw [refStep_get stores.refs q cell held]
  rfl

/-! ## The model's side, in closed form

Steps of the step goals: what the model's wake names on the profile, as stored takers. -/

/-- The takers that a profile state's wake names: the earliest, where a message is buffered. -/
def toWake (s : State) : List Taker := if s.messages.length = 0 then [] else s.takers.take 1

/-- **The model's wake on the profile, as the takers to wake** (`wake_profile`). -/
theorem wake_toWake {s : State} (h : FirstProfile s) :
    wake s = (toWake s).map (fun t => (⟨t.id, .again⟩ : Signal)) := by
  rw [wake_profile h]
  unfold toWake
  cases s.takers with
  | nil =>
    by_cases empty : s.messages.length = 0
    · rw [if_pos empty]; rfl
    · rw [if_neg empty]; rfl
  | cons t ts =>
    cases hm : s.messages with
    | nil => rfl
    | cons m ms => rfl

/-- Each taker to wake is a stored taker. -/
theorem toWake_stored (s : State) : ∀ t ∈ toWake s, t ∈ s.takers := by
  intro t member
  unfold toWake at member
  by_cases empty : s.messages.length = 0
  · rw [if_pos empty] at member
    exact absurd member List.not_mem_nil
  · rw [if_neg empty] at member
    exact List.mem_of_mem_take member

/-- The wake's pass on the encoding of a buffer and of takers reads the takers to wake. -/
theorem wake_encoded (tb : Table) (msg : Nat → Val) (messages : List Nat) (takers : List Taker) :
    (if (messages.map msg).length = 0 then [] else (takers.map (takerVal tb)).take 1) =
      (if messages.length = 0 then [] else takers.take 1).map (takerVal tb) := by
  rw [List.length_map]
  by_cases empty : messages.length = 0
  · rw [if_pos empty, if_pos empty]; rfl
  · rw [if_neg empty, if_neg empty, List.map_take]

theorem isDone_opened {s : State} (opened : s.phase = .opened) : isDone s = false := by
  unfold isDone
  rw [opened]

theorem isOpen_opened {s : State} (opened : s.phase = .opened) : isOpen s = true := by
  unfold isOpen
  rw [opened]

theorem settle_opened {s : State} (opened : s.phase = .opened) : settle s = (s, []) := by
  unfold settle
  rw [opened]

/-- The model's `withdrawOffer` in an opened queue: the offer leaves, and the wake is named. -/
theorem withdrawOffer_opened {s : State} (opened : s.phase = .opened) (id : Nat) :
    withdrawOffer s id =
      ({ s with offers := s.offers.filter (fun o => o.id != id) },
        wake { s with offers := s.offers.filter (fun o => o.id != id) }) := by
  unfold withdrawOffer
  rw [isDone_opened opened, if_neg Bool.false_ne_true]
  show ((settle { s with offers := s.offers.filter (fun o => o.id != id) }).1,
    (settle { s with offers := s.offers.filter (fun o => o.id != id) }).2 ++
      wake (settle { s with offers := s.offers.filter (fun o => o.id != id) }).1) = _
  rw [settle_opened (s := { s with offers := s.offers.filter (fun o => o.id != id) }) opened]
  rfl

/-! ## The table's one change frames every other request -/

/-- The hint of another request stays. -/
theorem takerVal_renew {tb : Table} {t : Taker} {id : Nat} (other : t.id ≠ id)
    (hint : DeferredKey) : takerVal (tb.renew id hint) t = takerVal tb t := by
  show takerOf (Val.promise (if t.id = id then hint else tb.hint t.id))
    (Val.promise (tb.handle t.id)) = _
  rw [if_neg other]
  rfl

theorem offerVal_renew {tb : Table} {o : Offer} {id : Nat} (other : o.id ≠ id)
    (hint : DeferredKey) (msg : Nat → Val) :
    offerVal (tb.renew id hint) msg o = offerVal tb msg o := by
  show offerOf (.bool o.batch) (Val.promise (if o.id = id then hint else tb.hint o.id))
    (Val.promise (tb.handle o.id)) (.list (o.rest.map msg)) = _
  rw [if_neg other]
  rfl

/-- Stored takers that are not the request keep their records. -/
theorem takers_renew (tb : Table) (ts : List Taker) (id : Nat) (hint : DeferredKey)
    (others : ∀ t ∈ ts, t.id ≠ id) :
    ts.map (takerVal (tb.renew id hint)) = ts.map (takerVal tb) :=
  List.map_congr_left fun t member => takerVal_renew (others t member) hint

/-- Pending offers that are not the request keep their records. -/
theorem offers_renew (tb : Table) (msg : Nat → Val) (os : List Offer) (id : Nat)
    (hint : DeferredKey) (others : ∀ o ∈ os, o.id ≠ id) :
    os.map (offerVal (tb.renew id hint) msg) = os.map (offerVal tb msg) :=
  List.map_congr_left fun o member => offerVal_renew (others o member) hint msg

/-- The cell after a fresh offer pends: the stored records stay, and the new offer holds the
step's hint. -/
theorem cell_pended (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat) (hint : DeferredKey)
    (foreign : ∀ t ∈ s.takers, t.id ≠ id) (fresh : ∀ o ∈ s.offers, o.id ≠ id) :
    cellVal (tb.renew id hint) msg { s with offers := s.offers ++ [⟨id, false, [a]⟩] } =
      cellOf (.nat (s.capacity.getD 0)) (.list (s.messages.map msg))
        (.list (s.offers.map (offerVal tb msg) ++
          [offerOf (.bool false) (Val.promise hint) (Val.promise (tb.handle id))
            (.list [msg a])]))
        (.list (s.takers.map (takerVal tb))) := by
  show cellOf _ _
    (.list ((s.offers ++ [(⟨id, false, [a]⟩ : Offer)]).map (offerVal (tb.renew id hint) msg)))
    (.list (s.takers.map (takerVal (tb.renew id hint)))) = _
  rw [List.map_append, offers_renew tb msg s.offers id hint fresh,
    takers_renew tb s.takers id hint foreign]
  have new : offerVal (tb.renew id hint) msg ⟨id, false, [a]⟩ =
      offerOf (.bool false) (Val.promise hint) (Val.promise (tb.handle id)) (.list [msg a]) := by
    show offerOf (.bool false) (Val.promise (if id = id then hint else tb.hint id))
      (Val.promise (tb.handle id)) (.list [msg a]) = _
    rw [if_pos rfl]
  rw [List.map_cons, List.map_nil, new]

/-! ## The model's `offer` on the profile, in closed form -/

theorem offer_behind {s : State} (h : FirstProfile s) (id a : Nat) (pending : s.offers ≠ []) :
    offer s id a = ({ s with offers := s.offers ++ [⟨id, false, [a]⟩] }, .wait, []) := by
  cases held : s.offers with
  | nil => exact absurd held pending
  | cons o os =>
    unfold offer isOpen
    rw [h.opened, h.suspend, held]
    rfl

theorem hasRoom_iff {s : State} {c : Nat} (capacity : s.capacity = some (c + 1)) :
    hasRoom s = decide (s.messages.length < c + 1) := by
  unfold hasRoom room
  rw [capacity]
  show decide (0 < c + 1 - s.messages.length) = _
  exact decide_eq_decide.mpr ⟨fun h => by omega, fun h => by omega⟩

theorem offer_room {s : State} (h : FirstProfile s) {c : Nat}
    (capacity : s.capacity = some (c + 1)) (id a : Nat) (noPending : s.offers = [])
    (free : s.messages.length < c + 1) :
    offer s id a = ({ s with messages := s.messages ++ [a] }, .accepted true,
      wake { s with messages := s.messages ++ [a] }) := by
  have room : hasRoom s = true := by rw [hasRoom_iff capacity, decide_eq_true free]
  unfold offer isOpen
  rw [room, h.opened, h.suspend, noPending]
  rfl

theorem offer_full {s : State} (h : FirstProfile s) {c : Nat}
    (capacity : s.capacity = some (c + 1)) (id a : Nat) (noPending : s.offers = [])
    (full : ¬ s.messages.length < c + 1) :
    offer s id a = ({ s with offers := s.offers ++ [⟨id, false, [a]⟩] }, .wait,
      wake { s with offers := s.offers ++ [⟨id, false, [a]⟩] }) := by
  have room : hasRoom s = false := by rw [hasRoom_iff capacity, decide_eq_false full]
  unfold offer isOpen
  rw [room, h.opened, h.suspend, noPending]
  rfl

/-! ## The model's consuming steps on the profile, in closed form -/

/-- How many pending offers enter the room of a state whose capacity is `c + 1`. -/
def fitCount (c : Nat) (s : State) : Nat := Nat.min (c + 1 - s.messages.length) s.offers.length

/-- The state after the offers that fit entered the buffer. -/
def afterAccept (c : Nat) (s : State) : State :=
  { s with messages := s.messages ++ (s.offers.take (fitCount c s)).flatMap (·.rest),
           offers := s.offers.drop (fitCount c s) }

/-- **After a consuming step on the profile**: the offers that fit enter and are answered, and
the earliest taker is named where a message is buffered (`acceptLoop_single`,
`wake_profile`). -/
theorem afterConsume_closed {s : State} (h : FirstProfile s) {c : Nat}
    (capacity : s.capacity = some (c + 1)) :
    afterConsume s =
      (afterAccept c s,
        (s.offers.take (fitCount c s)).map (fun o => (⟨o.id, .offered true⟩ : Signal)) ++
          (toWake (afterAccept c s)).map (fun t => (⟨t.id, .again⟩ : Signal))) := by
  have accepted : accept s = (afterAccept c s,
      (s.offers.take (fitCount c s)).map (fun o => (⟨o.id, .offered true⟩ : Signal))) := by
    unfold accept afterAccept fitCount
    rw [acceptLoop_single (room s) s.messages s.offers h.offers]
    unfold entered room
    rw [capacity]
    rfl
  have next : FirstProfile (afterAccept c s) := by
    have kept := accept_profile h
    rw [accepted] at kept
    exact kept
  unfold afterConsume
  rw [accepted]
  show ((settle (afterAccept c s)).1, _ ++ (settle (afterAccept c s)).2 ++
    wake (settle (afterAccept c s)).1) = _
  rw [settle_opened next.opened, List.append_nil, wake_toWake next]

/-- A consuming pull from a buffered state takes from the buffer. -/
theorem pull_buffered {s : State} {m : Nat} {ms : List Nat} (buffered : s.messages = m :: ms)
    (max : Nat) :
    pull s max = ((m :: ms).take max, { s with messages := (m :: ms).drop max }, []) := by
  unfold pull
  rw [buffered]
  rfl

/-- The model's `poll` on the profile, where it does not consume: no message is buffered, or a
taker waits. -/
theorem poll_idle {s : State} (h : FirstProfile s) (idle : s.messages = [] ∨ s.takers ≠ []) :
    poll s = (s, none, []) := by
  unfold poll
  rw [isDone_opened h.opened, ready_profile h]
  rcases idle with empty | waiting
  · rw [empty]
    rfl
  · cases held : s.takers with
    | nil => exact absurd held waiting
    | cons t ts =>
      have blocked : (false || !!s.messages.isEmpty || !(t :: ts).isEmpty) = true := by
        show (false || !!s.messages.isEmpty || true) = true
        rw [Bool.or_true]
      rw [blocked, if_pos rfl]

/-- The model's `poll` on the profile, where it consumes: a message is buffered and no taker
waits. The offers that fit the freed room enter, and nobody is woken. -/
theorem poll_consumes {s : State} (h : FirstProfile s) {c : Nat}
    (capacity : s.capacity = some (c + 1)) {m : Nat} {ms : List Nat}
    (buffered : s.messages = m :: ms) (alone : s.takers = []) :
    poll s = (afterAccept c { s with messages := ms }, some m,
      (s.offers.take (fitCount c { s with messages := ms })).map
        (fun o => (⟨o.id, .offered true⟩ : Signal))) := by
  have rest : FirstProfile { s with messages := ms } :=
    h.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) (List.Sublist.refl _)
  have consumed := afterConsume_closed rest (c := c) capacity
  have quiet : toWake (afterAccept c { s with messages := ms }) = [] := by
    show (if _ = 0 then [] else s.takers.take 1) = []
    rw [alone]
    exact ite_self _
  have step : poll s = ((afterConsume { s with messages := ms }).1, some m,
      (afterConsume { s with messages := ms }).2) := by
    unfold poll
    rw [isDone_opened h.opened, ready_profile h, pull_buffered buffered 1, buffered, alone]
    rfl
  rw [step, consumed, quiet, List.map_nil, List.append_nil]

/-! ## The take step's passes and the model's `take`, in closed form -/

/-- A fold that appends one image of each element is the list with the images. -/
theorem foldl_snoc_map {α β : Type} (g : α → β) :
    ∀ (xs : List α) (init : List β),
      xs.foldl (fun out x => out ++ [g x]) init = init ++ xs.map g
  | [], init => by rw [List.foldl_nil, List.map_nil, List.append_nil]
  | x :: xs, init => by
    rw [List.foldl_cons, foldl_snoc_map g xs, List.map_cons, List.append_assoc]
    rfl

/-- A fold that keeps a flag is the flag, or any element's test. -/
theorem foldl_or_any {α : Type} (p : α → Bool) :
    ∀ (xs : List α) (found : Bool), xs.foldl (fun found x => found || p x) found =
      (found || xs.any p)
  | [], found => by rw [List.foldl_nil, List.any_nil, Bool.or_false]
  | x :: xs, found => by
    rw [List.foldl_cons, foldl_or_any p xs, List.any_cons, Bool.or_assoc]

/-- The request's stored record, through the table that holds the step's hint. -/
theorem takerVal_renewed (tb : Table) (id : Nat) (hint : DeferredKey) {t : Taker}
    (same : t.id = id) :
    takerVal (tb.renew id hint) t =
      takerOf (Val.promise hint) (Val.promise (tb.handle id)) := by
  show takerOf (Val.promise (if t.id = id then hint else tb.hint t.id))
    (Val.promise (tb.handle t.id)) = _
  rw [if_pos same, same]

section TakePasses

variable {env : Env} {path : List Nat} {vals : List Val}

/-- `renewHint`: the takers, with the request's hint replaced. On the encoding of the stored
takers it reads their encoding through the table that holds the new hint. -/
theorem reads_renewHint {takers id hint : TermSrc} (tb : Table) (injective : tb.Injective)
    (ts : List Taker) (i : Nat) (h : DeferredKey) (depth : vals.length = env.names.length)
    (htakers : Reads takers env path vals (Val.list (ts.map (takerVal tb))))
    (hid : Captured id env path vals (Val.promise (tb.handle i)))
    (hhint : Captured hint env path vals (Val.promise h)) :
    Reads (Queue.renewHint takers id hint) env path vals
      (Val.list (ts.map (takerVal (tb.renew i h)))) := by
  have folded : Reads (Queue.renewHint takers id hint) env path vals
      (Val.list (ts.foldl (fun out t => out ++ [takerVal (tb.renew i h) t]) [])) :=
    reads_foldWith_model (takerVal tb) Val.list
      (fun out t => out ++ [takerVal (tb.renew i h) t]) ts [] ⟨0, 1, 1⟩ htakers
      (reads_noneOf htakers) fun out t => by
        refine (reads_snoc (reads_minted_acc depth path (Val.list out) (takerVal tb t))
          (reads_ifT (reads_sameTaker tb injective i depth hid (Val.list out) t)
            (reads_mkTaker (hid.underFold (Val.list out) (takerVal tb t))
              (hhint.underFold (Val.list out) (takerVal tb t)))
            (reads_minted_item depth path (Val.list out) (takerVal tb t)))).to ?_
        by_cases same : t.id = i
        · rw [decide_eq_true same, if_pos rfl, takerVal_renewed tb i h same]
        · rw [decide_eq_false same, if_neg Bool.false_ne_true, takerVal_renew same h]
  exact folded.to (by rw [foldl_snoc_map, List.nil_append])

end TakePasses

/-- The model's test of a taker's turn, as the take step computes it: the request is the
earliest taker, or it is not enrolled and no taker waits. -/
theorem earlier_isEmpty (ts : List Taker) (id : Nat) :
    ((ts.take 1).foldl (fun _ t => decide (t.id = id)) false ||
        (!(ts.foldl (fun found t => found || decide (t.id = id)) false) &&
          decide (ts.length = 0))) =
      (ts.takeWhile (fun t => t.id != id)).isEmpty := by
  cases ts with
  | nil => rfl
  | cons t rest =>
    have none : decide ((t :: rest).length = 0) = false := decide_eq_false (Nat.succ_ne_zero _)
    rw [none, Bool.and_false, Bool.or_false]
    show decide (t.id = id) = ((t :: rest).takeWhile (fun t => t.id != id)).isEmpty
    rw [List.takeWhile_cons]
    by_cases same : t.id = id
    · have stop : (t.id != id) = false := by
        show (!decide (t.id = id)) = false
        rw [decide_eq_true same]
        rfl
      rw [stop, if_neg Bool.false_ne_true, decide_eq_true same]
      rfl
    · have pass : (t.id != id) = true := by
        show (!decide (t.id = id)) = true
        rw [decide_eq_false same]
        rfl
      rw [pass, if_pos rfl, decide_eq_false same]
      rfl

/-- The model's `take` at the bounds one and one, in an opened queue: its three arms. -/
theorem take_eq {s : State} (h : FirstProfile s) (id : Nat) :
    take s ⟨id, 1, 1⟩ =
      if (ready s 1 && (earlier s id).isEmpty) = true then
        ((afterConsume (pull (removeTaker s id) 1).2.1).1, .got (pull (removeTaker s id) 1).1,
          (pull (removeTaker s id) 1).2.2 ++ (afterConsume (pull (removeTaker s id) 1).2.1).2)
      else if s.takers.any (fun u => u.id == id) = true then (s, .wait, [])
      else ({ s with takers := s.takers ++ [⟨id, 1, 1⟩] }, .wait, []) := by
  unfold take
  rw [h.opened]
  rfl

/-- The model's `take` where it consumes: a message is buffered, and no earlier taker waits.
The request leaves the takers, the offers that fit the freed room enter, and the earliest
taker that stays is named. -/
theorem take_consumes {s : State} (h : FirstProfile s) {c : Nat}
    (capacity : s.capacity = some (c + 1)) (id : Nat) {m : Nat} {ms : List Nat}
    (buffered : s.messages = m :: ms) (turn : (earlier s id).isEmpty = true) :
    take s ⟨id, 1, 1⟩ =
      (afterAccept c { removeTaker s id with messages := ms }, .got [m],
        (s.offers.take (fitCount c { removeTaker s id with messages := ms })).map
            (fun o => (⟨o.id, .offered true⟩ : Signal)) ++
          (toWake (afterAccept c { removeTaker s id with messages := ms })).map
            (fun t => (⟨t.id, .again⟩ : Signal))) := by
  have rest : FirstProfile { removeTaker s id with messages := ms } :=
    (removeTaker_profile id h).shrink rfl rfl rfl rfl rfl (List.Sublist.refl _)
      (List.Sublist.refl _)
  have consumed := afterConsume_closed rest (c := c) capacity
  have ready1 : ready s 1 = true := by
    rw [ready_profile h, buffered]
    rfl
  have pulled : pull (removeTaker s id) 1 =
      ([m], { removeTaker s id with messages := ms }, []) :=
    pull_buffered (s := removeTaker s id) buffered 1
  rw [take_eq h id, ready1, turn, Bool.and_true, if_pos rfl, pulled]
  show ((afterConsume { removeTaker s id with messages := ms }).1, TakeReply.got [m],
    [] ++ (afterConsume { removeTaker s id with messages := ms }).2) = _
  rw [consumed]
  rfl


/-- The cell where a waiting request's hint is replaced: the offers' records stay. -/
theorem cell_renewed (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (foreign : ∀ o ∈ s.offers, o.id ≠ id) :
    cellVal (tb.renew id hint) msg s =
      cellOf (.nat (s.capacity.getD 0)) (.list (s.messages.map msg))
        (.list (s.offers.map (offerVal tb msg)))
        (.list (s.takers.map (takerVal (tb.renew id hint)))) := by
  show cellOf _ _ (.list (s.offers.map (offerVal (tb.renew id hint) msg))) _ = _
  rw [offers_renew tb msg s.offers id hint foreign]

/-- The cell after a fresh taker enrols: the stored records stay, and the new taker holds the
step's hint. -/
theorem cell_enrolled (tb : Table) (msg : Nat → Val) (s : State) (id : Nat) (hint : DeferredKey)
    (others : ∀ t ∈ s.takers, t.id ≠ id) (foreign : ∀ o ∈ s.offers, o.id ≠ id) :
    cellVal (tb.renew id hint) msg { s with takers := s.takers ++ [⟨id, 1, 1⟩] } =
      cellOf (.nat (s.capacity.getD 0)) (.list (s.messages.map msg))
        (.list (s.offers.map (offerVal tb msg)))
        (.list (s.takers.map (takerVal tb) ++
          [takerOf (Val.promise hint) (Val.promise (tb.handle id))])) := by
  show cellOf _ _ (.list (s.offers.map (offerVal (tb.renew id hint) msg)))
    (.list ((s.takers ++ [(⟨id, 1, 1⟩ : Taker)]).map (takerVal (tb.renew id hint)))) = _
  rw [offers_renew tb msg s.offers id hint foreign, List.map_append,
    takers_renew tb s.takers id hint others, List.map_cons, List.map_nil,
    takerVal_renewed tb id hint (t := ⟨id, 1, 1⟩) rfl]

/-! ## The six step goals -/

/-- **The take step agrees with the model's `take` at the bounds one and one.** The cell holds
the state `s` of the first profile, through the table and the message map. The request `id` is
fresh or its own waiting taker, and `hint` is the hint that the step receives. The step's reply
is the model's. Its two lists are the model's signals: the offers that entered, then the takers
to wake. The stored value is the model's next state, through the table that holds `hint` at
`id` where the request waits. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem takeStep_agrees (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) {idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Captured hintSrc env path vals (Val.promise hint))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    ∃ reply entered woken,
      takeReplyVal msg (take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (take s ⟨id, 1, 1⟩).1 (take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      Reads (Queue.takeStep A idSrc hintSrc cellSrc) env path vals
        (Val.tuple [Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
            Val.list (woken.map (takerVal (tb.afterTake id hint (take s ⟨id, 1, 1⟩).2.1)))],
          cellVal (tb.afterTake id hint (take s ⟨id, 1, 1⟩).2.1) msg (take s ⟨id, 1, 1⟩).1]) := by
  obtain ⟨c, capacity⟩ := profile.positive
  have foreign : ∀ o ∈ s.offers, o.id ≠ id := requested
  -- the cell's fields
  have msgs := reads_field readsCell (cell_msgs _ _ _ _)
  have offers := reads_field readsCell (cell_offers _ _ _ _)
  have takers := reads_field readsCell (cell_takers _ _ _ _)
  have cap := reads_field readsCell (cell_cap _ _ _ _)
  -- the test: a message is buffered, and it is the request's turn
  have buffered : (!decide ((s.messages.map msg).length = 0)) = ready s 1 := by
    rw [ready_profile profile, List.length_map]
    cases s.messages with
    | nil => rfl
    | cons m ms => rfl
  have someMessage := (reads_notT (reads_isEmpty msgs)).to (congrArg Val.bool buffered)
  have head := reads_isHead tb injective s.takers id depth takers readsId
  have enrolled := (reads_enrolled tb injective s.takers id depth takers readsId).to
    (show Val.bool (s.takers.foldl (fun found t => found || decide (t.id = id)) false) =
        Val.bool (s.takers.any (fun u => u.id == id)) by
      rw [foldl_or_any, Bool.false_or]
      rfl)
  have noTakers := (reads_isEmpty takers).to
    (show Val.bool (decide ((s.takers.map (takerVal tb)).length = 0)) =
        Val.bool (decide (s.takers.length = 0)) by rw [List.length_map])
  have turn : Reads _ env path vals (Val.bool (earlier s id).isEmpty) :=
    (reads_orT head (reads_andT (reads_notT
      (reads_enrolled tb injective s.takers id depth takers readsId)) noTakers)).to
      (congrArg Val.bool (earlier_isEmpty s.takers id))
  have test := reads_andT someMessage turn
  -- the arm that consumes
  have rest : Reads (app "drop" [field cellSrc "msgs", nat 1]) env path vals
      (Val.list ((s.messages.drop 1).map msg)) :=
    (reads_drop msgs (reads_nat 1 env path vals)).to (by rw [List.map_drop])
  have room : Reads (app "sub" [field cellSrc "cap", Queue.len
      (app "drop" [field cellSrc "msgs", nat 1])]) env path vals
      (Val.nat (c + 1 - (s.messages.drop 1).length)) :=
    (reads_sub cap (reads_len rest)).to (by rw [List.length_map, capacity]; rfl)
  have removed := reads_removeTaker tb injective s.takers id depth takers readsId
  have gained := reads_gained tb msg _ (s.messages.drop 1) s.offers depth room rest offers
  have entering := reads_entering tb msg _ s.offers room offers
  have staying := reads_staying tb msg _ s.offers room offers
  have toWake' := (reads_wake removed gained).to (congrArg Val.list (wake_encoded tb msg _ _))
  have consumed := reads_recordSet
    (reads_recordSet (reads_recordSet readsCell gained (cell_setMsgs _ _ _ _ _)) removed
      (cell_setTakers _ _ _ _ _))
    staying (cell_setOffers _ _ _ _ _)
  have yes := reads_pair (reads_tuple3 (reads_head msgs) entering toWake') consumed
  -- the arm that waits
  have renewed := reads_renewHint tb injective s.takers id hint depth takers readsId readsHint
  have appended := reads_snoc takers (reads_mkTaker readsId.atScope readsHint.atScope)
  have waiting := reads_recordSet readsCell (reads_ifT enrolled renewed appended)
    (cell_setTakers _ _ _ _ _)
  have no := reads_pair
    (reads_tuple3 reads_noneT (reads_noneOf offers) (reads_noneOf takers)) waiting
  have whole := reads_ifT test yes no
  -- the model's three arms
  cases consumes : (ready s 1 && (earlier s id).isEmpty) with
  | true =>
    obtain ⟨isReady, isTurn⟩ := Bool.and_eq_true_iff.mp consumes
    rw [ready_profile profile] at isReady
    cases held : s.messages with
    | nil =>
      rw [held] at isReady
      cases isReady
    | cons m ms =>
      rw [consumes, if_pos rfl, held] at whole
      rw [take_consumes profile capacity id held isTurn]
      exact ⟨_, _, _, rfl, ⟨rfl, fun o member => List.mem_of_mem_take member,
        toWake_stored _⟩, whole⟩
  | false =>
    rw [consumes, if_neg Bool.false_ne_true] at whole
    have waits : take s ⟨id, 1, 1⟩ =
        if s.takers.any (fun u => u.id == id) = true then (s, .wait, [])
        else ({ s with takers := s.takers ++ [⟨id, 1, 1⟩] }, .wait, []) := by
      rw [take_eq profile id, consumes, if_neg Bool.false_ne_true]
    cases isEnrolled : s.takers.any (fun u => u.id == id) with
    | true =>
      rw [isEnrolled, if_pos rfl] at whole
      rw [waits, isEnrolled, if_pos rfl]
      refine ⟨_, [], [], rfl, ⟨rfl, fun _ none => absurd none List.not_mem_nil,
        fun _ none => absurd none List.not_mem_nil⟩, whole.to ?_⟩
      show _ = Val.tuple [Val.tuple [Store.Val.none, Val.list [], Val.list []],
        cellVal (tb.renew id hint) msg s]
      rw [cell_renewed tb msg s id hint foreign]
    | false =>
      have others : ∀ t ∈ s.takers, t.id ≠ id := fun t member same => by
        have found : s.takers.any (fun u => u.id == id) = true :=
          List.any_eq_true.mpr ⟨t, member, decide_eq_true same⟩
        rw [isEnrolled] at found
        cases found
      rw [isEnrolled, if_neg Bool.false_ne_true] at whole
      rw [waits, isEnrolled, if_neg Bool.false_ne_true]
      refine ⟨_, [], [], rfl, ⟨rfl, fun _ none => absurd none List.not_mem_nil,
        fun _ none => absurd none List.not_mem_nil⟩, whole.to ?_⟩
      show _ = Val.tuple [Val.tuple [Store.Val.none, Val.list [], Val.list []],
        cellVal (tb.renew id hint) msg { s with takers := s.takers ++ [⟨id, 1, 1⟩] }]
      rw [cell_enrolled tb msg s id hint others foreign]

/-- **The offer step agrees with the model's `offer`.** The request `id` is fresh: it names no
waiting taker and no pending offer. The message term reads the value of the model's message
`a`. The step's reply is the model's, it accepts no pending offer, and its list is the takers
that the model wakes. The stored value is the model's next state, through the table that holds
`hint` at `id` where the offer waits. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offerStep_agrees (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.offer id a))
    (fresh : ∀ o ∈ s.offers, o.id ≠ id) {idSrc hintSrc messageSrc cellSrc : TermSrc}
    {env : Env} {path : List Nat} {vals : List Val}
    (readsId : Reads idSrc env path vals (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc env path vals (Val.promise hint))
    (readsMessage : Reads messageSrc env path vals (msg a))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    ∃ woken,
      Notified s (offer s id a).1 (offer s id a).2.2 [] woken ∧
      Reads (Queue.offerStep A idSrc hintSrc messageSrc cellSrc) env path vals
        (Val.tuple [Val.tuple [offerReplyVal (offer s id a).2.1,
            Val.list (woken.map (takerVal (tb.afterOffer id hint (offer s id a).2.1)))],
          cellVal (tb.afterOffer id hint (offer s id a).2.1) msg (offer s id a).1]) := by
  obtain ⟨c, capacity⟩ := profile.positive
  have foreign : ∀ t ∈ s.takers, t.id ≠ id := requested
  -- the parts of the term, each at the value it reads
  have msgs := reads_field readsCell (cell_msgs _ _ _ _)
  have offers := reads_field readsCell (cell_offers _ _ _ _)
  have takers := reads_field readsCell (cell_takers _ _ _ _)
  have cap := reads_field readsCell (cell_cap _ _ _ _)
  have newOffer := reads_mkOffer A readsId readsHint (reads_bool false env path vals)
    (reads_app (.cons readsMessage (.cons reads_nilT .nil)) (atom_cons (msg a) []))
  have pending := (reads_recordSet readsCell (reads_snoc offers newOffer)
    (cell_setOffers _ _ _ _ _)).to (cell_pended tb msg s id a hint foreign fresh).symm
  have longer : Reads (Queue.snoc (field cellSrc "msgs") messageSrc) env path vals
      (Val.list ((s.messages ++ [a]).map msg)) :=
    (reads_snoc msgs readsMessage).to (by rw [List.map_append]; rfl)
  have accepted := reads_recordSet readsCell longer (cell_setMsgs _ _ _ _ _)
  have behind := reads_pair (reads_tuple2 reads_noneT (reads_noneOf takers)) pending
  have room := reads_pair
    (reads_tuple2 (reads_some (reads_bool true env path vals)) (reads_wake takers longer))
    accepted
  have full := reads_pair (reads_tuple2 reads_noneT (reads_wake takers msgs)) pending
  have hasPending : Reads (Queue.notT (Queue.isEmpty (field cellSrc "offers"))) env path vals
      (Val.bool (!decide (s.offers.length = 0))) :=
    (reads_notT (reads_isEmpty offers)).to (by rw [List.length_map])
  have hasRoom : Reads (app "lt" [Queue.len (field cellSrc "msgs"), field cellSrc "cap"]) env
      path vals (Val.bool (decide (s.messages.length < c + 1))) :=
    (reads_lt (reads_len msgs) cap).to (by rw [List.length_map, capacity]; rfl)
  have whole := reads_ifT hasPending behind (reads_ifT hasRoom room full)
  by_cases noPending : s.offers = []
  · have none : (!decide (s.offers.length = 0)) = false := by
      rw [noPending]
      rfl
    rw [none, if_neg Bool.false_ne_true] at whole
    by_cases free : s.messages.length < c + 1
    · -- room: the offer is accepted, and the earliest taker is named
      have next : FirstProfile { s with messages := s.messages ++ [a] } :=
        profile.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) (List.Sublist.refl _)
      rw [offer_room profile capacity id a noPending free]
      refine ⟨toWake { s with messages := s.messages ++ [a] },
        ⟨?_, fun _ none => absurd none List.not_mem_nil, toWake_stored _⟩, ?_⟩
      · show wake { s with messages := s.messages ++ [a] } = _
        rw [wake_toWake next]
        rfl
      · rw [decide_eq_true free, if_pos rfl] at whole
        exact whole.to (by rw [wake_encoded]; rfl)
    · -- full: the offer waits, and the model still names the earliest taker
      have next : FirstProfile { s with offers := s.offers ++ [⟨id, false, [a]⟩] } :=
        profile.pend id a fresh foreign
      rw [offer_full profile capacity id a noPending free]
      refine ⟨toWake s, ⟨?_, fun _ none => absurd none List.not_mem_nil, toWake_stored s⟩, ?_⟩
      · show wake { s with offers := s.offers ++ [⟨id, false, [a]⟩] } = _
        rw [wake_toWake next]
        rfl
      · rw [decide_eq_false free, if_neg Bool.false_ne_true] at whole
        refine whole.to ?_
        show _ = Val.tuple [Val.tuple [Store.Val.none,
          Val.list ((toWake s).map (takerVal (tb.renew id hint)))], _]
        rw [wake_encoded, takers_renew tb (toWake s) id hint
          fun t member => foreign t (toWake_stored s t member)]
        rfl
  · -- behind a pending offer: the offer waits, and nobody is named
    have some : (!decide (s.offers.length = 0)) = true := by
      rw [decide_eq_false fun zero => noPending (List.eq_nil_of_length_eq_zero zero)]
      rfl
    rw [some, if_pos rfl] at whole
    rw [offer_behind profile id a noPending]
    exact ⟨[], ⟨rfl, fun _ none => absurd none List.not_mem_nil,
      fun _ none => absurd none List.not_mem_nil⟩, whole⟩

/-- **The poll step agrees with the model's `poll`.** The reply is the model's, the list is the
offers that entered, and the model wakes no taker. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem pollStep_agrees (A : Ty) (tb : Table) (msg : Nat → Val) (s : State)
    (profile : FirstProfile s) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (depth : vals.length = env.names.length)
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    ∃ entered,
      Notified s (poll s).1 (poll s).2.2 entered [] ∧
      Reads (Queue.pollStep A cellSrc) env path vals
        (Val.tuple [Val.tuple [pollReplyVal msg (poll s).2.1,
            Val.list (entered.map (offerVal tb msg))],
          cellVal tb msg (poll s).1]) := by
  obtain ⟨c, capacity⟩ := profile.positive
  -- the parts of the term, each at the value it reads
  have msgs := reads_field readsCell (cell_msgs _ _ _ _)
  have offers := reads_field readsCell (cell_offers _ _ _ _)
  have takers := reads_field readsCell (cell_takers _ _ _ _)
  have cap := reads_field readsCell (cell_cap _ _ _ _)
  have rest : Reads (app "drop" [field cellSrc "msgs", nat 1]) env path vals
      (Val.list ((s.messages.drop 1).map msg)) :=
    (reads_drop msgs (reads_nat 1 env path vals)).to (by rw [List.map_drop])
  have room : Reads (app "sub" [field cellSrc "cap", Queue.len
      (app "drop" [field cellSrc "msgs", nat 1])]) env path vals
      (Val.nat (c + 1 - (s.messages.drop 1).length)) :=
    (reads_sub cap (reads_len rest)).to (by rw [List.length_map, capacity]; rfl)
  have gained := reads_gained tb msg _ (s.messages.drop 1) s.offers depth room rest offers
  have entering := reads_entering tb msg _ s.offers room offers
  have staying := reads_staying tb msg _ s.offers room offers
  have consumed := reads_recordSet
    (reads_recordSet readsCell gained (cell_setMsgs _ _ _ _ _)) staying
    (cell_setOffers _ _ _ _ _)
  have yes := reads_pair (reads_tuple2 (reads_head msgs) entering) consumed
  have no := reads_pair (reads_tuple2 reads_noneT (reads_noneOf offers)) readsCell
  have test : Reads (Queue.andT (Queue.notT (Queue.isEmpty (field cellSrc "msgs")))
      (Queue.isEmpty (field cellSrc "takers"))) env path vals
      (Val.bool (!decide (s.messages.length = 0) && decide (s.takers.length = 0))) :=
    (reads_andT (reads_notT (reads_isEmpty msgs)) (reads_isEmpty takers)).to
      (by rw [List.length_map, List.length_map])
  have whole := reads_ifT test yes no
  have idle : ∀ (quiet : s.messages = [] ∨ s.takers ≠ [])
      (refused : (!decide (s.messages.length = 0) && decide (s.takers.length = 0)) = false),
      ∃ entered,
        Notified s (poll s).1 (poll s).2.2 entered [] ∧
        Reads (Queue.pollStep A cellSrc) env path vals
          (Val.tuple [Val.tuple [pollReplyVal msg (poll s).2.1,
              Val.list (entered.map (offerVal tb msg))],
            cellVal tb msg (poll s).1]) := by
    intro quiet refused
    rw [refused, if_neg Bool.false_ne_true] at whole
    rw [poll_idle profile quiet]
    exact ⟨[], ⟨rfl, fun _ none => absurd none List.not_mem_nil,
      fun _ none => absurd none List.not_mem_nil⟩, whole⟩
  cases buffered : s.messages with
  | nil =>
    refine idle (Or.inl buffered) ?_
    rw [buffered]
    rfl
  | cons m ms =>
    cases alone : s.takers with
    | cons t ts =>
      refine idle (Or.inr fun none => ?_) ?_
      · rw [alone] at none
        cases none
      · rw [alone]
        exact Bool.and_false _
    | nil =>
      have accepts : (!decide (s.messages.length = 0) && decide (s.takers.length = 0)) = true := by
        rw [buffered, alone]
        rfl
      rw [accepts, if_pos rfl, buffered] at whole
      rw [poll_consumes profile capacity buffered alone]
      refine ⟨s.offers.take (fitCount c { s with messages := ms }), ⟨?_, ?_, ?_⟩, whole⟩
      · rw [List.map_nil, List.append_nil]
      · exact fun o member => List.mem_of_mem_take member
      · exact fun _ none => absurd none List.not_mem_nil

/-- **The size step agrees with the model's `size`.** The reply is the buffer's length. The
step is a term over the cell's value: it stores nothing and names no notification, as the
model's `size` answers no state and no signal (`cell_read`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem sizeStep_agrees (A : Ty) (tb : Table) (msg : Nat → Val) (s : State)
    (profile : FirstProfile s) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    Reads (Queue.sizeStep A cellSrc) env path vals (Val.nat (size s)) := by
  have opened : size s = s.messages.length := by
    unfold size isDone
    rw [profile.opened]
    rfl
  rw [opened]
  exact (reads_len (reads_field readsCell (cell_msgs _ _ _ _))).to (by rw [List.length_map])

/-- **The withdrawal of a take agrees with the model's `withdrawTake`.** The step accepts no
offer, its list is the takers that the model wakes, and the stored value is the model's next
state. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawTake_agrees (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) {idSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    ∃ woken,
      Notified s (withdrawTake s id).1 (withdrawTake s id).2 [] woken ∧
      Reads (Queue.withdrawTake A idSrc cellSrc) env path vals
        (Val.tuple [Val.list (woken.map (takerVal tb)), cellVal tb msg (withdrawTake s id).1]) := by
  have next : FirstProfile (removeTaker s id) := removeTaker_profile id profile
  refine ⟨toWake (removeTaker s id), ⟨?_, fun _ none => absurd none List.not_mem_nil,
    toWake_stored _⟩, ?_⟩
  · show wake (removeTaker s id) = _
    rw [wake_toWake next]
    rfl
  · have removed := reads_removeTaker tb injective s.takers id depth
      (reads_field readsCell (cell_takers _ _ _ _)) readsId
    have woken := reads_wake removed (reads_field readsCell (cell_msgs _ _ _ _))
    have stored := reads_recordSet readsCell removed (cell_setTakers _ _ _ _ _)
    exact (reads_pair woken stored).to (by rw [wake_encoded]; rfl)

/-- **The withdrawal of an offer agrees with the model's `withdrawOffer`.** The step accepts no
offer, its list is the takers that the model wakes, and the stored value is the model's next
state. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdrawOffer_agrees (A : Ty) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) {idSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {vals : List Val} (depth : vals.length = env.names.length)
    (readsId : Captured idSrc env path vals (Val.promise (tb.handle id)))
    (readsCell : Reads cellSrc env path vals (cellVal tb msg s)) :
    ∃ woken,
      Notified s (withdrawOffer s id).1 (withdrawOffer s id).2 [] woken ∧
      Reads (Queue.withdrawOffer A idSrc cellSrc) env path vals
        (Val.tuple [Val.list (woken.map (takerVal tb)),
          cellVal tb msg (withdrawOffer s id).1]) := by
  have next : FirstProfile { s with offers := s.offers.filter (fun o => o.id != id) } :=
    profile.shrink rfl rfl rfl rfl rfl (List.Sublist.refl _) List.filter_sublist
  rw [withdrawOffer_opened profile.opened]
  refine ⟨toWake s, ⟨?_, fun _ none => absurd none List.not_mem_nil, toWake_stored s⟩, ?_⟩
  · show wake { s with offers := s.offers.filter (fun o => o.id != id) } = _
    rw [wake_toWake next]
    rfl
  · have removed := reads_removeOffer tb msg injective s.offers id depth
      (reads_field readsCell (cell_offers _ _ _ _)) readsId
    have woken := reads_wake (reads_field readsCell (cell_takers _ _ _ _))
      (reads_field readsCell (cell_msgs _ _ _ _))
    have stored := reads_recordSet readsCell removed (cell_setOffers _ _ _ _ _)
    exact (reads_pair woken stored).to (by rw [wake_encoded]; rfl)

end Effect4.Queue.Model
