import Effect4.Laws.Modules.Step.Scope
import Effect4.Modules.Queue.Ops
import Effect4.Laws.Modules.Waiting
import Effect4.Laws.Modules.Store
import Effect4.Laws.Modules.Queue.Steps
import Effect4.Laws.Modules.Queue.Typing
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Auto.Semantics

/-!
# The laws of the Queue's first operations (decisions rows 233, 255 and 257)

The operations are `src/Effect4/Modules/Queue/Ops.lean`: `Queue.bounded`, `Queue.offer`,
`Queue.take`, `Queue.poll` and `Queue.size`, over the step terms of
`src/Effect4/Modules/Queue/Steps.lean` and the shared waiting wrapper
(`src/Effect4/Modules/Waiting.lean`).

- **Scope.** Each step term and each operation keeps the authoring scope judgment, for every
  scoped term of a caller. Each law is named so that `authoring_scoped` finds it.
- **The attempt laws.** Each operation has one statement at its own step term, under the binder
  of its own row. The cell holds the encoding of a state of the first profile. The store step
  then answers the model's reply, it writes the encoding of the model's next state, and it names
  the model's signals in order. The reply and the stored value are members of their types. A
  withdrawal has the same statement, `size` has the read law, and `bounded` makes the cell of the
  empty state.

- **Typing at every scope.** Each operation is typed at every typed scope, for every message
  type with `MessageTy` and every kept term of a caller: `bounded_types`, `size_types`,
  `poll_types`, `offer_types` and `take_types`, in the last section. Their rules are the shared
  ones of `src/Effect4/Laws/Modules/Waiting.lean`.

Each attempt law is one composition of what exists: the step's agreement
(`src/Effect4/Laws/Modules/Queue/Steps.lean`), `step_updates`, the step's typing
(`src/Effect4/Laws/Modules/Queue/Typing.lean`) and `step_keeps_cell`
(`src/Effect4/Laws/Modules/Store.lean`). It states no new fact of the model.

**The typing equation is no premise** (decisions row 257, points 1 and 2). The step's typing
theorem gives it at the row's own scope, for every message type with `MessageTy`, and
`Types.tree` reads it at the tree that `step_updates` names. So no application supplies it.

**Each law has two forms.** The first takes the capture of the request's identity and of its
hint as written premises (`Captured`, `CapturedTy`), with the caller's context: the typed
environment, the cell's value and the cell's membership. The second is at the operation's own
binders: the identity and the hint are names that `bindWith` mints. It states the scope's two
premises for each name: the scope binds the name, and no later binder shadows it. The battery
`Test/Program/QueueOps.lean` discharges those premises at the wrapper's own binders, and it
binds each statement's term to the operation's tree.

Placement. Scope: concept `initial-algebras-folds`, requirement R4, a step of the claim
`operation-data-scoped` and of the lifts' scope laws. Its consumer is `Api.Author.build` of each
client, which checks the scope of the tree that a client's source elaborates to. The attempt
laws: concept `translation-simulation`, requirement R10, parts of the proposed claim
`queue-expansion-agrees`. Their consumer is the run-level law of the next slice, which relates
the wrapper's run to the model. Typing: concept `store-typing`, requirement R4. Its consumer is
a client's admission, and its section states its reach.

Reach of an attempt law: one store step, from a cell that encodes a state of `FirstProfile`, with
the request's premise `Requested` and an injective table, at every scope and every message type
with `MessageTy`. It establishes no delivery, no order across steps, no cancellation law, no
budget, no liveness and nothing of a host. It does not say that a run reaches the step with such
a cell: the relation between a run's stores and a model state is the next slice's.
-/

set_option autoImplicit false

namespace Effect4.Queue

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## Scope: the step terms

A step term is built from the authoring builders, the shared words and folds with minted
binders. Each law unfolds the step to those builders, and `authoring_scoped` applies the lemma
of each. A record's construction is closed by hand: its entries are pairs. -/

/-- A waiting taker's record keeps scope. -/
theorem mkTaker_scoped {id hint : TermSrc} (hid : id.Scoped) (hhint : hint.Scoped) :
    (mkTaker id hint).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact hid
    · exact hhint)

/-- A pending offer's record keeps scope. -/
theorem mkOffer_scoped (A : Ty) {id hint batch rest : TermSrc} (hid : id.Scoped)
    (hhint : hint.Scoped) (hbatch : batch.Scoped) (hrest : rest.Scoped) :
    (mkOffer A id hint batch rest).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact hid
    · exact hhint
    · exact hbatch
    · exact hrest)

/-- The take step keeps scope. -/
theorem takeStep_scoped (A : Ty) {id hint s : TermSrc} (hid : id.Scoped) (hhint : hint.Scoped)
    (hs : s.Scoped) : (takeStep A id hint s).Scoped := by
  exact Step.«scoped» (Data.take A) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hhint (TermSrc.Scoped_cons hs TermSrc.Scoped_nil))))

/-- The offer step keeps scope. -/
theorem offerStep_scoped (A : Ty) {id hint message s : TermSrc} (hid : id.Scoped)
    (hhint : hint.Scoped) (hmessage : message.Scoped) (hs : s.Scoped) :
    (offerStep A id hint message s).Scoped := by
  exact Step.«scoped» (Data.offer A) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hhint (TermSrc.Scoped_cons hmessage (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))))

/-- The poll step keeps scope. -/
theorem pollStep_scoped (A : Ty) {s : TermSrc} (hs : s.Scoped) : (pollStep A s).Scoped := by
  exact Step.«scoped» (Data.poll A) (Input.source_scoped (TermSrc.Scoped_cons hs TermSrc.Scoped_nil))

/-- The size step keeps scope. -/
theorem sizeStep_scoped (A : Ty) {s : TermSrc} (hs : s.Scoped) : (sizeStep A s).Scoped := by
  exact Step.«scoped» (Data.size A) (Input.source_scoped (TermSrc.Scoped_cons hs TermSrc.Scoped_nil))

/-- The withdrawal of a take keeps scope. -/
theorem withdrawTake_scoped (A : Ty) {id s : TermSrc} (hid : id.Scoped) (hs : s.Scoped) :
    (withdrawTake A id s).Scoped := by
  exact Step.«scoped» (Data.withdrawTake A) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))

/-- The withdrawal of an offer keeps scope. -/
theorem withdrawOffer_scoped (A : Ty) {id s : TermSrc} (hid : id.Scoped) (hs : s.Scoped) :
    (withdrawOffer A id s).Scoped := by
  exact Step.«scoped» (Data.withdrawOffer A) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))

/-- The initial value keeps scope: it reads no name. -/
theorem empty_scoped (A : Ty) (capacity : Nat) : (empty A capacity).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact app_scoped "nil" TermSrc.Scoped_nil
    · exact nat_scoped capacity
    · exact app_scoped "nil" TermSrc.Scoped_nil
    · exact app_scoped "nil" TermSrc.Scoped_nil)

/-! ## Scope: the operations

Each law is one application of the wrapper's law and of the lifts' lemmas. The handle and the
message are a caller's terms, scoped at the operation's node. -/

/-- `Queue.bounded` keeps scope: one `Ref.make` of the initial value. -/
theorem bounded_scoped (A : Ty) (capacity : Nat) (positive : 0 < capacity) :
    (bounded A capacity positive).Scoped :=
  Ref.make_scoped (empty_scoped A capacity)

/-- The Queue's part of `take` keeps scope, for every scoped handle. -/
theorem take_scoped (A : Ty) {q : TermSrc} (hq : q.Scoped) : (take A q).Scoped :=
  waitRetry_scoped _ _
    { attempt := fun _ _ _ _ hid hhint hwait hdone =>
        bindWith_scoped
          (Ref.modifyWith_scoped hq fun _ hs => takeStep_scoped A hid hhint hs) fun _ hreply =>
            andThen_scoped (postAll_scoped (tupleAt_scoped hreply 1) (bool_scoped true))
              (andThen_scoped (postAll_scoped (tupleAt_scoped hreply 2) unit_scoped)
                (selectOptionWith_scoped (tupleAt_scoped hreply 0) hwait hdone))
      withdraw := fun _ hid =>
        bindWith_scoped
          (Ref.modifyWith_scoped hq fun _ hs => withdrawTake_scoped A hid hs) fun _ hwoken =>
            postAll_scoped hwoken unit_scoped }

/-- `Queue.offer` keeps scope, for every scoped handle and message. -/
theorem offer_scoped (A : Ty) {q message : TermSrc} (hq : q.Scoped) (hmessage : message.Scoped) :
    (offer A q message).Scoped :=
  waitAnswer_scoped
    { attempt := fun _ _ _ _ hid hhint hwait hdone =>
        bindWith_scoped
          (Ref.modifyWith_scoped hq fun _ hs => offerStep_scoped A hid hhint hmessage hs)
          fun _ hreply =>
            andThen_scoped (postAll_scoped (tupleAt_scoped hreply 1) unit_scoped)
              (selectOptionWith_scoped (tupleAt_scoped hreply 0) hwait hdone)
      withdraw := fun _ hid =>
        bindWith_scoped
          (Ref.modifyWith_scoped hq fun _ hs => withdrawOffer_scoped A hid hs) fun _ hwoken =>
            postAll_scoped hwoken unit_scoped }

/-- `Queue.poll` keeps scope, for every scoped handle. -/
theorem poll_scoped (A : Ty) {q : TermSrc} (hq : q.Scoped) : (poll A q).Scoped :=
  uninterruptible_scoped
    (bindWith_scoped (Ref.modifyWith_scoped hq fun _ hs => pollStep_scoped A hs) fun _ hreply =>
      andThen_scoped (postAll_scoped (tupleAt_scoped hreply 1) (bool_scoped true))
        (succeed_scoped (tupleAt_scoped hreply 0)))

/-- `Queue.size` keeps scope, for every scoped handle. -/
theorem size_scoped (A : Ty) {q : TermSrc} (hq : q.Scoped) : (size A q).Scoped :=
  bindWith_scoped (Ref.get_scoped hq) fun _ hcell => succeed_scoped (sizeStep_scoped A hcell)

end Effect4.Queue

namespace Effect4.Queue

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Typed
open Effect4.Modules
open Effect4.Queue.Model

/-! ## The attempt laws, with each capture as a premise

In each statement `env` is the scope of the operation's row, the node of the `Ref.modifyWith`.
`captured` holds the values of that scope and `tys` their types. The step term is elaborated one
level up, under the minted name of the cell's current value. The model's functions are written
with their namespace: `Model.take` is the model's, and `take` is the operation. -/

/-- **The attempt of `take` is the model's `take` at the bounds one and one.** The cell holds
the state `s` of the first profile. The identity and the hint are caller's terms of the step,
each with its capture. The step term under the row's own binder is one atomic update: the store
step answers the model's reply with the model's signals as two lists, and it writes the model's
next state. The reply and the stored value are members of their types. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) {idSrc hintSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise (tb.handle id)))
    (readsHint : Captured hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise hint))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    (typesHint : CapturedTy sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f reply entered woken,
      takeStep A idSrc hintSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      takeReplyVal msg (Model.take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (Model.take s ⟨id, 1, 1⟩).1 (Model.take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q
              (cellVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1) msg
                (Model.take s ⟨id, 1, 1⟩).1) },
          Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
            Val.list (woken.map
              (takerVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1)))]) ∧
      Fits w (Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
          Val.list (woken.map (takerVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1)))])
        (takeReplyTy A) ∧
      Fits w (cellVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1) msg
        (Model.take s ⟨id, 1, 1⟩).1) (Queue.cellTy A) := by
  obtain ⟨reply, entered, woken, encoded, notified, reads⟩ :=
    takeStep_agrees A tb msg s id hint profile requested injective
      (push_minted_length depth "current" _) readsId readsHint
      (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (takeStep_types sig atoms A message (push_minted_length tyDepth "current" _)
    typesId typesHint (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, reply, entered, woken, tree, encoded, notified, stepped, fitsReply, fitsNext⟩

/-- **The withdrawal of a take is the model's `withdrawTake`.** The same statement as an
attempt's: the store step answers the takers that the model wakes, and it writes the model's
next state. The table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_withdrawal (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) {idSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise (tb.handle id)))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f woken,
      withdrawTake A idSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      Notified s (Model.withdrawTake s id).1 (Model.withdrawTake s id).2 [] woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb msg (Model.withdrawTake s id).1) },
          Val.list (woken.map (takerVal tb))) ∧
      Fits w (Val.list (woken.map (takerVal tb))) wakeReplyTy ∧
      Fits w (cellVal tb msg (Model.withdrawTake s id).1) (Queue.cellTy A) := by
  obtain ⟨woken, notified, reads⟩ :=
    withdrawTake_agrees A tb msg s id profile injective (push_minted_length depth "current" _)
      readsId (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (withdrawTake_types sig atoms A message (push_minted_length tyDepth "current" _)
    typesId (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, woken, tree, notified, stepped, fitsReply, fitsNext⟩

/-- **The attempt of `offer` is the model's `offer`**, by a fresh request. No fold of the offer
step holds a caller's term, so the identity, the hint and the message are read at the row's
scope alone. The store step answers the model's reply and the takers that the model wakes, and
it writes the model's next state. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offer_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.offer id a))
    (fresh : ∀ o ∈ s.offers, o.id ≠ id) {idSrc hintSrc messageSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Reads idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise hint))
    (readsMessage : Reads messageSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (msg a))
    (typesId : TypesEach sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    (typesHint : TypesEach sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) Queue.answerTy)
    (typesMessage : TypesEach sig messageSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) A)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f woken,
      offerStep A idSrc hintSrc messageSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      Notified s (Model.offer s id a).1 (Model.offer s id a).2.2 [] woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q
              (cellVal (tb.afterOffer id hint (Model.offer s id a).2.1) msg
                (Model.offer s id a).1) },
          Val.tuple [offerReplyVal (Model.offer s id a).2.1,
            Val.list (woken.map
              (takerVal (tb.afterOffer id hint (Model.offer s id a).2.1)))]) ∧
      Fits w (Val.tuple [offerReplyVal (Model.offer s id a).2.1,
          Val.list (woken.map (takerVal (tb.afterOffer id hint (Model.offer s id a).2.1)))])
        offerReplyTy ∧
      Fits w (cellVal (tb.afterOffer id hint (Model.offer s id a).2.1) msg
        (Model.offer s id a).1) (Queue.cellTy A) := by
  obtain ⟨woken, notified, reads⟩ :=
    offerStep_agrees A tb msg s id a hint profile requested fresh readsId readsHint
      readsMessage (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (offerStep_types sig atoms A message typesId typesHint typesMessage
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, woken, tree, notified, stepped, fitsReply, fitsNext⟩

/-- **The withdrawal of an offer is the model's `withdrawOffer`.** The store step answers the
takers that the model wakes, and it writes the model's next state: an offer that a step already
accepted is not pending, so its message stays accepted (decisions row 222). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offer_withdrawal (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) {idSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise (tb.handle id)))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f woken,
      withdrawOffer A idSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      Notified s (Model.withdrawOffer s id).1 (Model.withdrawOffer s id).2 [] woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb msg (Model.withdrawOffer s id).1) },
          Val.list (woken.map (takerVal tb))) ∧
      Fits w (Val.list (woken.map (takerVal tb))) wakeReplyTy ∧
      Fits w (cellVal tb msg (Model.withdrawOffer s id).1) (Queue.cellTy A) := by
  obtain ⟨woken, notified, reads⟩ :=
    withdrawOffer_agrees A tb msg s id profile injective (push_minted_length depth "current" _)
      readsId (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (withdrawOffer_types sig atoms A message
    (push_minted_length tyDepth "current" _) typesId
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, woken, tree, notified, stepped, fitsReply, fitsNext⟩

/-- **The step of `poll` is the model's `poll`.** It takes no request. The store step answers
the model's reply and the offers that entered, and it writes the model's next state. The model
wakes no taker. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem poll_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State)
    (profile : FirstProfile s) {env : Env} {path : List Nat} {tys : List Ty} {w : Typed.World}
    {captured : List Val} (depth : captured.length = env.names.length)
    (tyDepth : tys.length = env.names.length) (typedEnv : EnvTyped w tys captured)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f entered,
      pollStep A (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      Notified s (Model.poll s).1 (Model.poll s).2.2 entered [] ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb msg (Model.poll s).1) },
          Val.tuple [pollReplyVal msg (Model.poll s).2.1,
            Val.list (entered.map (offerVal tb msg))]) ∧
      Fits w (Val.tuple [pollReplyVal msg (Model.poll s).2.1,
          Val.list (entered.map (offerVal tb msg))]) (pollReplyTy A) ∧
      Fits w (cellVal tb msg (Model.poll s).1) (Queue.cellTy A) := by
  obtain ⟨entered, notified, reads⟩ :=
    pollStep_agrees A tb msg s profile (push_minted_length depth "current" _)
      (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (pollStep_types sig atoms A message (push_minted_length tyDepth "current" _)
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, entered, tree, notified, stepped, fitsReply, fitsNext⟩

/-- **The read law of `size`.** The operation's `Ref.get` answers the cell's value and leaves
the stores (`cell_read`). Under the name that `bindWith` mints for that value, the size step
reads the model's `size`. Nothing is written, and no signal is named. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem size_read (A : Ty) (tb : Table) (msg : Nat → Val) (s : State)
    (profile : FirstProfile s) {env : Env} {path : List Nat} {captured : List Val}
    (depth : captured.length = env.names.length) {stores : Stores} {q : RefKey}
    (held : refPeek stores.refs q = some (cellVal tb msg s)) :
    syncOpStep (.refGet q) stores = some (stores, cellVal tb msg s) ∧
      Reads (sizeStep A (minted (env.mint "answer"))) (env.push [env.mint "answer"]) path
        (captured ++ [cellVal tb msg s]) (Val.nat (Model.size s)) :=
  ⟨cell_read held,
    sizeStep_agrees A tb msg s profile (reads_minted_last depth path "answer" _)⟩

/-- The initial value reads the cell of the empty state, at every table and message map. -/
theorem reads_empty (A : Ty) (tb : Table) (msg : Nat → Val) (capacity : Nat) (env : Env)
    (path : List Nat) (vals : List Val) :
    Reads (empty A capacity) env path vals (cellVal tb msg { capacity := some capacity }) :=
  reads_record (present := [("msgs", app "nil" []), ("cap", nat capacity),
      ("takers", app "nil" []), ("offers", app "nil" [])])
    (.cons reads_nilT (.cons (reads_nat capacity env path vals)
      (.cons reads_nilT (.cons reads_nilT .nil)))) rfl

/-- **`Queue.bounded` makes the cell of the empty state of the first profile.** A positive
capacity gives a state of the profile (`empty_profile`). The initial value reads that state's
cell, and the store step of `Ref.make` appends it and answers the new cell's handle. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem bounded_makes (A : Ty) (tb : Table) (msg : Nat → Val) (capacity : Nat)
    (positive : 0 < capacity) (env : Env) (path : List Nat) (vals : List Val)
    (stores : Stores) :
    FirstProfile { capacity := some capacity } ∧
      Reads (empty A capacity) env path vals (cellVal tb msg { capacity := some capacity }) ∧
      syncOpStep (.refMake (cellVal tb msg { capacity := some capacity })) stores =
        some ({ stores with
            refs := stores.refs ++ [cellVal tb msg { capacity := some capacity }] },
          Val.cell ⟨stores.refs.length⟩) := by
  obtain ⟨c, rfl⟩ : ∃ c, capacity = c + 1 := ⟨capacity - 1, by omega⟩
  exact ⟨empty_profile c, reads_empty A tb msg (c + 1) env path vals, rfl⟩

/-! ## The attempt laws at the operation's own binders

The wrapper binds the request's identity and its hint with `bindWith`, so each is a minted name:
`outer.mint "answer"` for the scope `outer` of its `bindWith`. Each statement below takes the
row's scope with two written premises for each name. The scope binds the name at a level, and no
later binder of the scope shadows it. The values and the types hold the request's handles at
those levels. The row's own binder is no later binder that shadows either name
(`mint_current_ne_answer`). -/

/-- **The attempt of `take` at the operation's own binders.** The identity and the hint are
names that `bindWith` mints. The scope binds each, and no later binder shadows either. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) {env outerId outerHint : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    {beforeId afterId beforeHint afterHint : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (idScope : env.names = beforeId ++ outerId.mint "answer" :: afterId)
    (idUnshadowed : ∀ name ∈ afterId, name ≠ outerId.mint "answer")
    (idHeld : captured[beforeId.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[beforeId.length]? = some idTy)
    (hintScope : env.names = beforeHint ++ outerHint.mint "answer" :: afterHint)
    (hintUnshadowed : ∀ name ∈ afterHint, name ≠ outerHint.mint "answer")
    (hintHeld : captured[beforeHint.length]? = some (Val.promise hint))
    (hintTyped : tys[beforeHint.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f reply entered woken,
      takeStep A (minted (outerId.mint "answer")) (minted (outerHint.mint "answer"))
        (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      takeReplyVal msg (Model.take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (Model.take s ⟨id, 1, 1⟩).1 (Model.take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q
              (cellVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1) msg
                (Model.take s ⟨id, 1, 1⟩).1) },
          Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
            Val.list (woken.map
              (takerVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1)))]) ∧
      Fits w (Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
          Val.list (woken.map (takerVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1)))])
        (takeReplyTy A) ∧
      Fits w (cellVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1) msg
        (Model.take s ⟨id, 1, 1⟩).1) (Queue.cellTy A) :=
  take_attempt sig atoms A message tb msg s id hint profile requested injective depth tyDepth
    typedEnv (captured_answer_in_row idScope idUnshadowed idHeld)
    (captured_answer_in_row hintScope hintUnshadowed hintHeld)
    (capturedTy_answer_in_row idScope idUnshadowed idTyped)
    (capturedTy_answer_in_row hintScope hintUnshadowed hintTyped) held member

/-- **The withdrawal of a take at the operation's own binders.** The identity is a name that
`bindWith` mints. The scope binds it, and no later binder shadows it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_withdrawal_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) {env outerId : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    {beforeId afterId : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (idScope : env.names = beforeId ++ outerId.mint "answer" :: afterId)
    (idUnshadowed : ∀ name ∈ afterId, name ≠ outerId.mint "answer")
    (idHeld : captured[beforeId.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[beforeId.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f woken,
      withdrawTake A (minted (outerId.mint "answer")) (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      Notified s (Model.withdrawTake s id).1 (Model.withdrawTake s id).2 [] woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb msg (Model.withdrawTake s id).1) },
          Val.list (woken.map (takerVal tb))) ∧
      Fits w (Val.list (woken.map (takerVal tb))) wakeReplyTy ∧
      Fits w (cellVal tb msg (Model.withdrawTake s id).1) (Queue.cellTy A) :=
  take_withdrawal sig atoms A message tb msg s id profile injective depth tyDepth typedEnv
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (capturedTy_answer_in_row idScope idUnshadowed idTyped) held member

/-- **The attempt of `offer` at the operation's own binders.** The identity and the hint are
names that `bindWith` mints. The scope binds each, and no later binder shadows either. The
message stays a caller's term, with its reading and its type at the row's scope. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offer_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.offer id a))
    (fresh : ∀ o ∈ s.offers, o.id ≠ id) {messageSrc : TermSrc} {env outerId outerHint : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    {beforeId afterId beforeHint afterHint : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (idScope : env.names = beforeId ++ outerId.mint "answer" :: afterId)
    (idUnshadowed : ∀ name ∈ afterId, name ≠ outerId.mint "answer")
    (idHeld : captured[beforeId.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[beforeId.length]? = some idTy)
    (hintScope : env.names = beforeHint ++ outerHint.mint "answer" :: afterHint)
    (hintUnshadowed : ∀ name ∈ afterHint, name ≠ outerHint.mint "answer")
    (hintHeld : captured[beforeHint.length]? = some (Val.promise hint))
    (hintTyped : tys[beforeHint.length]? = some Queue.answerTy)
    (readsMessage : Reads messageSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (msg a))
    (typesMessage : TypesEach sig messageSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) A)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f woken,
      offerStep A (minted (outerId.mint "answer")) (minted (outerHint.mint "answer")) messageSrc
        (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      Notified s (Model.offer s id a).1 (Model.offer s id a).2.2 [] woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q
              (cellVal (tb.afterOffer id hint (Model.offer s id a).2.1) msg
                (Model.offer s id a).1) },
          Val.tuple [offerReplyVal (Model.offer s id a).2.1,
            Val.list (woken.map
              (takerVal (tb.afterOffer id hint (Model.offer s id a).2.1)))]) ∧
      Fits w (Val.tuple [offerReplyVal (Model.offer s id a).2.1,
          Val.list (woken.map (takerVal (tb.afterOffer id hint (Model.offer s id a).2.1)))])
        offerReplyTy ∧
      Fits w (cellVal (tb.afterOffer id hint (Model.offer s id a).2.1) msg
        (Model.offer s id a).1) (Queue.cellTy A) :=
  offer_attempt sig atoms A message tb msg s id a hint profile requested fresh depth tyDepth
    typedEnv (captured_answer_in_row idScope idUnshadowed idHeld).atScope
    (captured_answer_in_row hintScope hintUnshadowed hintHeld).atScope readsMessage
    (capturedTy_answer_in_row idScope idUnshadowed idTyped).atScope
    (capturedTy_answer_in_row hintScope hintUnshadowed hintTyped).atScope typesMessage held
    member

/-- **The withdrawal of an offer at the operation's own binders.** The identity is a name that
`bindWith` mints. The scope binds it, and no later binder shadows it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offer_withdrawal_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (profile : FirstProfile s) (injective : tb.Injective) {env outerId : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    {beforeId afterId : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (idScope : env.names = beforeId ++ outerId.mint "answer" :: afterId)
    (idUnshadowed : ∀ name ∈ afterId, name ≠ outerId.mint "answer")
    (idHeld : captured[beforeId.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[beforeId.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A)) :
    ∃ f woken,
      withdrawOffer A (minted (outerId.mint "answer")) (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      Notified s (Model.withdrawOffer s id).1 (Model.withdrawOffer s id).2 [] woken ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb msg (Model.withdrawOffer s id).1) },
          Val.list (woken.map (takerVal tb))) ∧
      Fits w (Val.list (woken.map (takerVal tb))) wakeReplyTy ∧
      Fits w (cellVal tb msg (Model.withdrawOffer s id).1) (Queue.cellTy A) :=
  offer_withdrawal sig atoms A message tb msg s id profile injective depth tyDepth typedEnv
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (capturedTy_answer_in_row idScope idUnshadowed idTyped) held member

/-! ## Typing at every scope (decisions row 257)

Each operation is typed at every typed scope, for every message type with `MessageTy`. The
handle and the message are a caller's terms. `Queue.offer` and `Queue.take` read them under
their own binders, so each is a kept term (`Kept`, `src/Effect4/Laws/Modules/Waiting.lean`): a
variable that an author wrote is one, and so is a number or a Boolean literal. `Queue.size` and
`Queue.poll` read the handle at their own scope alone. A string literal is no kept term, and so
no message of these statements (the gap of seat QTYPES's receipt).

`bounded`, `size` and `poll` use no wrapper, and each proof follows the operation's tree. `take`
and `offer` are typed through the wrapper's own rules (`waitRetry_answers` and
`waitAnswer_answers`, `src/Effect4/Laws/Modules/Waiting.lean`). Each of the two proofs holds the
Queue's part alone: its attempt and its withdrawal, typed as `Waiter.Typed` asks. The step of
each `Ref.modifyWith` has the type that its step theorem gives, at the row's own scope
(`takeStep_types` and its siblings, `src/Effect4/Laws/Modules/Queue/Typing.lean`). The cell's
type and each reply's type are canonical and formed at a message type with `MessageTy`, which
is what the rows of a cell ask.

Placement. Concept `store-typing`, requirement R4. Reach: the checker's judgment `effTy` on the
operation's tree, at every typed scope and every path, at the native signature of any row
table: the tree has the operation's answer, no failure and no requirement. They establish no
run. Their consumer is a client's admission: `Api.Author.build` checks the tree that a client's
source elaborates to. -/

section OpsTyping

variable {table : RowTable}

/-- Every node of a message type that a cell holds is formed. -/
theorem message_nodes {A : Ty} (message : MessageTy A) : NodesFormed A :=
  Model.message_nodes_for_steps message

theorem offer_nodes {A : Ty} (message : MessageTy A) : NodesFormed (Queue.offerTy A) :=
  Model.offer_nodes_for_steps message

theorem cell_nodes {A : Ty} (message : MessageTy A) : NodesFormed (Queue.cellTy A) := by
  intro t member
  have member' : t ∈ [Queue.cellTy A] ++ (Formation.nodes .nat ++
      (Formation.nodes (.list A) ++ (Formation.nodes (.list (Queue.offerTy A)) ++
        (Formation.nodes (.list Queue.takerTy) ++ [])))) := member
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | h | h | h | h
  · show (["cap", "msgs", "offers", "takers"] : List String).Nodup
    decide
  · exact nodesFormed_of_check (T := .nat) (by decide) t h
  · exact nodesFormed_list (message_nodes message) t h
  · exact nodesFormed_list (offer_nodes message) t h
  · exact nodesFormed_of_check (T := .list Queue.takerTy) (by decide) t h

theorem takeReply_nodes {A : Ty} (message : MessageTy A) : NodesFormed (takeReplyTy A) := by
  intro t member
  have member' : t ∈ [takeReplyTy A] ++ (Formation.nodes (.option A) ++
      (Formation.nodes (.list (Queue.offerTy A)) ++
        (Formation.nodes (.list Queue.takerTy) ++ []))) := member
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | h | h | h
  · exact trivial
  · exact nodesFormed_option (message_nodes message) t h
  · exact nodesFormed_list (offer_nodes message) t h
  · exact nodesFormed_of_check (T := .list Queue.takerTy) (by decide) t h

theorem pollReply_nodes {A : Ty} (message : MessageTy A) : NodesFormed (pollReplyTy A) := by
  intro t member
  have member' : t ∈ [pollReplyTy A] ++ (Formation.nodes (.option A) ++
      Formation.nodes (.list (Queue.offerTy A))) := member
  simp only [List.mem_append, List.mem_singleton] at member'
  rcases member' with rfl | h | h
  · exact trivial
  · exact nodesFormed_option (message_nodes message) t h
  · exact nodesFormed_list (offer_nodes message) t h

theorem offerReply_nodes : NodesFormed offerReplyTy := nodesFormed_of_check (by decide)

theorem wakeReply_nodes : NodesFormed wakeReplyTy := nodesFormed_of_check (by decide)

/-- A pending offer's hint carries the offer's decided answer. -/
theorem offer_hintTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.offerTy A) "hint" = some (.deferredOf .bool .never) :=
  Record.fieldType_normal (offerTy_normal canonical) rfl

/-- A waiting taker's hint carries nothing. -/
theorem taker_hintTy :
    Record.fieldType false Queue.takerTy "hint" = some (.deferredOf .unit .never) :=
  Record.fieldType_normal takerTy_normal rfl

theorem takeReply_at {A : Ty} (canonical : A.normalize = A) :
    Tuple.typeAt (takeReplyTy A) 0 = some (.option A) ∧
      Tuple.typeAt (takeReplyTy A) 1 = some (.list (Queue.offerTy A)) ∧
      Tuple.typeAt (takeReplyTy A) 2 = some (.list Queue.takerTy) := by
  unfold Tuple.typeAt
  rw [takeReplyTy_normal canonical]
  exact ⟨rfl, rfl, rfl⟩

theorem pollReply_at {A : Ty} (canonical : A.normalize = A) :
    Tuple.typeAt (pollReplyTy A) 0 = some (.option A) ∧
      Tuple.typeAt (pollReplyTy A) 1 = some (.list (Queue.offerTy A)) := by
  unfold Tuple.typeAt
  rw [pollReplyTy_normal canonical]
  exact ⟨rfl, rfl⟩

theorem offerReply_at :
    Tuple.typeAt offerReplyTy 0 = some (.option .bool) ∧
      Tuple.typeAt offerReplyTy 1 = some (.list Queue.takerTy) :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- **The construction is typed at every scope**: it answers the handle of a cell at the
queue's cell type. -/
@[semantics "store-typing" (requirement := R4)]
theorem bounded_types (A : Ty) (message : MessageTy A) (capacity : Nat)
    (positive : 0 < capacity) (s : TypedScope) :
    Answers (nativeSignature table) (Queue.bounded A capacity positive) s
      (.refOf (Queue.cellTy A)) :=
  answers_refMake (cellTy_normal message.canonical) (cell_nodes message) fun _ =>
    typeAt_tree (empty_typed (nativeSignature table) rfl A message capacity s.env.names s.types)

/-- **`size` is typed at every scope**: it answers a number. -/
@[semantics "store-typing" (requirement := R4)]
theorem size_types (A : Ty) (message : MessageTy A) {q : TermSrc} {s : TypedScope}
    (hq : Typed (nativeSignature table) q s (.refOf (Queue.cellTy A))) :
    Answers (nativeSignature table) (Queue.size A q) s .nat :=
  answers_bindWith (answers_refGet (cellTy_normal message.canonical) (cell_nodes message) hq)
    fun _ hcell => answers_succeed fun path =>
      types_len rfl (types_cellMsgs message.canonical (hcell.here path))

/-- **`poll` is typed at every scope**: it answers an option of a message. -/
@[semantics "store-typing" (requirement := R4)]
theorem poll_types (A : Ty) (message : MessageTy A) {q : TermSrc} {s : TypedScope}
    (hq : Typed (nativeSignature table) q s (.refOf (Queue.cellTy A))) :
    Answers (nativeSignature table) (Queue.poll A q) s (.option A) := by
  have canonical := message.canonical
  refine answers_uninterruptible (answers_bindWith
    (answers_refModifyWith (cellTy_normal canonical) (cell_nodes message)
      (pollReplyTy_normal canonical) (pollReply_nodes message) hq
      fun _ hcurrent path => pollStep_types _ rfl A message (TypedScope.depth _) (hcurrent path))
    fun _ hreply => answers_andThen
      (postAll_answers hintTy_bool (offerTy_normal canonical) (offer_hintTy canonical)
        (hreply.tupleAt (pollReply_at canonical).2) (kept_bool true _))
      (answers_succeed fun path => (hreply.push.tupleAt (pollReply_at canonical).1).here path))

/-- **`offer` is typed at every scope**: it answers a Boolean. The handle and the message are
kept terms: the operation reads each under its own binders. -/
@[semantics "store-typing" (requirement := R4)]
theorem offer_types (A : Ty) (message : MessageTy A) {q m : TermSrc} {s : TypedScope}
    (hq : Kept (nativeSignature table) q s (.refOf (Queue.cellTy A)))
    (hm : Kept (nativeSignature table) m s A) :
    Answers (nativeSignature table) (Queue.offer A q m) s .bool := by
  have canonical := message.canonical
  have cellNormal := cellTy_normal canonical
  have cellNodes := cell_nodes message
  have offerReplyNormal : offerReplyTy.normalize = offerReplyTy := by decide +kernel
  have wakeReplyNormal : wakeReplyTy.normalize = wakeReplyTy := by decide +kernel
  have test : nativeAtomTy "causeIsInterrupt" [.exitOf .bool .never] = some .bool := by
    decide +kernel
  unfold Queue.offer
  exact waitAnswer_answers (F := .nat)
    { hint := hintTy_bool
      interrupted := test
      attempt := fun _ _ _ _ _ _ _ reach hid hhint hwait hdone =>
        answers_bindWith
          (answers_refModifyWith cellNormal cellNodes offerReplyNormal offerReply_nodes
            (hq.push.reach reach).here
            fun _ hcurrent path => offerStep_types _ rfl A message (hid.push.here path)
              (hhint.push.here path) ((hm.push.reach reach).push.here path) (hcurrent path))
          fun _ hreply => answers_andThen
            (postAll_answers hintTy_unit takerTy_normal taker_hintTy
              (hreply.tupleAt offerReply_at.2) (kept_unit _))
            (answers_selectOptionWith (P := .bool) rfl
              (fun path => (hreply.push.tupleAt offerReply_at.1).here path)
              (hwait _ (.push _ _ (.push _ _ .here)))
              fun _ hanswer => hdone _ _ (.push _ _ (.push _ _ (.push _ _ .here))) hanswer)
      withdraw := fun _ _ reach hid =>
        answers_bindWith
          (answers_refModifyWith cellNormal cellNodes wakeReplyNormal wakeReply_nodes
            (hq.push.reach reach).here
            fun _ hcurrent path => withdrawOffer_types _ rfl A message (TypedScope.depth _)
              (hid.push.captured path) (hcurrent path))
          fun _ hwoken =>
            postAll_answers hintTy_unit takerTy_normal taker_hintTy hwoken (kept_unit _) }

/-- **`take` is typed at every scope**: it answers a message. The handle is a kept term: the
operation reads it under its own binders. -/
@[semantics "store-typing" (requirement := R4)]
theorem take_types (A : Ty) (message : MessageTy A) {q : TermSrc} {s : TypedScope}
    (hq : Kept (nativeSignature table) q s (.refOf (Queue.cellTy A))) :
    Answers (nativeSignature table) (Queue.take A q) s A := by
  have canonical := message.canonical
  have cellNormal := cellTy_normal canonical
  have cellNodes := cell_nodes message
  have wakeReplyNormal : wakeReplyTy.normalize = wakeReplyTy := by decide +kernel
  have test : nativeAtomTy "causeIsInterrupt" [.exitOf .unit .never] = some .bool := by
    decide +kernel
  unfold Queue.take
  exact waitRetry_answers (F := .nat) canonical
    { hint := hintTy_unit
      interrupted := test
      attempt := fun _ _ _ _ _ _ _ reach hid hhint hwait hdone =>
        answers_bindWith
          (answers_refModifyWith cellNormal cellNodes (takeReplyTy_normal canonical)
            (takeReply_nodes message) (hq.push.reach reach).here
            fun _ hcurrent path => takeStep_types _ rfl A message (TypedScope.depth _)
              (hid.push.captured path) (hhint.push.captured path) (hcurrent path))
          fun _ hreply => answers_andThen
            (postAll_answers hintTy_bool (offerTy_normal canonical) (offer_hintTy canonical)
              (hreply.tupleAt (takeReply_at canonical).2.1) (kept_bool true _))
            (answers_andThen
              (postAll_answers hintTy_unit takerTy_normal taker_hintTy
                (hreply.push.tupleAt (takeReply_at canonical).2.2) (kept_unit _))
              (answers_selectOptionWith canonical
                (fun path => (hreply.push.push.tupleAt (takeReply_at canonical).1).here path)
                (hwait _ (.push _ _ (.push _ _ (.push _ _ .here))))
                fun _ hanswer =>
                  hdone _ _ (.push _ _ (.push _ _ (.push _ _ (.push _ _ .here)))) hanswer))
      withdraw := fun _ _ reach hid =>
        answers_bindWith
          (answers_refModifyWith cellNormal cellNodes wakeReplyNormal wakeReply_nodes
            (hq.push.reach reach).here
            fun _ hcurrent path => withdrawTake_types _ rfl A message (TypedScope.depth _)
              (hid.push.captured path) (hcurrent path))
          fun _ hwoken =>
            postAll_answers hintTy_unit takerTy_normal taker_hintTy hwoken (kept_unit _) }

end OpsTyping

end Effect4.Queue
