import Effect4.Modules.Queue.Ops
import Effect4.Laws.Modules.Waiting
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

Placement. Scope: concept `initial-algebras-folds`, requirement R4, a step of the claim
`operation-data-scoped` and of the lifts' scope laws. Its consumer is `Api.Author.build` of each
client, which checks the scope of the tree that a client's source elaborates to. Reach: every
scope. The scope laws establish no typing and no run.
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
  unfold takeStep gained entering staying fitting wake renewHint removeTaker isHead enrolled
    removeById minT snoc isEmpty len notT andT orT ifT same noneOf noneT nilT tuple
  authoring_scoped

/-- The offer step keeps scope. -/
theorem offerStep_scoped (A : Ty) {id hint message s : TermSrc} (hid : id.Scoped)
    (hhint : hint.Scoped) (hmessage : message.Scoped) (hs : s.Scoped) :
    (offerStep A id hint message s).Scoped := by
  unfold offerStep wake snoc isEmpty len notT ifT noneOf noneT nilT tuple
  authoring_scoped

/-- The poll step keeps scope. -/
theorem pollStep_scoped (A : Ty) {s : TermSrc} (hs : s.Scoped) : (pollStep A s).Scoped := by
  unfold pollStep gained entering staying fitting minT isEmpty len notT andT ifT noneOf noneT
    tuple
  authoring_scoped

/-- The size step keeps scope. -/
theorem sizeStep_scoped (A : Ty) {s : TermSrc} (hs : s.Scoped) : (sizeStep A s).Scoped := by
  unfold sizeStep len
  authoring_scoped

/-- The withdrawal of a take keeps scope. -/
theorem withdrawTake_scoped (A : Ty) {id s : TermSrc} (hid : id.Scoped) (hs : s.Scoped) :
    (withdrawTake A id s).Scoped := by
  unfold withdrawTake wake removeTaker removeById snoc isEmpty len ifT same noneOf nilT
  authoring_scoped

/-- The withdrawal of an offer keeps scope. -/
theorem withdrawOffer_scoped (A : Ty) {id s : TermSrc} (hid : id.Scoped) (hs : s.Scoped) :
    (withdrawOffer A id s).Scoped := by
  unfold withdrawOffer wake removeOffer removeById snoc isEmpty len ifT same noneOf nilT
  authoring_scoped

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
