import Effect4.Library.Semaphore.Ops
import Effect4.Laws.Step.Scope
import Effect4.Laws.Step.Waiting
import Effect4.Laws.Step.Store
import Effect4.Laws.Library.Semaphore.Steps
import Effect4.Laws.Library.Semaphore.Typing
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Auto.Semantics

/-!
# The laws of Semaphore's first operations (decisions rows 257, 259 to 261 and 276)

The operations are `src/Effect4/Library/Semaphore/Ops.lean`: `Semaphore.make`, `take`, `release`,
`takeIfAvailable`, `withPermits` and `withPermitsIfAvailable`, over the step terms of
`src/Effect4/Library/Semaphore/Steps.lean` and the shared wrapper
(`src/Effect4/Library/Waiting.lean`).

- **Scope.** Each step term and each operation keeps the authoring scope judgment, for every
  scoped term of a caller and every scoped body. Each law is named so that `authoring_scoped`
  finds it.
- **Typing at every scope.** Each operation is typed at every typed scope, for every kept term
  of a caller: `make_types`, `takeIfAvailable_types`, `release_types`, `take_types`,
  `withPermits_types` and `withPermitsIfAvailable_types`. A protected body has any effect type:
  it may fail, and it may require a service. Their rules are the shared ones of
  `src/Effect4/Laws/Step/Waiting.lean`.
- **The attempt laws.** Each step of an operation has one statement at its own step term, under
  the binder of its own row. The cell holds the encoding of a model state. The store step then
  answers the model's reply, and it writes the encoding of the model's next state. The reply
  and the stored value are members of their types. The steps are five: the take, its
  withdrawal, the release, a visit of the walk and the take that never waits. `make` makes the
  cell of the initial state.

Each attempt law is one composition of what exists: the step's agreement
(`src/Effect4/Laws/Library/Semaphore/Steps.lean`), `step_updates`, the step's typing
(`src/Effect4/Laws/Library/Semaphore/Typing.lean`) and `step_keeps_cell`
(`src/Effect4/Laws/Step/Store.lean`). It states no new fact of the model.

**The typing equation is no premise** (decisions row 257, points 1 and 2). The step's typing
theorem gives it at the row's own scope, and `Types.tree` reads it at the tree that
`step_updates` names.

**No law takes the profile.** No step reads it: the term and the model compute the same
truncated subtraction, the same removal by identity and the same first fitting waiter. The
profile's closure is a statement of its own (`profile_closed`,
`src/Effect4/Laws/Library/Semaphore/Profile.lean`), and a law of a run uses both. So each law
holds on every model state, which is more than a state of the first profile.

**Each law that reads a minted name has two forms.** The first takes each capture as a written
premise (`Captured`, `CapturedTy`). The second is at the operation's own binders: the identity
and the hint are names that `bindWith` mints, and the walk's cursor is the name that its loop
mints, read through `getOrElse`. It states the scope's two premises for each name: the scope
binds the name, and no later binder shadows it. The battery `Test/Program/SemaphoreOps.lean`
discharges those premises at each operation's own binders, and it binds each statement's term
to the operation's tree. The protected forms run the same rows: the take's loop of
`withPermits` stands at the scope of `take`'s.

Placement. Scope: concept `initial-algebras-folds`, requirement R4, a step of the claim
`operation-data-scoped` and of the lifts' scope laws. Its consumer is `Api.Author.build` of each
client, which checks the scope of the tree that a client's source elaborates to. Typing: concept
`store-typing`, requirement R4. Its consumer is a client's admission, and its section states its
reach. The attempt laws: concept `translation-simulation`, requirement R10, parts of the
proposed claim `semaphore-expansion-agrees`. Their consumer is the law of a run, in a later
slice, which relates the wrapper's run and the walk's to the model.

Reach of an attempt law: one store step, from a cell that encodes a model state, with an
injective table where the step tests an identity, at every scope. It establishes no delivery,
no order across steps or across visits, no cancellation law, no law of the protected permit, no
budget, no liveness and nothing of a host. It does not say that a run reaches the step with such
a cell. The premise of decisions row 261, that a release asks for at most what is taken, is no
premise here: the step is total, as the model's is.
-/

set_option autoImplicit false

namespace Effect4.Semaphore

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## Scope: the step terms

A step term is built from the authoring builders, the shared words and folds with minted
binders. Each law unfolds the step to those builders, and `authoring_scoped` applies the lemma
of each. A record's construction is closed by hand: its entries are pairs. -/

/-- A waiter's record keeps scope. -/
theorem mkWaiter_scoped {id need hint stamp : TermSrc} (hid : id.Scoped) (hneed : need.Scoped)
    (hhint : hint.Scoped) (hstamp : stamp.Scoped) : (mkWaiter id need hint stamp).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact hid
    · exact hneed
    · exact hhint
    · exact hstamp)

/-- The take step keeps scope. -/
theorem takeStep_scoped {need id hint s : TermSrc} (hneed : need.Scoped) (hid : id.Scoped)
    (hhint : hint.Scoped) (hs : s.Scoped) : (takeStep need id hint s).Scoped := by
  exact Step.«scoped» Data.take (Input.source_scoped
    (TermSrc.Scoped_cons hneed (TermSrc.Scoped_cons hid
      (TermSrc.Scoped_cons hhint (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))))

/-- The take-if-available step keeps scope. -/
theorem takeIfAvailableStep_scoped {need s : TermSrc} (hneed : need.Scoped) (hs : s.Scoped) :
    (takeIfAvailableStep need s).Scoped := by
  exact Step.«scoped» Data.takeIfAvailable (Input.source_scoped
    (TermSrc.Scoped_cons hneed (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))

/-- The release step keeps scope. -/
theorem releaseStep_scoped {count s : TermSrc} (hcount : count.Scoped) (hs : s.Scoped) :
    (releaseStep count s).Scoped := by
  exact Step.«scoped» Data.release (Input.source_scoped
    (TermSrc.Scoped_cons hcount (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))

/-- The visit step keeps scope. -/
theorem visitStep_scoped {cursor s : TermSrc} (hcursor : cursor.Scoped) (hs : s.Scoped) :
    (visitStep cursor s).Scoped := by
  exact Step.«scoped» Data.visit (Input.source_scoped
    (TermSrc.Scoped_cons hcursor (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))

/-- The withdrawal keeps scope. -/
theorem withdrawStep_scoped {id s : TermSrc} (hid : id.Scoped) (hs : s.Scoped) :
    (withdrawStep id s).Scoped := by
  exact Step.«scoped» Data.withdraw (Input.source_scoped
    (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hs TermSrc.Scoped_nil)))

/-- The initial value keeps scope: it reads no name. -/
theorem empty_scoped (permits : Nat) : (empty permits).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact nat_scoped permits
    · exact nat_scoped 0
    · exact app_scoped "nil" TermSrc.Scoped_nil
    · exact nat_scoped 0)

/-! ## Scope: the operations

Each law is one application of the shared forms' laws and of the lifts' lemmas. The handle and
the count are a caller's terms, scoped at the operation's node, and so is a protected body. -/

/-- `Semaphore.make` keeps scope: one `Ref.make` of the initial value. -/
theorem make_scoped (permits : Nat) (positive : 0 < permits) :
    (make permits positive).Scoped :=
  Ref.make_scoped (empty_scoped permits)

/-- Semaphore's part of the wrapper keeps scope, for every scoped handle and count. -/
theorem taker_scoped {q count : TermSrc} (hq : q.Scoped) (hcount : count.Scoped) :
    (taker q count).Scoped :=
  { attempt := fun _ _ _ _ hid hhint hwait hdone =>
      bindWith_scoped
        (Ref.modifyWith_scoped hq fun _ hs => takeStep_scoped hcount hid hhint hs) fun _ htook =>
          ifElse_scoped htook (hdone _ hcount) hwait
    withdraw := fun _ hid => Ref.modifyWith_scoped hq fun _ hs => withdrawStep_scoped hid hs }

/-- `Semaphore.take` keeps scope, for every scoped handle and count. -/
theorem take_scoped {q count : TermSrc} (hq : q.Scoped) (hcount : count.Scoped) :
    (take q count).Scoped :=
  waitRetry_scoped _ _ (taker_scoped hq hcount)

/-- The walk keeps scope, for every scoped handle: the loop's two names, a visit's reply and the
selected waiter's record are minted. -/
theorem walk_scoped {q : TermSrc} (hq : q.Scoped) : (walk q).Scoped :=
  iterateWith_scoped
    (app_scoped "some" (TermSrc.Scoped_cons (nat_scoped 0) TermSrc.Scoped_nil))
    (fun _ hcursor => app_scoped "isSome" (TermSrc.Scoped_cons hcursor TermSrc.Scoped_nil))
    (fun _ hcursor =>
      bindWith_scoped
        (Ref.modifyWith_scoped hq fun _ hs =>
          visitStep_scoped
            (app_scoped "getOrElse"
              (TermSrc.Scoped_cons hcursor (TermSrc.Scoped_cons (nat_scoped 0) TermSrc.Scoped_nil)))
            hs)
        fun _ hselected =>
          selectOptionWith_scoped hselected
            (succeed_scoped (app_scoped "none" TermSrc.Scoped_nil)) fun _ hwaiter =>
              andThen_scoped (Deferred.succeed_scoped (field_scoped hwaiter "hint") unit_scoped)
                (succeed_scoped (app_scoped "some" (TermSrc.Scoped_cons
                  (app_scoped "add" (TermSrc.Scoped_cons (field_scoped hwaiter "stamp")
                    (TermSrc.Scoped_cons (nat_scoped 1) TermSrc.Scoped_nil)))
                  TermSrc.Scoped_nil))))
    (fun _ _ _ hnext => hnext)
    (fun _ _ => unit_scoped)

/-- `Semaphore.release` keeps scope, for every scoped handle and count. -/
theorem release_scoped {q count : TermSrc} (hq : q.Scoped) (hcount : count.Scoped) :
    (release q count).Scoped :=
  uninterruptible_scoped
    (bindWith_scoped (Ref.modifyWith_scoped hq fun _ hs => releaseStep_scoped hcount hs)
      fun _ hreply =>
        andThen_scoped
          (ifElse_scoped (tupleAt_scoped hreply 1)
            (andThen_scoped (withFiber_scoped (Action.fork_scoped posted (walk_scoped hq)))
              (succeed_scoped unit_scoped))
            (succeed_scoped unit_scoped))
          (succeed_scoped (tupleAt_scoped hreply 0)))

/-- `Semaphore.takeIfAvailable` keeps scope, for every scoped handle and count. -/
theorem takeIfAvailable_scoped {q count : TermSrc} (hq : q.Scoped) (hcount : count.Scoped) :
    (takeIfAvailable q count).Scoped :=
  Ref.modifyWith_scoped hq fun _ hs => takeIfAvailableStep_scoped hcount hs

/-- `Semaphore.withPermits` keeps scope, for every scoped handle, count and body. -/
theorem withPermits_scoped {q count : TermSrc} {body : Src NativeOp} (hq : q.Scoped)
    (hcount : count.Scoped) (hbody : body.Scoped) : (withPermits q count body).Scoped :=
  protectedBy_scoped
    (fun _ hrestore => waitRetryAt_scoped _ _ hrestore (taker_scoped hq hcount))
    (fun _ _ => release_scoped hq hcount) (fun _ _ => hbody)

/-- `Semaphore.withPermitsIfAvailable` keeps scope, for every scoped handle, count and body. -/
theorem withPermitsIfAvailable_scoped {q count : TermSrc} {body : Src NativeOp} (hq : q.Scoped)
    (hcount : count.Scoped) (hbody : body.Scoped) :
    (withPermitsIfAvailable q count body).Scoped :=
  protectedBy_scoped (fun _ _ => takeIfAvailable_scoped hq hcount)
    (fun _ htook =>
      ifElse_scoped htook
        (andThen_scoped (release_scoped hq hcount) (succeed_scoped unit_scoped))
        (succeed_scoped unit_scoped))
    (fun _ htook =>
      ifElse_scoped htook
        (bindWith_scoped hbody fun _ hanswer =>
          succeed_scoped (app_scoped "some" (TermSrc.Scoped_cons hanswer TermSrc.Scoped_nil)))
        (succeed_scoped (app_scoped "none" TermSrc.Scoped_nil)))

end Effect4.Semaphore

namespace Effect4.Semaphore

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Typed
open Effect4.Modules
open Effect4.Semaphore.Model

/-! ## Typing at every scope (decisions row 257)

Each operation is typed at every typed scope. The handle and the count are a caller's terms.
Each operation reads them under its own binders, so each is a kept term (`Kept`,
`src/Effect4/Laws/Step/Waiting.lean`): a variable that an author wrote is one, and so is a
number literal. `Semaphore.takeIfAvailable` reads the handle at its own scope alone.

**A protected body is a caller's program.** It stands under the mask's saved state and the
acquired value, so its premise is its effect type at every scope that the surface's binders
reach. It has any effect type (`Has`): it may fail, and it may require a service. The protected
form keeps the body's answer, its failure type in normal form and its requirement.

Each proof follows the operation's tree. The step of each `Ref.modifyWith` has the type that its
step theorem gives, at the row's own scope (`takeStep_types` and its siblings,
`src/Effect4/Laws/Library/Semaphore/Typing.lean`). `take` is typed through the wrapper's own
rule, over Semaphore's part (`taker_typed`, `waitRetry_answers`). The walk reads its cursor and
the cell's own source under the visit's fold, through the two rules that hand a kept cursor and
a captured current value.

Placement. Concept `store-typing`, requirement R4. Reach: the checker's judgment `effTy` on the
operation's tree, at every typed scope and every path, at the native signature of any row
table. An operation that takes no body has its answer, no failure and no requirement. They
establish no run. Their consumer is a client's admission: `Api.Author.build` checks the tree
that a client's source elaborates to. A string literal is no kept term, and the statements
state nothing of one: a count is a number. -/

section OpsTyping

variable {table : RowTable}

open Conform.Effect4.Typing

/-- Every node of the cell's type is formed: the type is closed. -/
theorem cell_nodes : NodesFormed Semaphore.cellTy := nodesFormed_of_check (by decide)

theorem bool_nodes : NodesFormed .bool := nodesFormed_of_check (by decide)

theorem unit_nodes : NodesFormed .unit := nodesFormed_of_check (by decide)

theorem releaseReply_nodes : NodesFormed releaseReplyTy := nodesFormed_of_check (by decide)

theorem visitReply_nodes : NodesFormed visitReplyTy := nodesFormed_of_check (by decide)

theorem releaseReply_normal : releaseReplyTy.normalize = releaseReplyTy := by decide +kernel

theorem visitReply_normal : visitReplyTy.normalize = visitReplyTy := by decide +kernel

/-- A release's reply by position: the free count, and whether a waiter is enrolled. -/
theorem releaseReply_at :
    Tuple.typeAt releaseReplyTy 0 = some .nat ∧ Tuple.typeAt releaseReplyTy 1 = some .bool :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A waiter's hint carries nothing. -/
theorem waiter_hintTy :
    Record.fieldType false Semaphore.waiterTy "hint" = some (.deferredOf .unit .never) :=
  Record.fieldType_normal waiterTy_normal rfl

/-- `getOrElse` at an option of a stamp and a stamp. -/
theorem getOrElse_stamp : nativeAtomTy "getOrElse" [.option .nat, .nat] = some .nat := by
  decide +kernel

/-- The walk's cursor, read through `getOrElse`, keeps the type of a stamp under the surface's
binders. -/
theorem kept_cursorOr {cursor : TermSrc} {s : TypedScope}
    (hcursor : Kept (nativeSignature table) cursor s (.option .nat)) :
    Kept (nativeSignature table) (app "getOrElse" [cursor, nat 0]) s .nat :=
  fun t reach path _ =>
    types_app (.cons (hcursor t reach path _) (.cons (types_nat 0 _) .nil)) getOrElse_stamp

/-- **The construction is typed at every scope**: it answers the handle of a cell at
Semaphore's cell type. -/
@[semantics "store-typing" (requirement := R4)]
theorem make_types (permits : Nat) (positive : 0 < permits) (s : TypedScope) :
    Answers (nativeSignature table) (make permits positive) s (.refOf Semaphore.cellTy) :=
  answers_refMake cellTy_normal cell_nodes fun _ =>
    empty_types (nativeSignature table) rfl permits false

/-- **`takeIfAvailable` is typed at every scope**: it answers a Boolean. The count is a kept
term: the step reads it under the row's own binder. -/
@[semantics "store-typing" (requirement := R4)]
theorem takeIfAvailable_types {q count : TermSrc} {s : TypedScope}
    (hq : Typed (nativeSignature table) q s (.refOf Semaphore.cellTy))
    (hcount : Kept (nativeSignature table) count s .nat) :
    Answers (nativeSignature table) (takeIfAvailable q count) s .bool :=
  answers_refModifyWith cellTy_normal cell_nodes rfl bool_nodes hq fun _ hcurrent path =>
    takeIfAvailableStep_types _ rfl (hcount.push.here path) (hcurrent path)

/-- **The walk is typed at every scope**: it answers nothing. Its visit reads the walk's cursor
and the cell's own source under the visit's fold. A selected waiter's record is read after its
hint is resolved, under one more binder. -/
theorem walk_answers {q : TermSrc} {s : TypedScope}
    (hq : Kept (nativeSignature table) q s (.refOf Semaphore.cellTy)) :
    Answers (nativeSignature table) (walk q) s .unit := by
  have optionNormal : (Ty.option .nat).normalize = .option .nat := by decide +kernel
  have noneBelow : Ty.sub (.option .never) (.option .nat) = true := by decide +kernel
  unfold walk
  refine answers_iterateWith_kept (C0 := .option .nat) (C := .option .nat)
    (B := Ty.join (.option .never) (.option .nat))
    (C1 := Ty.join (.option .never) (.option .nat)) (D := .unit) rfl
    (fun path => types_some rfl (types_nat 0)) ?_ ?_ (fun _ _ _ ha => ha)
    (fun _ _ _ => types_unit) (Ty.subN_refl _)
    (subN_join_of_canonical rfl optionNormal optionNormal noneBelow (Ty.sub_refl _))
  · intro c hc path
    exact fun _ => types_app (.cons (hc path _) .nil) (nativeAtomTy_isSome .nat)
  · intro c hc
    dsimp only
    refine answers_bindWith
      (answers_refModifyWith_captured cellTy_normal cell_nodes visitReply_normal
        visitReply_nodes hq.push.here fun _ hcurrent path =>
          visitStep_types _ rfl (TypedScope.depth _) ((kept_cursorOr hc.push).captured path)
            (hcurrent path))
      fun selected hselected => ?_
    refine answers_selectOptionWith_kept (P := Semaphore.waiterTy) waiterTy_normal
      (fun path => hselected.here path) (answers_succeed fun _ => types_noneT rfl)
      fun waiter hwaiter => ?_
    exact answers_andThen
      (answers_deferredSucceed hintTy_unit
        (fun path _ => types_field (hwaiter.here path false) waiter_hintTy)
        (fun _ => types_unit))
      (answers_succeed fun path =>
        types_some rfl
          (types_add rfl (fun _ => types_field (hwaiter.push.here path false) waiter_stampTy)
            (types_nat 1)))

/-- **`release` is typed at every scope**: it answers a number, the free count. The handle and
the count are kept terms: the operation reads each under its own binders. -/
@[semantics "store-typing" (requirement := R4)]
theorem release_types {q count : TermSrc} {s : TypedScope}
    (hq : Kept (nativeSignature table) q s (.refOf Semaphore.cellTy))
    (hcount : Kept (nativeSignature table) count s .nat) :
    Answers (nativeSignature table) (release q count) s .nat := by
  have joined : Ty.join .unit .unit = .unit := by decide +kernel
  unfold release
  refine answers_uninterruptible (answers_bindWith
    (answers_refModifyWith cellTy_normal cell_nodes releaseReply_normal releaseReply_nodes
      hq.here fun _ hcurrent path =>
        releaseStep_types _ rfl (hcount.push.here path) (hcurrent path))
    fun reply hreply => ?_)
  have post := answers_ifElse (sig := nativeSignature table) (X := .unit) (Y := .unit)
    (test := tupleAt reply 1)
    (thenB := andThen (withFiber (Action.fork (walk q) posted)) (succeed unit))
    (elseB := succeed unit)
    (fun path => (hreply.tupleAt releaseReply_at.2).here path)
    (answers_andThen (answers_fork (walk_answers hq.push))
      (answers_succeed fun _ => types_unit))
    (answers_succeed fun _ => types_unit)
  rw [joined] at post
  exact answers_andThen post
    (answers_succeed fun path => (hreply.push.tupleAt releaseReply_at.1).here path)

/-- **Semaphore's part of the wrapper is typed** at the result type of a count, from every
scope that binds the handle and the count. Its attempt chooses by the take step's Boolean, so
it answers the join of its two exits. Its withdrawal answers nothing. -/
theorem taker_typed {q count : TermSrc} {s : TypedScope}
    (hq : Kept (nativeSignature table) q s (.refOf Semaphore.cellTy))
    (hcount : Kept (nativeSignature table) count s .nat) :
    (taker q count).Typed table s .nat .unit where
  hint := hintTy_unit
  interrupted :=
    (by decide +kernel : nativeAtomTy "causeIsInterrupt" [.exitOf .unit .never] = some .bool)
  attempt := fun t id hint wait done W D reach hid hhint hwait hdone => by
    have body := answers_bindWith (sig := nativeSignature table)
      (first := Ref.modifyWith q (takeStep count id hint))
      (rest := fun took => ifElse took (done count) wait)
      (answers_refModifyWith cellTy_normal cell_nodes rfl bool_nodes (hq.reach reach).here
        fun _ hcurrent path =>
          takeStep_types _ rfl (TypedScope.depth _) ((hcount.reach reach).push.here path)
            (hid.push.captured path) (hhint.push.here path) (hcurrent path))
      fun took htook =>
        answers_ifElse (fun path => htook.here path)
          (hdone _ count (.push _ _ .here) (hcount.reach reach).push.here)
          (hwait _ (.push _ _ .here))
    rw [Ty.join_comm] at body
    exact body
  withdraw := fun t id reach hid =>
    answers_refModifyWith cellTy_normal cell_nodes rfl unit_nodes (hq.reach reach).here
      fun _ hcurrent path =>
        withdrawStep_types _ rfl (TypedScope.depth _) (hid.push.captured path) (hcurrent path)

/-- **`take` is typed at every scope**: it answers a number, the count. The handle and the count
are kept terms: the operation reads each under its own binders. -/
@[semantics "store-typing" (requirement := R4)]
theorem take_types {q count : TermSrc} {s : TypedScope}
    (hq : Kept (nativeSignature table) q s (.refOf Semaphore.cellTy))
    (hcount : Kept (nativeSignature table) count s .nat) :
    Answers (nativeSignature table) (take q count) s .nat :=
  waitRetry_answers rfl (taker_typed hq.push hcount.push)

/-- **`withPermits` is typed at every scope**, for a body of any effect type at every scope that
the surface's binders reach. It keeps the body's answer, its failure type in normal form and
its requirement: the take's loop and the release add no failure and no requirement. -/
@[semantics "store-typing" (requirement := R4)]
theorem withPermits_types {q count : TermSrc} {body : Src NativeOp} {s : TypedScope}
    {b : EffTy} (hq : Kept (nativeSignature table) q s (.refOf Semaphore.cellTy))
    (hcount : Kept (nativeSignature table) count s .nat)
    (hbody : ∀ t : TypedScope, s.Reaches t → Has (nativeSignature table) body t b) :
    Has (nativeSignature table) (withPermits q count body) s
      ⟨b.answer, b.error.normalize, b.requires⟩ :=
  protectedBy_has (G := .nat) (F := .nat)
    (fun _ hrestore => waitRetryAt_answers rfl hrestore (taker_typed hq.push hcount.push))
    (fun _ _ => hbody _ (.push _ _ (.push _ _ .here)))
    (fun _ _ => release_types hq.push.push.push hcount.push.push.push)

/-- **`withPermitsIfAvailable` is typed at every scope**, for a body of any effect type whose
answer type is its own normal form. It answers an option of the body's answer, with the body's
failure type in normal form and its requirement. -/
@[semantics "store-typing" (requirement := R4)]
theorem withPermitsIfAvailable_types {q count : TermSrc} {body : Src NativeOp} {s : TypedScope}
    {b : EffTy} (canonical : b.answer.normalize = b.answer)
    (hq : Kept (nativeSignature table) q s (.refOf Semaphore.cellTy))
    (hcount : Kept (nativeSignature table) count s .nat)
    (hbody : ∀ t : TypedScope, s.Reaches t → Has (nativeSignature table) body t b) :
    Has (nativeSignature table) (withPermitsIfAvailable q count body) s
      ⟨.option b.answer, b.error.normalize, b.requires⟩ := by
  have joined : Ty.join .unit .unit = .unit := by decide +kernel
  have noneBelow : Ty.sub (.option .never) (.option b.answer) = true := by
    rw [Ty.sub_option]
    exact Ty.OrderProof.sub_never b.answer
  have absorbed : Ty.join (.option b.answer) (.option .never) = .option b.answer :=
    join_absorb (Ty.normalize_option_canonical canonical) rfl noneBelow
  have whole := protectedBy_has (table := table) (s := s) (G := .bool) (F := .unit)
    (acquire := fun _ => takeIfAvailable q count)
    (release := fun took =>
      ifElse took (andThen (release q count) (succeed unit)) (succeed unit))
    (body := fun took =>
      ifElse took (bindWith body fun answer => succeed (app "some" [answer])) (succeed noneT))
    (b := ⟨.option b.answer, b.error.normalize, b.requires⟩)
    (fun _ _ => takeIfAvailable_types hq.push.here hcount.push)
    (fun took htook => by
      refine (has_ifElse (fun path => htook.here path)
        (has_bindWith (hbody _ (.push _ _ (.push _ _ .here))) fun answer hanswer =>
          (answers_succeed fun path => types_some rfl (hanswer.here path)).has)
        (answers_succeed fun _ => types_noneT rfl).has).to ?_
      show (⟨Ty.join (.option b.answer) (.option .never),
        (b.error.join .never).join .never,
        (b.requires.union Machine.Env.Requirement.empty).union
          Machine.Env.Requirement.empty⟩ : EffTy) = _
      rw [absorbed, Ty.join_never_right, Ty.join_never_right, Ty.normalize_idem]
      simp only [Machine.Env.Requirement.empty, Machine.Env.Requirement.union,
        Row.union_empty_right])
    (fun took htook =>
      (answers_ifElse (X := .unit) (Y := .unit) (fun path => htook.push.here path)
        (answers_andThen (release_types hq.push.push.push hcount.push.push.push)
          (answers_succeed fun _ => types_unit))
        (answers_succeed fun _ => types_unit)).to joined)
  rw [Ty.normalize_idem] at whole
  exact whole

end OpsTyping

/-! ## The attempt laws, with each capture as a premise

In each statement `env` is the scope of the operation's row, the node of the `Ref.modifyWith`.
`captured` holds the values of that scope and `tys` their types. The step term is elaborated one
level up, under the minted name of the cell's current value. The model's functions are written
with their namespace: `Model.take` is the model's, and `take` is the operation. -/

/-- **The attempt of `take` is the model's `take`.** The cell holds the model state `s`. The
count is a caller's term of the step. The identity is one too, with its capture: it stands in
the removal's fold. The hint is the round's. The step term under the row's own binder is one
atomic update: the store step answers whether the request took, and it writes the model's next
state through the table that holds the hint at the request. The reply and the stored value are
members of their types. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (tb : Table)
    (s : State) (id n : Nat) (hint : DeferredKey) (injective : tb.Injective)
    {countSrc idSrc hintSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsCount : Reads countSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.nat n))
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.promise hint))
    (typesCount : TypesEach sig countSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) .nat)
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) idTy)
    (typesHint : TypesEach sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      takeStep countSrc idSrc hintSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) (Model.take s id n).1) },
          Val.bool (Model.take s id n).2) ∧
      Fits w (Val.bool (Model.take s id n).2) .bool ∧
      Fits w (cellVal (tb.renew id hint) (Model.take s id n).1) Semaphore.cellTy := by
  have reads := takeStep_agrees tb s id n hint injective (push_minted_length depth "current" _)
    readsCount readsId readsHint (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (takeStep_types sig atoms (push_minted_length tyDepth "current" _) typesCount
    typesId typesHint (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The withdrawal of a take is the model's `withdraw`.** The store step answers nothing, and
it writes the model's next state: the request's entry leaves, and no other field changes. The
table does not change. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_withdrawal (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (id : Nat) (injective : tb.Injective) {idSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.promise (tb.handle id)))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      withdrawStep idSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb (Model.withdraw s id)) },
          Val.unit) ∧
      Fits w Val.unit .unit ∧
      Fits w (cellVal tb (Model.withdraw s id)) Semaphore.cellTy := by
  have reads := withdrawStep_agrees tb s id injective (push_minted_length depth "current" _)
    readsId (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (withdrawStep_types sig atoms (push_minted_length tyDepth "current" _) typesId
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The step of `release` is the model's `release`.** The store step answers the free count
after the release and whether a waiter is enrolled, and it writes the model's next state. No
premise names the count: the step releases at most what is taken, as the model's does
(decisions row 261). No fold of the step holds a caller's term, so the count is read at the
row's scope alone. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem release_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (n : Nat) {countSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsCount : Reads countSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.nat n))
    (typesCount : TypesEach sig countSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) .nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      releaseStep countSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb (Model.release s n).1) },
          releaseReplyVal (Model.release s n).2) ∧
      Fits w (releaseReplyVal (Model.release s n).2) releaseReplyTy ∧
      Fits w (cellVal tb (Model.release s n).1) Semaphore.cellTy := by
  have reads := releaseStep_agrees tb s n readsCount (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (releaseStep_types sig atoms typesCount
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The step of `takeIfAvailable` is the model's `takeIfAvailable`.** The store step answers
whether the request took, and it writes the model's next state. It enrols nobody. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem takeIfAvailable_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (n : Nat) {countSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsCount : Reads countSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.nat n))
    (typesCount : TypesEach sig countSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) .nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      takeIfAvailableStep countSrc (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb (Model.takeIfAvailable s n).1) },
          Val.bool (Model.takeIfAvailable s n).2) ∧
      Fits w (Val.bool (Model.takeIfAvailable s n).2) .bool ∧
      Fits w (cellVal tb (Model.takeIfAvailable s n).1) Semaphore.cellTy := by
  have reads := takeIfAvailableStep_agrees tb s n readsCount
    (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (takeIfAvailableStep_types sig atoms typesCount
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **One visit of the walk is the model's `visit`.** The cursor is a caller's term of the step,
with its capture: it stands in the visit's fold. So does the cell's own source, and the row's
own name has that capture (`captured_current`). The store step answers the selected waiter's
record through the table, or nothing, and it writes the model's next state. A visit reserves
nothing: `taken` stays (`visit_reserves_nothing`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem visit_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (cursor : Nat) {cursorSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsCursor : Captured cursorSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.nat cursor))
    (typesCursor : CapturedTy sig cursorSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) .nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      visitStep cursorSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb (Model.visit s cursor).1) },
          visitReplyVal tb (Model.visit s cursor).2) ∧
      Fits w (visitReplyVal tb (Model.visit s cursor).2) visitReplyTy ∧
      Fits w (cellVal tb (Model.visit s cursor).1) Semaphore.cellTy := by
  have reads := visitStep_agrees tb s cursor (push_minted_length depth "current" _) readsCursor
    (captured_current depth path _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (visitStep_types sig atoms (push_minted_length tyDepth "current" _) typesCursor
    (capturedTy_current tyDepth path _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- The initial value reads the cell of the model's initial state, at every table. -/
theorem reads_empty (tb : Table) (permits : Nat) (env : Env) (path : List Nat)
    (vals : List Val) :
    Reads (Semaphore.empty permits) env path vals (cellVal tb (Model.initial permits)) :=
  reads_record (present := [("permits", nat permits), ("taken", nat 0),
      ("waiters", app "nil" []), ("next", nat 0)])
    (.cons (reads_nat permits env path vals) (.cons (reads_nat 0 env path vals)
      (.cons reads_nilT (.cons (reads_nat 0 env path vals) .nil)))) rfl

/-- **`Semaphore.make` makes the cell of the initial state.** The initial state is a state of
the profile's predicate (`initial_profile`). The initial value reads that state's cell, and the
store step of `Ref.make` appends it and answers the new cell's handle. The statement holds at
every total: the profile's predicate has no clause on the total, and `make` refuses zero where
an author writes it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem make_makes (tb : Table) (permits : Nat) (env : Env) (path : List Nat) (vals : List Val)
    (stores : Stores) :
    Profile (Model.initial permits) ∧
      Reads (Semaphore.empty permits) env path vals (cellVal tb (Model.initial permits)) ∧
      syncOpStep (.refMake (cellVal tb (Model.initial permits))) stores =
        some ({ stores with refs := stores.refs ++ [cellVal tb (Model.initial permits)] },
          Val.cell ⟨stores.refs.length⟩) :=
  ⟨initial_profile permits, reads_empty tb permits env path vals, rfl⟩

/-! ## The attempt laws at the operation's own binders

The wrapper binds the request's identity and its hint with `bindWith`, so each is a minted name:
`outer.mint "answer"` for the scope `outer` of its `bindWith`. The walk's loop binds its cursor:
`outer.mint "cursor"` for the scope `outer` of the loop, and the visit reads it through
`getOrElse`. Each statement below takes the row's scope with two written premises for each name.
The scope binds the name at a level, and no later binder of the scope shadows it. The values and
the types hold the request's handles, or the cursor, at those levels. The row's own binder is no
later binder that shadows any of them (`mint_current_ne_answer`, `mint_current_ne_cursor`).

The release and the take that never wait bind no name of their own around their rows: their
statements above are already at the operation's own binders. -/

/-- The walk's cursor, read through `getOrElse`, is a caller's term under the visit's fold: it
reads the stamp that the cursor holds. -/
theorem captured_cursorOr {cursor : TermSrc} {env : Env} {path : List Nat} {vals : List Val}
    {stamp : Nat} (h : Captured cursor env path vals (Store.Val.some (Val.nat stamp))) :
    Captured (app "getOrElse" [cursor, nat 0]) env path vals (Val.nat stamp) :=
  ⟨reads_app (.cons h.atScope (.cons (reads_nat 0 env path vals) .nil)) rfl,
    fun acc item =>
      reads_app (.cons (h.underFold acc item) (.cons (reads_nat 0 _ path _) .nil)) rfl⟩

/-- **The typed twin**: the cursor through `getOrElse` has a stamp's type under the visit's
fold. -/
theorem capturedTy_cursorOr {sig : Signature NativeOp} (atoms : sig.atomOf = nativeAtomTy)
    {cursor : TermSrc} {env : Env} {path : List Nat} {tys : List Ty}
    (h : CapturedTy sig cursor env path tys (.option .nat)) :
    CapturedTy sig (app "getOrElse" [cursor, nat 0]) env path tys .nat :=
  ⟨fun _ => types_app (.cons (h.atScope _) (.cons (types_nat 0 _) .nil))
      (atomOf_native atoms getOrElse_stamp),
    fun acc item _ => types_app (.cons (h.underFold acc item _) (.cons (types_nat 0 _) .nil))
      (atomOf_native atoms getOrElse_stamp)⟩

/-- **The attempt of `take` at the operation's own binders.** The identity and the hint are
names that `bindWith` mints. The scope binds each, and no later binder shadows either. The count
stays a caller's term, with its reading and its type at the row's scope. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (id n : Nat) (hint : DeferredKey) (injective : tb.Injective)
    {countSrc : TermSrc} {env outerId outerHint : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val} {beforeId afterId beforeHint afterHint : Names}
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
    (readsCount : Reads countSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb s]) (Val.nat n))
    (typesCount : TypesEach sig countSrc (env.push [env.mint "current"]) path
      (tys ++ [Semaphore.cellTy]) .nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      takeStep countSrc (minted (outerId.mint "answer")) (minted (outerHint.mint "answer"))
        (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) (Model.take s id n).1) },
          Val.bool (Model.take s id n).2) ∧
      Fits w (Val.bool (Model.take s id n).2) .bool ∧
      Fits w (cellVal (tb.renew id hint) (Model.take s id n).1) Semaphore.cellTy :=
  take_attempt sig atoms tb s id n hint injective depth tyDepth typedEnv readsCount
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (captured_answer_in_row hintScope hintUnshadowed hintHeld).atScope typesCount
    (capturedTy_answer_in_row idScope idUnshadowed idTyped)
    (capturedTy_answer_in_row hintScope hintUnshadowed hintTyped).atScope held member

/-- **The withdrawal of a take at the operation's own binders.** The identity is a name that
`bindWith` mints. The scope binds it, and no later binder shadows it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_withdrawal_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (id : Nat) (injective : tb.Injective) {env outerId : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    {beforeId afterId : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (idScope : env.names = beforeId ++ outerId.mint "answer" :: afterId)
    (idUnshadowed : ∀ name ∈ afterId, name ≠ outerId.mint "answer")
    (idHeld : captured[beforeId.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[beforeId.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      withdrawStep (minted (outerId.mint "answer")) (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb (Model.withdraw s id)) },
          Val.unit) ∧
      Fits w Val.unit .unit ∧
      Fits w (cellVal tb (Model.withdraw s id)) Semaphore.cellTy :=
  take_withdrawal sig atoms tb s id injective depth tyDepth typedEnv
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (capturedTy_answer_in_row idScope idUnshadowed idTyped) held member

/-- **One visit of the walk at the walk's own binder.** The cursor is the name that the walk's
loop mints, and it holds an option of a stamp: the visit reads it through `getOrElse`. The
scope binds the name, and no later binder shadows it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem visit_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (tb : Table) (s : State) (cursor : Nat) {env outer : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val} {before later : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (cursorScope : env.names = before ++ outer.mint "cursor" :: later)
    (cursorUnshadowed : ∀ name ∈ later, name ≠ outer.mint "cursor")
    (cursorHeld : captured[before.length]? = some (Store.Val.some (Val.nat cursor)))
    (cursorTyped : tys[before.length]? = some (.option .nat))
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb s))
    (member : Fits w (cellVal tb s) Semaphore.cellTy) :
    ∃ f,
      visitStep (app "getOrElse" [minted (outer.mint "cursor"), nat 0])
        (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb (Model.visit s cursor).1) },
          visitReplyVal tb (Model.visit s cursor).2) ∧
      Fits w (visitReplyVal tb (Model.visit s cursor).2) visitReplyTy ∧
      Fits w (cellVal tb (Model.visit s cursor).1) Semaphore.cellTy :=
  visit_attempt sig atoms tb s cursor depth tyDepth typedEnv
    (captured_cursorOr (captured_cursor_in_row cursorScope cursorUnshadowed cursorHeld))
    (capturedTy_cursorOr atoms
      (capturedTy_cursor_in_row cursorScope cursorUnshadowed cursorTyped)) held member

end Effect4.Semaphore
