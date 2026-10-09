import Effect4.Laws.Step.Scope
import Effect4.Library.Pool.Ops
import Effect4.Laws.Step.Waiting
import Effect4.Laws.Step.Store
import Effect4.Laws.Library.Pool.Steps
import Effect4.Laws.Library.Pool.Typing
import Effect4.Laws.Program.Authoring.Folds
import Effect4.Laws.Auto.Semantics

/-!
# The laws of Pool's first operations (decisions rows 257, 267 to 269, 276 and 279)

The operations are `src/Effect4/Library/Pool/Ops.lean`: `Pool.make`, `Pool.use` and the close
that `make` registers, over the step terms of `src/Effect4/Library/Pool/Steps.lean` and the
shared wrapper (`src/Effect4/Library/Waiting.lean`).

- **Scope.** Each step term and each program keeps the authoring scope judgment, for every
  scoped term of a caller, every scoped acquisition and every scoped body. Each law is named so
  that `authoring_scoped` finds it.
- **Typing at every scope.** `use_types`, `make_types` and `close_answers`, with the typing of
  each piece. A body and an acquisition have any effect type: each may fail, and each may
  require a service. `make_types` states what `make` requires: the acquisition's requirement,
  and the scope's service.
- **The attempt laws.** Each step of an operation has one statement at its own step term, under
  the binder of its own row. The cell holds the encoding of a model state. The store step then
  answers the model's reply, and it writes the encoding of the model's next state. The reply
  and the stored value are members of their types. The steps are six: the lease, its
  withdrawal, the return, the wake's selection, the close's first step and the closer's step.
  `make_makes` states the row that makes the cell.

Each attempt law is one composition of what exists: the step's agreement
(`src/Effect4/Laws/Library/Pool/Steps.lean`), `step_updates`, the step's typing
(`src/Effect4/Laws/Library/Pool/Typing.lean`) and `step_keeps_cell`
(`src/Effect4/Laws/Step/Store.lean`). It states no new fact of the model.

**The typing equation is no premise** (decisions row 257, points 1 and 2). The step's typing
theorem gives it at the row's own scope, and `Types.tree` reads it at the tree that
`step_updates` names.

**No law takes the profile.** No step reads it. The profile's closure is a statement of its own
(`profile_closed`, `src/Effect4/Laws/Library/Pool/Profile.lean`), and a law of a run uses both.
So each law holds on every model state, which is more than a state of the first profile.

**Each law that reads a minted name has two forms.** The first takes each capture as a written
premise (`Captured`, `CapturedTy`). The second is at the operation's own binders: the identity,
the hint and the leased item are names that `bindWith` mints. It states the scope's two premises
for each name: the scope binds the name, and no later binder shadows it. The battery
`Test/Program/PoolOps.lean` discharges those premises at each operation's own binders, and it
binds each statement's term to the operation's tree.

Placement. Scope: concept `initial-algebras-folds`, requirement R4, a step of the claim
`operation-data-scoped` and of the lifts' scope laws. Its consumer is `Api.Author.build` of each
client, which checks the scope of the tree that a client's source elaborates to. Typing: concept
`store-typing`, requirement R4. Its consumer is a client's admission, and its section states its
reach. The attempt laws: concept `translation-simulation`, requirement R10, parts of the
proposed claim `pool-expansion-agrees`. Their consumer is the law of a run, in a later slice,
which relates the wrapper's run, the wake's and the close's to the model.

Reach of an attempt law: one store step, from a cell that encodes a model state, with an
injective table where the step tests an identity, at every scope. It establishes no delivery,
no order across steps or across helpers, no cancellation law, no law of the protected lease, no
wait of the close along a run, no finalizer's run, no budget, no liveness and nothing of a
host. It does not say that a run reaches the step with such a cell.
-/

set_option autoImplicit false

namespace Effect4.Pool

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## Scope: the step terms and the initial value

A step term is built from the authoring builders, the shared words and folds with minted
binders. Each law unfolds the step to those builders, and `authoring_scoped` applies the lemma
of each. A record's construction is closed by hand: its entries are pairs. -/

/-- A waiter's record keeps scope. -/
theorem mkWaiter_scoped {id hint : TermSrc} (hid : id.Scoped) (hhint : hint.Scoped) :
    (mkWaiter id hint).Scoped :=
  Step.«scoped» Data.waiterPass (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hhint (TermSrc.Scoped_nil))))

/-- The lease step keeps scope. -/
theorem leaseStep_scoped {id hint s : TermSrc} (hid : id.Scoped) (hhint : hint.Scoped)
    (hs : s.Scoped) : (leaseStep id hint s).Scoped :=
  Step.«scoped» (Data.lease (.var 0)) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hhint (TermSrc.Scoped_cons hs (TermSrc.Scoped_nil)))))

/-- The return step keeps scope. -/
theorem returnStep_scoped {i l s : TermSrc} (hi : i.Scoped) (hl : l.Scoped) (hs : s.Scoped) :
    (returnStep i l s).Scoped :=
  Step.«scoped» (Data.giveBack (.var 0)) (Input.source_scoped (TermSrc.Scoped_cons hi (TermSrc.Scoped_cons hl (TermSrc.Scoped_cons hs (TermSrc.Scoped_nil)))))

/-- The selection step keeps scope. -/
theorem selectStep_scoped {count s : TermSrc} (hcount : count.Scoped) (hs : s.Scoped) :
    (selectStep count s).Scoped :=
  Step.«scoped» (Data.select (.var 0)) (Input.source_scoped (TermSrc.Scoped_cons hcount (TermSrc.Scoped_cons hs (TermSrc.Scoped_nil))))

/-- The withdrawal keeps scope. -/
theorem withdrawStep_scoped {id s : TermSrc} (hid : id.Scoped) (hs : s.Scoped) :
    (withdrawStep id s).Scoped :=
  Step.«scoped» (Data.withdraw (.var 0)) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hs (TermSrc.Scoped_nil))))

/-- The close's first step keeps scope. -/
theorem closeStep_scoped {s : TermSrc} (hs : s.Scoped) : (closeStep s).Scoped :=
  Step.«scoped» (Data.close (.var 0)) (Input.source_scoped (TermSrc.Scoped_cons hs (TermSrc.Scoped_nil)))

/-- The closer's step keeps scope. -/
theorem drainStep_scoped {id hint s : TermSrc} (hid : id.Scoped) (hhint : hint.Scoped)
    (hs : s.Scoped) : (drainStep id hint s).Scoped :=
  Step.«scoped» (Data.drain (.var 0)) (Input.source_scoped (TermSrc.Scoped_cons hid (TermSrc.Scoped_cons hhint (TermSrc.Scoped_cons hs (TermSrc.Scoped_nil)))))

/-- An idle item's record keeps scope. -/
theorem mkItem_scoped (A : Ty) {stamp resource : TermSrc} (hstamp : stamp.Scoped)
    (hresource : resource.Scoped) : (mkItem A stamp resource).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact hstamp
    · exact hresource
    · exact bool_scoped false
    · exact nat_scoped 0)

/-- Each item of the initial value keeps scope, where each resource does. -/
theorem itemsFrom_scoped (A : Ty) : ∀ (stamp : Nat) {resources : List TermSrc},
    (∀ r ∈ resources, r.Scoped) → ∀ x ∈ itemsFrom A stamp resources, x.Scoped
  | _, [], _, _, member => absurd member List.not_mem_nil
  | stamp, r :: rest, each, x, member => by
    rcases List.mem_cons.mp member with rfl | tail
    · exact mkItem_scoped A (nat_scoped stamp) (each r List.mem_cons_self)
    · exact itemsFrom_scoped A (stamp + 1)
        (fun r' inside => each r' (List.mem_cons_of_mem r inside)) x tail

/-- Each stamp of the initial value keeps scope: it reads no name. -/
theorem stampsFrom_scoped : ∀ (stamp : Nat) (resources : List TermSrc),
    ∀ x ∈ stampsFrom stamp resources, x.Scoped
  | _, [], _, member => absurd member List.not_mem_nil
  | stamp, _ :: rest, x, member => by
    rcases List.mem_cons.mp member with rfl | tail
    · exact nat_scoped stamp
    · exact stampsFrom_scoped (stamp + 1) rest x tail

/-- The initial value keeps scope, where each resource does. -/
theorem initial_scoped (A : Ty) {resources : List TermSrc} (h : ∀ r ∈ resources, r.Scoped) :
    (initial A resources).Scoped :=
  record_scoped _ (by
    intro entry member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact listOf_scoped (itemsFrom_scoped A 0 h)
    · exact listOf_scoped (stampsFrom_scoped 0 resources)
    · exact app_scoped "nil" TermSrc.Scoped_nil
    · exact bool_scoped false
    · exact nat_scoped 0)

/-! ## Scope: the programs

Each law is one application of the shared forms' laws and of the lifts' lemmas. The handle is a
caller's term, scoped at the operation's node. An acquisition is a caller's program, and a body
is a function of the resource's reader. -/

/-- The answer at a closed pool keeps scope: the fiber's id is under a minted name. -/
theorem refused_scoped : (refused : Src NativeOp).Scoped :=
  bindWith_scoped (withFiber_scoped Action.getId_scoped) fun _ hme =>
    failCause_scoped (Cause.interrupt_scoped (TermSrc.Scoped_some hme))

/-- Pool's part of the wrapper keeps scope, for every scoped handle. -/
theorem borrower_scoped {pool : TermSrc} (hpool : pool.Scoped) : (borrower pool).Scoped :=
  { attempt := fun _ _ _ _ hid hhint hwait hdone =>
      bindWith_scoped
        (Ref.modifyWith_scoped hpool fun _ hs => leaseStep_scoped hid hhint hs) fun _ hreply =>
          ifElse_scoped
            (app_scoped "or" (TermSrc.Scoped_cons (tupleAt_scoped hreply 0)
              (TermSrc.Scoped_cons
                (app_scoped "isSome" (TermSrc.Scoped_cons (tupleAt_scoped hreply 1)
                  TermSrc.Scoped_nil))
                TermSrc.Scoped_nil)))
            (hdone _ (tupleAt_scoped hreply 1)) hwait
    withdraw := fun _ hid => Ref.modifyWith_scoped hpool fun _ hs => withdrawStep_scoped hid hs }

/-- The lease keeps scope, for every scoped handle and every restore function that keeps it. -/
theorem lease_scoped (A : Ty) {pool : TermSrc} {restore : Src NativeOp → Src NativeOp}
    (hpool : pool.Scoped) (hrestore : ∀ e : Src NativeOp, e.Scoped → (restore e).Scoped) :
    (lease A pool restore).Scoped :=
  bindWith_scoped (waitRetryAt_scoped _ _ hrestore (borrower_scoped hpool)) fun _ hgot =>
    selectOptionWith_scoped hgot refused_scoped fun _ hitem => succeed_scoped hitem

/-- The resolution of the selected hints keeps scope: the loop's two names and the selected
waiter's record are minted. -/
theorem resolveAll_scoped {selected : TermSrc} (h : selected.Scoped) :
    (resolveAll selected).Scoped :=
  iterateWith_scoped (nat_scoped 0)
    (fun _ hi => app_scoped "lt" (TermSrc.Scoped_cons hi
      (TermSrc.Scoped_cons (app_scoped "length" (TermSrc.Scoped_cons h TermSrc.Scoped_nil))
        TermSrc.Scoped_nil)))
    (fun _ hi => selectOptionWith_scoped
      (app_scoped "get" (TermSrc.Scoped_cons h (TermSrc.Scoped_cons hi TermSrc.Scoped_nil)))
      (succeed_scoped unit_scoped)
      fun _ hwaiter => andThen_scoped
        (Deferred.succeed_scoped (field_scoped hwaiter "hint") unit_scoped)
        (succeed_scoped unit_scoped))
    (fun _ _ hi _ => app_scoped "succ" (TermSrc.Scoped_cons hi TermSrc.Scoped_nil))
    (fun _ _ => unit_scoped)

/-- The wake's helper keeps scope, for every scoped handle and count. -/
theorem wake_scoped {pool count : TermSrc} (hpool : pool.Scoped) (hcount : count.Scoped) :
    (wake pool count).Scoped :=
  bindWith_scoped (Ref.modifyWith_scoped hpool fun _ hs => selectStep_scoped hcount hs)
    fun _ hselected => resolveAll_scoped hselected

/-- The return keeps scope, for every scoped handle and item. -/
theorem giveBack_scoped {pool item : TermSrc} (hpool : pool.Scoped) (hitem : item.Scoped) :
    (giveBack pool item).Scoped :=
  bindWith_scoped
    (Ref.modifyWith_scoped hpool fun _ hs =>
      returnStep_scoped (field_scoped hitem "stamp") (field_scoped hitem "lease") hs)
    fun _ hreply =>
      ifElse_scoped (tupleAt_scoped hreply 1)
        (andThen_scoped
          (withFiber_scoped (Action.fork_scoped posted (wake_scoped hpool (nat_scoped 1))))
          (succeed_scoped unit_scoped))
        (succeed_scoped unit_scoped)

/-- `Pool.use` keeps scope, for every scoped handle and every body that keeps scope at a scoped
reader of the resource. -/
theorem use_scoped (A : Ty) {pool : TermSrc} {body : TermSrc → Src NativeOp}
    (hpool : pool.Scoped)
    (hbody : ∀ resource : TermSrc, resource.Scoped → (body resource).Scoped) :
    (use A pool body).Scoped :=
  protectedBy_scoped (fun _ hrestore => lease_scoped A hpool hrestore)
    (fun _ hitem => giveBack_scoped hpool hitem)
    (fun _ hitem => hbody _ (field_scoped hitem "resource"))

/-- The closer's part of the wrapper keeps scope, for every scoped handle. -/
theorem closer_scoped {pool : TermSrc} (hpool : pool.Scoped) : (closer pool).Scoped :=
  { attempt := fun _ _ _ _ hid hhint hwait hdone =>
      bindWith_scoped
        (Ref.modifyWith_scoped hpool fun _ hs => drainStep_scoped hid hhint hs) fun _ hdrained =>
          ifElse_scoped hdrained (hdone _ unit_scoped) hwait
    withdraw := fun _ hid => Ref.modifyWith_scoped hpool fun _ hs => withdrawStep_scoped hid hs }

/-- The close keeps scope, for every scoped handle. -/
theorem close_scoped {pool : TermSrc} (hpool : pool.Scoped) : (close pool).Scoped :=
  bindWith_scoped (Ref.modifyWith_scoped hpool fun _ hs => closeStep_scoped hs) fun _ hfirst =>
    andThen_scoped
      (ifElse_scoped
        (app_scoped "and" (TermSrc.Scoped_cons (tupleAt_scoped hfirst 0)
          (TermSrc.Scoped_cons
            (app_scoped "not" (TermSrc.Scoped_cons
              (app_scoped "isZero" (TermSrc.Scoped_cons (tupleAt_scoped hfirst 1)
                TermSrc.Scoped_nil))
              TermSrc.Scoped_nil))
            TermSrc.Scoped_nil)))
        (andThen_scoped
          (withFiber_scoped
            (Action.fork_scoped posted (wake_scoped hpool (tupleAt_scoped hfirst 1))))
          (succeed_scoped unit_scoped))
        (succeed_scoped unit_scoped))
      (waitRetry_scoped _ _ (closer_scoped hpool))

/-- The registration of a cleanup keeps scope: its two names are minted. -/
theorem atClose_scoped {cleanup : Src NativeOp} (h : cleanup.Scoped) : (atClose cleanup).Scoped :=
  minting_scoped _ fun acquired => minting_scoped _ fun exit =>
    acquireRelease_scoped acquired exit (succeed_scoped unit_scoped) h

/-- The acquisitions keep scope, for a scoped acquisition and a continuation that keeps scope at
scoped readers of the resources. -/
theorem acquireAll_scoped {acquire : Src NativeOp} (hacquire : acquire.Scoped) :
    ∀ (count : Nat) {k : List TermSrc → Src NativeOp},
      (∀ resources : List TermSrc, (∀ r ∈ resources, r.Scoped) → (k resources).Scoped) →
        (acquireAll acquire count k).Scoped
  | 0, _, hk => hk [] fun _ member => absurd member List.not_mem_nil
  | count + 1, _, hk =>
    bindWith_scoped hacquire fun _ hresource =>
      acquireAll_scoped hacquire count fun _ hrest =>
        hk _ fun r member =>
          (List.mem_cons.mp member).elim (fun same => same ▸ hresource) (hrest r)

/-- `Pool.make` keeps scope, for every scoped acquisition. -/
theorem make_scoped (A : Ty) (size : Nat) (positive : 0 < size) {acquire : Src NativeOp}
    (hacquire : acquire.Scoped) : (make A size acquire positive).Scoped :=
  acquireAll_scoped hacquire size fun _ hresources =>
    bindWith_scoped (Ref.make_scoped (initial_scoped A hresources)) fun _ hpool =>
      andThen_scoped (atClose_scoped (close_scoped hpool)) (succeed_scoped hpool)

end Effect4.Pool

namespace Effect4.Pool

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Typed
open Effect4.Modules
open Effect4.Pool.Model (ResourceTy leaseReplyTy returnReplyTy selectReplyTy closeReplyTy
  cellTy_normal itemTy_normal waiterTy_normal item_stampTy item_leaseTy initial_types
  leaseStep_types returnStep_types selectStep_types withdrawStep_types closeStep_types
  drainStep_types cellVal itemVal leaseReplyVal returnReplyVal selectReplyVal closeReplyVal
  leaseStep_agrees returnStep_agrees selectStep_agrees withdrawStep_agrees closeStep_agrees
  drainStep_agrees itemOf cellOf item_stamp item_lease Profile initial_profile)

/-! ## Typing at every scope (decisions row 257)

Each program is typed at every typed scope. The handle is a caller's term. `Pool.use` and the
close read it under their own binders, so it is a kept term (`Kept`,
`src/Effect4/Laws/Step/Waiting.lean`): a variable that an author wrote is one.

**A body and an acquisition are a caller's programs.** Each has any effect type (`Has`): it may
fail, and it may require a service. A body stands under the mask's saved state and the leased
item, and it reads the resource through a kept term. So its premise is its effect type for
every kept reader of a resource, at every scope that the surface's binders reach. An
acquisition stands under the earlier resources' names, so its premise is one effect type at
every reached scope.

**`use_types` keeps the body's effect type**: its answer, its failure type in normal form and
its requirement. The lease and the return add no failure and no requirement. A borrow at a
closed pool fails with an interruption, and an interruption is outside the failure column.

**`make_types` states what `make` requires.** `make` answers the handle. Its failure type is the
acquisition's, in normal form. Its requirement is the acquisition's, with the scope's service:
`make` registers the close as a finalizer of the scope that it runs in. So a client reads from
the type that a pool is made inside a scope.

Each proof follows the program's tree. The step of each `Ref.modifyWith` has the type that its
step theorem gives, at the row's own scope (`src/Effect4/Laws/Library/Pool/Typing.lean`). The
lease and the closer's wait are typed through the wrapper's own rule, over Pool's two parts
(`borrower_typed`, `closer_typed`, `waitRetryAt_answers`, `waitRetry_answers`).

Placement. Concept `store-typing`, requirement R4. Reach: the checker's judgment `effTy` on the
program's tree, at every typed scope and every path, at the native signature of any row table;
a resource type with `ResourceTy`. They establish no run. Their consumer is a client's
admission: `Api.Author.build` checks the tree that a client's source elaborates to. A string
literal is no kept term, and the statements state nothing of one. -/

section OpsTyping

variable {table : RowTable}

open Conform.Effect4.Typing
open Effect4.Machine.Env (Requirement)

/-- Every node of a resource type that a cell holds is formed. -/
theorem resource_nodes {A : Ty} (resource : ResourceTy A) : NodesFormed A := fun t member =>
  nodesFormed_of_check resource.item t (by
    show t ∈ [Ty.record (Pool.itemFields A)] ++ (Formation.nodes .nat ++ (Formation.nodes A ++ _))
    exact List.mem_append_right _ (List.mem_append_right _ (List.mem_append_left _ member)))

theorem item_nodes {A : Ty} (resource : ResourceTy A) : NodesFormed (Pool.itemTy A) := by
  intro t member
  have member' : t ∈ [Pool.itemTy A] ++ (Formation.nodes .bool ++ (Formation.nodes .nat ++
      (Formation.nodes A ++ (Formation.nodes .nat ++ [])))) := member
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | h | h | h | h
  · show (["borrowed", "lease", "resource", "stamp"] : List String).Nodup
    decide
  · exact nodesFormed_of_check (T := .bool) (by decide) t h
  · exact nodesFormed_of_check (T := .nat) (by decide) t h
  · exact resource_nodes resource t h
  · exact nodesFormed_of_check (T := .nat) (by decide) t h

theorem cell_nodes {A : Ty} (resource : ResourceTy A) : NodesFormed (Pool.cellTy A) := by
  intro t member
  have member' : t ∈ [Pool.cellTy A] ++ (Formation.nodes (.list .nat) ++ (Formation.nodes .bool ++
      (Formation.nodes (.list (Pool.itemTy A)) ++ (Formation.nodes .nat ++
        (Formation.nodes (.list Pool.waiterTy) ++ []))))) := member
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | h | h | h | h | h
  · show (["available", "closing", "items", "next", "waiters"] : List String).Nodup
    decide
  · exact nodesFormed_of_check (T := .list .nat) (by decide) t h
  · exact nodesFormed_of_check (T := .bool) (by decide) t h
  · exact nodesFormed_list (item_nodes resource) t h
  · exact nodesFormed_of_check (T := .nat) (by decide) t h
  · exact nodesFormed_of_check (T := .list Pool.waiterTy) (by decide) t h

theorem leaseReply_nodes {A : Ty} (resource : ResourceTy A) : NodesFormed (leaseReplyTy A) := by
  intro t member
  have member' : t ∈ [leaseReplyTy A] ++ (Formation.nodes .bool ++
      Formation.nodes (.option (Pool.itemTy A))) := member
  simp only [List.mem_append, List.mem_singleton] at member'
  rcases member' with rfl | h | h
  · exact trivial
  · exact nodesFormed_of_check (T := .bool) (by decide) t h
  · exact nodesFormed_option (item_nodes resource) t h

theorem returnReply_nodes : NodesFormed returnReplyTy := nodesFormed_of_check (by decide)

theorem selectReply_nodes : NodesFormed selectReplyTy := nodesFormed_of_check (by decide)

theorem closeReply_nodes : NodesFormed closeReplyTy := nodesFormed_of_check (by decide)

theorem bool_nodes : NodesFormed .bool := nodesFormed_of_check (by decide)

theorem unit_nodes : NodesFormed .unit := nodesFormed_of_check (by decide)

theorem selectReply_normal : selectReplyTy.normalize = selectReplyTy := by decide +kernel

theorem closeReply_normal : closeReplyTy.normalize = closeReplyTy := by decide +kernel

/-- A lease's reply by position: whether the pool refused, and the leased item, if any. -/
theorem leaseReply_at {A : Ty} (canonical : A.normalize = A) :
    Tuple.typeAt (leaseReplyTy A) 0 = some .bool ∧
      Tuple.typeAt (leaseReplyTy A) 1 = some (.option (Pool.itemTy A)) := by
  unfold Tuple.typeAt
  rw [Model.leaseReplyTy_normal canonical]
  exact ⟨rfl, rfl⟩

/-- A return's reply by position: whether the lease returned, and whether a wake is owed. -/
theorem returnReply_at :
    Tuple.typeAt returnReplyTy 0 = some .bool ∧ Tuple.typeAt returnReplyTy 1 = some .bool :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- The reply of the close's first step by position: whether it began the close, and the count
of the waiters. -/
theorem closeReply_at :
    Tuple.typeAt closeReplyTy 0 = some .bool ∧ Tuple.typeAt closeReplyTy 1 = some .nat :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- A waiter's hint carries nothing. -/
theorem waiter_hintTy :
    Record.fieldType false Pool.waiterTy "hint" = some (.deferredOf .unit .never) :=
  Record.fieldType_normal waiterTy_normal rfl

/-- An item's resource has the resource's type. -/
theorem item_resourceTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Pool.itemTy A) "resource" = some A :=
  Record.fieldType_normal (itemTy_normal canonical) rfl

/-- **The answer at a closed pool is typed at every scope**: it answers nothing, it has no
failure type and it requires nothing. The interruption names the fiber's own id, a number. -/
theorem refused_answers (s : TypedScope) : Answers (nativeSignature table) refused s .never :=
  answers_bindWith (answers_getId s) fun _ hme => answers_interrupt hme.here

/-- **Pool's part of the wrapper is typed** at the result type of an option of an item, from
every scope that binds the handle. Its attempt chooses by one Boolean of the lease step's
reply, so it answers the join of its two exits. Its withdrawal answers nothing. -/
theorem borrower_typed {A : Ty} (resource : ResourceTy A) {pool : TermSrc} {s : TypedScope}
    (hpool : Kept (nativeSignature table) pool s (.refOf (Pool.cellTy A))) :
    (borrower pool).Typed table s (.option (Pool.itemTy A)) .unit where
  hint := hintTy_unit
  interrupted :=
    (by decide +kernel : nativeAtomTy "causeIsInterrupt" [.exitOf .unit .never] = some .bool)
  attempt := fun t id hint wait done W D reach hid hhint hwait hdone => by
    have at1 := (leaseReply_at resource.canonical).2
    have body := answers_bindWith (sig := nativeSignature table)
      (first := Ref.modifyWith pool (leaseStep id hint))
      (rest := fun reply =>
        ifElse (orT (tupleAt reply 0) (app "isSome" [tupleAt reply 1]))
          (done (tupleAt reply 1)) wait)
      (answers_refModifyWith_captured (cellTy_normal resource.canonical) (cell_nodes resource)
        (Model.leaseReplyTy_normal resource.canonical) (leaseReply_nodes resource)
        (hpool.reach reach).here fun _ hcurrent path =>
          leaseStep_types _ rfl resource.canonical (TypedScope.depth _) (hid.push.captured path)
            (hhint.push.here path) (hcurrent path))
      fun reply hreply =>
        answers_ifElse
          (fun path => types_orT rfl
            ((hreply.tupleAt (leaseReply_at resource.canonical).1).here path)
            fun _ => types_app (.cons ((hreply.tupleAt at1).here path _) .nil)
              (nativeAtomTy_isSome (Pool.itemTy A)))
          (hdone _ (tupleAt reply 1) (.push _ _ .here) (hreply.tupleAt at1).here)
          (hwait _ (.push _ _ .here))
    rw [Ty.join_comm] at body
    exact body
  withdraw := fun t id reach hid =>
    answers_refModifyWith (cellTy_normal resource.canonical) (cell_nodes resource) rfl unit_nodes
      (hpool.reach reach).here fun _ hcurrent path =>
        withdrawStep_types _ rfl resource.canonical (TypedScope.depth _) (hid.push.captured path)
          (hcurrent path)

/-- **The lease is typed at every scope**: it answers an item's record, with no failure. The
restore function keeps what its argument answers, at every scope that the surface's binders
reach. Where the pool refuses, the branch answers nothing: the join with it is the item's
type. -/
theorem lease_answers {A : Ty} (resource : ResourceTy A) {pool : TermSrc}
    {restore : Src NativeOp → Src NativeOp} {s : TypedScope}
    (hpool : Kept (nativeSignature table) pool s (.refOf (Pool.cellTy A)))
    (hrestore : ∀ (t : TypedScope) (inner : Src NativeOp) (Y : Ty), s.Reaches t →
      Answers (nativeSignature table) inner t Y →
        Answers (nativeSignature table) (restore inner) t Y) :
    Answers (nativeSignature table) (lease A pool restore) s (Pool.itemTy A) := by
  have itemNormal := itemTy_normal resource.canonical
  have joined : Ty.join .never (Pool.itemTy A) = Pool.itemTy A :=
    (Ty.join_never _).trans itemNormal
  unfold lease
  exact (answers_bindWith
    (waitRetryAt_answers (Ty.normalize_option_canonical itemNormal) hrestore
      (borrower_typed resource hpool))
    fun _ hgot =>
      answers_selectOptionWith itemNormal (fun path => hgot.here path) (refused_answers _)
        fun _ hitem => answers_succeed hitem).to joined

/-- **The resolution of the selected hints is typed at every scope**: it answers nothing. The
selected records are a kept term: the loop reads them under its own binders. -/
theorem resolveAll_answers {selected : TermSrc} {s : TypedScope}
    (hselected : Kept (nativeSignature table) selected s (.list Pool.waiterTy)) :
    Answers (nativeSignature table) (resolveAll selected) s .unit := by
  have joined : Ty.join .unit .unit = .unit := by decide +kernel
  have succTy : nativeAtomTy "succ" [.nat] = some .nat := NativeAtom.monoApply_self [.nat] .nat
  unfold resolveAll
  refine answers_iterateWith (C0 := .nat) (C := .nat) (B := .unit) (C1 := .nat) (D := .unit) rfl
    (fun _ => types_nat 0) ?_ ?_ ?_ (fun _ _ _ => types_unit) (Ty.subN_refl _) (Ty.subN_refl _)
  · intro c hc path
    exact types_lt rfl (hc path) (types_len rfl (hselected.push.here path))
  · intro c hc
    have body := answers_selectOptionWith (sig := nativeSignature table)
      (scrutinee := app "get" [selected, c]) (arm0 := succeed unit) (X := .unit) (Y := .unit)
      (arm1 := fun waiter =>
        andThen (Deferred.succeed (field waiter "hint") unit) (succeed unit))
      waiterTy_normal
      (fun path _ => types_app (.cons (hselected.push.here path _) (.cons (hc path _) .nil))
        (nativeAtomTy_get Pool.waiterTy))
      (answers_succeed fun _ => types_unit)
      (fun _ hwaiter => answers_andThen
        (answers_deferredSucceed hintTy_unit
          (fun path _ => types_field (hwaiter path false) waiter_hintTy) (fun _ => types_unit))
        (answers_succeed fun _ => types_unit))
    rw [joined] at body
    exact body
  · intro c a hc _ path _
    exact types_app (.cons (hc path _) .nil) succTy

/-- **The wake's helper is typed at every scope**: it answers nothing. The count is a kept
term: the selection step reads it under the row's own binder. -/
theorem wake_answers {A : Ty} (resource : ResourceTy A) {pool count : TermSrc} {s : TypedScope}
    (hpool : Typed (nativeSignature table) pool s (.refOf (Pool.cellTy A)))
    (hcount : Kept (nativeSignature table) count s .nat) :
    Answers (nativeSignature table) (wake pool count) s .unit := by
  unfold wake
  exact answers_bindWith
    (answers_refModifyWith (cellTy_normal resource.canonical) (cell_nodes resource)
      selectReply_normal selectReply_nodes hpool fun _ hcurrent path =>
        selectStep_types _ rfl resource.canonical (hcount.push.here path) (hcurrent path))
    fun _ hselected => resolveAll_answers hselected

/-- **The return is typed at every scope**: it answers nothing. The handle and the item's
record are kept terms. The step reads the item's two stamps under its folds. -/
theorem giveBack_answers {A : Ty} (resource : ResourceTy A) {pool item : TermSrc}
    {s : TypedScope} (hpool : Kept (nativeSignature table) pool s (.refOf (Pool.cellTy A)))
    (hitem : Kept (nativeSignature table) item s (Pool.itemTy A)) :
    Answers (nativeSignature table) (giveBack pool item) s .unit := by
  have joined : Ty.join .unit .unit = .unit := by decide +kernel
  unfold giveBack
  refine answers_bindWith
    (answers_refModifyWith (cellTy_normal resource.canonical) (cell_nodes resource)
      Model.returnReplyTy_normal returnReply_nodes hpool.here fun _ hcurrent path =>
        returnStep_types _ rfl resource.canonical (TypedScope.depth _)
          ((hitem.push.field (item_stampTy resource.canonical)).captured path)
          ((hitem.push.field (item_leaseTy resource.canonical)).captured path) (hcurrent path))
    fun reply hreply => ?_
  have post := answers_ifElse (sig := nativeSignature table) (X := .unit) (Y := .unit)
    (test := tupleAt reply 1)
    (thenB := andThen (withFiber (Action.fork (wake pool (nat 1)) posted)) (succeed unit))
    (elseB := succeed unit)
    (fun path => (hreply.tupleAt returnReply_at.2).here path)
    (answers_andThen (answers_fork (wake_answers resource hpool.push.here (kept_nat 1 _)))
      (answers_succeed fun _ => types_unit))
    (answers_succeed fun _ => types_unit)
  rw [joined] at post
  exact post

/-- **`Pool.use` is typed at every scope**, for a body of one effect type at every kept reader
of a resource and at every scope that the surface's binders reach. It keeps the body's answer,
its failure type in normal form and its requirement: the lease and the return add no failure and
no requirement. -/
@[semantics "store-typing" (requirement := R4)]
theorem use_types {A : Ty} (resource : ResourceTy A) {pool : TermSrc}
    {body : TermSrc → Src NativeOp} {s : TypedScope} {b : EffTy}
    (hpool : Kept (nativeSignature table) pool s (.refOf (Pool.cellTy A)))
    (hbody : ∀ (t : TypedScope) (r : TermSrc), s.Reaches t →
      Kept (nativeSignature table) r t A → Has (nativeSignature table) (body r) t b) :
    Has (nativeSignature table) (use A pool body) s
      ⟨b.answer, b.error.normalize, b.requires⟩ :=
  protectedBy_has (G := Pool.itemTy A) (F := .unit)
    (fun _ hrestore => lease_answers resource hpool.push hrestore)
    (fun _ hitem => hbody _ _ (.push _ _ (.push _ _ .here))
      (hitem.field (item_resourceTy resource.canonical)))
    (fun _ hitem => giveBack_answers resource hpool.push.push.push hitem.push)

/-- **The closer's part of the wrapper is typed** at the result type of nothing, from every
scope that binds the handle. Its attempt chooses by the closer's step's Boolean. -/
theorem closer_typed {A : Ty} (resource : ResourceTy A) {pool : TermSrc} {s : TypedScope}
    (hpool : Kept (nativeSignature table) pool s (.refOf (Pool.cellTy A))) :
    (closer pool).Typed table s .unit .unit where
  hint := hintTy_unit
  interrupted :=
    (by decide +kernel : nativeAtomTy "causeIsInterrupt" [.exitOf .unit .never] = some .bool)
  attempt := fun t id hint wait done W D reach hid hhint hwait hdone => by
    have body := answers_bindWith (sig := nativeSignature table)
      (first := Ref.modifyWith pool (drainStep id hint))
      (rest := fun drained => ifElse drained (done unit) wait)
      (answers_refModifyWith (cellTy_normal resource.canonical) (cell_nodes resource) rfl
        bool_nodes (hpool.reach reach).here fun _ hcurrent path =>
          drainStep_types _ rfl resource.canonical (TypedScope.depth _) (hid.push.captured path)
            (hhint.push.here path) (hcurrent path))
      fun _ hdrained =>
        answers_ifElse (fun path => hdrained.here path)
          (hdone _ unit (.push _ _ .here) fun _ => types_unit)
          (hwait _ (.push _ _ .here))
    rw [Ty.join_comm] at body
    exact body
  withdraw := fun t id reach hid =>
    answers_refModifyWith (cellTy_normal resource.canonical) (cell_nodes resource) rfl unit_nodes
      (hpool.reach reach).here fun _ hcurrent path =>
        withdrawStep_types _ rfl resource.canonical (TypedScope.depth _) (hid.push.captured path)
          (hcurrent path)

/-- **The close is typed at every scope**: it answers nothing, it has no failure and it
requires nothing. So it is a release that cannot fail, and `make` registers it. -/
@[semantics "store-typing" (requirement := R4)]
theorem close_answers {A : Ty} (resource : ResourceTy A) {pool : TermSrc} {s : TypedScope}
    (hpool : Kept (nativeSignature table) pool s (.refOf (Pool.cellTy A))) :
    Answers (nativeSignature table) (close pool) s .unit := by
  have joined : Ty.join .unit .unit = .unit := by decide +kernel
  unfold close
  refine answers_bindWith
    (answers_refModifyWith (cellTy_normal resource.canonical) (cell_nodes resource)
      closeReply_normal closeReply_nodes hpool.here fun _ hcurrent path =>
        closeStep_types _ rfl resource.canonical (hcurrent path))
    fun first hfirst => ?_
  have count := hfirst.tupleAt closeReply_at.2
  have post := answers_ifElse (sig := nativeSignature table) (X := .unit) (Y := .unit)
    (test := andT (tupleAt first 0) (notT (app "isZero" [tupleAt first 1])))
    (thenB := andThen (withFiber (Action.fork (wake pool (tupleAt first 1)) posted))
      (succeed unit))
    (elseB := succeed unit)
    (fun path => types_andT rfl ((hfirst.tupleAt closeReply_at.1).here path)
      (types_notT rfl (types_isZero rfl (count.here path))))
    (answers_andThen (answers_fork (wake_answers resource hpool.push.here count))
      (answers_succeed fun _ => types_unit))
    (answers_succeed fun _ => types_unit)
  rw [joined] at post
  exact answers_andThen post (waitRetry_answers rfl (closer_typed resource hpool.push.push.push))

/-- **The registration of a cleanup is typed at every scope**, for a cleanup that answers a
type with no failure and no requirement. It answers nothing, and it requires the scope's
service. -/
theorem atClose_has {cleanup : Src NativeOp} {s : TypedScope} {F : Ty}
    (hcleanup : Answers (nativeSignature table) cleanup
      (s.push2 .answer .exit .unit (.exitOf .unknown .unknown)) F) :
    Has (nativeSignature table) (atClose cleanup) s
      ⟨.unit, .never, Requirement.single (nativeSignature table).scopeKey⟩ := by
  have registered := has_acquireRelease (sig := nativeSignature table) (s := s)
    (a := EffTy.pure .unit) (r := EffTy.pure F) (acquire := succeed unit) (release := cleanup)
    (answers_succeed fun _ => types_unit).has hcleanup.has rfl
  refine Has.to (src := atClose cleanup) registered ?_
  show (⟨.unit, .never, (Requirement.empty.union Requirement.empty).union
    (Requirement.single (nativeSignature table).scopeKey)⟩ : EffTy) = _
  simp only [Requirement.empty, Requirement.union, Row.union_empty_left]

/-- The failure type of `count` acquisitions before a tail, as the checker joins them. -/
def errorsOf (e tail : Ty) : Nat → Ty
  | 0 => tail
  | count + 1 => e.join (errorsOf e tail count)

/-- The requirement of `count` acquisitions before a tail, as the checker unions them. -/
def requiresOf (r tail : Requirement) : Nat → Requirement
  | 0 => tail
  | count + 1 => r.union (requiresOf r tail count)

/-- At least one acquisition before a tail that cannot fail: the failure type is the
acquisition's, in normal form. -/
theorem errorsOf_never (e : Ty) : ∀ count : Nat, errorsOf e .never (count + 1) = e.normalize
  | 0 => Ty.join_never_right e
  | count + 1 => by
    show e.join (errorsOf e .never (count + 1)) = _
    rw [errorsOf_never e count, ← Ty.join_never_right e, ← Ty.join_assoc, Ty.join_self,
      Ty.join_never_right, Ty.join_never_right, Ty.normalize_idem]

/-- At least one acquisition before a tail: the requirement is the acquisition's with the
tail's. -/
theorem requiresOf_succ (r tail : Requirement) :
    ∀ count : Nat, requiresOf r tail (count + 1) = r.union tail
  | 0 => rfl
  | count + 1 => by
    show r.union (requiresOf r tail (count + 1)) = _
    rw [requiresOf_succ r tail count]
    simp only [Requirement.union, ← Row.union_assoc, Row.union_idem]

/-- **The acquisitions are typed at every scope**, for an acquisition of one effect type at
every reached scope, and a continuation of one effect type at every list of kept readers of
the resources. The answer is the continuation's. The failure types and the requirements are as
the checker joins them. -/
theorem acquireAll_has {acquire : Src NativeOp} {a tail : EffTy} :
    ∀ (count : Nat) {k : List TermSrc → Src NativeOp} {s : TypedScope},
      (∀ t, s.Reaches t → Has (nativeSignature table) acquire t a) →
      (∀ (t : TypedScope) (resources : List TermSrc), s.Reaches t → resources.length = count →
        (∀ r ∈ resources, Kept (nativeSignature table) r t a.answer) →
          Has (nativeSignature table) (k resources) t tail) →
      Has (nativeSignature table) (acquireAll acquire count k) s
        ⟨tail.answer, errorsOf a.error tail.error count,
          requiresOf a.requires tail.requires count⟩
  | 0, _, s, _, hk => hk s [] .here rfl fun _ member => absurd member List.not_mem_nil
  | count + 1, k, s, hacquire, hk =>
    has_bindWith (hacquire s .here) fun resource hresource =>
      acquireAll_has count (fun t reach => hacquire t reach.of_push)
        fun t rest reach size each =>
          hk t (resource :: rest) reach.of_push (by rw [List.length_cons, size])
            fun r member =>
              (List.mem_cons.mp member).elim (fun same => same ▸ hresource.reach reach)
                (each r)

/-- **`Pool.make` is typed at every scope**, for an acquisition of one effect type at every
scope that the surface's binders reach, whose answer is the resource's type. It answers the
handle of a cell at Pool's cell type. Its failure type is the acquisition's, in normal form: a
failed acquisition fails `make`. **Its requirement is the acquisition's, with the scope's
service**: `make` registers the close as a finalizer of the scope that it runs in, so a pool is
made inside a scope. -/
@[semantics "store-typing" (requirement := R4)]
theorem make_types {A : Ty} (resource : ResourceTy A) (size : Nat) (positive : 0 < size)
    {acquire : Src NativeOp} {s : TypedScope} {a : EffTy} (answers : a.answer = A)
    (hacquire : ∀ t, s.Reaches t → Has (nativeSignature table) acquire t a) :
    Has (nativeSignature table) (make A size acquire positive) s
      ⟨.refOf (Pool.cellTy A), a.error.normalize,
        a.requires.union (Requirement.single (nativeSignature table).scopeKey)⟩ := by
  obtain ⟨count, rfl⟩ : ∃ count, size = count + 1 := ⟨size - 1, by omega⟩
  have whole := acquireAll_has (table := table) (acquire := acquire) (a := a)
    (tail := ⟨.refOf (Pool.cellTy A), .never,
      Requirement.single (nativeSignature table).scopeKey⟩)
    (count + 1) (s := s)
    (k := fun resources =>
      bindWith (Ref.make (initial A resources)) fun pool =>
        andThen (atClose (close pool)) (succeed pool))
    hacquire
    (fun t resources _ size each => by
      have nonempty : resources ≠ [] := fun none => by
        rw [none] at size
        exact absurd size (Nat.succ_ne_zero count).symm
      refine (has_bindWith
        (answers_refMake (cellTy_normal resource.canonical) (cell_nodes resource) fun path =>
          initial_types (nativeSignature table) rfl resource nonempty
            (fun r member => (answers ▸ each r member).here path) false).has
        fun pool hpool =>
          has_andThen (atClose_has (close_answers resource hpool.push2))
            (answers_succeed hpool.push.here).has).to ?_
      show (⟨.refOf (Pool.cellTy A), Ty.never.join (Ty.never.join Ty.never),
        Requirement.empty.union ((Requirement.single (nativeSignature table).scopeKey).union
          Requirement.empty)⟩ : EffTy) = _
      have never : Ty.never.join Ty.never = Ty.never := by decide +kernel
      rw [never, never]
      simp only [Requirement.empty, Requirement.union, Row.union_empty_left,
        Row.union_empty_right])
  refine whole.to ?_
  rw [errorsOf_never, requiresOf_succ]

end OpsTyping

/-! ## The attempt laws, with each capture as a premise

In each statement `env` is the scope of the operation's row, the node of the `Ref.modifyWith`.
`captured` holds the values of that scope and `tys` their types. The step term is elaborated one
level up, under the minted name of the cell's current value. The model's functions are written
with their namespace: `Model.lease` is the model's, and `lease` is the program. -/

/-- **The attempt of a lease is the model's `lease`.** The cell holds the model state `s`. The
identity is a caller's term of the step, with its capture: it stands in the removal's fold. The
hint is the round's. The cell's own source stands in the two folds over the items, and the row's
own name has that capture (`captured_current`). The store step answers whether the pool refused
and the leased item's record, if any. It writes the model's next state through the table that
holds the hint at the request. The reply and the stored value are members of their types. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem lease_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) {A : Ty}
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State) (id : Nat)
    (hint : DeferredKey) (injective : tb.Injective) {idSrc hintSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.promise hint))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) idTy)
    (typesHint : TypesEach sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      leaseStep idSrc hintSrc (minted (env.mint "current")) (env.push [env.mint "current"])
        path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) res (Model.lease s id).1) },
          leaseReplyVal res (Model.lease s id).2) ∧
      Fits w (leaseReplyVal res (Model.lease s id).2) (leaseReplyTy A) ∧
      Fits w (cellVal (tb.renew id hint) res (Model.lease s id).1) (Pool.cellTy A) := by
  have reads := leaseStep_agrees tb res s id hint injective
    (push_minted_length depth "current" _) readsId readsHint (captured_current depth path _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (leaseStep_types sig atoms canonical (push_minted_length tyDepth "current" _)
    typesId typesHint (capturedTy_current tyDepth path _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The withdrawal of a request is the model's `withdraw`.** The store step answers nothing,
and it writes the model's next state: the request's entry leaves, and no other field changes.
The table does not change. A borrower's withdrawal and the closer's are this one statement. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdraw_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) {A : Ty}
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State) (id : Nat)
    (injective : tb.Injective) {idSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.promise (tb.handle id)))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      withdrawStep idSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb res (Model.withdraw s id)) }, Val.unit) ∧
      Fits w Val.unit .unit ∧
      Fits w (cellVal tb res (Model.withdraw s id)) (Pool.cellTy A) := by
  have reads := withdrawStep_agrees tb res s id injective (push_minted_length depth "current" _)
    readsId (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (withdrawStep_types sig atoms canonical (push_minted_length tyDepth "current" _)
    typesId (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The step of a return is the model's `giveBack`.** The item's stamp and the lease's stamp
are a caller's terms of the step, each with its capture: each stands in the two folds over the
items. The store step answers whether the lease returned and whether a wake is owed, and it
writes the model's next state. No premise names the lease: a return of a lease that holds
nothing changes nothing, as the model's does. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem return_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) {A : Ty}
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State)
    (item lease : Nat) {itemSrc leaseSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsItem : Captured itemSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.nat item))
    (readsLease : Captured leaseSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.nat lease))
    (typesItem : CapturedTy sig itemSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) .nat)
    (typesLease : CapturedTy sig leaseSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) .nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      returnStep itemSrc leaseSrc (minted (env.mint "current")) (env.push [env.mint "current"])
        path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb res (Model.giveBack s item lease).1) },
          returnReplyVal (Model.giveBack s item lease).2) ∧
      Fits w (returnReplyVal (Model.giveBack s item lease).2) returnReplyTy ∧
      Fits w (cellVal tb res (Model.giveBack s item lease).1) (Pool.cellTy A) := by
  have reads := returnStep_agrees tb res s item lease (push_minted_length depth "current" _)
    readsItem readsLease (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (returnStep_types sig atoms canonical (push_minted_length tyDepth "current" _)
    typesItem typesLease (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The selection of a wake is the model's `select`.** The count is a caller's term of the
step, read at the row's scope alone: the step folds nothing. The store step answers the
selected waiters' records through the table, in order, and it writes the model's next state. A
selection reserves nothing: only the waiters change (`select_takes_first`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem select_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) {A : Ty}
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State) (count : Nat)
    {countSrc : TermSrc} {env : Env} {path : List Nat} {tys : List Ty} {w : Typed.World}
    {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsCount : Reads countSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.nat count))
    (typesCount : TypesEach sig countSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) .nat)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      selectStep countSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path =
        .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb res (Model.select s count).1) },
          selectReplyVal tb (Model.select s count).2) ∧
      Fits w (selectReplyVal tb (Model.select s count).2) selectReplyTy ∧
      Fits w (cellVal tb res (Model.select s count).1) (Pool.cellTy A) := by
  have reads := selectStep_agrees tb res s count readsCount
    (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (selectStep_types sig atoms canonical typesCount
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The close's first step is the model's `close`.** The store step answers whether it began
the close and the count of the waiters, and it writes the model's next state: the pool refuses
new leases from now on (`close_refuses`). -/
@[semantics "translation-simulation" (requirement := R10)]
theorem close_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) {A : Ty}
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State) {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      closeStep (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q (cellVal tb res (Model.close s).1) },
          closeReplyVal (Model.close s).2) ∧
      Fits w (closeReplyVal (Model.close s).2) closeReplyTy ∧
      Fits w (cellVal tb res (Model.close s).1) (Pool.cellTy A) := by
  have reads := closeStep_agrees tb res s (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (closeStep_types sig atoms canonical
    (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-- **The attempt of the closer is the model's `drain`.** The closer's identity is a caller's
term of the step, with its capture: it stands in the removal's fold. The hint is the round's.
The store step answers whether no lease is outstanding (`drain_waits`). It writes the model's
next state through the table that holds the hint at the closer. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem drain_attempt (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) {A : Ty}
    (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State) (id : Nat)
    (hint : DeferredKey) (injective : tb.Injective) {idSrc hintSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {w : Typed.World} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb res s]) (Val.promise hint))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) idTy)
    (typesHint : TypesEach sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Pool.cellTy A]) idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      drainStep idSrc hintSrc (minted (env.mint "current")) (env.push [env.mint "current"])
        path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) res (Model.drain s id).1) },
          Val.bool (Model.drain s id).2) ∧
      Fits w (Val.bool (Model.drain s id).2) .bool ∧
      Fits w (cellVal (tb.renew id hint) res (Model.drain s id).1) (Pool.cellTy A) := by
  have reads := drainStep_agrees tb res s id hint injective
    (push_minted_length depth "current" _) readsId readsHint
    (reads_minted_last depth path "current" _)
  obtain ⟨f, tree, stepped⟩ := step_updates held reads
  have typed := (drainStep_types sig atoms canonical (push_minted_length tyDepth "current" _)
    typesId typesHint (types_minted_last tyDepth path "current" _) false).tree tree
  obtain ⟨fitsReply, fitsNext⟩ :=
    step_keeps_cell sig atoms typedEnv typed held member (reads.eval tree)
  exact ⟨f, tree, stepped, fitsReply, fitsNext⟩

/-! ## The construction -/

/-- An idle item's record, built from a stamp and a resource's value. -/
theorem reads_mkItem (A : Ty) {stamp resource : TermSrc} {env : Env} {path : List Nat}
    {vals : List Val} {n : Nat} {v : Val} (hstamp : Reads stamp env path vals (Val.nat n))
    (hresource : Reads resource env path vals v) :
    Reads (mkItem A stamp resource) env path vals
      (itemOf (.bool false) (.nat 0) v (.nat n)) :=
  reads_record (present := [("stamp", stamp), ("resource", resource), ("borrowed", bool false),
      ("lease", nat 0)])
    (.cons hstamp (.cons hresource (.cons (reads_bool false env path vals)
      (.cons (reads_nat 0 env path vals) .nil)))) rfl

/-- The items of the initial value read the model's items as it is made, through the resources'
values. -/
theorem reads_itemsFrom (A : Ty) (res : Nat → Val) {env : Env} {path : List Nat}
    {vals : List Val} : ∀ (stamp : Nat) {resources : List TermSrc} {names : List Nat},
      Pointwise (fun src r => Reads src env path vals (res r)) resources names →
        ReadsAll (itemsFrom A stamp resources) env path vals
          ((Model.itemsFrom stamp names).map (itemVal res))
  | _, _, _, .nil => .nil
  | stamp, _, _, .cons hr rest =>
    .cons (reads_mkItem A (reads_nat stamp env path vals) hr) (reads_itemsFrom A res (stamp + 1) rest)

/-- The stamps of the initial value read the model's idle stamps as the pool is made. -/
theorem reads_stampsFrom (res : Nat → Val) {env : Env} {path : List Nat} {vals : List Val} :
    ∀ (stamp : Nat) {resources : List TermSrc} {names : List Nat},
      Pointwise (fun src r => Reads src env path vals (res r)) resources names →
        ReadsAll (stampsFrom stamp resources) env path vals
          (((Model.itemsFrom stamp names).map (·.stamp)).map Val.nat)
  | _, _, _, .nil => .nil
  | stamp, _, _, .cons _ rest =>
    .cons (reads_nat stamp env path vals) (reads_stampsFrom res (stamp + 1) rest)

/-- The initial value reads the cell of the model's initial state, at every table, where each
resource's term reads its value. -/
theorem reads_initial (tb : Table) (res : Nat → Val) (A : Ty) {env : Env} {path : List Nat}
    {vals : List Val} {resources : List TermSrc} {names : List Nat}
    (each : Pointwise (fun src r => Reads src env path vals (res r)) resources names) :
    Reads (initial A resources) env path vals (cellVal tb res (Model.initial names)) :=
  reads_record (present := [("items", listOf (itemsFrom A 0 resources)),
      ("available", listOf (stampsFrom 0 resources)), ("waiters", nilT),
      ("closing", bool false), ("next", nat 0)])
    (.cons (reads_listOf (reads_itemsFrom A res 0 each))
      (.cons (reads_listOf (reads_stampsFrom res 0 each))
        (.cons reads_nilT (.cons (reads_bool false env path vals)
          (.cons (reads_nat 0 env path vals) .nil))))) rfl

/-- **`Pool.make` makes the cell of the initial state.** The initial state is a state of the
profile (`initial_profile`), at every list of resources. The initial value reads that state's
cell, where each acquired resource's reader reads its value. The store step of `Ref.make`
appends that cell and answers its handle. The statement is of the one row that makes the cell:
it states nothing of the acquisitions and nothing of the close's registration. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem make_makes (tb : Table) (res : Nat → Val) (A : Ty) {env : Env} {path : List Nat}
    {vals : List Val} {resources : List TermSrc} {names : List Nat} (stores : Stores)
    (each : Pointwise (fun src r => Reads src env path vals (res r)) resources names) :
    Profile (Model.initial names) ∧
      Reads (initial A resources) env path vals (cellVal tb res (Model.initial names)) ∧
      syncOpStep (.refMake (cellVal tb res (Model.initial names))) stores =
        some ({ stores with refs := stores.refs ++ [cellVal tb res (Model.initial names)] },
          Val.cell ⟨stores.refs.length⟩) :=
  ⟨initial_profile names, reads_initial tb res A each, rfl⟩

/-! ## The attempt laws at the operation's own binders

The wrapper binds a request's identity and its hint with `bindWith`, so each is a minted name:
`outer.mint "answer"` for the scope `outer` of its `bindWith`. The protected form binds the
leased item's record so too, and the return reads two fields of it. Each statement below takes
the row's scope with two written premises for each name. The scope binds the name at a level,
and no later binder of the scope shadows it. The values and the types hold the request's
handles, or the item's record, at those levels. The row's own binder is no later binder that
shadows any of them (`mint_current_ne_answer`).

The selection and the close's first step read no minted name under a fold: their statements
above are already at the operation's own binders. -/

/-- **The attempt of a lease at the operation's own binders.** The identity and the hint are
names that `bindWith` mints. The scope binds each, and no later binder shadows either. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem lease_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State)
    (id : Nat) (hint : DeferredKey) (injective : tb.Injective) {env outerId outerHint : Env}
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
    (hintTyped : tys[beforeHint.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      leaseStep (minted (outerId.mint "answer")) (minted (outerHint.mint "answer"))
        (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) res (Model.lease s id).1) },
          leaseReplyVal res (Model.lease s id).2) ∧
      Fits w (leaseReplyVal res (Model.lease s id).2) (leaseReplyTy A) ∧
      Fits w (cellVal (tb.renew id hint) res (Model.lease s id).1) (Pool.cellTy A) :=
  lease_attempt sig atoms canonical tb res s id hint injective depth tyDepth typedEnv
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (captured_answer_in_row hintScope hintUnshadowed hintHeld).atScope
    (capturedTy_answer_in_row idScope idUnshadowed idTyped)
    (capturedTy_answer_in_row hintScope hintUnshadowed hintTyped).atScope held member

/-- **The withdrawal of a request at the operation's own binders.** The identity is a name that
`bindWith` mints. The scope binds it, and no later binder shadows it. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem withdraw_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State)
    (id : Nat) (injective : tb.Injective) {env outerId : Env} {path : List Nat} {tys : List Ty}
    {w : Typed.World} {captured : List Val} {beforeId afterId : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (idScope : env.names = beforeId ++ outerId.mint "answer" :: afterId)
    (idUnshadowed : ∀ name ∈ afterId, name ≠ outerId.mint "answer")
    (idHeld : captured[beforeId.length]? = some (Val.promise (tb.handle id)))
    (idTyped : tys[beforeId.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      withdrawStep (minted (outerId.mint "answer")) (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal tb res (Model.withdraw s id)) }, Val.unit) ∧
      Fits w Val.unit .unit ∧
      Fits w (cellVal tb res (Model.withdraw s id)) (Pool.cellTy A) :=
  withdraw_attempt sig atoms canonical tb res s id injective depth tyDepth typedEnv
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (capturedTy_answer_in_row idScope idUnshadowed idTyped) held member

/-- **The step of a return at the hook's own binder.** The leased item's record is the name
that the protected form's `bindWith` mints. The step reads the item's stamp and the lease's
stamp as two fields of it, each under the step's folds. The scope binds the name, and no later
binder shadows it. The return is the model's `giveBack` at the record's two stamps. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem return_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State)
    (it : Model.Item) {env outerItem : Env} {path : List Nat} {tys : List Ty} {w : Typed.World}
    {captured : List Val} {before after : Names}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (itemScope : env.names = before ++ outerItem.mint "answer" :: after)
    (itemUnshadowed : ∀ name ∈ after, name ≠ outerItem.mint "answer")
    (itemHeld : captured[before.length]? = some (itemVal res it))
    (itemTyped : tys[before.length]? = some (Pool.itemTy A))
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      returnStep (field (minted (outerItem.mint "answer")) "stamp")
        (field (minted (outerItem.mint "answer")) "lease") (minted (env.mint "current"))
        (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q
              (cellVal tb res (Model.giveBack s it.stamp it.lease).1) },
          returnReplyVal (Model.giveBack s it.stamp it.lease).2) ∧
      Fits w (returnReplyVal (Model.giveBack s it.stamp it.lease).2) returnReplyTy ∧
      Fits w (cellVal tb res (Model.giveBack s it.stamp it.lease).1) (Pool.cellTy A) :=
  return_attempt sig atoms canonical tb res s it.stamp it.lease depth tyDepth typedEnv
    (captured_field (captured_answer_in_row itemScope itemUnshadowed itemHeld)
      (item_stamp _ _ _ _))
    (captured_field (captured_answer_in_row itemScope itemUnshadowed itemHeld)
      (item_lease _ _ _ _))
    (capturedTy_field (capturedTy_answer_in_row itemScope itemUnshadowed itemTyped)
      (item_stampTy canonical))
    (capturedTy_field (capturedTy_answer_in_row itemScope itemUnshadowed itemTyped)
      (item_leaseTy canonical)) held member

/-- **The attempt of the closer at the wrapper's own binders.** The closer's identity and its
hint are names that `bindWith` mints. The scope binds each, and no later binder shadows
either. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem drain_attempt_minted (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) (tb : Table) (res : Nat → Val) (s : Model.State)
    (id : Nat) (hint : DeferredKey) (injective : tb.Injective) {env outerId outerHint : Env}
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
    (hintTyped : tys[beforeHint.length]? = some idTy)
    {stores : Stores} {q : RefKey} (held : refPeek stores.refs q = some (cellVal tb res s))
    (member : Fits w (cellVal tb res s) (Pool.cellTy A)) :
    ∃ f,
      drainStep (minted (outerId.mint "answer")) (minted (outerHint.mint "answer"))
        (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with
            refs := refPoke stores.refs q (cellVal (tb.renew id hint) res (Model.drain s id).1) },
          Val.bool (Model.drain s id).2) ∧
      Fits w (Val.bool (Model.drain s id).2) .bool ∧
      Fits w (cellVal (tb.renew id hint) res (Model.drain s id).1) (Pool.cellTy A) :=
  drain_attempt sig atoms canonical tb res s id hint injective depth tyDepth typedEnv
    (captured_answer_in_row idScope idUnshadowed idHeld)
    (captured_answer_in_row hintScope hintUnshadowed hintHeld).atScope
    (capturedTy_answer_in_row idScope idUnshadowed idTyped)
    (capturedTy_answer_in_row hintScope hintUnshadowed hintTyped).atScope held member

end Effect4.Pool
