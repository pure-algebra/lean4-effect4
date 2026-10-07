import Effect4.Modules.Semaphore.Steps
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# The typing of Semaphore's cell and of its five steps (decisions rows 257 and 265)

The module is `src/Effect4/Modules/Semaphore/`: the cell (`Cell.lean`) and the step terms
(`Steps.lean`). This file states that the checker types the initial value and each step at the
cell's type, at every scope of names.

Each statement is in the shape of the Queue's general forms
(`src/Effect4/Laws/Modules/Queue/Typing.lean`). For every caller's terms that have the
arguments' types, the step has the type of the pair of its reply and the cell. A caller's term
that stands in a fold's body keeps its type under the fold's two binders: that is a premise
(`CapturedTy`, `src/Effect4/Laws/Modules/Checking.lean`). The take step and the withdrawal take
the identity so. The visit takes the cursor and the cell's own source so, because its fold
reads the free count in its body.

| Statement | The step's type |
| --- | --- |
| `empty_types` | the cell's type |
| `takeStep_types`, `takeIfAvailableStep_types` | the pair of a Boolean and the cell |
| `releaseStep_types` | the pair of `[a number, a Boolean]` and the cell |
| `visitStep_types` | the pair of an option of a waiter and the cell |
| `withdrawStep_types` | the pair of nothing and the cell |

Placement. Concept `store-typing`, requirement R4: each is a part of the proposed claim
`semaphore-accounting-preserved`, on the side of the cell's type. Reach: the checker's `argTy`
on the step's tree under each literal flag, at every scope; the signature's atoms are the
native table's. Their consumer is the public law, in the slice of the operations that wait:
with a step's typing, `step_keeps_cell` (`src/Effect4/Laws/Modules/Store.lean`) gives that one
`Ref.modify` of the step keeps the cell a member of the cell's type.

The statements establish no agreement with the model, no typing of a wrapper and nothing about
a target. The checker's typing of a step is not program admission. The cell's type is closed,
so each side condition of a record rule is decided by `rfl` or by `decide`. The proofs read
the checker's rule at each node, through the shared builder rules. The finite controls are in
`Test/Program/SemaphoreSteps.lean`.
-/

set_option autoImplicit false

namespace Effect4.Semaphore.Model

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The types of the steps' replies -/

/-- A release's reply: the free count, and whether a waiter is enrolled. A pair, as the checker
normalizes a tuple of two. -/
def releaseReplyTy : Ty := .prod .nat .bool

/-- A visit's reply: the selected waiter's record, if any. -/
def visitReplyTy : Ty := .option Semaphore.waiterTy

/-! ## The two records: normal forms, reads, overwrites and a construction

Each is one application of a record rule at a closed record type
(`src/Effect4/Laws/Program/Typing/TermIntro.lean`). -/

theorem waiterTy_normal : Semaphore.waiterTy.normalize = Semaphore.waiterTy := rfl

theorem cellTy_normal : Semaphore.cellTy.normalize = Semaphore.cellTy := rfl

theorem waiterFields_formed :
    Formation.check (Formation.sites false [] (.record Semaphore.waiterFields)) = none := by
  decide

theorem cellFields_formed :
    Formation.check (Formation.sites false [] (.record Semaphore.cellFields)) = none := by
  decide

theorem cell_permitsTy : Record.fieldType false Semaphore.cellTy "permits" = some .nat :=
  Record.fieldType_normal cellTy_normal rfl

theorem cell_takenTy : Record.fieldType false Semaphore.cellTy "taken" = some .nat :=
  Record.fieldType_normal cellTy_normal rfl

theorem cell_waitersTy :
    Record.fieldType false Semaphore.cellTy "waiters" = some (.list Semaphore.waiterTy) :=
  Record.fieldType_normal cellTy_normal rfl

theorem cell_nextTy : Record.fieldType false Semaphore.cellTy "next" = some .nat :=
  Record.fieldType_normal cellTy_normal rfl

theorem waiter_idTy : Record.fieldType false Semaphore.waiterTy "id" = some idTy :=
  Record.fieldType_normal waiterTy_normal rfl

theorem waiter_needTy : Record.fieldType false Semaphore.waiterTy "need" = some .nat :=
  Record.fieldType_normal waiterTy_normal rfl

theorem waiter_stampTy : Record.fieldType false Semaphore.waiterTy "stamp" = some .nat :=
  Record.fieldType_normal waiterTy_normal rfl

/-- The overwrite of `taken` keeps the cell's type. -/
theorem cell_setTakenTy :
    Record.setType Semaphore.cellTy "taken" .nat = some Semaphore.cellTy :=
  Record.setType_same cellTy_normal rfl rfl

/-- The waiters' overwrite keeps the cell's type. -/
theorem cell_setWaitersTy :
    Record.setType Semaphore.cellTy "waiters" (.list Semaphore.waiterTy) =
      some Semaphore.cellTy :=
  Record.setType_same cellTy_normal rfl rfl

/-- The overwrite of `next` keeps the cell's type. -/
theorem cell_setNextTy : Record.setType Semaphore.cellTy "next" .nat = some Semaphore.cellTy :=
  Record.setType_same cellTy_normal rfl rfl

/-- A waiter's construction, each field at its declared type, answers a waiter's type. -/
theorem waiter_checkTy :
    Record.check Semaphore.waiterFields ["id", "need", "hint", "stamp"]
        [idTy, .nat, idTy, .nat] =
      some Semaphore.waiterTy :=
  Record.check_declared (fields := Semaphore.waiterFields) (by decide)

/-- The initial value's construction answers the cell's type: the empty list of waiters is
below the declared list. -/
theorem empty_checkTy :
    Record.check Semaphore.cellFields ["permits", "taken", "waiters", "next"]
        [.nat, .nat, .list .never, .nat] =
      some Semaphore.cellTy := by
  have fits : Record.argumentsFit Semaphore.cellFields
      [("permits", Ty.nat), ("taken", Ty.nat), ("waiters", Ty.list .never), ("next", Ty.nat)] =
        true := by
    unfold Record.argumentsFit
    rw [Bool.and_eq_true]
    refine ⟨rfl, List.all_eq_true.mpr fun field member => ?_⟩
    simp only [Semaphore.cellFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact Ty.sub_refl _
    · exact Ty.sub_refl _
    · exact sub_nil_list _
    · exact Ty.sub_refl _
  unfold Record.check
  show (if _ then some (Ty.normalize (.record Semaphore.cellFields)) else none) = _
  have named : (["permits", "taken", "waiters", "next"] : List String).Nodup := by decide
  rw [if_pos ⟨named, named, fits⟩]
  rfl

section Builders

variable {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}

/-! ## The cell's fields and overwrites, at a source of the cell's type -/

theorem types_cellPermits {s : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (field s "permits") env path types .nat :=
  fun _ => types_field (hs false) cell_permitsTy

theorem types_cellTaken {s : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (field s "taken") env path types .nat :=
  fun _ => types_field (hs false) cell_takenTy

theorem types_cellWaiters {s : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (field s "waiters") env path types (.list Semaphore.waiterTy) :=
  fun _ => types_field (hs false) cell_waitersTy

theorem types_cellNext {s : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (field s "next") env path types .nat :=
  fun _ => types_field (hs false) cell_nextTy

theorem types_setTaken {s v : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy)
    (hv : TypesEach sig v env path types .nat) :
    TypesEach sig (recordSet s "taken" v) env path types Semaphore.cellTy :=
  fun _ => types_recordSet (hs false) (hv true) cell_setTakenTy

theorem types_setWaiters {s v : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy)
    (hv : TypesEach sig v env path types (.list Semaphore.waiterTy)) :
    TypesEach sig (recordSet s "waiters" v) env path types Semaphore.cellTy :=
  fun _ => types_recordSet (hs false) (hv true) cell_setWaitersTy

theorem types_setNext {s v : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy)
    (hv : TypesEach sig v env path types .nat) :
    TypesEach sig (recordSet s "next" v) env path types Semaphore.cellTy :=
  fun _ => types_recordSet (hs false) (hv true) cell_setNextTy

/-- A waiter's record, built from an identity, a count, a hint and a stamp. -/
theorem types_mkWaiter {id need hint stamp : TermSrc}
    (hid : TypesEach sig id env path types idTy)
    (hneed : TypesEach sig need env path types .nat)
    (hhint : TypesEach sig hint env path types idTy)
    (hstamp : TypesEach sig stamp env path types .nat) :
    TypesEach sig (Semaphore.mkWaiter id need hint stamp) env path types Semaphore.waiterTy :=
  fun _ => types_record waiterFields_formed
    (.cons (hid true) (.cons (hneed true) (.cons (hhint true) (.cons (hstamp true) .nil))))
    waiter_checkTy

variable (atoms : sig.atomOf = nativeAtomTy)
include atoms

/-! ## The passes, typed once -/

/-- `freeT`: the free count. -/
theorem types_freeT {s : TermSrc} (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.freeT s) env path types .nat :=
  types_sub atoms (types_cellPermits hs) (types_cellTaken hs)

/-- `fitsT`: whether a count fits the free count. -/
theorem types_fitsT {need s : TermSrc} (hneed : TypesEach sig need env path types .nat)
    (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.fitsT need s) env path types .bool :=
  types_notT atoms (types_lt atoms (types_freeT atoms hs) hneed)

/-- `removeWaiter`: the waiters without the request. The shared fold, at a waiter's type. -/
theorem types_removeWaiter {waiters id : TermSrc} (depth : types.length = env.names.length)
    (hwaiters : TypesEach sig waiters env path types (.list Semaphore.waiterTy))
    (hid : CapturedTy sig id env path types idTy) :
    TypesEach sig (Semaphore.removeWaiter waiters id) env path types
      (.list Semaphore.waiterTy) :=
  types_removeById atoms depth waiterTy_normal waiter_idTy hwaiters hid

/-- `eligibleT`: whether a visit may select a waiter. -/
theorem types_eligibleT {cursor s w : TermSrc}
    (hcursor : TypesEach sig cursor env path types .nat)
    (hs : TypesEach sig s env path types Semaphore.cellTy)
    (hw : TypesEach sig w env path types Semaphore.waiterTy) :
    TypesEach sig (Semaphore.eligibleT cursor s w) env path types .bool :=
  types_andT atoms
    (types_notT atoms
      (types_lt atoms (fun _ => types_field (hw false) waiter_stampTy) hcursor))
    (types_notT atoms
      (types_lt atoms (types_freeT atoms hs) (fun _ => types_field (hw false) waiter_needTy)))

/-- `fromFirst`: the waiters from the first one that a visit may select. The cursor and the
cell both stand in the fold's body, so each is taken with its typed capture. -/
theorem types_fromFirst {cursor s : TermSrc} (depth : types.length = env.names.length)
    (hcursor : CapturedTy sig cursor env path types .nat)
    (hs : CapturedTy sig s env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.fromFirst cursor s) env path types (.list Semaphore.waiterTy) :=
  fun _ => types_foldWith_same (types_cellWaiters hs.atScope false)
    (types_noneOf atoms (types_cellWaiters hs.atScope) false)
    ((types_ifT atoms
      (types_orT atoms
        (types_notT atoms (types_isEmpty atoms
          (types_minted_acc depth path (.list Semaphore.waiterTy) Semaphore.waiterTy)))
        (types_eligibleT atoms
          (hcursor.underFold (.list Semaphore.waiterTy) Semaphore.waiterTy)
          (hs.underFold (.list Semaphore.waiterTy) Semaphore.waiterTy)
          (types_minted_item depth path (.list Semaphore.waiterTy) Semaphore.waiterTy)))
      (types_snoc atoms waiterTy_normal
        (types_minted_acc depth path (.list Semaphore.waiterTy) Semaphore.waiterTy)
        (types_minted_item depth path (.list Semaphore.waiterTy) Semaphore.waiterTy))
      (types_minted_acc depth path (.list Semaphore.waiterTy) Semaphore.waiterTy)
      (by rw [Ty.normalize, waiterTy_normal])) false)
    (Ty.subN_refl (.list Semaphore.waiterTy))

/-- `visitFrom`: a visit's reply and stored value, from the waiters that start at the selected
one. -/
theorem types_visitFrom {rest s : TermSrc}
    (hrest : TypesEach sig rest env path types (.list Semaphore.waiterTy))
    (hs : TypesEach sig s env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.visitFrom rest s) env path types
      (.prod visitReplyTy Semaphore.cellTy) :=
  have waiters := types_cellWaiters hs
  types_ifT atoms (types_isZero atoms (types_freeT atoms hs))
    (types_pair atoms (types_head atoms (types_noneOf atoms waiters)) hs)
    (types_pair atoms (types_head atoms hrest)
      (types_setWaiters hs
        (types_append atoms
          (types_take atoms waiters
            (types_sub atoms (types_len atoms waiters) (types_len atoms hrest)))
          (types_drop atoms hrest (types_nat 1)) waiterTy_normal)))
    (Ty.normalize_prod_canonical (Ty.normalize_option_canonical waiterTy_normal) cellTy_normal rfl rfl)

end Builders

/-! ## The initial value and the five steps, typed at every scope -/

/-- **The initial value has the cell's type**, at every total and in every scope. -/
@[semantics "store-typing" (requirement := R4)]
theorem empty_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    (permits : Nat) {env : Env} {path : List Nat} {types : List Ty} :
    TypesEach sig (Semaphore.empty permits) env path types Semaphore.cellTy :=
  fun _ => types_record cellFields_formed
    (.cons (types_nat permits true)
      (.cons (types_nat 0 true) (.cons (types_nilT atoms true) (.cons (types_nat 0 true) .nil))))
    empty_checkTy

/-- **The take step is typed at every scope.** The request's identity stands in the removal's
fold, so it is taken with its typed capture. The count and the hint stand outside every
fold. -/
@[semantics "store-typing" (requirement := R4)]
theorem takeStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {needSrc idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (depth : types.length = env.names.length)
    (typesNeed : TypesEach sig needSrc env path types .nat)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesHint : TypesEach sig hintSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.takeStep needSrc idSrc hintSrc cellSrc) env path types
      (.prod .bool Semaphore.cellTy) := by
  have rest := types_removeWaiter atoms depth (types_cellWaiters typesCell) typesId
  have took := types_pair atoms (types_bool true)
    (types_setWaiters
      (types_setTaken typesCell (types_add atoms (types_cellTaken typesCell) typesNeed)) rest)
  have enrolled := types_pair atoms (types_bool false)
    (types_setNext
      (types_setWaiters typesCell
        (types_snoc atoms waiterTy_normal rest
          (types_mkWaiter typesId.atScope typesNeed typesHint (types_cellNext typesCell))))
      (types_add atoms (types_cellNext typesCell) (types_nat 1)))
  exact types_ifT atoms (types_fitsT atoms typesNeed typesCell) took enrolled
    (Ty.normalize_prod_canonical rfl cellTy_normal rfl rfl)

/-- **The take-if-available step is typed at every scope.** No fold: each argument is typed at
the scope alone. -/
@[semantics "store-typing" (requirement := R4)]
theorem takeIfAvailableStep_types {Op : Type} (sig : Signature Op)
    (atoms : sig.atomOf = nativeAtomTy) {needSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty}
    (typesNeed : TypesEach sig needSrc env path types .nat)
    (typesCell : TypesEach sig cellSrc env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.takeIfAvailableStep needSrc cellSrc) env path types
      (.prod .bool Semaphore.cellTy) :=
  types_ifT atoms (types_fitsT atoms typesNeed typesCell)
    (types_pair atoms (types_bool true)
      (types_setTaken typesCell (types_add atoms (types_cellTaken typesCell) typesNeed)))
    (types_pair atoms (types_bool false) typesCell)
    (Ty.normalize_prod_canonical rfl cellTy_normal rfl rfl)

/-- **The release step is typed at every scope.** No fold. -/
@[semantics "store-typing" (requirement := R4)]
theorem releaseStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {countSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (typesCount : TypesEach sig countSrc env path types .nat)
    (typesCell : TypesEach sig cellSrc env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.releaseStep countSrc cellSrc) env path types
      (.prod releaseReplyTy Semaphore.cellTy) := by
  have left := types_sub atoms (types_cellTaken typesCell) typesCount
  have reply := types_tuple2 atoms (types_sub atoms (types_cellPermits typesCell) left)
    (types_notT atoms (types_isEmpty atoms (types_cellWaiters typesCell))) rfl rfl rfl rfl
  exact types_pair atoms reply (types_setTaken typesCell left)

/-- **The visit step is typed at every scope.** The cursor and the cell's own source stand in
the fold's body, so each is taken with its typed capture. -/
@[semantics "store-typing" (requirement := R4)]
theorem visitStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {cursorSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (depth : types.length = env.names.length)
    (typesCursor : CapturedTy sig cursorSrc env path types .nat)
    (typesCell : CapturedTy sig cellSrc env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.visitStep cursorSrc cellSrc) env path types
      (.prod visitReplyTy Semaphore.cellTy) :=
  types_visitFrom atoms (types_fromFirst atoms depth typesCursor typesCell) typesCell.atScope

/-- **The withdrawal is typed at every scope.** The request's identity stands in the removal's
fold. -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat} {types : List Ty}
    (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types Semaphore.cellTy) :
    TypesEach sig (Semaphore.withdrawStep idSrc cellSrc) env path types
      (.prod .unit Semaphore.cellTy) :=
  types_pair atoms types_unit
    (types_setWaiters typesCell
      (types_removeWaiter atoms depth (types_cellWaiters typesCell) typesId))

end Effect4.Semaphore.Model
