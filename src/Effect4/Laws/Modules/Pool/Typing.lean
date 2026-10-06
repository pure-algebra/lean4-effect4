import Effect4.Modules.Pool.Steps
import Effect4.Laws.Modules.Checking
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# The typing of Pool's cell and of its six steps (decisions rows 257, 267 and 276)

The module is `src/Effect4/Modules/Pool/`: the cell (`Cell.lean`) and the step terms
(`Steps.lean`). This file states that the checker types the initial value and each step at the
cell's type, at every scope of names, for every resource type that is its own normal form.

Each statement is in the shape of the Queue's and of Semaphore's general forms
(`src/Effect4/Laws/Modules/Queue/Typing.lean`,
`src/Effect4/Laws/Modules/Semaphore/Typing.lean`). For every caller's terms that have the
arguments' types, the step has the type of the pair of its reply and the cell. A caller's term
that stands in a fold's body keeps its type under the fold's two binders: that is a premise
(`CapturedTy`, `src/Effect4/Laws/Modules/Checking.lean`).

| Statement | The step's type | A caller's term under a fold |
| --- | --- | --- |
| `initial_types` | the cell's type | none |
| `leaseStep_types` | the pair of `[a Boolean, an option of an item]` and the cell | the identity, and the cell's own source |
| `returnStep_types` | the pair of `[a Boolean, a Boolean]` and the cell | the item's stamp and the lease's stamp |
| `selectStep_types` | the pair of a list of waiters and the cell | none: the step folds nothing |
| `withdrawStep_types` | the pair of nothing and the cell | the identity |
| `closeStep_types` | the pair of `[a Boolean, a number]` and the cell | none |
| `drainStep_types` | the pair of a Boolean and the cell | the identity |

Placement. Concept `store-typing`, requirement R4: each is a part of the proposed claim
`pool-profile-preserved`, on the side of the cell's type. Reach: the checker's `argTy` on the
step's tree under each literal flag, at every scope; the signature's atoms are the native
table's; the resource's type is its own normal form. Their consumer is the public law, in the
slice of the public operations: with a step's typing, `step_keeps_cell`
(`src/Effect4/Laws/Modules/Store.lean`) gives that one `Ref.modify` of the step keeps the cell a
member of the cell's type.

The statements establish no agreement with the model, no typing of a wrapper and nothing about
a target. The checker's typing of a step is not program admission. The proofs read the
checker's rule at each node, through the shared builder rules. The lease's two folds over the
items read the front idle stamp in their bodies, by a fold of its own: its rule is applied
under the outer fold's binders (`types_headStamp`, `depth_under`). The finite controls are in
`Test/Program/PoolSteps.lean`.
-/

set_option autoImplicit false

namespace Effect4.Pool.Model

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **A resource type that the checker types in a cell.** It is its own normal form, so the
cell's type at it is the type that the checker answers. The two record declarations that hold
it are formed: an item's and the cell's (`Formation.check`,
`src/Effect4/Program/Formation.lean`). The five steps construct no item and no cell, so their
typing takes the normal form alone. -/
structure ResourceTy (A : Ty) : Prop where
  canonical : A.normalize = A
  item : Formation.check (Formation.sites false [] (.record (Pool.itemFields A))) = none
  cell : Formation.check (Formation.sites false [] (.record (Pool.cellFields A))) = none

instance (A : Ty) : Decidable (ResourceTy A) :=
  decidable_of_iff
    (A.normalize = A ∧
      Formation.check (Formation.sites false [] (.record (Pool.itemFields A))) = none ∧
      Formation.check (Formation.sites false [] (.record (Pool.cellFields A))) = none)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.canonical, h.item, h.cell⟩⟩

/-! ## The types of the steps' replies -/

/-- A lease's reply: whether the pool refused, and the leased item's record, if any. A pair, as
the checker normalizes a tuple of two. -/
def leaseReplyTy (A : Ty) : Ty := .prod .bool (.option (Pool.itemTy A))

/-- A return's reply: whether the lease returned, and whether a wake is owed. -/
def returnReplyTy : Ty := .prod .bool .bool

/-- A selection's reply: the selected waiters' records. -/
def selectReplyTy : Ty := .list Pool.waiterTy

/-- The reply of the close's first step: whether it began the close, and the count of the
waiters. -/
def closeReplyTy : Ty := .prod .bool .nat

/-! ## The three records: normal forms, reads, overwrites and constructions

Each is one application of a record rule at a record type in normal form
(`src/Effect4/Laws/Program/Typing/TermIntro.lean`). A waiter's type is closed. An item's and the
cell's hold the resource's type, so their normal forms take its normal form. -/

theorem waiterTy_normal : Pool.waiterTy.normalize = Pool.waiterTy := rfl

theorem waiterFields_formed :
    Formation.check (Formation.sites false [] (.record Pool.waiterFields)) = none := by
  decide

theorem waiter_idTy : Record.fieldType false Pool.waiterTy "id" = some idTy :=
  Record.fieldType_normal waiterTy_normal rfl

/-- A waiter's construction, each field at its declared type, answers a waiter's type. -/
theorem waiter_checkTy :
    Record.check Pool.waiterFields ["id", "hint"] [idTy, idTy] = some Pool.waiterTy :=
  Record.check_declared (fields := Pool.waiterFields) (by decide)

section Records

variable {A : Ty} (canonical : A.normalize = A)
include canonical

theorem itemTy_normal : (Pool.itemTy A).normalize = Pool.itemTy A := by
  show Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  show Ty.record [("borrowed", false, Ty.normalize .bool), ("lease", false, Ty.normalize .nat),
    ("resource", false, Ty.normalize A), ("stamp", false, Ty.normalize .nat)] = _
  rw [canonical]
  rfl

/-- An item's written declaration normalizes to an item's type. -/
theorem itemFields_normal : Ty.normalize (.record (Pool.itemFields A)) = Pool.itemTy A := by
  rw [Ty.normalize_record]
  show Ty.record [("borrowed", false, Ty.normalize .bool), ("lease", false, Ty.normalize .nat),
    ("resource", false, Ty.normalize A), ("stamp", false, Ty.normalize .nat)] = _
  rw [canonical]
  rfl

theorem cellTy_normal : (Pool.cellTy A).normalize = Pool.cellTy A := by
  show Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  show Ty.record [("available", false, Ty.normalize (.list .nat)),
    ("closing", false, Ty.normalize .bool),
    ("items", false, Ty.normalize (.list (Pool.itemTy A))), ("next", false, Ty.normalize .nat),
    ("waiters", false, Ty.normalize (.list Pool.waiterTy))] = _
  rw [Ty.normalize_list_canonical (itemTy_normal canonical)]
  rfl

/-- The cell's written declaration normalizes to the cell's type. -/
theorem cellFields_normal : Ty.normalize (.record (Pool.cellFields A)) = Pool.cellTy A := by
  rw [Ty.normalize_record]
  show Ty.record [("available", false, Ty.normalize (.list .nat)),
    ("closing", false, Ty.normalize .bool),
    ("items", false, Ty.normalize (.list (Pool.itemTy A))), ("next", false, Ty.normalize .nat),
    ("waiters", false, Ty.normalize (.list Pool.waiterTy))] = _
  rw [Ty.normalize_list_canonical (itemTy_normal canonical)]
  rfl

theorem cell_itemsTy :
    Record.fieldType false (Pool.cellTy A) "items" = some (.list (Pool.itemTy A)) :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem cell_availableTy :
    Record.fieldType false (Pool.cellTy A) "available" = some (.list .nat) :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem cell_waitersTy :
    Record.fieldType false (Pool.cellTy A) "waiters" = some (.list Pool.waiterTy) :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem cell_closingTy : Record.fieldType false (Pool.cellTy A) "closing" = some .bool :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem cell_nextTy : Record.fieldType false (Pool.cellTy A) "next" = some .nat :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem item_stampTy : Record.fieldType false (Pool.itemTy A) "stamp" = some .nat :=
  Record.fieldType_normal (itemTy_normal canonical) rfl

theorem item_borrowedTy : Record.fieldType false (Pool.itemTy A) "borrowed" = some .bool :=
  Record.fieldType_normal (itemTy_normal canonical) rfl

theorem item_leaseTy : Record.fieldType false (Pool.itemTy A) "lease" = some .nat :=
  Record.fieldType_normal (itemTy_normal canonical) rfl

/-- The items' overwrite keeps the cell's type. -/
theorem cell_setItemsTy :
    Record.setType (Pool.cellTy A) "items" (.list (Pool.itemTy A)) = some (Pool.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl
    (Ty.normalize_list_canonical (itemTy_normal canonical))

/-- The idle stamps' overwrite keeps the cell's type. -/
theorem cell_setAvailableTy :
    Record.setType (Pool.cellTy A) "available" (.list .nat) = some (Pool.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl rfl

/-- The waiters' overwrite keeps the cell's type. -/
theorem cell_setWaitersTy :
    Record.setType (Pool.cellTy A) "waiters" (.list Pool.waiterTy) = some (Pool.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl rfl

/-- The overwrite of `closing` keeps the cell's type. -/
theorem cell_setClosingTy :
    Record.setType (Pool.cellTy A) "closing" .bool = some (Pool.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl rfl

/-- The overwrite of `next` keeps the cell's type. -/
theorem cell_setNextTy : Record.setType (Pool.cellTy A) "next" .nat = some (Pool.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl rfl

/-- The overwrite of `borrowed` keeps an item's type. -/
theorem item_setBorrowedTy :
    Record.setType (Pool.itemTy A) "borrowed" .bool = some (Pool.itemTy A) :=
  Record.setType_same (itemTy_normal canonical) rfl rfl

/-- The overwrite of `lease` keeps an item's type. -/
theorem item_setLeaseTy : Record.setType (Pool.itemTy A) "lease" .nat = some (Pool.itemTy A) :=
  Record.setType_same (itemTy_normal canonical) rfl rfl

/-- An item's construction, each field at its declared type, answers an item's type. -/
theorem item_checkTy :
    Record.check (Pool.itemFields A) ["stamp", "resource", "borrowed", "lease"]
        [.nat, A, .bool, .nat] =
      some (Pool.itemTy A) := by
  rw [← itemFields_normal canonical]
  have named : (["stamp", "resource", "borrowed", "lease"] : List String).Nodup := by decide
  exact Record.check_declared (fields := Pool.itemFields A) named

/-- The initial value's construction answers the cell's type: the empty list of waiters is
below the declared list. -/
theorem initial_checkTy :
    Record.check (Pool.cellFields A) ["items", "available", "waiters", "closing", "next"]
        [.list (Pool.itemTy A), .list .nat, .list .never, .bool, .nat] =
      some (Pool.cellTy A) := by
  have fits : Record.argumentsFit (Pool.cellFields A)
      [("items", Ty.list (Pool.itemTy A)), ("available", Ty.list .nat),
        ("waiters", Ty.list .never), ("closing", Ty.bool), ("next", Ty.nat)] = true := by
    unfold Record.argumentsFit
    rw [Bool.and_eq_true]
    refine ⟨rfl, List.all_eq_true.mpr fun field member => ?_⟩
    simp only [Pool.cellFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact Ty.sub_refl _
    · exact Ty.sub_refl _
    · exact sub_nil_list _
    · exact Ty.sub_refl _
    · exact Ty.sub_refl _
  unfold Record.check
  show (if _ then some (Ty.normalize (.record (Pool.cellFields A))) else none) = _
  have named : (["items", "available", "waiters", "closing", "next"] : List String).Nodup := by
    decide
  rw [if_pos ⟨named, named, fits⟩, cellFields_normal canonical]

end Records

section Builders

variable {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}
variable {A : Ty} (canonical : A.normalize = A)
include canonical

/-! ## The cell's fields and overwrites, at a source of the cell's type -/

theorem types_cellItems {s : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (field s "items") env path types (.list (Pool.itemTy A)) :=
  fun _ => types_field (hs false) (cell_itemsTy canonical)

theorem types_cellAvailable {s : TermSrc}
    (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (field s "available") env path types (.list .nat) :=
  fun _ => types_field (hs false) (cell_availableTy canonical)

theorem types_cellWaiters {s : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (field s "waiters") env path types (.list Pool.waiterTy) :=
  fun _ => types_field (hs false) (cell_waitersTy canonical)

theorem types_cellClosing {s : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (field s "closing") env path types .bool :=
  fun _ => types_field (hs false) (cell_closingTy canonical)

theorem types_cellNext {s : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (field s "next") env path types .nat :=
  fun _ => types_field (hs false) (cell_nextTy canonical)

theorem types_setItems {s v : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A))
    (hv : TypesEach sig v env path types (.list (Pool.itemTy A))) :
    TypesEach sig (recordSet s "items" v) env path types (Pool.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setItemsTy canonical)

theorem types_setAvailable {s v : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A))
    (hv : TypesEach sig v env path types (.list .nat)) :
    TypesEach sig (recordSet s "available" v) env path types (Pool.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setAvailableTy canonical)

theorem types_setWaiters {s v : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A))
    (hv : TypesEach sig v env path types (.list Pool.waiterTy)) :
    TypesEach sig (recordSet s "waiters" v) env path types (Pool.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setWaitersTy canonical)

theorem types_setClosing {s v : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A))
    (hv : TypesEach sig v env path types .bool) :
    TypesEach sig (recordSet s "closing" v) env path types (Pool.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setClosingTy canonical)

theorem types_setNext {s v : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A))
    (hv : TypesEach sig v env path types .nat) :
    TypesEach sig (recordSet s "next" v) env path types (Pool.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setNextTy canonical)

/-- `leasedAs`: an item as a lease of a stamp holds it. -/
theorem types_leasedAs {lease it : TermSrc} (hlease : TypesEach sig lease env path types .nat)
    (hit : TypesEach sig it env path types (Pool.itemTy A)) :
    TypesEach sig (Pool.leasedAs lease it) env path types (Pool.itemTy A) :=
  fun _ => types_recordSet
    (types_recordSet (hit false) (types_bool true true) (item_setBorrowedTy canonical))
    (hlease true) (item_setLeaseTy canonical)

/-- The folded item as the next lease holds it, under a fold's binders. -/
theorem types_leasedItem {s : TermSrc} {accT : Ty} (depth : types.length = env.names.length)
    (hs : CapturedTy sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.leasedAs (field s "next") (minted (env.mint "item")))
      (env.push [env.mint "acc", env.mint "item"]) path (types ++ [accT, Pool.itemTy A])
      (Pool.itemTy A) :=
  types_leasedAs canonical (types_cellNext canonical (hs.underFold accT (Pool.itemTy A)))
    (types_minted_item depth path accT (Pool.itemTy A))

variable (atoms : sig.atomOf = nativeAtomTy)
include atoms

/-! ## The passes, typed once -/

/-- `withdrawn`: the cell without the request. The shared removal pass, at a waiter's type. -/
theorem types_withdrawn {id s : TermSrc} (depth : types.length = env.names.length)
    (hid : CapturedTy sig id env path types idTy)
    (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.withdrawn id s) env path types (Pool.cellTy A) :=
  types_setWaiters canonical hs
    (types_removeById atoms depth waiterTy_normal waiter_idTy (types_cellWaiters canonical hs)
      hid)

/-- `noItem`: no item, at the type of an option of an item. -/
theorem types_noItem {s : TermSrc} (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.noItem s) env path types (.option (Pool.itemTy A)) :=
  types_head atoms (types_noneOf atoms (types_cellItems canonical hs))

/-- `headStamp`: the stamp at the front of the idle stamps. A fold whose body reads no caller's
term, so the rule holds at every scope, and under another fold's binders too. -/
theorem types_headStamp {s : TermSrc} (depth : types.length = env.names.length)
    (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.headStamp s) env path types .nat :=
  fun _ => types_foldWith_same
    (types_take atoms (types_cellAvailable canonical hs) (types_nat 1) false)
    (types_nat 0 false) (types_minted_item depth path .nat .nat false) (Ty.subN_refl .nat)

/-- The test of the lease's two folds, under their binders: the folded item's stamp against
the front idle stamp of the caller's cell. -/
theorem types_atFront {s : TermSrc} {accT : Ty} (depth : types.length = env.names.length)
    (hs : CapturedTy sig s env path types (Pool.cellTy A)) :
    TypesEach sig (app "eq" [field (minted (env.mint "item")) "stamp", Pool.headStamp s])
      (env.push [env.mint "acc", env.mint "item"]) path (types ++ [accT, Pool.itemTy A]) .bool :=
  types_eq atoms
    (fun _ => types_field (types_minted_item depth path accT (Pool.itemTy A) false)
      (item_stampTy canonical))
    (types_headStamp canonical atoms
      (depth_under depth (env.mint "acc") (env.mint "item") accT (Pool.itemTy A))
      (hs.underFold accT (Pool.itemTy A)))

/-- `marked`: the items, with the front idle item leased. The cell stands in the fold's body,
so it is taken with its typed capture. -/
theorem types_marked {s : TermSrc} (depth : types.length = env.names.length)
    (hs : CapturedTy sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.marked s) env path types (.list (Pool.itemTy A)) :=
  fun _ => types_foldWith_same (types_cellItems canonical hs.atScope false)
    (types_noneOf atoms (types_cellItems canonical hs.atScope) false)
    (types_snoc atoms (itemTy_normal canonical)
      (types_minted_acc depth path (.list (Pool.itemTy A)) (Pool.itemTy A))
      (types_ifT atoms (types_atFront canonical atoms depth hs)
        (types_leasedItem canonical depth hs)
        (types_minted_item depth path (.list (Pool.itemTy A)) (Pool.itemTy A))) false)
    (Ty.subN_refl (.list (Pool.itemTy A)))

/-- `leasedOf`: the front idle item as its new lease holds it. -/
theorem types_leasedOf {s : TermSrc} (depth : types.length = env.names.length)
    (hs : CapturedTy sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.leasedOf s) env path types (.list (Pool.itemTy A)) :=
  fun _ => types_foldWith_same (types_cellItems canonical hs.atScope false)
    (types_noneOf atoms (types_cellItems canonical hs.atScope) false)
    (types_ifT atoms (types_atFront canonical atoms depth hs)
      (types_snoc atoms (itemTy_normal canonical)
        (types_minted_acc depth path (.list (Pool.itemTy A)) (Pool.itemTy A))
        (types_leasedItem canonical depth hs))
      (types_minted_acc depth path (.list (Pool.itemTy A)) (Pool.itemTy A)) false)
    (Ty.subN_refl (.list (Pool.itemTy A)))

/-- `holdsT`: whether a lease holds an item, at one item's record. -/
theorem types_holdsT {i l it : TermSrc} (hi : TypesEach sig i env path types .nat)
    (hl : TypesEach sig l env path types .nat)
    (hit : TypesEach sig it env path types (Pool.itemTy A)) :
    TypesEach sig (Pool.holdsT i l it) env path types .bool :=
  types_andT atoms
    (types_eq atoms (fun _ => types_field (hit false) (item_stampTy canonical)) hi)
    (types_andT atoms (fun _ => types_field (hit false) (item_borrowedTy canonical))
      (types_eq atoms (fun _ => types_field (hit false) (item_leaseTy canonical)) hl))

/-- `heldBy`: whether a lease holds an item. The two stamps stand in the fold's body. -/
theorem types_heldBy {i l s : TermSrc} (depth : types.length = env.names.length)
    (hi : CapturedTy sig i env path types .nat) (hl : CapturedTy sig l env path types .nat)
    (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.heldBy i l s) env path types .bool :=
  fun _ => types_foldWith_same (types_cellItems canonical hs false) (types_bool false false)
    (types_orT atoms (types_minted_acc depth path .bool (Pool.itemTy A))
      (types_holdsT canonical atoms (hi.underFold .bool (Pool.itemTy A))
        (hl.underFold .bool (Pool.itemTy A))
        (types_minted_item depth path .bool (Pool.itemTy A))) false)
    (Ty.subN_refl .bool)

/-- `freed`: the items, with the returned item idle again. -/
theorem types_freed {i l s : TermSrc} (depth : types.length = env.names.length)
    (hi : CapturedTy sig i env path types .nat) (hl : CapturedTy sig l env path types .nat)
    (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.freed i l s) env path types (.list (Pool.itemTy A)) :=
  fun _ => types_foldWith_same (types_cellItems canonical hs false)
    (types_noneOf atoms (types_cellItems canonical hs) false)
    (types_snoc atoms (itemTy_normal canonical)
      (types_minted_acc depth path (.list (Pool.itemTy A)) (Pool.itemTy A))
      (types_ifT atoms
        (types_holdsT canonical atoms (hi.underFold (.list (Pool.itemTy A)) (Pool.itemTy A))
          (hl.underFold (.list (Pool.itemTy A)) (Pool.itemTy A))
          (types_minted_item depth path (.list (Pool.itemTy A)) (Pool.itemTy A)))
        (fun _ => types_recordSet
          (types_minted_item depth path (.list (Pool.itemTy A)) (Pool.itemTy A) false)
          (types_bool false true) (item_setBorrowedTy canonical))
        (types_minted_item depth path (.list (Pool.itemTy A)) (Pool.itemTy A))) false)
    (Ty.subN_refl (.list (Pool.itemTy A)))

/-- `outstanding`: whether a lease is outstanding. A fold whose body reads no caller's term. -/
theorem types_outstanding {s : TermSrc} (depth : types.length = env.names.length)
    (hs : TypesEach sig s env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.outstanding s) env path types .bool :=
  fun _ => types_foldWith_same (types_cellItems canonical hs false) (types_bool false false)
    (types_orT atoms (types_minted_acc depth path .bool (Pool.itemTy A))
      (fun _ => types_field (types_minted_item depth path .bool (Pool.itemTy A) false)
        (item_borrowedTy canonical)) false)
    (Ty.subN_refl .bool)

/-- A lease's reply: a Boolean and an option of an item. -/
theorem types_leaseReply {closed item : TermSrc}
    (hclosed : TypesEach sig closed env path types .bool)
    (hitem : TypesEach sig item env path types (.option (Pool.itemTy A))) :
    TypesEach sig (tuple [closed, item]) env path types (leaseReplyTy A) :=
  types_tuple2 atoms hclosed hitem rfl
    (Ty.normalize_option_canonical (itemTy_normal canonical)) rfl rfl

end Builders

/-- A waiter's record, built from an identity and a hint. -/
theorem types_mkWaiter {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat}
    {types : List Ty} {id hint : TermSrc} (hid : TypesEach sig id env path types idTy)
    (hhint : TypesEach sig hint env path types idTy) :
    TypesEach sig (Pool.mkWaiter id hint) env path types Pool.waiterTy :=
  fun _ => types_record waiterFields_formed (.cons (hid true) (.cons (hhint true) .nil))
    waiter_checkTy

/-! ## The initial value's items and stamps

The initial value writes its two lists out from the resources, with no fold
(`Pool.itemsFrom`, `Pool.stampsFrom`, `src/Effect4/Modules/Pool/Cell.lean`). -/

section Initial

variable {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}
variable {A : Ty}

/-- An idle item's record, built from a stamp and a resource. -/
theorem types_mkItem (resource : ResourceTy A) {stamp value : TermSrc}
    (hstamp : TypesEach sig stamp env path types .nat)
    (hvalue : TypesEach sig value env path types A) :
    TypesEach sig (Pool.mkItem A stamp value) env path types (Pool.itemTy A) :=
  fun _ => types_record resource.item
    (.cons (hstamp true)
      (.cons (hvalue true) (.cons (types_bool false true) (.cons (types_nat 0 true) .nil))))
    (item_checkTy resource.canonical)

/-- Each item of the initial value has an item's type. -/
theorem types_itemsFrom (resource : ResourceTy A) : ∀ (stamp : Nat) (resources : List TermSrc),
    (∀ r ∈ resources, TypesEach sig r env path types A) →
      ∀ x ∈ Pool.itemsFrom A stamp resources, TypesEach sig x env path types (Pool.itemTy A)
  | _, [], _, _, member => absurd member List.not_mem_nil
  | stamp, r :: rest, each, x, member => by
    rcases List.mem_cons.mp member with rfl | tail
    · exact types_mkItem resource (types_nat stamp) (each r List.mem_cons_self)
    · exact types_itemsFrom resource (stamp + 1) rest
        (fun r' inside => each r' (List.mem_cons_of_mem r inside)) x tail

/-- Each stamp of the initial value is a number. -/
theorem types_stampsFrom : ∀ (stamp : Nat) (resources : List TermSrc),
    ∀ x ∈ Pool.stampsFrom stamp resources, TypesEach sig x env path types .nat
  | _, [], _, member => absurd member List.not_mem_nil
  | stamp, _ :: rest, x, member => by
    rcases List.mem_cons.mp member with rfl | tail
    · exact types_nat stamp
    · exact types_stampsFrom (stamp + 1) rest x tail

theorem itemsFrom_ne_nil (A : Ty) (stamp : Nat) :
    ∀ {resources : List TermSrc}, resources ≠ [] → Pool.itemsFrom A stamp resources ≠ []
  | [], nonempty => absurd rfl nonempty
  | _ :: _, _ => List.cons_ne_nil _ _

theorem stampsFrom_ne_nil (stamp : Nat) :
    ∀ {resources : List TermSrc}, resources ≠ [] → Pool.stampsFrom stamp resources ≠ []
  | [], nonempty => absurd rfl nonempty
  | _ :: _, _ => List.cons_ne_nil _ _

end Initial

/-! ## The initial value and the six steps, typed at every scope -/

/-- **The initial value has the cell's type**, at every list of at least one resource and in
every scope, where each resource has the resource's type under each literal flag. The size is
at least 1 (decisions row 267): the two lists of an empty pool would have the empty element
type. -/
@[semantics "store-typing" (requirement := R4)]
theorem initial_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (resource : ResourceTy A) {resources : List TermSrc} (nonempty : resources ≠ [])
    {env : Env} {path : List Nat} {types : List Ty}
    (typesEach : ∀ r ∈ resources, TypesEach sig r env path types A) :
    TypesEach sig (Pool.initial A resources) env path types (Pool.cellTy A) :=
  fun _ => types_record resource.cell
    (.cons
      (types_listOf atoms (itemTy_normal resource.canonical) (itemsFrom_ne_nil A 0 nonempty)
        (types_itemsFrom resource 0 resources typesEach) true)
      (.cons
        (types_listOf atoms rfl (stampsFrom_ne_nil 0 nonempty) (types_stampsFrom 0 resources)
          true)
        (.cons (types_nilT atoms true)
          (.cons (types_bool false true) (.cons (types_nat 0 true) .nil)))))
    (initial_checkTy resource.canonical)

/-- **The lease step is typed at every scope.** The request's identity stands in the removal's
fold, and the cell's own source stands in the two folds over the items, so each is taken with
its typed capture. The hint stands outside every fold. -/
@[semantics "store-typing" (requirement := R4)]
theorem leaseStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {idSrc hintSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty} (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesHint : TypesEach sig hintSrc env path types idTy)
    (typesCell : CapturedTy sig cellSrc env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.leaseStep idSrc hintSrc cellSrc) env path types
      (.prod (leaseReplyTy A) (Pool.cellTy A)) := by
  have cell := typesCell.atScope
  have gone := types_withdrawn canonical atoms depth typesId cell
  have none := types_noItem canonical atoms cell
  have refused := types_pair atoms (types_leaseReply canonical atoms (types_bool true) none) gone
  have enrolled := types_pair atoms (types_leaseReply canonical atoms (types_bool false) none)
    (types_setWaiters canonical cell
      (types_snoc atoms waiterTy_normal
        (types_removeById atoms depth waiterTy_normal waiter_idTy
          (types_cellWaiters canonical cell) typesId)
        (types_mkWaiter typesId.atScope typesHint)))
  have leased := types_pair atoms
    (types_leaseReply canonical atoms (types_bool false)
      (types_head atoms (types_leasedOf canonical atoms depth typesCell)))
    (types_setNext canonical
      (types_setAvailable canonical
        (types_setItems canonical gone (types_marked canonical atoms depth typesCell))
        (types_drop atoms (types_cellAvailable canonical cell) (types_nat 1)))
      (types_add atoms (types_cellNext canonical cell) (types_nat 1)))
  exact types_ifT atoms (types_cellClosing canonical cell) refused
    (types_ifT atoms (types_isEmpty atoms (types_cellAvailable canonical cell)) enrolled leased)

/-- **The return step is typed at every scope.** The item's stamp and the lease's stamp stand
in the two folds over the items, so each is taken with its typed capture. -/
@[semantics "store-typing" (requirement := R4)]
theorem returnStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {itemSrc leaseSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty} (depth : types.length = env.names.length)
    (typesItem : CapturedTy sig itemSrc env path types .nat)
    (typesLease : CapturedTy sig leaseSrc env path types .nat)
    (typesCell : TypesEach sig cellSrc env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.returnStep itemSrc leaseSrc cellSrc) env path types
      (.prod returnReplyTy (Pool.cellTy A)) := by
  have returned := types_pair atoms
    (types_tuple2 atoms (types_bool true)
      (types_notT atoms (types_isEmpty atoms (types_cellWaiters canonical typesCell)))
      rfl rfl rfl rfl)
    (types_setAvailable canonical
      (types_setItems canonical typesCell
        (types_freed canonical atoms depth typesItem typesLease typesCell))
      (types_front atoms rfl typesItem.atScope (types_cellAvailable canonical typesCell)))
  have stale := types_pair atoms
    (types_tuple2 atoms (types_bool false) (types_bool false) rfl rfl rfl rfl) typesCell
  exact types_ifT atoms (types_heldBy canonical atoms depth typesItem typesLease typesCell)
    returned stale

/-- **The selection step is typed at every scope.** No fold: each argument is typed at the
scope alone. -/
@[semantics "store-typing" (requirement := R4)]
theorem selectStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {countSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty}
    (typesCount : TypesEach sig countSrc env path types .nat)
    (typesCell : TypesEach sig cellSrc env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.selectStep countSrc cellSrc) env path types
      (.prod selectReplyTy (Pool.cellTy A)) :=
  have waiters := types_cellWaiters canonical typesCell
  types_pair atoms (types_take atoms waiters typesCount)
    (types_setWaiters canonical typesCell (types_drop atoms waiters typesCount))

/-- **The withdrawal is typed at every scope.** The request's identity stands in the removal's
fold. -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {idSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty} (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.withdrawStep idSrc cellSrc) env path types
      (.prod .unit (Pool.cellTy A)) :=
  types_pair atoms types_unit (types_withdrawn canonical atoms depth typesId typesCell)

/-- **The close's first step is typed at every scope.** No fold. -/
@[semantics "store-typing" (requirement := R4)]
theorem closeStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (typesCell : TypesEach sig cellSrc env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.closeStep cellSrc) env path types (.prod closeReplyTy (Pool.cellTy A)) :=
  types_pair atoms
    (types_tuple2 atoms (types_notT atoms (types_cellClosing canonical typesCell))
      (types_len atoms (types_cellWaiters canonical typesCell)) rfl rfl rfl rfl)
    (types_setClosing canonical typesCell (types_bool true))

/-- **The closer's step is typed at every scope** (decisions row 276, point 2). The closer's
identity stands in the removal's fold, so it is taken with its typed capture. The hint and the
cell's own source stand outside every fold that reads a caller's term. -/
@[semantics "store-typing" (requirement := R4)]
theorem drainStep_types {Op : Type} (sig : Signature Op) (atoms : sig.atomOf = nativeAtomTy)
    {A : Ty} (canonical : A.normalize = A) {idSrc hintSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty} (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesHint : TypesEach sig hintSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types (Pool.cellTy A)) :
    TypesEach sig (Pool.drainStep idSrc hintSrc cellSrc) env path types
      (.prod .bool (Pool.cellTy A)) := by
  have enrolled := types_pair atoms (types_bool false)
    (types_setWaiters canonical typesCell
      (types_snoc atoms waiterTy_normal
        (types_removeById atoms depth waiterTy_normal waiter_idTy
          (types_cellWaiters canonical typesCell) typesId)
        (types_mkWaiter typesId.atScope typesHint)))
  have drained := types_pair atoms (types_bool true)
    (types_withdrawn canonical atoms depth typesId typesCell)
  exact types_ifT atoms (types_outstanding canonical atoms depth typesCell) enrolled drained

end Effect4.Pool.Model
