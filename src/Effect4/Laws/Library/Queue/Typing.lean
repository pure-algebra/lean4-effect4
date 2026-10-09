import Effect4.Laws.Step.Waiting
import Effect4.Library.Queue.Steps
import Effect4.Program.Typing
import Effect4.Program.Native
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.TyView
import Effect4.Laws.Step.Checking
import Effect4.Laws.Step
import Effect4.Library.Queue.Data
import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Auto.Semantics

/-!
# The typing of the Queue's cell and of its six steps (decisions rows 255 and 257)

The module is `src/Effect4/Library/Queue/`: the cell (`Cell.lean`) and the step terms
(`Steps.lean`). This file states that the checker types the initial value and each step at the
cell's type, for every message type that it types in a cell (`MessageTy`).

Placement. Concept `store-typing`. Requirement R4. The file holds two forms of each step's
typing.

- **At the step's own scope** (`takeStep_typed` and its four siblings, `empty_typed`,
  `sizeStep_typed`): one typing judgment of the checker (`termTy`) on a step's tree, under the
  names of its arguments and the cell's value last. Each of the five steps of a `Ref.modify` is
  the instance of the form below at the statement's own names.
- **At every scope** (`takeStep_types` and its four siblings): for every caller's terms that
  have the arguments' types and keep them under a fold's binders, the step has its stated type
  (`Types`, `CapturedTy`, `src/Effect4/Laws/Step/Checking.lean`). The wrapper applies this
  form at its own scope, with no second elaboration.

Their consumer is the wrapper's law, in the public path's slice: with a step's typing,
`step_keeps_cell` (`src/Effect4/Laws/Step/Store.lean`) gives that one `Ref.modify` of the
step keeps the cell a member of the cell's type. `typeAt_tree` recovers the tree and its
`termTy` equation from a statement at the step's own scope. Reach: the signature's atoms are the
native table's, and no premise names `sig.constAtom`, because no step holds a string literal. A
caller's term has its type under each literal flag, so a string literal is no caller's term
here.

The statements establish no agreement with the model, no typing of a wrapper and nothing about
a target. The checker's typing of a step is not program admission. All seven are proved, each
in place of its planned goal (decisions row 203). The proofs read the checker's rule at each
node (`src/Effect4/Laws/Program/Typing/TermIntro.lean`), with the cell's type as its own normal
form (`cellTy_normal`). Each pass of `Steps.lean` is typed once, at the cell's, an offer's and a
taker's type. The finite controls are in `Test/Program/QueueSteps.lean`: each statement at 27
message types, with red controls.
-/

set_option autoImplicit false

namespace Effect4.Queue.Model

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-- **A message type that the checker types in a cell.** It is its own normal form, so the
cell's type at it is the type that the checker answers. The two record declarations that hold
it are formed: the cell's and a pending offer's (`Formation.check`,
`src/Effect4/Program/Formation.lean`). -/
structure MessageTy (A : Ty) : Prop where
  canonical : A.normalize = A
  cell : Formation.check (Formation.sites false [] (.record (Queue.cellFields A))) = none
  offer : Formation.check (Formation.sites false [] (.record (Queue.offerFields A))) = none

instance (A : Ty) : Decidable (MessageTy A) :=
  decidable_of_iff
    (A.normalize = A ∧
      Formation.check (Formation.sites false [] (.record (Queue.cellFields A))) = none ∧
      Formation.check (Formation.sites false [] (.record (Queue.offerFields A))) = none)
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.canonical, h.cell, h.offer⟩⟩

/-! ## The types of the steps' replies -/

/-- A take's reply: the message when it consumed, the offers that the step accepted, and the
takers to wake. -/
def takeReplyTy (A : Ty) : Ty :=
  .tuple [.option A, .list (Queue.offerTy A), .list Queue.takerTy]

/-- An offer's reply: its decided answer when it does not wait, and the takers to wake. A pair,
as the checker normalizes a tuple of two. -/
def offerReplyTy : Ty := .prod (.option .bool) (.list Queue.takerTy)

/-- A poll's reply: the message when it consumed, and the offers that the step accepted. -/
def pollReplyTy (A : Ty) : Ty := .prod (.option A) (.list (Queue.offerTy A))

/-- A withdrawal's reply: the takers to wake. -/
def wakeReplyTy : Ty := .list Queue.takerTy

/-! ## The cell's type is its own normal form, at a canonical message type -/

theorem offerTy_normal {A : Ty} (canonical : A.normalize = A) :
    (Queue.offerTy A).normalize = Queue.offerTy A := by
  show Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  show Ty.record [("batch", false, Ty.normalize .bool), ("hint", false, Ty.normalize Queue.answerTy),
    ("id", false, Ty.normalize idTy), ("rest", false, Ty.normalize (.list A))] = _
  have rest : Ty.normalize (.list A) = .list A := by
    show Ty.list (Ty.normalize A) = _
    rw [canonical]
  rw [rest]
  rfl

theorem cellTy_normal {A : Ty} (canonical : A.normalize = A) :
    (Queue.cellTy A).normalize = Queue.cellTy A := by
  show Ty.normalize (.record _) = _
  rw [Ty.normalize_record]
  show Ty.record [("cap", false, Ty.normalize .nat), ("msgs", false, Ty.normalize (.list A)),
    ("offers", false, Ty.normalize (.list (Queue.offerTy A))),
    ("takers", false, Ty.normalize (.list Queue.takerTy))] = _
  have msgs : Ty.normalize (.list A) = .list A := by
    show Ty.list (Ty.normalize A) = _
    rw [canonical]
  have offers : Ty.normalize (.list (Queue.offerTy A)) = .list (Queue.offerTy A) := by
    show Ty.list (Ty.normalize (Queue.offerTy A)) = _
    rw [offerTy_normal canonical]
  rw [msgs, offers]
  rfl

/-- The type of the cell's buffer, as the checker reads the field. -/
theorem cell_msgsTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.cellTy A) "msgs" = some (.list A) :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

/-- The cell's written declaration normalizes to the cell's type. -/
theorem cellFields_normal {A : Ty} (canonical : A.normalize = A) :
    Ty.normalize (.record (Queue.cellFields A)) = Queue.cellTy A := by
  rw [Ty.normalize_record]
  show Ty.record [("cap", false, Ty.normalize .nat), ("msgs", false, Ty.normalize (.list A)),
    ("offers", false, Ty.normalize (.list (Queue.offerTy A))),
    ("takers", false, Ty.normalize (.list Queue.takerTy))] = _
  have msgs : Ty.normalize (.list A) = .list A := by
    show Ty.list (Ty.normalize A) = _
    rw [canonical]
  have offers : Ty.normalize (.list (Queue.offerTy A)) = .list (Queue.offerTy A) := by
    show Ty.list (Ty.normalize (Queue.offerTy A)) = _
    rw [offerTy_normal canonical]
  rw [msgs, offers]
  rfl

/-! ## The Queue's records: reads, overwrites and constructions

Each is one application of a record rule at a record type in normal form
(`src/Effect4/Laws/Program/Typing/TermIntro.lean`): the cell's type, an offer's or a taker's.
The side conditions are a lookup that `rfl` decides and distinct names that `decide` decides. -/

/-- A taker's type is its own normal form. -/
theorem takerTy_normal : Queue.takerTy.normalize = Queue.takerTy := rfl

/-- A taker's written declaration is formed. -/
theorem takerFields_formed :
    Formation.check (Formation.sites false [] (.record Queue.takerFields)) = none := by decide

/-- An offer's written declaration normalizes to an offer's type. -/
theorem offerFields_normal {A : Ty} (canonical : A.normalize = A) :
    Ty.normalize (.record (Queue.offerFields A)) = Queue.offerTy A := by
  rw [Ty.normalize_record]
  show Ty.record [("batch", false, Ty.normalize .bool),
    ("hint", false, Ty.normalize Queue.answerTy), ("id", false, Ty.normalize idTy),
    ("rest", false, Ty.normalize (.list A))] = _
  have rest : Ty.normalize (.list A) = .list A := Ty.normalize_list_canonical canonical
  rw [rest]
  rfl

theorem cell_capTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.cellTy A) "cap" = some .nat :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem cell_offersTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.cellTy A) "offers" = some (.list (Queue.offerTy A)) :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem cell_takersTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.cellTy A) "takers" = some (.list Queue.takerTy) :=
  Record.fieldType_normal (cellTy_normal canonical) rfl

theorem offer_idTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.offerTy A) "id" = some idTy :=
  Record.fieldType_normal (offerTy_normal canonical) rfl

theorem offer_restTy {A : Ty} (canonical : A.normalize = A) :
    Record.fieldType false (Queue.offerTy A) "rest" = some (.list A) :=
  Record.fieldType_normal (offerTy_normal canonical) rfl

theorem taker_idTy : Record.fieldType false Queue.takerTy "id" = some idTy :=
  Record.fieldType_normal takerTy_normal rfl

/-- The buffer's overwrite keeps the cell's type. -/
theorem cell_setMsgsTy {A : Ty} (canonical : A.normalize = A) :
    Record.setType (Queue.cellTy A) "msgs" (.list A) = some (Queue.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl (Ty.normalize_list_canonical canonical)

/-- The takers' overwrite keeps the cell's type. -/
theorem cell_setTakersTy {A : Ty} (canonical : A.normalize = A) :
    Record.setType (Queue.cellTy A) "takers" (.list Queue.takerTy) = some (Queue.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl rfl

/-- The offers' overwrite keeps the cell's type. -/
theorem cell_setOffersTy {A : Ty} (canonical : A.normalize = A) :
    Record.setType (Queue.cellTy A) "offers" (.list (Queue.offerTy A)) = some (Queue.cellTy A) :=
  Record.setType_same (cellTy_normal canonical) rfl
    (Ty.normalize_list_canonical (offerTy_normal canonical))

/-- A taker's construction, each field at its declared type, answers a taker's type. -/
theorem taker_checkTy :
    Record.check Queue.takerFields ["id", "hint"] [idTy, idTy] =
      some Queue.takerTy :=
  Record.check_declared (fields := Queue.takerFields) (by decide)

/-- An offer's construction, each field at its declared type, answers an offer's type. -/
theorem offer_checkTy {A : Ty} (canonical : A.normalize = A) :
    Record.check (Queue.offerFields A) ["id", "hint", "batch", "rest"]
        [idTy, Queue.answerTy, .bool, .list A] =
      some (Queue.offerTy A) := by
  have distinct : ((Queue.offerFields A).map Prod.fst).Nodup := by
    show (["id", "hint", "batch", "rest"] : List String).Nodup
    decide
  have checked := Record.check_declared distinct
  rw [offerFields_normal canonical] at checked
  exact checked

/-! ## The replies: normal forms, and an answer with no message below one with a message

An arm of a step that answers no message answers `none`, whose type is an option of the empty
union. So a step's two arms have two types, and `ite` answers the greater one. -/

/-- A take's reply type is its own normal form. -/
theorem takeReplyTy_normal {A : Ty} (canonical : A.normalize = A) :
    (takeReplyTy A).normalize = takeReplyTy A :=
  Ty.normalize_triple_canonical (Ty.normalize_option_canonical canonical)
    (Ty.normalize_list_canonical (offerTy_normal canonical)) rfl

/-- A poll's reply type is its own normal form. -/
theorem pollReplyTy_normal {A : Ty} (canonical : A.normalize = A) :
    (pollReplyTy A).normalize = pollReplyTy A :=
  Ty.normalize_prod_canonical (Ty.normalize_option_canonical canonical)
    (Ty.normalize_list_canonical (offerTy_normal canonical)) rfl rfl

/-- A reply of two parts that answers no message is below the reply that answers one, each
beside the stored value's type. Used by the poll step and the offer step. -/
theorem idlePair_sub (T L C : Ty) :
    Ty.sub (.prod (.prod (.option .never) L) C) (.prod (.prod (.option T) L) C) = true := by
  rw [Ty.sub_prod, Ty.sub_prod, Ty.sub_option, Ty.OrderProof.sub_never, Ty.sub_refl L,
    Ty.sub_refl C]
  rfl

/-- A reply of three parts that answers no message is below the reply that answers one, each
beside the stored value's type. Used by the take step. -/
theorem idleTriple_sub (T L K C : Ty) :
    Ty.sub (.prod (.tuple [.option .never, L, K]) C) (.prod (.tuple [.option T, L, K]) C) =
      true := by
  rw [Ty.sub_prod, Ty.sub_refl C, Bool.and_true]
  apply Ty.sub_tuple_of_items
  · rfl
  · intro p member
    rcases List.mem_cons.mp member with rfl | member
    · show Ty.sub (.option .never) (.option T) = true
      rw [Ty.sub_option]
      exact Ty.OrderProof.sub_never T
    rcases List.mem_cons.mp member with rfl | member
    · exact Ty.sub_refl L
    rcases List.mem_cons.mp member with rfl | member
    · exact Ty.sub_refl K
    · exact absurd member List.not_mem_nil

/-! ## The passes, typed once

Each builder of `src/Effect4/Library/Queue/Steps.lean` that reads or writes a record of the
cell, and each pass, at the cell's, an offer's and a taker's type. A pass that places a
caller's term in a fold's body takes it with its typed capture (`CapturedTy`). -/

section Passes

variable {Op : Type} {sig : Signature Op} {env : Env} {path : List Nat} {types : List Ty}

theorem types_cellCap {A : Ty} (canonical : A.normalize = A) {s : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A)) :
    TypesEach sig (field s "cap") env path types .nat :=
  fun _ => types_field (hs false) (cell_capTy canonical)

theorem types_cellMsgs {A : Ty} (canonical : A.normalize = A) {s : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A)) :
    TypesEach sig (field s "msgs") env path types (.list A) :=
  fun _ => types_field (hs false) (cell_msgsTy canonical)

theorem types_cellOffers {A : Ty} (canonical : A.normalize = A) {s : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A)) :
    TypesEach sig (field s "offers") env path types (.list (Queue.offerTy A)) :=
  fun _ => types_field (hs false) (cell_offersTy canonical)

theorem types_cellTakers {A : Ty} (canonical : A.normalize = A) {s : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A)) :
    TypesEach sig (field s "takers") env path types (.list Queue.takerTy) :=
  fun _ => types_field (hs false) (cell_takersTy canonical)

theorem types_setMsgs {A : Ty} (canonical : A.normalize = A) {s v : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A))
    (hv : TypesEach sig v env path types (.list A)) :
    TypesEach sig (recordSet s "msgs" v) env path types (Queue.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setMsgsTy canonical)

theorem types_setTakers {A : Ty} (canonical : A.normalize = A) {s v : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A))
    (hv : TypesEach sig v env path types (.list Queue.takerTy)) :
    TypesEach sig (recordSet s "takers" v) env path types (Queue.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setTakersTy canonical)

theorem types_setOffers {A : Ty} (canonical : A.normalize = A) {s v : TermSrc}
    (hs : TypesEach sig s env path types (Queue.cellTy A))
    (hv : TypesEach sig v env path types (.list (Queue.offerTy A))) :
    TypesEach sig (recordSet s "offers" v) env path types (Queue.cellTy A) :=
  fun _ => types_recordSet (hs false) (hv true) (cell_setOffersTy canonical)

/-- A waiting taker's record, built from an identity and a hint. -/
theorem types_mkTaker {id hint : TermSrc} (hid : TypesEach sig id env path types idTy)
    (hhint : TypesEach sig hint env path types idTy) :
    TypesEach sig (Queue.mkTaker id hint) env path types Queue.takerTy :=
  fun _ => types_record takerFields_formed (.cons (hid true) (.cons (hhint true) .nil))
    taker_checkTy

/-- A pending offer's record. -/
theorem types_mkOffer {A : Ty} (message : MessageTy A) {id hint batch rest : TermSrc}
    (hid : TypesEach sig id env path types idTy)
    (hhint : TypesEach sig hint env path types Queue.answerTy)
    (hbatch : TypesEach sig batch env path types .bool)
    (hrest : TypesEach sig rest env path types (.list A)) :
    TypesEach sig (Queue.mkOffer A id hint batch rest) env path types (Queue.offerTy A) :=
  fun _ => types_record message.offer
    (.cons (hid true) (.cons (hhint true) (.cons (hbatch true) (.cons (hrest true) .nil))))
    (offer_checkTy message.canonical)

variable (atoms : sig.atomOf = nativeAtomTy)
include atoms

/-- The wake's pass: a list of the takers' type. -/
theorem types_wake {takers msgs : TermSrc} {T M : Ty}
    (htakers : TypesEach sig takers env path types (.list T))
    (hmsgs : TypesEach sig msgs env path types (.list M))
    (canonical : T.normalize = T := by decide) :
    TypesEach sig (Queue.wake takers msgs) env path types (.list T) :=
  types_ifT atoms (types_isEmpty atoms hmsgs) (types_noneOf atoms htakers)
    (types_take atoms htakers (types_nat 1)) (by rw [Ty.normalize, canonical])

/-- `enrolled`: whether the request waits among the takers. -/
theorem types_enrolled {takers id : TermSrc} (depth : types.length = env.names.length)
    (htakers : TypesEach sig takers env path types (.list Queue.takerTy))
    (hid : CapturedTy sig id env path types idTy) :
    TypesEach sig (Queue.enrolled takers id) env path types .bool :=
  fun _ => types_foldWith_same (htakers false) (types_bool false false)
    (types_orT atoms (types_minted_acc depth path .bool Queue.takerTy)
      (types_sameItem atoms depth taker_idTy hid) false)
    (Ty.subN_refl .bool)

/-- `isHead`: whether the request is the earliest taker. -/
theorem types_isHead {takers id : TermSrc} (depth : types.length = env.names.length)
    (htakers : TypesEach sig takers env path types (.list Queue.takerTy))
    (hid : CapturedTy sig id env path types idTy) :
    TypesEach sig (Queue.isHead takers id) env path types .bool :=
  fun _ => types_foldWith_same (types_take atoms htakers (types_nat 1) false)
    (types_bool false false)
    (types_sameItem (accT := .bool) atoms depth taker_idTy hid false)
    (Ty.subN_refl .bool)

/-- `removeTaker`: the takers without the request. -/
theorem types_removeTaker {takers id : TermSrc} (depth : types.length = env.names.length)
    (htakers : TypesEach sig takers env path types (.list Queue.takerTy))
    (hid : CapturedTy sig id env path types idTy) :
    TypesEach sig (Queue.removeTaker takers id) env path types (.list Queue.takerTy) :=
  types_removeById atoms depth takerTy_normal taker_idTy htakers hid

/-- `removeOffer`: the pending offers without the request. -/
theorem types_removeOffer {A : Ty} (canonical : A.normalize = A) {offers id : TermSrc}
    (depth : types.length = env.names.length)
    (hoffers : TypesEach sig offers env path types (.list (Queue.offerTy A)))
    (hid : CapturedTy sig id env path types idTy) :
    TypesEach sig (Queue.removeOffer offers id) env path types (.list (Queue.offerTy A)) :=
  types_removeById atoms depth (offerTy_normal canonical) (offer_idTy canonical) hoffers hid

/-- `renewHint`: the takers, with the request's hint replaced. The request's identity and its
hint both stand in the fold's body. -/
theorem types_renewHint {takers id hint : TermSrc} (depth : types.length = env.names.length)
    (htakers : TypesEach sig takers env path types (.list Queue.takerTy))
    (hid : CapturedTy sig id env path types idTy)
    (hhint : CapturedTy sig hint env path types idTy) :
    TypesEach sig (Queue.renewHint takers id hint) env path types (.list Queue.takerTy) :=
  fun _ => types_foldWith_same (htakers false) (types_noneOf atoms htakers false)
    (types_snoc atoms takerTy_normal
      (types_minted_acc depth path (.list Queue.takerTy) Queue.takerTy)
      (types_ifT atoms (types_sameItem atoms depth taker_idTy hid)
        (types_mkTaker (hid.underFold (.list Queue.takerTy) Queue.takerTy)
          (hhint.underFold (.list Queue.takerTy) Queue.takerTy))
        (types_minted_item depth path (.list Queue.takerTy) Queue.takerTy) takerTy_normal) false)
    (Ty.subN_refl (.list Queue.takerTy))

/-- `fitting`: how many pending offers enter the room. -/
theorem types_fitting {room offers : TermSrc} {T : Ty}
    (hroom : TypesEach sig room env path types .nat)
    (hoffers : TypesEach sig offers env path types (.list T)) :
    TypesEach sig (Queue.fitting room offers) env path types .nat :=
  types_minT atoms hroom (types_len atoms hoffers)

/-- `entering`: the offers that enter. -/
theorem types_entering {room offers : TermSrc} {T : Ty}
    (hroom : TypesEach sig room env path types .nat)
    (hoffers : TypesEach sig offers env path types (.list T)) :
    TypesEach sig (Queue.entering room offers) env path types (.list T) :=
  types_take atoms hoffers (types_fitting atoms hroom hoffers)

/-- `staying`: the offers that stay pending. -/
theorem types_staying {room offers : TermSrc} {T : Ty}
    (hroom : TypesEach sig room env path types .nat)
    (hoffers : TypesEach sig offers env path types (.list T)) :
    TypesEach sig (Queue.staying room offers) env path types (.list T) :=
  types_drop atoms hoffers (types_fitting atoms hroom hoffers)

/-- `gained`: the buffer with the messages of the offers that enter. -/
theorem types_gained {A : Ty} (canonical : A.normalize = A) {room msgs offers : TermSrc}
    (depth : types.length = env.names.length)
    (hroom : TypesEach sig room env path types .nat)
    (hmsgs : TypesEach sig msgs env path types (.list A))
    (hoffers : TypesEach sig offers env path types (.list (Queue.offerTy A))) :
    TypesEach sig (Queue.gained room msgs offers) env path types (.list A) :=
  fun _ => types_foldWith_same (types_entering atoms hroom hoffers false) (hmsgs false)
    ((types_append atoms (types_minted_acc depth path (.list A) (Queue.offerTy A))
      (fun _ => types_field (types_minted_item depth path (.list A) (Queue.offerTy A) false)
        (offer_restTy canonical)) canonical) false)
    (Ty.subN_refl (.list A))

end Passes

/-! ## The five steps of a `Ref.modify`, typed at every scope

Each is in the shape of its agreement statement
(`src/Effect4/Laws/Library/Queue/Steps.lean`): at every scope, for every caller's terms that
have the arguments' types and keep them under a fold's binders, the step has its stated type.

Placement. Concept `store-typing`, requirement R4: each is the general form of the statement of
the same step below. Reach: the checker's `argTy` on the step's tree under each literal flag,
at every scope; `sig.atomOf = nativeAtomTy`; `MessageTy A`. They establish no agreement with the
model, no typing of a wrapper and nothing of a target. Consumers: the wrapper's law at its own
scope, and the statement of the same step. -/

/-- Formation helpers for the R4 Queue step typing laws below. These discharge record and
ascription checks from the existing MessageTy premise; they establish no program admission. -/
@[semantics "store-typing" (requirement := R4)]
theorem message_nodes_for_steps {A : Ty} (message : MessageTy A) : NodesFormed A := fun t member =>
  nodesFormed_of_check message.cell t (by
    show t ∈ [Ty.record (Queue.cellFields A)] ++ (([Ty.list A] ++ Formation.nodes A) ++ _)
    exact List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ member)))

@[semantics "store-typing" (requirement := R4)]
theorem offer_nodes_for_steps {A : Ty} (message : MessageTy A) : NodesFormed (Queue.offerTy A) := by
  intro t member
  have member' : t ∈ [Queue.offerTy A] ++ (Formation.nodes .bool ++
      (Formation.nodes Queue.answerTy ++ (Formation.nodes idTy ++
        (Formation.nodes (.list A) ++ [])))) := member
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member'
  rcases member' with rfl | h | h | h | h
  · show (["batch", "hint", "id", "rest"] : List String).Nodup
    decide
  · exact nodesFormed_of_check (T := .bool) (by decide) t h
  · exact nodesFormed_of_check (T := Queue.answerTy) (by decide) t h
  · exact nodesFormed_of_check (T := idTy) (by decide) t h
  · exact nodesFormed_list (message_nodes_for_steps message) t h

/-- Formation of a one-field annotation, consumed by the R4 Queue step typing laws. -/
@[semantics "store-typing" (requirement := R4)]
theorem ascribe_formed_for_steps (T : Ty) (formed : NodesFormed T) :
    Formation.check (Formation.sites false [] (.record (ascribeFields T))) = none := by
  apply (Formation.check_eq_none_iff _).mpr
  apply formed_sites
  intro t member
  change t ∈ [.record (ascribeFields T)] ++ (Formation.nodes T ++ []) at member
  simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
  rcases member with rfl | member
  · show (["v"] : List String).Nodup
    decide
  · exact formed t member

/-- **The withdrawal of an offer is typed at every scope.** -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawOffer_types (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types (Queue.cellTy A)) :
    TypesEach sig (Queue.withdrawOffer A idSrc cellSrc) env path types
      (.prod wakeReplyTy (Queue.cellTy A)) := by
  refine Step.typed (Γ := Data.withdrawΓ A) sig atoms
    (Input.types_cons typesId.atScope (Input.types_cons typesCell Input.types_nil))
    (Data.withdrawOffer A) ?_ depth
  have cellN := cellTy_normal message.canonical
  have offerN := offerTy_normal message.canonical
  dsimp only [Step.Lists.map, Step.Lists.mapWith, Step.Lists.filter, Step.Lists.removeBy,
    Step.Lists.any, Step.Lists.withAccumulator, Step.rename, Step.renameAlg,
    Step.renamedFields, Step.Facts, Step.cata, Step.cataFields, Step.cataItems, Step.factsAlg,
    tupleFacts, tupleFacts.tupleNormals, ItemResults.All,
    FieldResults.All, Data.withdrawTake, Data.withdrawOffer, Data.removeTaker,
    Data.removeOffer, Data.wake, Data.mkTaker, Queue.takerRecord]
  aesop (add safe apply [Ty.normalize_prod_canonical, Ty.normalize_list_canonical,
    Ty.normalize_option_canonical])

/-- **The withdrawal of a take is typed at every scope.** -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawTake_types (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) {idSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types (Queue.cellTy A)) :
    TypesEach sig (Queue.withdrawTake A idSrc cellSrc) env path types
      (.prod wakeReplyTy (Queue.cellTy A)) := by
  refine Step.typed (Γ := Data.withdrawΓ A) sig atoms
    (Input.types_cons typesId.atScope (Input.types_cons typesCell Input.types_nil))
    (Data.withdrawTake A) ?_ depth
  have cellN := cellTy_normal message.canonical
  have offerN := offerTy_normal message.canonical
  dsimp only [Step.Lists.map, Step.Lists.mapWith, Step.Lists.filter, Step.Lists.removeBy,
    Step.Lists.any, Step.Lists.withAccumulator, Step.rename, Step.renameAlg,
    Step.renamedFields, Step.Facts, Step.cata, Step.cataFields, Step.cataItems, Step.factsAlg,
    tupleFacts, tupleFacts.tupleNormals, ItemResults.All,
    FieldResults.All, Data.withdrawTake, Data.withdrawOffer, Data.removeTaker,
    Data.removeOffer, Data.wake, Data.mkTaker, Queue.takerRecord]
  aesop (add safe apply [Ty.normalize_prod_canonical, Ty.normalize_list_canonical,
    Ty.normalize_option_canonical])

set_option maxHeartbeats 800000 in
/-- **The poll step is typed at every scope.** The arm that consumes answers a message, and the
arm that does not answers none: the step has the first arm's type. -/
@[semantics "store-typing" (requirement := R4)]
theorem pollStep_types (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) {cellSrc : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (typesCell : TypesEach sig cellSrc env path types (Queue.cellTy A)) :
    TypesEach sig (Queue.pollStep A cellSrc) env path types
      (.prod (pollReplyTy A) (Queue.cellTy A)) := by
  refine Step.typed (Γ := [Queue.cellTy A]) sig atoms
    (Input.types_cons typesCell Input.types_nil) (Data.poll A) ?_ (depth)
  have canonical := message.canonical
  have optionF := ascribe_formed_for_steps (.option A) (nodesFormed_option (message_nodes_for_steps message))
  have boolF := ascribe_formed_for_steps (.option .bool) (nodesFormed_of_check (by decide))
  have listF := ascribe_formed_for_steps (.list A) (nodesFormed_list (message_nodes_for_steps message))
  have takerF : Formation.check (Formation.sites false [] (.record Queue.takerRecord)) = none := by decide
  have offerF := (Formation.check_eq_none_iff _).mpr (formed_sites (offer_nodes_for_steps message) [])
  have cellN := cellTy_normal message.canonical
  have offerN := offerTy_normal message.canonical
  have cellRecordN : (Ty.record (Queue.cellRecord A)).normalize = .record (Queue.cellRecord A) := cellN
  have offerRecordN : (Ty.record (Queue.offerRecord A)).normalize = .record (Queue.offerRecord A) := offerN
  have takeN := takeReplyTy_normal message.canonical
  have pollN := pollReplyTy_normal message.canonical
  have takerN := takerTy_normal
  clear typesCell atoms depth
  dsimp only [Step.Lists.map, Step.Lists.mapWith, Step.Lists.filter, Step.Lists.removeBy,
    Step.Lists.any, Step.Lists.withAccumulator, Step.rename, Step.renameAlg,
    Step.renamedFields, Step.Facts, Step.cata, Step.cataFields, Step.cataItems, Step.factsAlg,
    tupleFacts, tupleFacts.tupleNormals, ItemResults.All,
    FieldResults.All, Data.take, Data.offer, Data.poll, Data.gained, Data.entering,
    Data.staying, Data.fitting, Data.enrolled, Data.isHead, Data.renewHint,
    Data.removeTaker, Data.removeOffer, Data.wake, Data.mkTaker, Data.mkOffer,
    Queue.takerRecord, Queue.offerRecord]
  aesop (add safe apply [Ty.normalize_prod_canonical, Ty.normalize_list_canonical,
    Ty.normalize_option_canonical])

set_option maxHeartbeats 800000 in
/-- **The offer step is typed at every scope.** No fold of the step holds a caller's term, so
each argument is typed at the scope alone. The message has the cell's message type itself. -/
@[semantics "store-typing" (requirement := R4)]
theorem offerStep_types (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) {idSrc hintSrc messageSrc cellSrc : TermSrc} {env : Env}
    {path : List Nat} {types : List Ty}
    (typesId : TypesEach sig idSrc env path types idTy)
    (typesHint : TypesEach sig hintSrc env path types Queue.answerTy)
    (typesMessage : TypesEach sig messageSrc env path types A)
    (typesCell : TypesEach sig cellSrc env path types (Queue.cellTy A)) :
    TypesEach sig (Queue.offerStep A idSrc hintSrc messageSrc cellSrc) env path types
      (.prod offerReplyTy (Queue.cellTy A)) := by
  refine Step.typed (Γ := Data.offerΓ A) sig atoms
    (Input.types_cons typesId (Input.types_cons typesHint (Input.types_cons typesMessage (Input.types_cons typesCell Input.types_nil)))) (Data.offer A) ?_ (by trivial)
  have canonical := message.canonical
  have optionF := ascribe_formed_for_steps (.option A) (nodesFormed_option (message_nodes_for_steps message))
  have boolF := ascribe_formed_for_steps (.option .bool) (nodesFormed_of_check (by decide))
  have listF := ascribe_formed_for_steps (.list A) (nodesFormed_list (message_nodes_for_steps message))
  have takerF : Formation.check (Formation.sites false [] (.record Queue.takerRecord)) = none := by decide
  have offerF := (Formation.check_eq_none_iff _).mpr (formed_sites (offer_nodes_for_steps message) [])
  have cellN := cellTy_normal message.canonical
  have offerN := offerTy_normal message.canonical
  have cellRecordN : (Ty.record (Queue.cellRecord A)).normalize = .record (Queue.cellRecord A) := cellN
  have offerRecordN : (Ty.record (Queue.offerRecord A)).normalize = .record (Queue.offerRecord A) := offerN
  have takeN := takeReplyTy_normal message.canonical
  have pollN := pollReplyTy_normal message.canonical
  have takerN := takerTy_normal
  clear typesId typesHint typesMessage typesCell atoms
  dsimp only [Step.Lists.map, Step.Lists.mapWith, Step.Lists.filter, Step.Lists.removeBy,
    Step.Lists.any, Step.Lists.withAccumulator, Step.rename, Step.renameAlg,
    Step.renamedFields, Step.Facts, Step.cata, Step.cataFields, Step.cataItems, Step.factsAlg,
    tupleFacts, tupleFacts.tupleNormals, ItemResults.All,
    FieldResults.All, Data.take, Data.offer, Data.poll, Data.gained, Data.entering,
    Data.staying, Data.fitting, Data.enrolled, Data.isHead, Data.renewHint,
    Data.removeTaker, Data.removeOffer, Data.wake, Data.mkTaker, Data.mkOffer,
    Queue.takerRecord, Queue.offerRecord]
  aesop (add safe apply [Ty.normalize_prod_canonical, Ty.normalize_list_canonical,
    Ty.normalize_option_canonical])

set_option maxHeartbeats 800000 in
/-- **The take step is typed at every scope.** The request's identity and its hint stand in a
fold's body, so each is taken with its typed capture. The arm that consumes answers a message,
and the arm that waits answers none: the step has the first arm's type. -/
@[semantics "store-typing" (requirement := R4)]
theorem takeStep_types (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) {idSrc hintSrc cellSrc : TermSrc} {env : Env} {path : List Nat}
    {types : List Ty} (depth : types.length = env.names.length)
    (typesId : CapturedTy sig idSrc env path types idTy)
    (typesHint : CapturedTy sig hintSrc env path types idTy)
    (typesCell : TypesEach sig cellSrc env path types (Queue.cellTy A)) :
    TypesEach sig (Queue.takeStep A idSrc hintSrc cellSrc) env path types
      (.prod (takeReplyTy A) (Queue.cellTy A)) := by
  refine Step.typed (Γ := Data.takeΓ A) sig atoms
    (Input.types_cons typesId.atScope (Input.types_cons typesHint.atScope (Input.types_cons typesCell Input.types_nil))) (Data.take A) ?_ (depth)
  have canonical := message.canonical
  have optionF := ascribe_formed_for_steps (.option A) (nodesFormed_option (message_nodes_for_steps message))
  have boolF := ascribe_formed_for_steps (.option .bool) (nodesFormed_of_check (by decide))
  have listF := ascribe_formed_for_steps (.list A) (nodesFormed_list (message_nodes_for_steps message))
  have takerF : Formation.check (Formation.sites false [] (.record Queue.takerRecord)) = none := by decide
  have offerF := (Formation.check_eq_none_iff _).mpr (formed_sites (offer_nodes_for_steps message) [])
  have cellN := cellTy_normal message.canonical
  have offerN := offerTy_normal message.canonical
  have cellRecordN : (Ty.record (Queue.cellRecord A)).normalize = .record (Queue.cellRecord A) := cellN
  have offerRecordN : (Ty.record (Queue.offerRecord A)).normalize = .record (Queue.offerRecord A) := offerN
  have takeN := takeReplyTy_normal message.canonical
  have pollN := pollReplyTy_normal message.canonical
  have takerN := takerTy_normal
  clear typesId typesHint typesCell atoms depth
  dsimp only [Step.Lists.map, Step.Lists.mapWith, Step.Lists.filter, Step.Lists.removeBy,
    Step.Lists.any, Step.Lists.withAccumulator, Step.rename, Step.renameAlg,
    Step.renamedFields, Step.Facts, Step.cata, Step.cataFields, Step.cataItems, Step.factsAlg,
    tupleFacts, tupleFacts.tupleNormals, ItemResults.All,
    FieldResults.All, Data.take, Data.offer, Data.poll, Data.gained, Data.entering,
    Data.staying, Data.fitting, Data.enrolled, Data.isHead, Data.renewHint,
    Data.removeTaker, Data.removeOffer, Data.wake, Data.mkTaker, Data.mkOffer,
    Queue.takerRecord, Queue.offerRecord]
  aesop (add safe apply [Ty.normalize_prod_canonical, Ty.normalize_list_canonical,
    Ty.normalize_option_canonical])

/-- **The initial value has the cell's type**, at every capacity and in every scope. -/
@[semantics "store-typing" (requirement := R4)]
theorem empty_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy) (A : Ty)
    (message : MessageTy A) (capacity : Nat) (names : List String) (types : List Ty) :
    typeAt sig names types (Queue.empty A capacity) = some (Queue.cellTy A) := by
  have fits : Record.argumentsFit (Queue.cellFields A)
      [("msgs", Ty.list .never), ("cap", Ty.nat), ("takers", Ty.list .never),
        ("offers", Ty.list .never)] = true := by
    unfold Record.argumentsFit
    rw [Bool.and_eq_true]
    refine ⟨rfl, List.all_eq_true.mpr fun field member => ?_⟩
    simp only [Queue.cellFields, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact sub_nil_list _
    · exact Ty.sub_refl _
    · exact sub_nil_list _
    · exact sub_nil_list _
  have nilTy : ∀ const : Bool, argTy sig types const (.app "nil" .nil) = some (Ty.list .never) := by
    intro const
    show sig.atomOf "nil" [] = _
    rw [atoms]
    rfl
  have capTy : argTy sig types true (.lit (.nat capacity)) = some Ty.nat := rfl
  have noneTy : argsTy sig types true .nil = some [] := rfl
  have values : argsTy sig types true (.cons (.app "nil" .nil) (.cons (.lit (.nat capacity))
      (.cons (.app "nil" .nil) (.cons (.app "nil" .nil) .nil)))) =
      some [Ty.list .never, Ty.nat, Ty.list .never, Ty.list .never] := by
    simp only [argsTy_cons, nilTy, capTy, noneTy, Option.bind_some]
  show (match Formation.check (Formation.sites false [] (.record (Queue.cellFields A))) with
    | some _ => none
    | none => (argsTy sig types true (.cons (.app "nil" .nil) (.cons (.lit (.nat capacity))
        (.cons (.app "nil" .nil) (.cons (.app "nil" .nil) .nil))))).bind
          (Record.check (Queue.cellFields A) ["msgs", "cap", "takers", "offers"])) = _
  rw [message.cell, values]
  show Record.check (Queue.cellFields A) ["msgs", "cap", "takers", "offers"]
    [Ty.list .never, Ty.nat, Ty.list .never, Ty.list .never] = _
  unfold Record.check
  show (if _ then some (Ty.normalize (.record (Queue.cellFields A))) else none) = _
  have named : (["msgs", "cap", "takers", "offers"] : List String).Nodup := by decide
  rw [if_pos ⟨named, named, fits⟩, cellFields_normal message.canonical]

/-- **The take step is typed at the cell's type**: under the request's identity, its hint and
the cell's value, it answers the pair of a take's reply and the cell's next value. -/
@[semantics "store-typing" (requirement := R4)]
theorem takeStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "hint", "s"] [idTy, idTy, Queue.cellTy A]
        (Queue.takeStep A (var "id") (var "hint") (var "s")) =
      some (.prod (takeReplyTy A) (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact takeStep_types sig atoms A message (idSrc := var "id") (hintSrc := var "hint")
    (cellSrc := var "s") (env := { names := ["id", "hint", "s"] }) (path := [])
    (types := [idTy, idTy, Queue.cellTy A]) rfl (capturedTy_var rfl rfl rfl)
    (capturedTy_var rfl rfl rfl) (types_var rfl rfl rfl) false

/-- **The offer step is typed at the cell's type**: under the request's identity, its hint at
the answer's type, the message and the cell's value. -/
@[semantics "store-typing" (requirement := R4)]
theorem offerStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "hint", "a", "s"] [idTy, Queue.answerTy, A, Queue.cellTy A]
        (Queue.offerStep A (var "id") (var "hint") (var "a") (var "s")) =
      some (.prod offerReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact offerStep_types sig atoms A message (idSrc := var "id") (hintSrc := var "hint")
    (messageSrc := var "a") (cellSrc := var "s") (env := { names := ["id", "hint", "a", "s"] })
    (path := []) (types := [idTy, Queue.answerTy, A, Queue.cellTy A])
    (types_var rfl rfl rfl) (types_var rfl rfl rfl) (types_var rfl rfl rfl)
    (types_var rfl rfl rfl) false

/-- **The poll step is typed at the cell's type.** -/
@[semantics "store-typing" (requirement := R4)]
theorem pollStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["s"] [Queue.cellTy A] (Queue.pollStep A (var "s")) =
      some (.prod (pollReplyTy A) (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact pollStep_types sig atoms A message (cellSrc := var "s") (env := { names := ["s"] })
    (path := []) (types := [Queue.cellTy A]) rfl (types_var rfl rfl rfl) false

/-- **The size step is a number**, over the cell's value. It is no term of a `Ref.modify`. -/
@[semantics "store-typing" (requirement := R4)]
theorem sizeStep_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["s"] [Queue.cellTy A] (Queue.sizeStep A (var "s")) = some .nat :=
  typeAt_of_types (Step.typed sig atoms (env := { names := ["s"] }) (path := [])
    (types := [Queue.cellTy A]) (Input.types_cons (src0 := var "s") (types_var rfl rfl rfl)
      Input.types_nil) (Data.size A) ⟨cellTy_normal message.canonical, trivial⟩ (by trivial) false)

/-- **The withdrawal of a take is typed at the cell's type.** -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawTake_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "s"] [idTy, Queue.cellTy A]
        (Queue.withdrawTake A (var "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact withdrawTake_types sig atoms A message (idSrc := var "id") (cellSrc := var "s")
    (env := { names := ["id", "s"] }) (path := []) (types := [idTy, Queue.cellTy A]) rfl
    (capturedTy_var rfl rfl rfl) (types_var rfl rfl rfl) false

/-- **The withdrawal of an offer is typed at the cell's type.** -/
@[semantics "store-typing" (requirement := R4)]
theorem withdrawOffer_typed (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    (A : Ty) (message : MessageTy A) :
    typeAt sig ["id", "s"] [idTy, Queue.cellTy A]
        (Queue.withdrawOffer A (var "id") (var "s")) =
      some (.prod wakeReplyTy (Queue.cellTy A)) := by
  apply typeAt_of_types
  exact withdrawOffer_types sig atoms A message (idSrc := var "id") (cellSrc := var "s")
    (env := { names := ["id", "s"] }) (path := []) (types := [idTy, Queue.cellTy A]) rfl
    (capturedTy_var rfl rfl rfl) (types_var rfl rfl rfl) false

end Effect4.Queue.Model
