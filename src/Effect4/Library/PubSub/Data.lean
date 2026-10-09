module
public import Effect4.Library.PubSub.Cell
public import Effect4.Step.Inputs
public import Effect4.Step.Lists
meta import Effect4.Step.Elab
meta import Effect4.Step.Elab.Inputs

/-! Six pure single-slot operations over named inputs and existing Step folds.
No waiter, publisher backlog, delivery, scope or identity allocation enters these terms. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.PubSub.Data
open Effect4.Program Effect4.Modules

step_context% CellInputs (cell : cellTy)
step_context% NamedInputs (id : .nat, cell : cellTy)
step_context% PublishInputs (message : .nat, cell : cellTy)

def initial : Step [] cellTy := record_step% {
  value := .none, remaining := .nat 0, publisherIndex := .nat 0, subscribers := .nil }

def subscribe : Step NamedInputs.types (.prod .unit cellTy) := step_inputs% NamedInputs =>
  .pair .unit (.set cell subscribersF (.snoc (.get cell subscribersF)
    (record_step% { id := id, cursor := .get cell publisherIndexF })))

def tryPublish : Step PublishInputs.types (.prod .bool cellTy) := step_inputs% PublishInputs =>
  .ite (.not (.isZero (.get cell remainingF))) (.pair (.bool false) cell)
    (.ite (.isZero (.len (.get cell subscribersF))) (.pair (.bool true) cell)
      (.pair (.bool true) (.set (.set (.set cell valueF (.some message))
        remainingF (.len (.get cell subscribersF))) publisherIndexF
          (.add (.get cell publisherIndexF) (.nat 1)))))

def unread {Γ : List Ty} (cell : Step Γ cellTy) (id : Step Γ .nat) : Step Γ .bool :=
  let subscribers := Step.get cell subscribersF
  Step.Lists.any subscribers (item_step% subscribers with sub =>
    .and (.eq (.get sub idF) id) (.not (.eq (.get sub cursorF) (.get cell publisherIndexF))))

def markRead {Γ : List Ty} (cell : Step Γ cellTy) (id : Step Γ .nat) :
    Step Γ (.list subscriberTy) :=
  let subscribers := Step.get cell subscribersF
  Step.Lists.map subscribers (item_step% subscribers with sub =>
    .ite (.eq (.get sub idF) id) (.set sub cursorF (.get cell publisherIndexF)) sub)

def poll : Step NamedInputs.types (.prod (.option .nat) cellTy) := step_inputs% NamedInputs =>
  let remaining := Step.sub (.get cell remainingF) (.nat 1)
  .ite (.or (.isZero (.get cell remainingF)) (.not (unread cell id))) (.pair .none cell)
    (.pair (.get cell valueF)
      (.set (.set (.set cell remainingF remaining) valueF
        (.ite (.isZero remaining) .none (.get cell valueF))) subscribersF (markRead cell id)))

def registered {Γ : List Ty} (cell : Step Γ cellTy) (id : Step Γ .nat) : Step Γ .bool :=
  let subscribers := Step.get cell subscribersF
  Step.Lists.any subscribers (item_step% subscribers with sub => .eq (.get sub idF) id)

def remove {Γ : List Ty} (cell : Step Γ cellTy) (id : Step Γ .nat) : Step Γ (.list subscriberTy) :=
  let subscribers := Step.get cell subscribersF
  Step.Lists.removeBy subscribers (item_step% subscribers with sub => .eq (.get sub idF) id)

def unsubscribe : Step NamedInputs.types (.prod .unit cellTy) := step_inputs% NamedInputs =>
  let remaining := Step.ite (.and (.not (.isZero (.get cell remainingF))) (unread cell id))
    (.sub (.get cell remainingF) (.nat 1)) (.get cell remainingF)
  .ite (.not (registered cell id)) (.pair .unit cell)
    (.pair .unit (.set (.set (.set cell remainingF remaining) valueF
      (.ite (.isZero remaining) .none (.get cell valueF))) subscribersF
        (remove cell id)))

def slide : Step CellInputs.types (.prod .unit cellTy) := step_inputs% CellInputs =>
  .ite (.isZero (.get cell remainingF)) (.pair .unit cell)
    (.pair .unit (.set (.set cell remainingF (.nat 0)) valueF .none))
end Effect4.PubSub.Data
