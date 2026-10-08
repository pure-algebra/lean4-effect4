module

public import Effect4.Modules.Queue.Data
meta import Effect4.Modules.Step.Elab.Inputs
public import Effect4.Program.Authoring.Tuples
public import Effect4.Program.Authoring.Folds

/-!
# Modules.Queue.Steps — the Queue's six steps, each one pure term over the cell (row 255)

A step is the pure part of one operation of the Queue's first profile: a positive capacity and
the `suspend` strategy, with `take` and `offer` of one message. Five steps are terms for a
`Ref.modify`: each answers the pair of its reply and the cell's next value. `sizeStep` is a term
over the value that a `Ref.get` answers, and it writes nothing.

| Step | The model's function | Its answer |
| --- | --- | --- |
| `takeStep` | `take` at the bounds one and one | `[message?, accepted offers, takers to wake]` |
| `offerStep` | `offer` | `[decided?, takers to wake]` |
| `pollStep` | `poll` | `[message?, accepted offers]` |
| `sizeStep` | `size` | the buffer's length |
| `withdrawTake` | `withdrawTake` | the takers to wake |
| `withdrawOffer` | `withdrawOffer` | the takers to wake |

The model is `src/Effect4/Laws/Modules/Queue/Model.lean`. The rules of a step (the design's F2,
`docs/research/2026-10-05-claude-lead/queue-readiness/queue-steps-design.md`):

- **A step names its notifications as the model does, and in the model's order**: the offers
  that the step accepted, then the taker to wake. They are lists of the stored request records,
  so a wrapper posts one helper for each record's hint.
- **The six operations translate stored `Step` data** from `Queue.Data`.
- **Captured inputs keep their original caller scope**, through the shared fold compiler.
- **Record construction uses canonical schemas**, and empty constants carry checked ascriptions.
- **A step frames every field that it does not change**: it writes the cell by `recordSet`.
- **The accept pass is the closed form of `acceptLoop_single`**
  (`src/Effect4/Laws/Modules/Queue/Profile.lean`): `take`, `drop` and one fold.

The term language has no local binding, so a step repeats its passes (decisions row 255). Every
builder takes the message type `A` first, and a builder that writes no declaration does not read
it. Nothing here performs an effect: `Queue.make`, `Queue.offer` and `Queue.take` come with the
wrapper, after the mask.

The laws are in `src/Effect4/Laws/Modules/Queue/`: the typing statements (`Typing.lean`), the
relation to the model (`Relation.lean`) and the six step goals (`Steps.lean`). The connectors
of a step to the store are shared (`src/Effect4/Laws/Modules/Store.lean`). The batteries are
under `Test/Program/`: `QueueSteps.lean` (types, sizes and the
hygiene controls), `QueueScenarios.lean` (runs on the machine), `QueueAgreement.lean` (each step
against the model, on every state of a finite universe) and `QueueRelation.lean` (each goal's
conclusion on that universe).
-/

@[expose] public section

namespace Effect4.Queue

open Effect4.Program Effect4.Program.Authoring
open Effect4.Modules

/-! ## The Queue's records

The words of a step term are shared: one application of a native atom each
(`src/Effect4/Modules/Words.lean`). Their consumers here are the two records, the passes and the
steps below. -/

/-- A waiting taker's record. -/
def mkTaker (id hint : TermSrc) : TermSrc := record takerFields [("id", id), ("hint", hint)]

/-- A pending offer's record. -/
def mkOffer (A : Ty) (id hint batch rest : TermSrc) : TermSrc :=
  record (offerFields A) [("id", id), ("hint", hint), ("batch", batch), ("rest", rest)]

/-! ## The passes

Each helper that folds uses `foldWith`: its two names are minted, so a caller's term keeps its
reading inside the body. The two removals are the shared pass `removeById`. -/

/-- Whether the request `id` waits among the takers. -/
def enrolled (takers id : TermSrc) : TermSrc :=
  foldWith takers (bool false) fun found t => orT found (same (field t "id") id)

/-- Whether the request `id` is the earliest taker. -/
def isHead (takers id : TermSrc) : TermSrc :=
  foldWith (app "take" [takers, nat 1]) (bool false) fun _ t => same (field t "id") id

/-- The takers without the request `id`: the shared removal pass. -/
def removeTaker (takers id : TermSrc) : TermSrc := removeById takers id

/-- The takers, with the hint of the request `id` replaced. -/
def renewHint (takers id hint : TermSrc) : TermSrc :=
  foldWith takers (noneOf takers) fun out t =>
    snoc out (ifT (same (field t "id") id) (mkTaker id hint) t)

/-- The pending offers without the request `id`: the shared removal pass. -/
def removeOffer (offers id : TermSrc) : TermSrc := removeById offers id

/-- The model's `wake` in the first profile: the earliest taker, when a message is buffered. A
list of at most one taker. -/
def wake (takers msgs : TermSrc) : TermSrc :=
  ifT (isEmpty msgs) (noneOf takers) (app "take" [takers, nat 1])

/-! The model's accept pass on single offers, in its closed form (`acceptLoop_single`): as many
offers as fit enter, in arrival order. Three terms with one fold. The general pass, with five
values and a stop flag, comes back with the batches. -/

/-- How many pending offers enter the room. -/
def fitting (room offers : TermSrc) : TermSrc := minT room (len offers)

/-- The offers that enter: the step answers them, in arrival order. -/
def entering (room offers : TermSrc) : TermSrc := app "take" [offers, fitting room offers]

/-- The offers that stay pending. -/
def staying (room offers : TermSrc) : TermSrc := app "drop" [offers, fitting room offers]

/-- The buffer with the messages of the offers that enter. -/
def gained (room msgs offers : TermSrc) : TermSrc :=
  foldWith (entering room offers) msgs fun buffer o => app "append" [buffer, field o "rest"]

/-! ## The steps -/

/-- **The model's `take` at the bounds one and one**, as the term of a `Ref.modify` over the
cell `s`. Answer: `[message?, accepted offers, takers to wake]`, the notifications in the
model's order. It consumes when a message is buffered and no earlier taker waits. Otherwise it
enrols the request `id` with its hint, or renews the hint of a request that waits already. -/
def takeStep (A : Ty) (id hint s : TermSrc) : TermSrc :=
  (Data.take A).term (input_sources% (Data.TakeInputs A) {state := s, hint := hint, id := id})

/-- **The model's `offer` under `suspend`**, as the term of a `Ref.modify`. Answer:
`[decided?, takers to wake]`. Behind a pending offer it waits and notifies nobody. With room it
is accepted. At a full buffer it waits, and the model still wakes the earliest taker. -/
def offerStep (A : Ty) (id hint a s : TermSrc) : TermSrc :=
  (Data.offer A).term (input_sources% (Data.OfferInputs A) {state := s, message := a, hint := hint, id := id})

/-- **The model's `poll`**, as the term of a `Ref.modify`. Answer: `[message?, accepted
offers]`. It consumes when a message is buffered and no taker waits, so it wakes no taker. -/
def pollStep (A : Ty) (s : TermSrc) : TermSrc :=
  (Data.poll A).term (input_sources% (Data.CellInputs A) {state := s})

/-- **The model's `size` in an opened queue**: the buffer's length. A term over the value that a
`Ref.get` answers. It is no term of a `Ref.modify`, and it writes nothing. -/
def sizeStep (A : Ty) (s : TermSrc) : TermSrc :=
  (Data.size A).term (input_sources% (Data.CellInputs A) {state := s})

/-- The withdrawal of a taker, translated from its stored step. -/
def withdrawTake (A : Ty) (id s : TermSrc) : TermSrc :=
  (Data.withdrawTake A).term (input_sources% (Data.WithdrawInputs A) {state := s, id := id})

/-- **The model's `withdrawOffer` in an opened queue**, as the term of a `Ref.modify`. Answer:
the takers to wake. An offer that a step already accepted is not there, so only the wake
remains. -/
def withdrawOffer (A : Ty) (id s : TermSrc) : TermSrc :=
  (Data.withdrawOffer A).term (input_sources% (Data.WithdrawInputs A) {state := s, id := id})

namespace Data
theorem sizeStep_eq (A : Ty) (s : TermSrc) : sizeStep A s = (size A).term (Input.source [s]) := rfl
end Data

end Effect4.Queue
