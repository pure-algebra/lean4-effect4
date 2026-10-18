import Effect4.Program.Typing.SourceSession

/-!
# Program.Typing.SourceDocument — a document as its accepted actions

**The question.** A tool edits one program over many requests, and two writers may share it. A
revision number alone does not name a history. A document here is its origin and its accepted
actions. Its state is what the actions replay to, and its proof field says so (`Doc.replayedState`).
Only the origin and the history persist; a load replays them and refuses a failed action by its
index.

## The face

| Operation | It takes | It answers |
| --- | --- | --- |
| `Doc.open_` | an origin: identity, application and sketch | a document with an empty history |
| `Doc.check` | a document and a snapshot | `foreign`, then `stale`, or acceptance |
| `Doc.step` | an oracle, a document, a snapshot and an action | the next document and a receipt, or a refusal |
| `Doc.snap` | a document | its identity and revision; the revision is the history's length |
| `replayDoc` | an origin and a history | the replayed session, or the first refused action's index |
| `Place.resolve` | an application, a sketch and a place | the address and its sub-program, or a place refusal |

## The actions

One interpreter, `DocInternal.apply`, runs every action. `Doc.step` and the replay both call it.

- **`commit`** runs its items in order, each against the session the earlier items left. The place
  resolves first, then the policy feed. The first refusal refuses the batch, so the caller keeps
  the old document. An empty batch refuses `empty`. A commit is one revision.
- **`draft`** feeds one edit under the draft policy.
- **`revert`** names an entry. It undoes the entry's items in reverse order, under the entry's own
  policy. Each item first checks that the current sub-program equals the item's product. An
  omission's hole row stays.

The undo ledger lives in the replayed state (`DocInternal.State`), never in persistence. Equal
sessions with different histories can select different inverses, so the ledger cannot be read off
a session.

## What this module is not

- It runs no program, and it decides no admission.
- It persists nothing; `Doc.history` is what a store keeps.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
namespace Effect4.Program
open Check

/-- **A document's identity**: a name and an opening generation that the session owner allocates. -/
structure DocId where
  name : String := "default"
  generation : Nat := 0
deriving DecidableEq, Repr

/-- **What a commit item does** at its resolved address. -/
inductive Change where
  /-- put the program at the address -/
  | fill (q : NativeEff)
  /-- declare a hole with the focus's type and put it at the address -/
  | omitHole (name : String)
deriving DecidableEq

/-- **The checked fold**: the supplied action interpreter runs once for each item, in order. -/
def Checked.fold {σ α : Type} (f : σ → α → Checked σ) (initial : Checked σ)
    (xs : List α) : Checked σ :=
  xs.foldl (fun current a => current.bind' (fun s => f s a)) initial

/-- Helper of step_replay; the checked fold's value is the ordinary fold of action values. -/
theorem Checked.fold_value {σ α : Type} (f : σ → α → Checked σ)
    (initial : Checked σ) (xs : List α) :
    (Checked.fold f initial xs).value = xs.foldl (fun s a => (f s a).value) initial.value := by
  induction xs generalizing initial with
  | nil => rfl
  | cons a rest ih =>
    change (Checked.fold f (initial.bind' (fun s => f s a)) rest).value = _
    rw [ih]
    rfl

/-- **Where a commit item acts.** -/
inductive Place where
  /-- the one occurrence of the hole with this index in the hole table -/
  | hole (index : Nat)
  /-- the address, which must still hold the expected sub-program -/
  | at_ (path : List Nat) (expected : NativeEff)

/-- **Why a place does not resolve.** -/
inductive PlaceRefusal where
  /-- the hole table has no row with this index -/
  | outOfRange (index : Nat)
  /-- the program holds no occurrence of the hole -/
  | absent (index : Nat)
  /-- the program holds the hole at more than one address -/
  | repeated (index : Nat) (paths : List (List Nat))
  /-- the address no longer holds the expected sub-program -/
  | moved (path : List Nat)

/-- **Resolve a place** in a sketch: the address and the sub-program it holds. A hole resolves only
where it occurs exactly once. -/
def Place.resolve (app : SigApp) (s : Sketch) : Place → Except PlaceRefusal (List Nat × NativeEff)
  | .hole k =>
    if k < s.holes.length then
      let q := Sketch.hole app k
      match (Node.addresses (.eff s.program)).filter
          (fun p => decide ((Node.eff s.program).at_ p = some (.eff q))) with
      | [] => .error (.absent k)
      | [p] => .ok (p, q)
      | ps => .error (.repeated k ps)
    else .error (.outOfRange k)
  | .at_ p q =>
    if (Node.eff s.program).at_ p = some (.eff q) then .ok (p, q) else .error (.moved p)

/-- **A snapshot**: the document and the revision a caller read. -/
structure Snap where
  doc : DocId
  revision : Nat
deriving DecidableEq

/-- **A document action**: the unit of a document's history. -/
inductive DocAction where
  /-- feed the items in order under one policy, as one revision -/
  | commit (items : List (Place × Change)) (policy : FeedPolicy)
  /-- feed one edit under the draft policy -/
  | draft (e : Edit)
  /-- undo the accepted entry with this index -/
  | revert (entry : Nat)

/-- **Where a document starts**: its identity, its application and its sketch. -/
structure DocOrigin where
  id : DocId
  app : SigApp
  sketch : Sketch

/-- **Why a document refuses an action.** The refusal returns no document. -/
inductive DocRefusal where
  /-- the snapshot names another document; the receiving document's identity is given -/
  | foreign (expected : DocId)
  /-- the snapshot names another revision; the current snapshot is given -/
  | stale (now : Snap)
  /-- a commit with no items -/
  | empty
  /-- a revert of an entry the history does not hold -/
  | noEntry (entry : Nat)
  /-- the item with this index did not resolve its place -/
  | place (item : Nat) (why : PlaceRefusal)
  /-- the item with this index was refused by the feed -/
  | feed (item : Nat) (why : FeedRefusal)

/-- **What an accepted action did**: the journal's steps, in order. -/
structure Receipt where
  steps : List Edit.Step

namespace DocInternal

/-- **One undo item**: the address, the sub-program the edit replaced, and the one it put there. -/
structure UndoItem where
  path : List Nat
  before : NativeEff
  product : NativeEff

/-- **One entry of the undo ledger**: an accepted action's policy and its items. -/
structure Entry where
  policy : FeedPolicy
  items : List UndoItem

/-- **The replayed state**: the session, and one ledger entry per accepted action. -/
structure State where
  session : SourceSession
  entries : List Entry

/-- **What one accepted action produces**: the session, the receipt and the ledger entry. -/
structure Fresh where
  session : SourceSession
  receipt : Receipt
  entry : Entry

/-- **The undo item of a step**: where the edit replaced a program and the new session holds one. -/
def record (s : SourceSession) (step : Edit.Step) : List UndoItem :=
  match step.replaced, (Node.eff s.sketch.program).at_ step.edit.path with
  | some before, some (.eff product) => [⟨step.edit.path, before, product⟩]
  | _, _ => []

/-- **The edit a change makes** at a resolved address. An omission takes the focus's type. -/
def editOf (s : SourceSession) (path : List Nat) : Change → Except FeedRefusal Edit
  | .fill q => .ok (.fill path q)
  | .omitHole name =>
    match s.focusAt path with
    | some focus => .ok (.omitAt path (Row.hole name focus.ty.answer focus.ty.error focus.ty.requires.elems))
    | none => .error (.noFocus path)

/-- **A commit's batch**: each item against the session the earlier items left; the first refusal
refuses the batch. -/
def batch (o : Oracle) (policy : FeedPolicy) (s : SourceSession) (index : Nat) :
    List (Place × Change) → Checked (Except DocRefusal Fresh)
  | [] => pure (.ok ⟨s, ⟨[]⟩, ⟨policy, []⟩⟩)
  | (place, change) :: rest => do
    match place.resolve s.app s.sketch with
    | .error why => pure (.error (.place index why))
    | .ok (path, _) =>
      match editOf s path change with
      | .error why => pure (.error (.feed index why))
      | .ok edit =>
        match ← s.feed o policy edit with
        | .error why => pure (.error (.feed index why))
        | .ok (next, step) =>
          match ← batch o policy next (index + 1) rest with
          | .error why => pure (.error why)
          | .ok later => pure (.ok ⟨later.session, ⟨step :: later.receipt.steps⟩,
              ⟨policy, record next step ++ later.entry.items⟩⟩)

/-- **A revert's inverses**: each item checks its product is still in place, then feeds the
replaced sub-program back under the entry's policy. -/
def undoItems (o : Oracle) (policy : FeedPolicy) (s : SourceSession) (index : Nat) :
    List UndoItem → Checked (Except DocRefusal Fresh)
  | [] => pure (.ok ⟨s, ⟨[]⟩, ⟨policy, []⟩⟩)
  | item :: rest => do
    match (Place.at_ item.path item.product).resolve s.app s.sketch with
    | .error why => pure (.error (.place index why))
    | .ok _ =>
      match ← s.feed o policy (.fill item.path item.before) with
      | .error why => pure (.error (.feed index why))
      | .ok (next, step) =>
        match ← undoItems o policy next (index + 1) rest with
        | .error why => pure (.error why)
        | .ok later => pure (.ok ⟨later.session, ⟨step :: later.receipt.steps⟩,
            ⟨policy, record next step ++ later.entry.items⟩⟩)

/-- The sole document action interpreter. The replay and public step both use it. -/
def apply (o : Oracle) (st : State) : DocAction → Checked (Except DocRefusal Fresh)
  | .commit [] _ => pure (.error .empty)
  | .commit items policy => batch o policy st.session 0 items
  | .draft edit => do
    match ← st.session.feed o .draft edit with
    | .error why => pure (.error (.feed 0 why))
    | .ok (next, step) => pure (.ok ⟨next, ⟨[step]⟩, ⟨.draft, record next step⟩⟩)
  | .revert index =>
    match st.entries[index]? with
    | none => pure (.error (.noEntry index))
    | some entry => undoItems o entry.policy st.session 0 entry.items.reverse

/-- **Advance the replayed state** by an action's answer; a refusal carries the action's index. -/
def advance (st : State) : Except DocRefusal Fresh → Except (Nat × DocRefusal) State
  | .error why => .error (st.entries.length, why)
  | .ok fresh => .ok ⟨fresh.session, st.entries ++ [fresh.entry]⟩

/-- **One replay step**: a refused prefix stays refused; otherwise the interpreter runs once. -/
def replayStep (o : Oracle) (current : Except (Nat × DocRefusal) State) (a : DocAction) :
    Checked (Except (Nat × DocRefusal) State) := do
  match current with
  | .error why => pure (.error why)
  | .ok st =>
    let out ← apply o st a
    pure (advance st out)

/-- **The replay's start**: the origin's session and an empty ledger. -/
def initial (o : Oracle) (origin : DocOrigin) : Checked (Except (Nat × DocRefusal) State) := do
  let s ← SourceSession.«open» o origin.app origin.sketch
  pure (.ok ⟨s, []⟩)

/-- **Replay a history** through the oracle, recording every check. -/
def replayChecked (o : Oracle) (origin : DocOrigin) (history : List DocAction) :
    Checked (Except (Nat × DocRefusal) State) :=
  Checked.fold (replayStep o) (initial o origin) history

/-- **The replayed state** of a history: the uncached replay's value. -/
def replayState (origin : DocOrigin) (history : List DocAction) : Except (Nat × DocRefusal) State :=
  history.foldl (fun st a => (replayStep Oracle.uncached st a).value)
    (initial Oracle.uncached origin).value

/-- Helper of step_replay; the supplied oracle changes no replay value. -/
theorem replayChecked_value (o : Oracle) (origin : DocOrigin) (history : List DocAction) :
    (replayChecked o origin history).value = replayState origin history := by
  rw [Oracle.eq_uncached o]
  exact Checked.fold_value _ _ _

/-- Helper of step_replay; replay appends one application of the same interpreter. -/
theorem replayState_snoc (origin : DocOrigin) (history : List DocAction) (a : DocAction) :
    replayState origin (history ++ [a]) =
      (replayStep Oracle.uncached (replayState origin history) a).value := by
  unfold replayState
  rw [List.foldl_append]
  rfl
end DocInternal

/-- **Replay a document**: the session its history replays to, or the first refused action. -/
def replayDoc (origin : DocOrigin) (history : List DocAction) : Except (Nat × DocRefusal) SourceSession :=
  (DocInternal.replayState origin history).map (·.session)

/-- A sealed document retains the full state produced by its accepted actions.
Only origin and history persist; replay reconstructs this runtime state. -/
structure Doc where
  private mk ::
  origin : DocOrigin
  history : List DocAction
  runtime : DocInternal.State
  replayedState : DocInternal.replayState origin history = .ok runtime

namespace Doc
open DocInternal

/-- **The document's session**: the replayed state's. -/
def session (d : Doc) : SourceSession := d.runtime.session

/-- Helper of step_replay: the retained runtime witness gives the same source-session observation. -/
theorem replayed (d : Doc) : replayDoc d.origin d.history = .ok d.session := by
  unfold replayDoc
  rw [d.replayedState]
  rfl

/-- **The current snapshot**: the identity and the history's length. -/
def snap (d : Doc) : Snap := ⟨d.origin.id, d.history.length⟩

/-- The document's identity. -/
def id (d : Doc) : DocId := d.origin.id
/-- The document's revision: the number of accepted actions. -/
def revision (d : Doc) : Nat := d.history.length

/-- **Check a snapshot**: another document refuses `foreign`, then another revision `stale`. -/
def check (d : Doc) (at_ : Snap) : Except DocRefusal Unit :=
  if at_.doc ≠ d.origin.id then .error (.foreign d.origin.id)
  else if at_.revision ≠ d.history.length then .error (.stale d.snap)
  else .ok ()

/-- **Open** a document at its origin, with an empty history. -/
def open_ (origin : DocOrigin) : Checked Doc :=
  let c := SourceSession.«open» Oracle.uncached origin.app origin.sketch
  let answer : Doc := ⟨origin, [], ⟨c.value, []⟩, rfl⟩
  c.bind' fun _ => pure answer

/-- Helper of step_replay: one action extends the complete replay witness and its undo ledger. -/
theorem sealRuntime {o : Oracle} (d : Doc) {action : DocAction} {fresh : Fresh}
    (ha : (apply o d.runtime action).value = .ok fresh) :
    replayState d.origin (d.history ++ [action]) =
      .ok ⟨fresh.session, d.runtime.entries ++ [fresh.entry]⟩ := by
  rw [Oracle.eq_uncached o] at ha
  rw [replayState_snoc, d.replayedState]
  change advance d.runtime (apply Oracle.uncached d.runtime action).value = _
  rw [ha]
  rfl

/-- One accepted action adds one history entry. A refusal returns no replacement document.
Every action reads the retained runtime ledger and calls the sole interpreter once. -/
def step (o : Oracle) (d : Doc) (at_ : Snap) (action : DocAction) :
    Checked (Except DocRefusal (Doc × Receipt)) := do
  match d.check at_ with
  | .error why => pure (.error why)
  | .ok () =>
    let c := apply o d.runtime action
    let answer := match h : c.value with
      | .error why => .error why
      | .ok fresh => .ok (⟨d.origin, d.history ++ [action],
          ⟨fresh.session, d.runtime.entries ++ [fresh.entry]⟩,
          sealRuntime d h⟩, fresh.receipt)
    c.bind' fun _ => pure answer

end Doc

end Effect4.Program
