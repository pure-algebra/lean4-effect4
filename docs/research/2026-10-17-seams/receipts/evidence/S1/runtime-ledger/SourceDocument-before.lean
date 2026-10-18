import Effect4.Program.Typing.SourceSession
set_option autoImplicit false
set_option maxRecDepth 20000
namespace Effect4.Program
open Check
structure DocId where
  name : String := "default"
  generation : Nat := 0
deriving DecidableEq, Repr
inductive Change where
  | fill (q : NativeEff)
  | omitHole (name : String)
deriving DecidableEq
/-- The checked fold uses the supplied action interpreter once for each accepted prefix item. -/
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

inductive Place where
  | hole (index : Nat)
  | at_ (path : List Nat) (expected : NativeEff)

inductive PlaceRefusal where
  | outOfRange (index : Nat)
  | absent (index : Nat)
  | repeated (index : Nat) (paths : List (List Nat))
  | moved (path : List Nat)

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

structure Snap where
  doc : DocId
  revision : Nat

inductive DocAction where
  | commit (items : List (Place × Change)) (policy : FeedPolicy)
  | draft (e : Edit)
  | revert (entry : Nat)

structure DocOrigin where
  id : DocId
  app : SigApp
  sketch : Sketch

inductive DocRefusal where
  | foreign (expected : DocId)
  | stale (now : Snap)
  | empty
  | noEntry (entry : Nat)
  | place (item : Nat) (why : PlaceRefusal)
  | feed (item : Nat) (why : FeedRefusal)

structure Receipt where
  steps : List Edit.Step

namespace DocInternal
structure UndoItem where
  path : List Nat
  before : NativeEff
  product : NativeEff

structure Entry where
  policy : FeedPolicy
  items : List UndoItem

structure State where
  session : SourceSession
  entries : List Entry

structure Fresh where
  session : SourceSession
  receipt : Receipt
  entry : Entry

def record (s : SourceSession) (step : Edit.Step) : List UndoItem :=
  match step.replaced, (Node.eff s.sketch.program).at_ step.edit.path with
  | some before, some (.eff product) => [⟨step.edit.path, before, product⟩]
  | _, _ => []

def editOf (s : SourceSession) (path : List Nat) : Change → Except FeedRefusal Edit
  | .fill q => .ok (.fill path q)
  | .omitHole name =>
    match s.focusAt path with
    | some focus => .ok (.omitAt path (Row.hole name focus.ty.answer focus.ty.error focus.ty.requires.elems))
    | none => .error (.noFocus path)

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

def advance (st : State) : Except DocRefusal Fresh → Except (Nat × DocRefusal) State
  | .error why => .error (st.entries.length, why)
  | .ok fresh => .ok ⟨fresh.session, st.entries ++ [fresh.entry]⟩

def replayStep (o : Oracle) (current : Except (Nat × DocRefusal) State) (a : DocAction) :
    Checked (Except (Nat × DocRefusal) State) := do
  match current with
  | .error why => pure (.error why)
  | .ok st =>
    let out ← apply o st a
    pure (advance st out)

def initial (o : Oracle) (origin : DocOrigin) : Checked (Except (Nat × DocRefusal) State) := do
  let s ← SourceSession.«open» o origin.app origin.sketch
  pure (.ok ⟨s, []⟩)

def replayChecked (o : Oracle) (origin : DocOrigin) (history : List DocAction) :
    Checked (Except (Nat × DocRefusal) State) :=
  Checked.fold (replayStep o) (initial o origin) history

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

def replayDoc (origin : DocOrigin) (history : List DocAction) : Except (Nat × DocRefusal) SourceSession :=
  (DocInternal.replayState origin history).map (·.session)

structure Doc where
  private mk ::
  origin : DocOrigin
  history : List DocAction
  session : SourceSession
  replayed : replayDoc origin history = .ok session

namespace Doc
open DocInternal

def snap (d : Doc) : Snap := ⟨d.origin.id, d.history.length⟩

def id (d : Doc) : DocId := d.origin.id
def revision (d : Doc) : Nat := d.history.length

def check (d : Doc) (at_ : Snap) : Except DocRefusal Unit :=
  if at_.doc ≠ d.origin.id then .error (.foreign d.origin.id)
  else if at_.revision ≠ d.history.length then .error (.stale d.snap)
  else .ok ()

def open_ (origin : DocOrigin) : Checked Doc :=
  let c := SourceSession.«open» Oracle.uncached origin.app origin.sketch
  let answer : Doc := ⟨origin, [], c.value, rfl⟩
  c.bind' fun _ => pure answer

/-- Helper of step_replay; seal a known successful full replay state. -/
theorem sealReplay {o : Oracle} {d : Doc} {st : State} {action : DocAction} {fresh : Fresh}
    (hp : replayState d.origin d.history = .ok st)
    (ha : (apply o st action).value = .ok fresh) :
    replayDoc d.origin (d.history ++ [action]) = .ok fresh.session := by
  rw [Oracle.eq_uncached o] at ha
  unfold replayDoc
  rw [replayState_snoc, hp]
  change (advance st (apply Oracle.uncached st action).value).map (·.session) = _
  rw [ha]
  rfl

/-- Helper of step_replay; a new entry does not inspect older undo receipts. -/
theorem sealFresh {o : Oracle} (d : Doc) {action : DocAction} {fresh : Fresh}
    (ha : ∀ st : State, st.session = d.session → (apply o st action).value = .ok fresh) :
    replayDoc d.origin (d.history ++ [action]) = .ok fresh.session := by
  cases hp : replayState d.origin d.history with
  | error why =>
    have h := d.replayed
    change (replayState d.origin d.history).map (·.session) = _ at h
    rw [hp] at h
    contradiction
  | ok st =>
    have h := d.replayed
    change (replayState d.origin d.history).map (·.session) = _ at h
    rw [hp] at h
    have hs : st.session = d.session := Except.ok.inj h
    exact sealReplay hp (ha st hs)

/-- Reconstruct receipts only when a revert needs them, through the canonical action interpreter. -/
def past (o : Oracle) (d : Doc) : Checked State :=
  let c := replayChecked o d.origin d.history
  let st := match h : c.value with
    | .ok st => st
    | .error why => False.elim (by
        have hd := d.replayed
        change (replayState d.origin d.history).map (·.session) = _ at hd
        rw [← replayChecked_value o d.origin d.history, h] at hd
        contradiction)
  c.bind' fun _ => pure st

/-- Helper of step_replay; reconstructed receipts name the already validated history. -/
theorem past_valid (o : Oracle) (d : Doc) :
    replayState d.origin d.history = .ok (past o d).value := by
  unfold past
  dsimp only [Checked.bind', Checked.pure']
  split
  · rename_i st h
    exact (replayChecked_value o d.origin d.history).symm.trans h
  · rename_i why h
    have hd := d.replayed
    change (replayState d.origin d.history).map (·.session) = _ at hd
    rw [← replayChecked_value o d.origin d.history, h] at hd
    contradiction

/-- A validated new entry uses the current session without replaying earlier entries. -/
def freshStep (o : Oracle) (d : Doc) (action : DocAction)
    (independent : ∀ a b : State, a.session = b.session → apply o a action = apply o b action) :
    Checked (Except DocRefusal (Doc × Receipt)) :=
  let c := apply o ⟨d.session, []⟩ action
  let answer := match h : c.value with
    | .error why => .error why
    | .ok fresh => .ok (⟨d.origin, d.history ++ [action], fresh.session,
        sealFresh d (fun st hs => by
          rw [independent st ⟨d.session, []⟩ hs]
          exact h)⟩, fresh.receipt)
  c.bind' fun _ => pure answer

/-- One accepted action adds one history entry. A refusal returns no replacement document. -/
def step (o : Oracle) (d : Doc) (at_ : Snap) (action : DocAction) :
    Checked (Except DocRefusal (Doc × Receipt)) := do
  match d.check at_ with
  | .error why => pure (.error why)
  | .ok () =>
    match action with
    | .commit items policy => freshStep o d (.commit items policy) (by
        intro a b h
        cases items with
        | nil => rfl
        | cons item rest => simp only [apply, h])
    | .draft edit => freshStep o d (.draft edit) (by
        intro a b h
        simp only [apply, h])
    | .revert index =>
      let p := past o d
      let c := apply o p.value (.revert index)
      let answer := match h : c.value with
        | .error why => .error why
        | .ok fresh => .ok (⟨d.origin, d.history ++ [.revert index], fresh.session,
            sealReplay (past_valid o d) h⟩, fresh.receipt)
      p.bind' fun _ => c.bind' fun _ => pure answer

end Doc

end Effect4.Program
