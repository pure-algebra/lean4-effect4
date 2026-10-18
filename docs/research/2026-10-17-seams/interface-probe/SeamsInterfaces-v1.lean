import Effect4

/-!
# The authoring system's seams: the final interfaces, elaborated

Interface probe for `docs/research/2026-10-17-seams/interfaces.md`, at the tree `774ddc3d7`.

- Every data declaration is the proposed one, elaborated against the tree.
- Operations whose bodies are slice work are fields of a `…Spec` structure, so their types
  elaborate without a body.
- Proof-carrying values take their replay function as a parameter (`…Of`).
- Four claims the design rests on are checked here for real: the oracle has one value up to
  equality (§1), a writer trace over it is valid by construction (§1), a hole place resolves only
  at a unique occurrence (§2), and a root guarded by generation refuses A→B→A (§4).

The namespace `SeamsProbe` keeps every name apart from the tree. Nothing here lands.
-/

set_option autoImplicit false
set_option maxRecDepth 20000

namespace SeamsProbe
open Effect4 Effect4.Program Effect4.Store

/-! ## 1. Checking -/

namespace Check

/-- Everything one check reads; its canonical bytes are a complete key. -/
inductive CheckInput where
  /-- a sketch through its layer references, at the application extended by its holes -/
  | module (app : SigApp) (holes : RowTable) (program : NativeEff)
  /-- a part of an expansion, or a filling inside its candidate's expansion, in its context -/
  | part (sig : SigData) (env : TyEnv) (program : NativeEff)

/-- A check's answer, rooted at the empty path. -/
structure Verdict where
  result : Except TypeRefusal EffTy
  table : List Table.Entry

/-- The uncached meaning: the existing owners, unchanged. -/
def run : CheckInput → Verdict
  | .module app holes p =>
      let s : Sketch := { program := p, holes := holes }
      ⟨s.sourceCheck app, s.sourceAnnotate app⟩
  | .part d env q =>
      let o := Annotate.check d.signature env [] q
      ⟨o.2, o.1⟩

/-- A certified oracle: the only way a consumer checks. Its agreement field erases. -/
structure Oracle where
  ask : CheckInput → Verdict
  agrees : ∀ i, ask i = run i

def Oracle.uncached : Oracle := ⟨run, fun _ => rfl⟩

/-- **The oracle has one value up to equality.** So a memo, the store's action cache or
Incremental behind an oracle can change cost and never an answer, for every consumer at once. -/
theorem Oracle.eq_uncached (o : Oracle) : o = Oracle.uncached := by
  cases o with
  | mk ask agrees =>
    have h : ask = run := funext agrees
    subst h
    rfl

/-- The consequence every consumer inherits, with no proof of its own. -/
theorem Oracle.transparent {α : Sort _} (f : Oracle → α) (o : Oracle) :
    f o = f Oracle.uncached := by
  rw [Oracle.eq_uncached o]

/-- The checks a computation asked, each with its answer, in order. -/
abbrev Trace := List (CheckInput × Verdict)

/-- A consumer's result with its trace: a writer over the certified oracle. The trace feeds the
learning adapter and never a reply. -/
structure Checked (α : Type) where
  value : α
  trace : Trace

instance : Monad Checked where
  pure a := ⟨a, []⟩
  bind x f := let y := f x.value; ⟨y.value, x.trace ++ y.trace⟩

def Checked.ask (o : Oracle) (i : CheckInput) : Checked Verdict := ⟨o.ask i, [(i, o.ask i)]⟩

/-- Every trace entry is the uncached answer of its key. -/
def Checked.Valid {α : Type} (x : Checked α) : Prop := ∀ p ∈ x.trace, p.2 = run p.1

theorem Checked.ask_valid (o : Oracle) (i : CheckInput) : (Checked.ask o i).Valid := by
  intro p hp
  simp only [Checked.ask, List.mem_singleton] at hp
  subst hp
  exact o.agrees i

theorem Checked.pure_valid {α : Type} (a : α) : (pure a : Checked α).Valid := by
  intro p hp
  exact nomatch hp

theorem Checked.bind_valid {α β : Type} {x : Checked α} {f : α → Checked β}
    (hx : x.Valid) (hf : ∀ a, (f a).Valid) : (x >>= f).Valid := by
  intro p hp
  simp only [bind, List.mem_append] at hp
  cases hp with
  | inl h => exact hx p h
  | inr h => exact hf x.value p h

/-- The learning adapter: plain data. Validity is a predicate, not a field, so the one place
where entries are trusted is visible: `Oracle.ofMemo` asks for the proof. In Lean only learned
entries can supply it; in OCaml the proof is erased, and the store-backed adapter is that one
trusted call site (a declared host assumption, checked by sampled recomputation). -/
structure Memo where
  entries : List (CheckInput × Verdict)

def Memo.Valid (m : Memo) : Prop := ∀ p ∈ m.entries, p.2 = run p.1

def Memo.empty : Memo := ⟨[]⟩

theorem Memo.empty_valid : Memo.empty.Valid := fun _ h => nomatch h

/-- Learn a trace. -/
def Memo.learn (m : Memo) (t : Trace) : Memo := ⟨t ++ m.entries⟩

theorem Memo.learn_valid {m : Memo} {t : Trace} (hm : m.Valid) (ht : ∀ p ∈ t, p.2 = run p.1) :
    (m.learn t).Valid := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact ht p h
  · exact hm p h

/-- A memo-backed oracle: a hit, else `run`. Key comparison is a parameter here; the
implementation compares canonical bytes. -/
def Oracle.ofMemo (beq : CheckInput → CheckInput → Bool) (lawful : ∀ a b, beq a b = true → a = b)
    (m : Memo) (hm : m.Valid) : Oracle where
  ask i := match m.entries.find? (fun p => beq p.1 i) with
    | some p => p.2
    | none => run i
  agrees i := by
    show (match m.entries.find? (fun p => beq p.1 i) with
      | some p => p.2
      | none => run i) = run i
    split
    · rename_i p hp
      have hmem := List.mem_of_find?_eq_some hp
      have hkey : beq p.1 i = true := List.find?_some (p := fun q : CheckInput × Verdict => beq q.1 i) hp
      rw [hm p hmem, lawful _ _ hkey]
    · rfl

/-- A dependency's role and the projection of its addresses into the module. -/
inductive DepRole where
  /-- a declared body, rebased at its path -/
  | body (index : Nat)
  /-- the main program at `[1]` -/
  | main
  /-- the layer spine: `[0,0] ++ p` projects to `[2] ++ p`; wrapper entries are dropped; an empty
  spine is checked directly, never as the synthetic empty `mergeAll` -/
  | layers

structure Dep where
  role : DepRole
  base : List Nat
  input : CheckInput

inductive Site where
  | address (path : List Nat)
  | inCopy (site path : List Nat)
  | column (at_ : List Nat)
  | application

/-- A located explanation; `part` is set only for a local failure, which it replays. -/
structure Explanation where
  refusal : TypeRefusal
  site : Site
  part : Option CheckInput

structure Spec where
  deps : CheckInput → List Dep
  combine : CheckInput → List Verdict → Verdict
  explain : Oracle → CheckInput → Checked (Option Explanation)
  /-- an imported answer enters only after recomputation agrees; the rest come back refused -/
  memoImport : Memo → List (CheckInput × Verdict) → Memo × List CheckInput

end Check

/-! ## 2. The edit side: one policy-aware feed, and the document over it -/

namespace Edit2

/-- How a feed treats a change of type at its focus. -/
inductive FeedPolicy where
  /-- apply; recheck the whole expansion when the focus's type changes (today's `feed`) -/
  | draft
  /-- accept only an edit whose focus keeps its exact type; refuse without a whole recheck -/
  | keepExact
  /-- apply, recheck, and accept only a sketch that checks -/
  | recheck

inductive FeedRefusal where
  | noProgram (path : List Nat)
  /-- the filling's verdict at its focus is not the focus's exact type -/
  | notKept (focus : TyEnv × EffTy) (verdict : Except TypeRefusal EffTy)
  | typeChanged (old : Option EffTy) (new : EffTy)
  | localChanged (old new : Option (TyEnv × EffTy))
  | refused (why : List TypeRefusal)

structure FeedSpec where
  /-- The one feed. `draft` is today's `SourceSession.feedStep`; `keepExact` asks one part check
  and splices; every check goes through the oracle. -/
  feed : Check.Oracle → FeedPolicy → SourceSession → Edit →
    Check.Checked (Except FeedRefusal (SourceSession × Edit.Step))

/-- Where an edit lands. -/
inductive Place where
  | hole (index : Nat)
  | at_ (path : List Nat) (expected : NativeEff)

inductive PlaceRefusal where
  | outOfRange (index : Nat)
  | absent (index : Nat)
  | repeated (index : Nat) (paths : List (List Nat))
  | moved (path : List Nat)

/-- Resolve a place in a sketch as written: a hole resolves only at its one occurrence. -/
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

/-- The document's history alphabet: one accepted action is one revision. -/
inductive DocAction where
  /-- a checked batch, resolved in order against a temporary document; atomic; one revision -/
  | commit (items : List (Place × Change)) (policy : FeedPolicy)
  | draft (e : Edit)
  /-- an append-only revert of a named earlier action, after a current-target check -/
  | revert (entry : Nat)
  /-- a published fill set: its fills, applied in the base's address order, checked once -/
  | publish (fills : List (List Nat × NativeEff))

structure DocOrigin where
  id : DocId
  app : SigApp
  sketch : Sketch

inductive DocRefusal where
  | empty
  | place (item : Nat) (why : PlaceRefusal)
  | feed (item : Nat) (why : FeedRefusal)
  | revert (entry : Nat) (why : PlaceRefusal)
  | publish (why : MaterializeRefusal)

/-- What an accepted action produced: one step per item, each with the program it replaced. -/
structure Receipt where
  steps : List Edit.Step

/-- The document over its validating replay. -/
structure DocOf (replayDoc : DocOrigin → List DocAction → Except DocRefusal SourceSession) where
  private mk ::
  origin : DocOrigin
  history : List DocAction
  session : SourceSession
  replayed : replayDoc origin history = .ok session

/-- A snapshot's name inside one state, scoped to its base: copied from a reply, never built. -/
structure Snap where
  doc : DocId
  revision : Nat

/-- The fill set over its construction: pending additions certified at a fixed anchor. -/
structure FillSetOf (addRaw : Snap → Sketch → SigApp → List (List Nat × NativeEff) →
    List (List Nat × NativeEff)) where
  private mk ::
  anchor : Snap
  base : Sketch
  app : SigApp
  entries : List (List Nat × NativeEff)
  constructed : ∃ submitted, addRaw anchor base app submitted = entries

structure DocSpec where
  Doc : Type
  open_ : DocOrigin → Check.Checked Doc
  step : Check.Oracle → Doc → DocAction → Check.Checked (Except DocRefusal (Doc × Receipt))
  snap : Doc → Snap
  session : Doc → SourceSession

end Edit2

/-! ## 3. The protocol -/

namespace Tool

structure RunId where
  n : Nat

inductive RunForm where
  | view | record | journal

inductive PreviewQuery where
  | settle (tape : List Machine.ExitV) (limit : Nat)
  | frames (tape : List Machine.ExitV) (limit : Nat)
  | explore (budget width : Nat)

inductive Action where
  | open_ (name : String) (app : SigApp) (sketch : Sketch)
  | edit (at_ : Edit2.Snap) (a : Edit2.DocAction)
  /-- pending additions: per-item outcomes inside a successful answer -/
  | fill (at_ : Edit2.Snap) (batch : List (List Nat × NativeEff))
  | publish (at_ : Edit2.Snap)
  | reset
  | start (at_ : Edit2.Snap) (budget : Api.Budget)
  | restore (record : LiveRecord)
  /-- events folded over a temporary run; an unresolved selector refuses the whole request -/
  | play (run : RunId) (events : List Run.Event)

/-- A client's wanted method versions, for negotiation. -/
structure Wanted where
  method : String
  versions : List Nat

inductive Query where
  | doc (at_ : Option (List Nat))
  | history
  | fills
  | suggest (at_ : Edit2.Snap) (place : Edit2.Place) (supplied : List NativeEff) (cursor limit : Nat)
  | run (id : RunId) (form : RunForm)
  | preview (q : PreviewQuery)
  | dry (a : Action)
  | negotiate (wanted : List Wanted)

inductive Request where
  | act (a : Action)
  | ask (q : Query)

/-- A run's origin, kept as data so it survives later edits. -/
inductive Origin where
  | snapshot (snap : Edit2.Snap) (app : SigApp) (sketch : Sketch)
  | standalone

structure HoleView where
  index : Nat
  row : Row
  path : List Nat
  focus : Option (TyEnv × EffTy)

structure DocView where
  snap : Edit2.Snap
  type : Option EffTy
  refusals : List TypeRefusal
  holes : List HoleView

inductive Refusal where
  | noDocument
  | stale (now : Edit2.Snap)
  | foreign (now : Edit2.Snap)
  | doc (why : Edit2.DocRefusal)
  | fillsStale (anchor now : Edit2.Snap)
  | fillsEmpty
  | admission (why : AdmitRefusal)
  | restore (why : LiveRecord.Refusal)
  | preview (why : Run.Preview.Refusal)
  | noRun (id : RunId)
  | unresolved (id : RunId) (event : Nat) (sel : Run.Sel)
  | noVersion (method : String)

/-- An action's answer; also the payload of a `dry` query. -/
inductive ActionAnswer where
  | opened (view : DocView)
  | edited (view : DocView) (receipt : Edit2.Receipt)
  | filled (outcomes : List AddOutcome)
  | published (view : DocView)
  | reset (discarded : List (List Nat × NativeEff))
  | started (run : RunId) (origin : Origin) (view : Live.View)
  | played (run : RunId) (verdicts : List Run.Verdict) (view : Live.View)
  | restored (run : RunId) (view : Live.View)

structure Candidate where
  program : NativeEff
  fit : Except Edit2.FeedRefusal EffTy
  key : Check.CheckInput

inductive Answer where
  | acted (a : ActionAnswer)
  | doc (view : DocView)
  | history (actions : List Edit2.DocAction)
  | fills (pending : List (List Nat × NativeEff))
  | suggested (candidates : List Candidate) (nextCursor : Option Nat)
  | run (id : RunId) (record : LiveRecord)
  | preview (frames : List Live.View)
  | dry (result : Except Refusal ActionAnswer)
  | negotiated (selected : List (String × Nat))

structure Reply where
  result : Except Refusal Answer
  now : Option Edit2.Snap

/-- The tool's state over the canonical replay of its accepted actions. -/
structure StateOf (Raw : Type) (empty : Raw) (replay : Raw → List Action → Raw) where
  private mk ::
  raw : Raw
  reached : ∃ as : List Action, replay empty as = raw

structure Spec where
  State : Type
  empty : State
  serve : Check.Oracle → State → Request → Check.Checked (State × Reply)
  /-- the accepted actions since `empty`: the persisted form, and the witness's list -/
  transcript : State → List Action

end Tool

/-! ## 4. The store -/

namespace Cas

/-- A root's policy, fixed at creation. -/
inductive RootPolicy where
  | swap
  | journal
  | pin
deriving DecidableEq

/-- What a mover expects: the resident digest and its generation. -/
structure Head (D : Type) where
  digest : D
  generation : Nat
deriving DecidableEq

inductive Move where
  | create (name : String) (policy : RootPolicy) (target : AnyRef)
  | advance (name : String) (expected : Head Digest) (target : AnyRef)
  /-- the only way a result node enters -/
  | record (query result : Digest)

structure Txn where
  nodes : List Node
  moves : List Move

inductive Read where
  | node (d : Digest)
  | root (name : String)
  | results (query : Digest)
  | closure (r : AnyRef)

/-- The store's events: a transaction, or one interrupted after `kept` of its fresh nodes. -/
inductive Event where
  | commit (t : Txn)
  | interrupt (t : Txn) (kept : Nat)

structure CasOf (replay : List Event → Store) where
  private mk ::
  store : Store
  reached : ∃ es : List Event, replay es = store

structure ActionId where
  name : String
  engine : Digest

structure Query (κ : Type) where
  action : ActionId
  input : κ

structure Answered (ρ : Type) where
  query : Digest
  output : ρ

/-- A session's journal entry (kind 7): its transcript, one accepted action per entry. -/
inductive SessionEntry where
  | origin (version : Nat) (engine : Digest)
  | action (parent : Digest) (a : Tool.Action) (after : Option Digest)

/-- A saved run's job (kind 16): the record's identity without its journal. -/
structure Job where
  version : Nat
  app : SigApp
  program : Digest
  session : String
  binding : String
  budget : Api.Budget
  rowNames : List (String × Nat)
  engine : Digest

/-- A saved run's tape segment (kind 17). -/
structure Tape where
  job : Digest
  parent : Option Digest
  commands : List Api.Runner.Command

structure Spec where
  Cas : Type
  empty : Cas
  commit : Cas → Txn → Except Admission Cas
  interrupt : Cas → Txn → Nat → Cas
  read : Cas → Read → List (Digest × Node)

/-! ### A finite control of the root rule, over a digest type `D` -/

structure Root (D : Type) where
  name : String
  policy : RootPolicy
  head : Head D

inductive MoveOutcome where
  | moved | duplicate | stale | pinned | missing
deriving DecidableEq

/-- The rule: an identical target is a duplicate; else the expected head must be resident, and a
pin never moves. (A journal root's parent check needs the carrier and is not modelled here.) -/
def advance {D : Type} [DecidableEq D] (r : Root D) (expected : Head D) (target : D) :
    Root D × MoveOutcome :=
  if r.head.digest = target then (r, .duplicate)
  else if r.policy = .pin then (r, .pinned)
  else if r.head = expected then ({ r with head := ⟨target, r.head.generation + 1⟩ }, .moved)
  else (r, .stale)

def r0 : Root Nat := ⟨"s", .swap, ⟨1, 0⟩⟩
def r1 := (advance r0 ⟨1, 0⟩ 2).1     -- A → B
def r2 := (advance r1 ⟨2, 1⟩ 1).1     -- B → A
-- A writer that read A at generation 0 is refused, though the digest is A again.
#guard (advance r2 ⟨1, 0⟩ 3).2 = .stale
#guard (advance r2 ⟨1, 2⟩ 3).2 = .moved
-- A retry of a completed move is a duplicate, and never overwrites a newer head.
#guard (advance r2 ⟨2, 1⟩ 1).2 = .duplicate
#guard (advance ⟨"p", .pin, ⟨1, 0⟩⟩ ⟨1, 0⟩ 2).2 = .pinned

end Cas

/-! ### A finite control of hole places (Codex's `repeatedHole`) -/

namespace PlaceControl
open Edit2

def app : SigApp := { rows := [Row.hole "ask" .nat] }
def h0 : Row := Row.hole "h0" .nat
def single : Sketch := ⟨.bind (.perform (.external 0) (.lit .unit)) (Sketch.hole app 0), [h0]⟩
def repeated : Sketch := ⟨.bind (Sketch.hole app 0) (Sketch.hole app 0), [h0]⟩

#guard (Place.resolve app single (.hole 0)).toOption.map (·.1) = some [1]
#guard match Place.resolve app repeated (.hole 0) with
  | .error (.repeated 0 [[0], [1]]) => true
  | _ => false
#guard match Place.resolve app single (.hole 1) with
  | .error (.outOfRange 1) => true
  | _ => false
#guard match Place.resolve app single (.at_ [0] (.succeed (.lit (.nat 1)))) with
  | .error (.moved [0]) => true
  | _ => false

end PlaceControl

end SeamsProbe

#eval IO.println "SeamsInterfaces: declarations elaborate; oracle, trace, place and root controls pass"
