import Effect4

/-!
# The authoring system's seams: the final interfaces, elaborated (version 2)

Interface probe for `docs/research/2026-10-17-seams/interfaces.md` version 2, at the tree `774ddc3d7`.
Version 1 is `SeamsInterfaces-v1.lean` beside it, the text that `../self-review.md` reviewed.

- Every data declaration is the proposed one, elaborated against the tree.
- Operations whose bodies are slice work are fields of a `…Spec` structure, so their types
  elaborate without a body. Some `Spec`s also carry law statements as `Prop` fields: their types
  elaborate here, and their proofs are slice work.
- Proof-carrying values take their replay function as a parameter (`…Of`).
- Checked here for real:
  - the oracle has one value up to equality, and every consumer inherits it (§1);
  - `Checked` and `Memo` carry their validity, so a trace or a memo is valid by construction (§1);
  - a memo answers through any sound hit rule and still agrees with `run` (§1);
  - the tool state keeps its transcript as data, and reachability follows from it (§3);
  - a hole place resolves only at a unique occurrence (§2 control);
  - a root guarded by a generation refuses A→B→A and an obsolete retry, stale first (§4 control).

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
  /-- a sketch through its layer references, at the application extended by its holes; the root
  address `[]` is always checked through this key -/
  | module (app : SigApp) (holes : RowTable) (program : NativeEff)
  /-- a part of an expansion, or a filling inside its candidate's expansion, in its context -/
  | part (sig : SigData) (env : TyEnv) (program : NativeEff)
deriving DecidableEq

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

/-- **The oracle has one value up to equality.** So a memo or Incremental behind an oracle can
change cost and never an answer, for every consumer at once. -/
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

/-- Every entry is the uncached answer of its key. -/
def TraceValid (t : Trace) : Prop := ∀ p ∈ t, p.2 = run p.1

/-- A consumer's result with its trace: a writer over the certified oracle. The constructor is
private and the validity is a field, so the only traces are those `pure`, `bind` and `ask` build.
The generated OCaml interface keeps the whole package abstract; the trace feeds `Memo.learn` and
never a reply. -/
structure Checked (α : Type) where
  private mk ::
  value : α
  trace : Trace
  valid : TraceValid trace

namespace Checked

def pure' {α : Type} (a : α) : Checked α := ⟨a, [], fun _ h => nomatch h⟩

def bind' {α β : Type} (x : Checked α) (f : α → Checked β) : Checked β :=
  ⟨(f x.value).value, x.trace ++ (f x.value).trace, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact x.valid p h
    · exact (f x.value).valid p h⟩

instance : Monad Checked where
  pure := pure'
  bind := bind'

/-- Ask the oracle and record the key with its answer. The implementation's module arm asks its
parts first and combines them (`combine_deps`), so the parts are learned too. -/
def ask (o : Oracle) (i : CheckInput) : Checked Verdict :=
  ⟨o.ask i, [(i, o.ask i)], fun p hp => by
    simp only [List.mem_singleton] at hp
    subst hp
    exact o.agrees i⟩

theorem ask_value (o : Oracle) (i : CheckInput) : (ask o i).value = run i := o.agrees i

end Checked

/-- The learning memo, in-process only. The constructor is private and the validity is a field:
the only memos are `empty` and what `learn` builds from `Checked` traces. Nothing imports
entries, so no call site is trusted; in OCaml the memo's trust is the generated code's, the
existing lowering boundary. -/
structure Memo where
  private mk ::
  entries : Trace
  valid : TraceValid entries

def Memo.empty : Memo := ⟨[], fun _ h => nomatch h⟩

def Memo.learn {α : Type} (m : Memo) (c : Checked α) : Memo :=
  ⟨c.trace ++ m.entries, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact c.valid p h
    · exact m.valid p h⟩

/-- When an entry may answer an asked key. A rule is sound when a valid entry it selects is the
uncached answer of the asked key; the oracle's agreement then follows for every memo. -/
structure HitRule where
  hit : CheckInput → CheckInput × Verdict → Bool
  sound : ∀ i e, hit i e = true → e.2 = run e.1 → e.2 = run i

/-- An exact hit: the entry's key is the asked key. -/
def HitRule.exact : HitRule where
  hit i e := decide (e.1 = i)
  sound i e h he := by
    have hk : e.1 = i := of_decide_eq_true h
    rw [he, hk]

/-- Either rule. -/
def HitRule.or (r s : HitRule) : HitRule where
  hit i e := r.hit i e || s.hit i e
  sound i e h he := by
    simp only [Bool.or_eq_true] at h
    cases h with
    | inl h => exact r.sound i e h he
    | inr h => exact s.sound i e h he

/-- A memo-backed oracle under a sound hit rule: a hit, else `run`. -/
def Memo.oracle (m : Memo) (r : HitRule) : Oracle where
  ask i := match m.entries.find? (r.hit i) with
    | some e => e.2
    | none => run i
  agrees i := by
    show (match m.entries.find? (r.hit i) with
      | some e => e.2
      | none => run i) = run i
    split
    · rename_i e he
      exact r.sound i e (List.find?_some (p := r.hit i) he)
        (m.valid e (List.mem_of_find?_eq_some he))
    · rfl

/-! Implementation data of `Check`, not its interface. -/
namespace Internal

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

end Internal

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
  /-- today's prefix-extension hit: a positive part verdict answers at a row table that extends its
  own; its `sound` field is the planned law `run_part_extends` -/
  extension : HitRule
  explain : Oracle → CheckInput → Checked (Option Explanation)
  /-- internal: the module arm's parts and their combination; `combine_deps` is their law -/
  deps : CheckInput → List Internal.Dep
  combine : CheckInput → List Verdict → Verdict

end Check

/-! ## 2. The edit side: one policy-aware feed, the document, the fill set -/

namespace Edit2

/-- How a feed treats a change of type at its focus. -/
inductive FeedPolicy where
  /-- apply; recheck the whole expansion when the focus's type changes (today's `feed`) -/
  | draft
  /-- accept only an edit whose focus keeps its exact type. Below the root it asks one part check
  inside the candidate's expansion: not kept refuses with no whole recheck; kept splices when the
  whole expanded edit agrees, and otherwise rechecks and compares the types. At the root it checks
  the module key and compares the root type. -/
  | keepExact
  /-- apply, recheck, and accept only a sketch that checks -/
  | recheck

/-- In this order: the address, the focus, the part's fit, then the whole expansion. -/
inductive FeedRefusal where
  | noProgram (path : List Nat)
  | noFocus (path : List Nat)
  /-- the filling's verdict at its focus is not the focus's exact type -/
  | notKept (focus : TyEnv × EffTy) (verdict : Except TypeRefusal EffTy)
  | refused (why : List TypeRefusal)
  | typeChanged (old : Option EffTy) (new : EffTy)
  | localChanged (old new : Option (TyEnv × EffTy))

structure FeedSpec where
  /-- The one feed. `draft` is today's `SourceSession.feedStep`; every check goes through the
  oracle. -/
  feed : Check.Oracle → FeedPolicy → SourceSession → Edit →
    Check.Checked (Except FeedRefusal (SourceSession × Edit.Step))
  /-- the one owner of part keys: the key of a filling at a non-root address, inside the
  candidate's expansion; `none` at the root and where no program is -/
  partKey : SourceSession → List Nat → NativeEff → Option Check.CheckInput

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

/-- A snapshot's name inside one state, scoped to its base: copied from a reply, never built. -/
structure Snap where
  doc : DocId
  revision : Nat

/-- The document's history alphabet: one accepted action is one revision. Publication is a
`commit` built by the fill set, so it has no constructor of its own. -/
inductive DocAction where
  /-- a checked batch, resolved in order against a temporary document; atomic; one revision -/
  | commit (items : List (Place × Change)) (policy : FeedPolicy)
  | draft (e : Edit)
  /-- an append-only revert of a named earlier action: its items undone in reverse order, each after
  a current-target check, under the entry's own policy -/
  | revert (entry : Nat)

structure DocOrigin where
  id : DocId
  app : SigApp
  sketch : Sketch

/-- In this order: `foreign`, `stale`, then the action's own refusals. -/
inductive DocRefusal where
  | foreign (expected : DocId)
  | stale (now : Snap)
  | empty
  | noEntry (entry : Nat)
  | place (item : Nat) (why : PlaceRefusal)
  | feed (item : Nat) (why : FeedRefusal)

/-- What an accepted action produced: one step per item, each with the program it replaced. -/
structure Receipt where
  steps : List Edit.Step

/-- The document over its validating replay; a failed action names its index. -/
structure DocOf (replayDoc : DocOrigin → List DocAction → Except (Nat × DocRefusal) SourceSession) where
  private mk ::
  origin : DocOrigin
  history : List DocAction
  session : SourceSession
  replayed : replayDoc origin history = .ok session

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
  /-- the one staleness rule, used by every action that names a snapshot -/
  check : Doc → Snap → Except DocRefusal Unit
  step : Check.Oracle → Doc → Snap → DocAction → Check.Checked (Except DocRefusal (Doc × Receipt))
  snap : Doc → Snap
  session : Doc → SourceSession
  history : Doc → List DocAction

inductive PublishRefusal where
  | empty

structure FillSpec (Doc : Type) where
  FillSet : Type
  open_ : Doc → FillSet
  anchor : FillSet → Snap
  /-- pending additions, each certified by the `keepExact` feed at the anchor; the root refuses -/
  add : Check.Oracle → FillSet → List (List Nat × NativeEff) →
    Check.Checked (FillSet × List AddOutcome)
  /-- the publication action: the entries in the base's address order, as `commit` items at their
  holes, kept exact; the caller steps it at the anchor, so a moved document refuses `stale` -/
  publication : FillSet → Except PublishRefusal DocAction
  pending : FillSet → List (List Nat × NativeEff)

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

inductive Query where
  | doc (at_ : Option (List Nat))
  | history
  | fills
  | suggest (at_ : Edit2.Snap) (place : Edit2.Place) (supplied : List NativeEff) (cursor limit : Nat)
  | run (id : RunId) (form : RunForm)
  | preview (q : PreviewQuery)
  | dry (a : Action)
  /-- the supported method versions; selection is the connection's, outside the state -/
  | discover

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

/-- In this order: `noDocument`, then the document's own (`foreign`, `stale`, …), then the action's. -/
inductive Refusal where
  | noDocument
  | doc (why : Edit2.DocRefusal)
  | fillsStale (anchor now : Edit2.Snap)
  | fillsEmpty
  | admission (why : AdmitRefusal)
  | restore (why : LiveRecord.Refusal)
  | preview (why : Run.Preview.Refusal)
  | noRun (id : RunId)
  | unresolved (id : RunId) (event : Nat) (sel : Run.Sel)

/-- An action's answer; also the payload of a `dry` query. -/
inductive ActionAnswer where
  | opened (view : DocView)
  | edited (view : DocView) (receipt : Edit2.Receipt)
  | filled (outcomes : List AddOutcome)
  | published (view : DocView) (receipt : Edit2.Receipt)
  | reset (discarded : List (List Nat × NativeEff))
  | started (run : RunId) (origin : Origin) (view : Live.View)
  | played (run : RunId) (verdicts : List Run.Verdict) (view : Live.View)
  | restored (run : RunId) (view : Live.View)

structure Candidate where
  program : NativeEff
  fit : Except Edit2.FeedRefusal EffTy
  key : Check.CheckInput

inductive RunAnswer where
  | view (v : Live.View)
  | record (r : LiveRecord)
  | journal (commands : List Api.Runner.Command)

inductive Answer where
  | acted (a : ActionAnswer)
  | doc (view : DocView)
  | history (actions : List Edit2.DocAction)
  | fills (anchor : Option Edit2.Snap) (pending : List (List Nat × NativeEff))
  | suggested (candidates : List Candidate) (nextCursor : Option Nat)
  | run (id : RunId) (a : RunAnswer)
  | preview (frames : List Live.View)
  | dry (result : Except Refusal ActionAnswer)
  | methods (supported : List (String × List Nat))

structure Reply where
  result : Except Refusal Answer
  now : Option Edit2.Snap

/-- The tool's state: its accepted actions as data, and the raw state their validating replay
returns. A stored action that fails names its index. -/
structure StateOf (Raw : Type) (empty : Raw)
    (replayAccepted : Raw → List Action → Except (Nat × Refusal) Raw) where
  private mk ::
  transcript : List Action
  raw : Raw
  replayed : replayAccepted empty transcript = .ok raw

/-- Reachability follows from the data; nothing is read off an erased witness. -/
theorem StateOf.reached {Raw : Type} {empty : Raw}
    {replayAccepted : Raw → List Action → Except (Nat × Refusal) Raw}
    (s : StateOf Raw empty replayAccepted) : ∃ as, replayAccepted empty as = .ok s.raw :=
  ⟨s.transcript, s.replayed⟩

structure Spec where
  State : Type
  empty : State
  serve : Check.Oracle → State → Request → Check.Checked (State × Reply)
  /-- the accepted actions since `empty`: the persisted form -/
  transcript : State → List Action
  /-- law statement: an accepted action appends exactly itself -/
  serve_appends : ∀ o s a, (serve o s (.act a)).value.2.result.isOk = true →
    transcript (serve o s (.act a)).value.1 = transcript s ++ [a]
  /-- law statement: a query changes nothing -/
  serve_query : ∀ o s q, (serve o s (.ask q)).value.1 = s
  /-- law statement: a refused request changes nothing -/
  serve_refuses : ∀ o s r, (serve o s r).value.2.result.isOk = false → (serve o s r).value.1 = s

end Tool

/-! ## 4. The store -/

namespace Cas

/-- A root's policy, fixed at creation with its target kind. It replaces Lean's five and OCaml's
seven root planes; a plane is the root name's first segment. -/
inductive RootPolicy where
  | swap
  | journal
  | pin
deriving DecidableEq

/-- What a mover expects: the resident digest and its generation (today's `Root.version`). -/
structure Head (D : Type) where
  digest : D
  generation : Nat
deriving DecidableEq

structure Root where
  name : String
  policy : RootPolicy
  kind : Kind
  head : Head Digest

/-- No move records a result: a result node's association is checked at node admission. -/
inductive Move where
  | create (name : String) (policy : RootPolicy) (target : AnyRef)
  | advance (name : String) (expected : Head Digest) (target : AnyRef)

structure Txn where
  nodes : List Node
  moves : List Move

inductive NodeOutcome where
  | fresh | duplicate

inductive MoveOutcome where
  | created (generation : Nat)
  | advanced (generation : Nat)
  | duplicate (generation : Nat)

/-- A commit's answer: one outcome per node and per move. -/
structure Receipt where
  nodes : List (Digest × NodeOutcome)
  moves : List MoveOutcome

/-- The refusals a commit adds to today's `Admission` (the implementation extends `Admission` in
place; this probe cannot). -/
inductive TxnRefusal where
  | node (index : Nat) (why : Admission)
  | handleInContent (index : Nat)
  | badEnvelope (index : Nat)
  | poisoned (index : Nat) (query resident : Digest)
  | noRoot (name : String)
  | staleRoot (name : String) (expected actual : Option (Head Digest))
  | pinned (name : String)
  | target (name : String) (why : Admission)
  | fork (name : String) (head target : Digest)

inductive Read where
  | node (d : Digest)
  | root (name : String)
  | results (query : Digest)
  | closure (r : AnyRef)

inductive ReadRefusal where
  | missing (d : Digest)
  | kind (expected actual : Kind)
  | spec
  | version (found : Nat)
  | payload

/-- Where an interrupted commit stops: after `kept` fresh nodes are durable, roots old; or after the
root table is published, with the acknowledgement lost. -/
inductive Cut where
  | nodes (kept : Nat)
  | published

/-- The model's events. An interruption applies only to a transaction that `commit` accepts. -/
inductive Event where
  | commit (t : Txn)
  | interrupt (t : Txn) (cut : Cut)

structure CasOf (replay : List Event → Except TxnRefusal Store) where
  private mk ::
  store : Store
  reached : ∃ es : List Event, replay es = .ok store

/-- An action's identity; the version covers its output format. -/
structure ActionId where
  name : String
  version : Nat
  engine : Digest

/-- An action query (kind 8). An action whose output varies puts a run identity in its input. -/
structure Query (κ : Type) where
  action : ActionId
  input : κ

/-- The one result envelope (kind 9): its designated query edge and a value tree whose references
stay visible. -/
structure Answered (κ : Type) where
  version : Nat
  query : Ref (Query κ)
  output : Val

/-- A session's journal entry (kind 7): its transcript, one accepted action per entry. -/
inductive SessionEntry where
  | origin (protocol codec : Nat) (engine : Digest)
  | action (parent : Ref SessionEntry) (a : Tool.Action) (after : Option (Ref NativeEff))

/-- A saved run's job (kind 16): the record's identity without its journal. -/
structure Job where
  version : Nat
  app : SigApp
  program : Ref NativeEff
  session : String
  binding : String
  budget : Api.Budget
  rowNames : List (String × Nat)
  engine : Digest
  origin : Option (Ref SessionEntry)

/-- A saved run's tape segment (kind 17). -/
inductive Tape where
  | mk (job : Ref Job) (parent : Option (Ref Tape)) (commands : List Api.Runner.Command)

structure Spec where
  Cas : Type
  empty : Cas
  /-- atomic: nodes in order against the store they grow, then moves in order -/
  commit : Cas → Txn → Except TxnRefusal (Receipt × Cas)
  read : Cas → Read → List (Digest × Node)
  /-- the one typed read: version, kind, spec, exact payload -/
  get : {α : Type} → [Content α] → Cas → Ref α → Except ReadRefusal α
  /-- the model's interrupted commit, for the disk comparison; not an operation of the disk -/
  interrupted : Cas → Txn → Cut → Except TxnRefusal Cas

/-! ### A finite control of the root rule, over a digest type `D` -/

structure RootM (D : Type) where
  policy : RootPolicy
  head : Head D

inductive Outcome where
  | moved | duplicate | stale | pinned
deriving DecidableEq

/-- The rule, stale first: the expected head must be resident; then an identical target is a
duplicate; then a pin never moves. (A journal root's parent check needs the carrier.) -/
def advance {D : Type} [DecidableEq D] (r : RootM D) (expected : Head D) (target : D) :
    RootM D × Outcome :=
  if r.head ≠ expected then (r, .stale)
  else if r.head.digest = target then (r, .duplicate)
  else if r.policy = .pin then (r, .pinned)
  else ({ r with head := ⟨target, r.head.generation + 1⟩ }, .moved)

def r0 : RootM Nat := ⟨.swap, ⟨1, 1⟩⟩    -- created at A, generation 1
def r1 := (advance r0 ⟨1, 1⟩ 2).1        -- A → B, generation 2
def r2 := (advance r1 ⟨2, 2⟩ 1).1        -- B → A, generation 3
-- A writer that read A at generation 1 is refused, though the digest is A again.
#guard (advance r2 ⟨1, 1⟩ 3).2 = .stale
-- An obsolete retry of the B → A move is stale, though its target is resident (stale first).
#guard (advance r2 ⟨2, 2⟩ 1).2 = .stale
-- A fresh expectation with the resident target is a duplicate; with a new target it moves.
#guard (advance r2 ⟨1, 3⟩ 1).2 = .duplicate
#guard (advance r2 ⟨1, 3⟩ 3).2 = .moved
#guard (advance r2 ⟨1, 3⟩ 3).1.head = ⟨3, 4⟩
#guard (advance ⟨.pin, ⟨1, 1⟩⟩ ⟨1, 1⟩ 2).2 = .pinned
#guard (advance ⟨.pin, ⟨1, 1⟩⟩ ⟨1, 1⟩ 1).2 = .duplicate

end Cas

/-! ## 5. The exchange -/

namespace Exchange

/-- What a request runs against. -/
inductive Base where
  /-- an exact chain head: queries only; an act refuses `readOnly` -/
  | at_ (entry : Ref Cas.SessionEntry)
  /-- the named session's head; `none` creates the session -/
  | head (name : String) (expected : Option (Cas.Head Digest))
  /-- a new session root whose chain continues from `from_` -/
  | fork (from_ : Ref Cas.SessionEntry) (name : String)

structure Envelope where
  base : Base
  request : Tool.Request

/-- Loading's refusals, in the order of its six steps. -/
inductive LoadRefusal where
  | unreadable (at_ : Digest) (why : Cas.ReadRefusal)
  | noOrigin
  | version (protocol codec : Nat)
  | parent (at_ : Digest)
  | refused (index : Nat) (why : Tool.Refusal)
  | after (index : Nat)

inductive Refusal where
  | staleBase (expected now : Option (Cas.Head Digest))
  | readOnly
  | load (why : LoadRefusal)
  | store (why : Cas.TxnRefusal)

structure Spec (T : Tool.Spec) (C : Cas.Spec) where
  load : Check.Oracle → C.Cas → Ref Cas.SessionEntry → Check.Checked (Except LoadRefusal T.State)
  /-- the reply, and the new head after an accepted act; a whole-request refusal is a reply -/
  apply : Check.Oracle → C.Cas → Envelope →
    Check.Checked (Except Refusal (Tool.Reply × Option (Cas.Head Digest) × C.Cas))

end Exchange

/-! ### Finite controls -/

/-! Codex's `repeatedHole`: a hole place resolves only at its one occurrence. -/
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

/-! The self-review's `transcriptOf` control, answered: the transcript is a field. -/
namespace TranscriptControl

def replayCount (r : Nat) (as : List Tool.Action) : Except (Nat × Tool.Refusal) Nat :=
  .ok (r + as.length)

def s1 : Tool.StateOf Nat 0 replayCount := ⟨[.reset], 1, rfl⟩

#guard s1.transcript.length = 1
#guard s1.raw = 1

end TranscriptControl

/-! A memo answers through the exact rule, and its oracle agrees with `run`. -/
namespace MemoControl
open Check

def key : CheckInput := .part ⟨{}, [], .root⟩ [] (.succeed (.lit (.nat 2)))
def learned : Memo := Memo.empty.learn (Checked.ask Oracle.uncached key)

#guard learned.entries.length = 1
#guard (learned.entries.find? (HitRule.exact.hit key)).isSome

end MemoControl

end SeamsProbe

#eval IO.println "SeamsInterfaces v2: declarations elaborate; oracle, trace, memo, transcript, place and root controls pass"
