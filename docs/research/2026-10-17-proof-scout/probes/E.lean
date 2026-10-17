import Tools.Session
import Effect4.Laws.Api.Live
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Run.Tree

/-!
# Probe E: persistent keyed live sessions, and the preview boundary

Slice E of the authoring review, with the preview repairs the additional review asks for.

* `LiveRecord`, `save`, `restore`: a live session as first-order data, and its restoration
  through admission (a refusing entry point, finding F2 of the session note). The record keeps
  the row spellings, so the restoration is exact.
* `restore_save`: a saved live session restores to the same run. Placement: concept
  `host-session-protocol`, property `typed-replay-session`; question: the proposed claim
  `live-session-persists` (role compatibility), extending `journal_replays` at R13. Reach: every
  `Live`. It composes `admitProgram_eq_ok`, `Live.feedAll_wire` and `Live.journal_replays`. It does
  not establish that another host's journal replays, host reconnection, external resources or
  exactly-once side effects. Consumer: the session tool's `save` and `load`. Requirement R13,
  serving R6.
* `checkedTape`: the reply tape of the call tree, each reply admitted at its row before it is
  given (`Kit.replyFault`). `checkedTape_admits` is its one law, by definition. Placement:
  concept `host-session-protocol`, property `reply-at-call-instance` at the row's columns;
  question: the preview interface's proposed obligation of the additional review (role
  compatibility). Reach: the call tree's runs under the tape. It does not establish agreement
  with the machine (`Tree.ofProgram_eq_denoteRowsB` is a planned goal) or anything beyond the
  rows' own columns. Consumer: the tool's `settle` and `frames` when a tape is supplied.
  Requirement R12.

The keyed reply controls reuse `Sel.resolve` and the session's keyed slots; their laws are
`Api.HostSession.readReply_store_other`, `submit_key_independence` and `session_keys_once`.
-/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 800000

namespace ProofScout.E

open Effect4 Effect4.Machine Effect4.Program Effect4.Store
open Effect4.Api.Runner (Command)

/-! ## The record -/

/-- A live session as data: its application, program, name, binding, budgets, journal and row
spellings. No certificate: restoration reruns admission. -/
structure LiveRecord where
  app : SigApp
  program : NativeEff
  session : String
  binding : String
  budget : Api.Budget
  journal : List Command
  rowNames : List (String × Nat)

/-- Save a live session. -/
def save (l : Live) : LiveRecord :=
  ⟨l.run.built.app, l.run.built.program, l.run.id, l.run.profile, l.run.budget, l.run.journal,
    l.run.built.rowNames⟩

/-- Restore a live session: admit the program, open it, and replay the journal through the
session's checks. -/
def restore (r : LiveRecord) : Except AdmitRefusal Live :=
  match admitProgram r.program r.app with
  | .error why => .error why
  | .ok admitted =>
    .ok ((Live.open ⟨r.app, r.program, admitted, r.rowNames⟩ r.session r.budget r.binding).feedAll
      (r.journal.map .wire))

/-- **A saved live session restores to the same run.** -/
theorem restore_save (l : Live) : ∃ l', restore (save l) = .ok l' ∧ l'.run = l.run := by
  refine ⟨(Live.open l.run.built l.run.id l.run.budget l.run.profile).feedAll
    (l.run.journal.map .wire), ?_, ?_⟩
  · unfold restore save
    dsimp only
    rw [admitProgram_eq_ok l.run.built.admitted]
  · rw [Live.feedAll_wire]
    exact Live.journal_replays l

/-! ## The preview's reply tape, admitted -/

/-- A reply tape whose replies are admitted at their row first. A reply that the row refuses is
not given, and the call waits: a frontier, never a guessed value. -/
def checkedTape (app : SigApp) : Run.Tree.Host (List ExitV) := fun row _ tape =>
  match tape with
  | [] => none
  | ex :: rest => if (Run.Kit.replyFault app row ex).isNone then some (ex, rest) else none

/-- Every reply the checked tape gives passes reply admission at its row. -/
theorem checkedTape_admits {app : SigApp} {row : Nat} {v : Store.Val} {tape rest : List ExitV}
    {ex : ExitV} (h : checkedTape app row v tape = some (ex, rest)) :
    Run.Kit.replyFault app row ex = none := by
  unfold checkedTape at h
  split at h
  · cases h
  · split at h
    · rename_i hok
      cases h
      exact Option.isNone_iff_eq_none.mp hok
    · cases h

/-! ## Controls -/

def opts : Supervision.ForkOptions :=
  { daemon := false, startImmediately := true, maskMode := .inherit }

/-- Two children, each calling the one hole row, both awaited. -/
def pairSketch : Sketch :=
  { program := .bind (.withFiber (.fork (Sketch.hole {} 0) opts))
      (.bind (.withFiber (.fork (Sketch.hole {} 0) opts))
        (.bind (.awaitFiber (.var 0) .awaitValue) (.awaitFiber (.var 1) .awaitValue))),
    holes := [Row.hole "h" .nat] }
def pairApp : SigApp := ({} : SigApp).withHoles pairSketch.holes

def pairLive : Option Live :=
  match admitProgram pairSketch.program pairApp with
  | .ok admitted => some (Live.open ⟨pairApp, pairSketch.program, admitted, [("h", 0)]⟩ "multi")
  | .error _ => none

def started : Option Live := pairLive.map fun l => (l.feed .start).1
def ok (n : Nat) : Api.HostSession.Answer := .ofExit (.success (.nat n))

-- The checked sketch starts at its full application, and both children wait on the row.
#guard pairLive.isSome
#guard (started.map fun l => (Run.live l.run).length) = some 2

-- Red control (case 10): the row names two live calls, so a reply by row is refused.
#guard (started.map fun l => (l.feed (.receive (.row "h") (ok 5))).2) =
  some (.unresolved (.row "h"))

-- Green twin: the exact key of the first call takes its reply, and the second call keeps waiting.
def firstKey : Option Api.HostSession.Key :=
  started.bind fun l => (Run.live l.run).head?.map (·.key)
def afterFirst : Option Live := started.bind fun l => firstKey.map fun k =>
  l.feedAll [.receive (.key k) (ok 5), .apply (.key k), .flush]
#guard (afterFirst.map fun l => (Run.live l.run).length) = some 1
#guard (afterFirst.bind fun l => firstKey.map fun k => (Run.live l.run).any (·.key == k)) =
  some false

-- Persistence (case 11): the record of the half-answered session restores to the same run.
#guard (afterFirst.map fun l => match restore (save l) with
  | .ok l' => l'.run.journal == l.run.journal && l'.run.phases == l.run.phases &&
      (Run.live l'.run).length == 1
  | .error _ => false) = some true

-- The record is first-order: its fields travel through their canonical bytes.
#guard (afterFirst.map fun l =>
  let r := save l
  (Canonical.decode (Canonical.encode (r.app.rows, r.app.services, r.app.types, r.program,
      r.session, r.binding, r.budget.fuel, r.budget.compileFuel, r.journal, r.rowNames)) :
    Option (RowTable × List (ServiceKey × Ty) × TyDecls × NativeEff × String × String × Nat ×
      Nat × List Command × List (String × Nat))) ==
  some (r.app.rows, r.app.services, r.app.types, r.program, r.session, r.binding, r.budget.fuel,
      r.budget.compileFuel, r.journal, r.rowNames)) = some true

-- Red at HEAD (preview): a raw tape gives a string to a natural-number hole, and the call tree
-- finishes with it. The checked tape leaves the call waiting instead.
def holeSketch : Sketch := { program := Sketch.hole {} 0, holes := [Row.hole "hole" .nat] }
def holeApp : SigApp := ({} : SigApp).withHoles holeSketch.holes
#guard match Run.Tree.settle holeApp.rows 8 Run.Tree.Host.tape
    [.success (.str "wrong type")] holeSketch.program with
  | some (_, o) => match o.stop with
    | .finished (.success (.str "wrong type")) => true
    | _ => false
  | none => false
#guard match Run.Tree.settle holeApp.rows 8 (checkedTape holeApp)
    [.success (.str "wrong type")] holeSketch.program with
  | some (_, o) => match o.stop with
    | .waiting 0 .unit => true
    | _ => false
  | none => false
#guard match Run.Tree.settle holeApp.rows 8 (checkedTape holeApp)
    [.success (.nat 4)] holeSketch.program with
  | some (_, o) => match o.stop with
    | .finished (.success (.nat 4)) => true
    | _ => false
  | none => false

-- Red at HEAD (preview): a form outside the tree's arms ends as `Eval.outside`. The gate refuses
-- it at its address first; `Run.atBudget` routes a built program there to the machine instead.
def outsideTree : NativeEff := .scoped (.succeed (.lit (.nat 7)))
#guard Run.Tree.outsideAt outsideTree = some []
#guard Run.Tree.outsideAt holeSketch.program = none

end ProofScout.E
