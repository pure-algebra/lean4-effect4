import Effect4.Tool.Origin
import Effect4.Program.Typing.FillSet
import Effect4.Program.Typing.CheckCache
import Effect4.Run.LiveRecord
import Effect4.Run.Preview

/-!
# Tool.Protocol — the tool's requests and replies, as data

**The question.** An agent, the view and a native shell all drive one authoring session. Each sends
a request and reads a reply. Requests and replies here are first-order data, so a transcript can be
stored, replayed and compared across drivers. `Tool.serve` (`Tool/Serve.lean`) owns their meaning.

- An `Action` changes the state when it is accepted: open a document, edit it, add and publish
  fills, start, restore and play runs.
- A `Query` reads the state and never changes it, a `dry` run included. The document's reads are
  its view, the inspection at an address, the whole address table, the addresses, and the term
  slots of a node.
- A `Reply` carries the answer or one located `Refusal`, and the current snapshot.

Three outcome kinds stay apart: a refused request leaves the state unchanged; a refused item inside
a fill batch is an outcome inside an accepted answer; a run command whose phase refuses is recorded
in the run's journal.

This module stays non-module through the program specialization-site imports (decisions row 202).
-/
set_option autoImplicit false
namespace Effect4.Tool
open Effect4 Effect4.Program
/-- **A run's identity**: its index in the state's run list. -/
structure RunId where
  n : Nat

/-- **How a run query answers**: the view, the saved record, or the ordered journal. -/
inductive RunForm where
  | view | record | journal

/-- **A preview of the document's program**, over a host tape. -/
inductive PreviewQuery where
  | settle (tape : List Machine.ExitV) (limit : Nat)
  | frames (tape : List Machine.ExitV) (limit : Nat)
  | explore (budget width : Nat)

/-- **A request that changes the state when accepted.** -/
inductive Action where
  | open_ (name : String) (app : SigApp) (sketch : Sketch)
  | edit (at_ : Program.Snap) (a : Program.DocAction)
  /-- pending additions: per-item outcomes inside a successful answer -/
  | fill (at_ : Program.Snap) (batch : List (List Nat × NativeEff))
  | publish (at_ : Program.Snap)
  | reset
  | start (at_ : Program.Snap) (budget : Api.Budget)
  | restore (record : LiveRecord)
  /-- events folded over a temporary run; an unresolved selector refuses the whole request -/
  | play (run : RunId) (events : List Run.Event)

/-- **A request that reads the state.** -/
inductive Query where
  | doc (at_ : Option (List Nat))
  | history
  | fills
  | suggest (at_ : Program.Snap) (place : Program.Place) (supplied : List NativeEff) (cursor limit : Nat)
  | run (id : RunId) (form : RunForm)
  | preview (q : PreviewQuery)
  | dry (a : Action)
  /-- the supported method versions; selection is the connection's, outside the state -/
  | discover
  /-- the whole address table, one entry for each address of the program as written -/
  | table
  /-- the addresses of the program as written, in the table's order -/
  | addresses
  /-- the term slots of the node at an address: the one slot named, or every slot -/
  | slots (at_ : List Nat) (slot : Option ExtSlot)

/-- **A request**: an action or a query. -/
inductive Request where
  | act (a : Action)
  | ask (q : Query)

/-- **One hole occurrence** in the document: its row, its address and its typed focus. -/
structure HoleView where
  index : Nat
  row : Program.Row
  path : List Nat
  focus : Option (TyEnv × EffTy)

/-- **What the tool answers at an address**: the sub-program, its signature context, its focus,
its table entry and any refusal there. -/
structure Inspection where
  path : List Nat
  expected : NativeEff
  context : SigData
  focus : Option (Focus NativeOp)
  entry : Option Table.Entry
  refusal : Option TypeRefusal

/-- **One term slot of a node**: its term, the environment the term reads, and the term's type
there. A slot has an environment and a type where the rule's earlier reads type. -/
structure SlotView where
  slot : ExtSlot
  term : Option Term
  env : Option TyEnv
  ty : Option Ty

/-- **What the tool shows of a document**: snapshot, root type, refusals, holes and an optional
inspection. -/
structure DocView where
  snap : Program.Snap
  type : Option EffTy
  refusals : List TypeRefusal
  holes : List HoleView
  inspection : Option Inspection

/-- In this order: `noDocument`, then the document's own (`foreign`, `stale`, …), then the action's. -/
inductive Refusal where
  | noDocument
  | doc (why : Program.DocRefusal)
  | fillsStale (anchor now : Program.Snap)
  | fillsEmpty
  | admission (why : AdmitRefusal)
  | restore (why : LiveRecord.Refusal)
  | preview (why : Run.Preview.Refusal)
  | noRun (id : RunId)
  | unresolved (id : RunId) (event : Nat) (sel : Run.Sel)
  | suggest (why : Program.FeedRefusal)
  | place (why : Program.PlaceRefusal)
  | noProgram (path : List Nat)

/-- An action's answer; also the payload of a `dry` query. -/
inductive ActionAnswer where
  | opened (view : DocView)
  | edited (view : DocView) (receipt : Program.Receipt)
  | filled (outcomes : List AddOutcome)
  | published (view : DocView) (receipt : Program.Receipt)
  | reset (discarded : List (List Nat × NativeEff))
  | started (run : RunId) (origin : Origin) (view : Live.View)
  | played (run : RunId) (verdicts : List Run.Verdict) (view : Live.View)
  | restored (run : RunId) (view : Live.View)

/-- **A suggestion's candidate**: the program, where it came from, its check key and evidence. -/
structure Candidate where
  program : NativeEff
  sourcePath : Option (List Nat)
  key : Check.CheckInput
  evidence : Program.CheckCache.Evidence

/-- **A run query's answer**, in the requested form. -/
inductive RunAnswer where
  | view (v : Live.View)
  | record (r : LiveRecord)
  | journal (commands : List Api.Runner.Command)

/-- **A preview's answer**: settled outcomes, frames, or explored paths. -/
inductive PreviewAnswer where
  | settled (result : Option (Nat × Run.Tree.Outcome (List Machine.ExitV)))
  | frames (results : List (Run.Tree.Outcome (List Machine.ExitV)))
  | explored (paths : List Run.Tree.Path)

/-- **A request's answer.** -/
inductive Answer where
  | acted (a : ActionAnswer)
  | doc (view : DocView)
  | history (actions : List Program.DocAction)
  | fills (anchor : Option Program.Snap) (pending : List (List Nat × NativeEff))
  | suggested (candidates : List Candidate) (nextCursor : Option Nat)
  | run (id : RunId) (a : RunAnswer)
  | preview (result : PreviewAnswer)
  | dry (result : Except Refusal ActionAnswer)
  | methods (supported : List (String × List Nat))
  | table (entries : List Table.Entry)
  | addresses (paths : List (List Nat))
  /-- `typed`: the node is typed in its part, so every slot with a term has an environment and a
  type there (`hasTy_extSlotEnv`) -/
  | slots (at_ : List Nat) (typed : Bool) (slots : List SlotView)

/-- **A reply**: the answer or a refusal, and the current snapshot. -/
structure Reply where
  result : Except Refusal Answer
  now : Option Program.Snap


/-- **A request's method name**, as the wire and `discover` spell it. -/
def Request.method : Request → String
  | .act (.open_ ..) => "open"
  | .act (.edit ..) => "edit"
  | .act (.fill ..) => "fill"
  | .act (.publish ..) => "publish"
  | .act .reset => "reset"
  | .act (.start ..) => "start"
  | .act (.restore ..) => "restore"
  | .act (.play ..) => "play"
  | .ask (.doc ..) => "doc"
  | .ask .history => "history"
  | .ask .fills => "fills"
  | .ask (.suggest ..) => "suggest"
  | .ask (.run ..) => "run"
  | .ask (.preview ..) => "preview"
  | .ask (.dry ..) => "dry"
  | .ask .discover => "discover"
  | .ask .table => "table"
  | .ask .addresses => "addresses"
  | .ask (.slots ..) => "slots"

/-- **The supported methods**, each at version 1. Selection is the connection's, outside the state. -/
def supportedMethods : List (String × List Nat) :=
  ["open","edit","fill","publish","reset","start","restore","play",
    "doc","history","fills","suggest","run","preview","dry","discover","table","addresses",
    "slots"].map
    fun name => (name,[1])
end Effect4.Tool
