import Effect4.Tool.Origin
import Effect4.Tool.RequestSyntax
import Effect4.Program.Typing.FillSet
import Effect4.Program.Typing.Suggest
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

One declaration owns the methods (`tool_requests`, `Tool/RequestSyntax.lean`). It declares the two
sums from their cases, and beside them the finite `MethodKey`, one key for each case, with its wire
name and its kind. `Request.method` and `supportedMethods` read the keys. The method table
(`methodDescriptor`, `Tool/Methods.lean`) holds the same names and versions, with each method's
shapes, what it does and its hints.

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

/-- **A method's kind**: an action changes the state when it is accepted, and a query reads it. -/
inductive MethodKind where
  | action
  | query
deriving DecidableEq

tool_requests
  actions [
    | open_ (name : String) (app : SigApp) (sketch : Sketch) wire "open"
    | edit (at_ : Program.Snap) (a : Program.DocAction)
    /-- pending additions: per-item outcomes inside a successful answer -/
    | fill (at_ : Program.Snap) (batch : List (List Nat × NativeEff))
    | publish (at_ : Program.Snap)
    | reset
    | start (at_ : Program.Snap) (budget : Api.Budget)
    | restore (record : LiveRecord)
    /-- events folded over a temporary run; an unresolved selector refuses the whole request -/
    | play (run : RunId) (events : List Run.Event)
  ]
  queries [
    | doc (at_ : Option (List Nat))
    | history
    | fills
    | suggest (at_ : Program.Snap) (place : Program.Place) (supplied : List NativeEff)
        (cursor limit : Nat)
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
  ]

/-- **A request that changes the state when accepted.** -/
add_decl_doc Action

/-- **A request that reads the state.** -/
add_decl_doc Query

/-- **A request**: an action or a query. -/
add_decl_doc Request

/-- **One hole occurrence** in the document: its row, its address and its typed focus. -/
structure HoleView where
  index : Nat
  row : Program.Row
  path : List Nat
  focus : Option (TyEnv × EffTy)

/-- **One declared hole**: its index in the hole table, its name, the exact program that performs
it (`Sketch.hole`: the row after the application's rows, on a unit request), and whether the
program performs it anywhere. A declared hole the program never performs shows here: hole 0 of
an application with one row is `external 1`, never `external 0`. -/
structure HoleDecl where
  index : Nat
  name : String
  perform : NativeEff
  performed : Bool
deriving DecidableEq

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

/-- **What the tool shows of a document**: snapshot, root type, refusals, every hole occurrence,
every declared hole with its exact `perform` term, and an optional inspection. -/
structure DocView where
  snap : Program.Snap
  type : Option EffTy
  refusals : List TypeRefusal
  holes : List HoleView
  declared : List HoleDecl
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

/-- **A run query's answer**, in the requested form. -/
inductive RunAnswer where
  | view (v : Live.View)
  | record (r : LiveRecord)
  | journal (commands : List Api.Runner.Command)

/-- **A preview run, as the tool answers it**: its steps, how it stopped, and the tape it left
unread. The machine's stores stay inside the run (`Run.Tree.Outcome.stores`). -/
structure PreviewRun where
  steps : List Run.Tree.Step
  stop : Run.Tree.Stop
  unread : List Machine.ExitV

/-- The answer of a tree run, without its stores. -/
def PreviewRun.of (o : Run.Tree.Outcome (List Machine.ExitV)) : PreviewRun :=
  ⟨o.steps, o.stop, o.state⟩

/-- **A preview's answer**: settled outcomes, frames, or explored paths. -/
inductive PreviewAnswer where
  | settled (result : Option (Nat × PreviewRun))
  | frames (results : List PreviewRun)
  | explored (paths : List Run.Tree.Path)

/-- **A request's answer.** -/
inductive Answer where
  | acted (a : ActionAnswer)
  | doc (view : DocView)
  | history (actions : List Program.DocAction)
  | fills (anchor : Option Program.Snap) (pending : List (List Nat × NativeEff))
  | suggested (candidates : List Suggest.Suggestion) (nextCursor : Option Nat)
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


/-- **A method's versions**: every method is at version 1. -/
def MethodKey.versions (_ : MethodKey) : List Nat := [1]

/-- **A request's method name**, as the wire and `discover` spell it: its key's wire name, which
is its descriptor's name (`method_name_agrees`, `Laws/Tool/Wire.lean`). -/
def Request.method (r : Request) : String := r.methodKey.name

/-- **The supported methods**: every key's wire name with its versions, in the keys' order, as the
descriptors hold them (`supportedMethods_descriptors`, `Laws/Tool/Wire.lean`). Selection is the
connection's, outside the state. -/
def supportedMethods : List (String × List Nat) :=
  MethodKey.all.map fun k => (k.name, k.versions)

/-- Every request's method is supported: the supported methods are every key's, and each request
has a key. -/
theorem method_supported (r : Request) : (supportedMethods.lookup r.method).isSome = true := by
  cases r with
  | act a => cases a <;> rfl
  | ask q => cases q <;> rfl
end Effect4.Tool
