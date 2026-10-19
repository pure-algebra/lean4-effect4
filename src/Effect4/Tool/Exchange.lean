import Effect4.Tool.Workspace
import Effect4.Tool.Serve

/-!
# Tool.Exchange — workspaces over the store (seams ST4)

A workspace is a journal root `workspace/<name>` over a chain of `WorkspaceEntry` nodes
(`Tool/Workspace.lean`). `Exchange.load` reads a chain back into a tool state, and
`Exchange.apply` serves one request at a base and publishes an accepted action.

**Loading**, in six steps, each with its refusal:

1. read every entry through the store's typed read (`Cas.get`: version, kind, specification and
   exact payload; `unreadable`);
2. check parent order by the entries' indices, and that index 0 names an origin (`early`,
   `outOfOrder`, `noOrigin`); the walk is structural in the index, so it needs no fuel;
3. check the origin's protocol and codec versions (`version`);
4. replay the actions from the empty state through `serve`, under the caller's oracle; the first
   refused action refuses (`refused index`);
5. compare every stored `after` with replay's program at its prefix (`after index`);
6. return the replayed state, whose transcript equation `State` carries.

The engine an origin records is not compared: a different engine is accepted when every action
replays and every `after` matches, as `Core.Validated` reruns validation when trust changes.

**The exchange**: resolve the base and load its chain; compare the head expectation (`staleBase`);
serve; publish nothing for a query or a refused request; commit an accepted action's entry, the
schemas and program it needs, and the head move in one `Cas.commit`. The commit's own head
comparison catches a race after resolution, A→B→A included (`staleBase`). `staleBase` names a
moved workspace head; a moved document revision stays the tool's own `stale` refusal, inside the
reply. An exact-entry base serves queries only (`readOnly`).

`Port` owns the four store operations: typed entries, roots, schema membership and commit.
The definitions below are generic in a pure store value. `casPort` supplies the reached store.
The laws at that instance are in `src/Effect4/Laws/Tool/Exchange.lean`: `load_own`,
`apply_commits_once` and `apply_refuses`. Arbitrary port instances carry no store-law claim.
-/

set_option autoImplicit false

namespace Effect4.Tool

open Effect4 Effect4.Store Effect4.Program.Check

/-- Why a stored chain does not load. -/
inductive LoadRefusal where
  /-- the entry at this address does not read at kind `entry` -/
  | unreadable (at_ : Digest) (why : ReadRefusal)
  /-- the chain reaches its origin at this address while the action at this transcript index is
  still owed -/
  | early (at_ : Digest) (index : Nat)
  /-- the action at this address records another transcript index than its place in the chain -/
  | outOfOrder (at_ : Digest) (expected found : Nat)
  /-- the first action's parent is not an origin -/
  | noOrigin (at_ : Digest)
  /-- the origin records a protocol or codec version this tool does not read -/
  | version (protocol codec : Nat)
  /-- the stored action at this index does not replay -/
  | refused (index : Nat) (why : Refusal)
  /-- the stored program after the action at this index is not replay's -/
  | after (index : Nat)

/-- The steps of a chain, oldest first: each action with its stored `after`. -/
abbrev Steps := List (Action × Option (Ref Program.NativeEff))

/-- A chain read back: its origin and its steps. -/
structure Chain where
  protocol : Nat
  codec : Nat
  engine : Digest
  steps : Steps

namespace Exchange

/-- The exchange's four store operations. This interface describes pure store values.
The native disk adapter must represent host faults separately from model refusals.
`contains` serves schema publication, which needs no node payload. -/
class Port (σ : Type) where
  entry : σ → Digest → Except LoadRefusal WorkspaceEntry
  root : σ → String → Option Root
  contains : σ → Digest → Bool
  commit : σ → Txn → Except TxnRefusal (Receipt × σ)

/-- The existing reached store supplies the exchange's model instance. -/
instance casPort : Port Cas where
  entry cas d := match Cas.get (α := WorkspaceEntry) cas ⟨d⟩ with
    | .error why => .error (.unreadable d why)
    | .ok entry => .ok entry
  root cas name := cas.store.root? name
  contains cas d := (cas.store.find d).isSome
  commit := Cas.commit

variable {σ : Type} [Port σ]

/-- The entry at an address, through the port's typed read. -/
def entryAt (cas : σ) (d : Digest) : Except LoadRefusal WorkspaceEntry :=
  Port.entry cas d

/-- The origin a first action names. -/
def originAt (cas : σ) (d : Digest) (steps : Steps) : Except LoadRefusal Chain :=
  match entryAt cas d with
  | .error why => .error why
  | .ok (.origin protocol codec engine) => .ok ⟨protocol, codec, engine, steps⟩
  | .ok (.action ..) => .error (.noOrigin d)

/-- Walk from the action entry at `d`, expected at transcript index `n`, to the origin. -/
def walk (cas : σ) : Nat → Digest → Steps → Except LoadRefusal Chain
  | n, d, steps =>
    match entryAt cas d with
    | .error why => .error why
    | .ok (.origin ..) => .error (.early d n)
    | .ok (.action parent index a after) =>
      if index = n then
        match n with
        | 0 => originAt cas parent.digest ((a, after) :: steps)
        | m + 1 => walk cas m parent.digest ((a, after) :: steps)
      else .error (.outOfOrder d n index)

/-- The chain ending at an entry: an origin alone, or an action walked to its origin. -/
def chainAt (cas : σ) (d : Digest) : Except LoadRefusal Chain :=
  match entryAt cas d with
  | .error why => .error why
  | .ok (.origin protocol codec engine) => .ok ⟨protocol, codec, engine, []⟩
  | .ok (.action _ index _ _) => walk cas index d []

/-- The document's program after a state, by reference; `none` with no document open. -/
def afterOf (raw : Internal.Raw) : Option (Ref Program.NativeEff) :=
  raw.doc.map fun d => address d.session.sketch.program

/-- One replayed step after `serve`: the next state, or the step's refusal. -/
def stepped (index : Nat) (after : Option (Ref Program.NativeEff)) (served : State × Reply) :
    Except LoadRefusal State :=
  match served.2.result with
  | .error why => .error (.refused index why)
  | .ok _ => if afterOf served.1.raw = after then .ok served.1 else .error (.after index)

/-- Replay steps through `serve`, from transcript index `index`, comparing each stored `after`. -/
def replay (o : Oracle) : Nat → State → Steps → Checked (Except LoadRefusal State)
  | _, s, [] => pure (.ok s)
  | index, s, (a, after) :: rest => do
    let served ← serve o s (.act a)
    match stepped index after served with
    | .error why => pure (.error why)
    | .ok next => replay o (index + 1) next rest

/-- **Load a chain** into a tool state: the six steps above. -/
def load (o : Oracle) (cas : σ) (head : Ref WorkspaceEntry) : Checked (Except LoadRefusal State) :=
  match chainAt cas head.digest with
  | .error why => pure (.error why)
  | .ok chain =>
    if chain.protocol = protocolVersion ∧ chain.codec = codecVersion then
      replay o 0 empty chain.steps
    else pure (.error (.version chain.protocol chain.codec))

/-- Where a request starts: an exact entry (queries only), a named workspace's head, or a new
workspace continuing from an entry. -/
inductive Base where
  | at_ (entry : Ref WorkspaceEntry)
  /-- `none` creates the workspace -/
  | head (name : String) (expected : Option (Head Digest))
  | fork (from_ : Ref WorkspaceEntry) (name : String)

/-- One request at a base. -/
structure Envelope where
  base : Base
  request : Request

/-- Why an exchange refuses. A request the tool refuses is a reply, not an exchange refusal. -/
inductive Refusal where
  | load (why : LoadRefusal)
  /-- an action at an exact-entry base -/
  | readOnly
  /-- the workspace head is not the expected one, before serving or at the commit -/
  | staleBase (name : String) (expected actual : Option (Head Digest))
  /-- the store refused the publication for another reason -/
  | store (why : TxnRefusal)

/-- A named workspace's root. -/
def rootName (name : String) : String := "workspace/" ++ name

/-- Where an accepted action publishes. -/
inductive Publish where
  | readOnly
  /-- a new workspace: an origin, then the action -/
  | create (name : String)
  /-- the workspace's next entry, after the expected head -/
  | advance (name : String) (head : Head Digest)
  /-- a new workspace continuing from an entry -/
  | fork (name : String) (parent : Ref WorkspaceEntry)

/-- The workspace a publication names. -/
def Publish.name? : Publish → Option String
  | .readOnly => none
  | .create name | .advance name _ | .fork name _ => some name

/-- A resolved base: the loaded state, and where an accepted action publishes. -/
structure Resolved where
  state : State
  publish : Publish

/-- Load a base's state, or refuse. -/
def loaded (o : Oracle) (cas : σ) (entry : Ref WorkspaceEntry) (publish : Publish) :
    Checked (Except Refusal Resolved) := do
  match ← load o cas entry with
  | .error why => pure (.error (.load why))
  | .ok s => pure (.ok ⟨s, publish⟩)

/-- **Resolve a base**: compare the head expectation, then load the chain it names. -/
def resolve (o : Oracle) (cas : σ) : Base → Checked (Except Refusal Resolved)
  | .at_ entry => loaded o cas entry .readOnly
  | .head name none =>
    match Port.root cas (rootName name) with
    | some root => pure (.error (.staleBase name none (some root.head)))
    | none => pure (.ok ⟨empty, .create name⟩)
  | .head name (some expected) =>
    match Port.root cas (rootName name) with
    | none => pure (.error (.staleBase name (some expected) none))
    | some root =>
      if root.head = expected then loaded o cas ⟨expected.digest⟩ (.advance name expected)
      else pure (.error (.staleBase name (some expected) (some root.head)))
  | .fork from_ name =>
    match Port.root cas (rootName name) with
    | some root => pure (.error (.staleBase name none (some root.head)))
    | none => loaded o cas from_ (.fork name from_)

/-- The schema nodes a publication needs that the store does not hold: the genesis, the entry's
specification and, with a program, the program's. -/
def schemas (cas : σ) (program : Bool) : List Node :=
  (if Port.contains cas genesisAddress then [] else [genesisNode]) ++
  (if Port.contains cas (specOf WorkspaceEntry) then [] else [nodeOf (shape WorkspaceEntry).document]) ++
  (if program ∧ !Port.contains cas (specOf Program.NativeEff)
    then [nodeOf (shape Program.NativeEff).document] else [])

/-- The entry an accepted action appends after `parent`, from the state it was served at. -/
def entryAfter (parent : Ref WorkspaceEntry) (s : State) (a : Action) (next : State) : WorkspaceEntry :=
  .action parent s.transcript.length a (afterOf next.raw)

/-- The nodes before an action's entry: the missing schemas and the program after it. -/
def support (cas : σ) (next : State) : List Node :=
  schemas cas (afterOf next.raw).isSome ++ (next.raw.doc.map fun d => [nodeOf d.session.sketch.program]).getD []

/-- **The publication** of an accepted action served at `s`: the nodes children first, then the
one head move. -/
def publication (engine : Digest) (cas : σ) (s : State) (a : Action) (next : State) :
    Publish → Option Txn
  | .readOnly => none
  | .create name =>
    let origin : WorkspaceEntry := .origin protocolVersion codecVersion engine
    let entry := entryAfter (address origin) s a next
    some ⟨support cas next ++ [nodeOf origin, nodeOf entry],
      [.create (rootName name) .journal ⟨.entry, (address entry).digest⟩]⟩
  | .advance name head =>
    let entry := entryAfter ⟨head.digest⟩ s a next
    some ⟨support cas next ++ [nodeOf entry],
      [.advance (rootName name) head ⟨.entry, (address entry).digest⟩]⟩
  | .fork name parent =>
    let entry := entryAfter parent s a next
    some ⟨support cas next ++ [nodeOf entry],
      [.create (rootName name) .journal ⟨.entry, (address entry).digest⟩]⟩

/-- The workspace head after an exchange, where the base names a workspace. -/
def headOf (cas : σ) (publish : Publish) : Option (Head Digest) :=
  publish.name?.bind fun name => (Port.root cas (rootName name)).map Root.head

/-- **After serving**: publish an accepted action in one commit, or return the store unchanged. -/
def finish (engine : Digest) (cas : σ) (resolved : Resolved) (request : Request) (next : State)
    (reply : Reply) : Except Refusal (Reply × Option (Head Digest) × σ) :=
  match request, reply.result with
  | .act a, .ok _ =>
    match publication engine cas resolved.state a next resolved.publish with
    | none => .error .readOnly
    | some txn =>
      match Port.commit cas txn with
      | .ok (_, cas') => .ok (reply, headOf cas' resolved.publish, cas')
      | .error (.staleRoot _ expected actual) =>
        .error (.staleBase ((resolved.publish.name?).getD "") expected actual)
      | .error why => .error (.store why)
  | _, _ => .ok (reply, headOf cas resolved.publish, cas)

/-- **Serve one request at a base**: the reply, the workspace head, and the store. A query and a
refused request publish nothing; an accepted action commits once. -/
def apply (o : Oracle) (engine : Digest) (cas : σ) (env : Envelope) :
    Checked (Except Refusal (Reply × Option (Head Digest) × σ)) := do
  match ← resolve o cas env.base with
  | .error why => pure (.error why)
  | .ok resolved =>
    match env.request, resolved.publish with
    | .act _, .readOnly => pure (.error .readOnly)
    | _, _ =>
      let served ← serve o resolved.state env.request
      pure (finish engine cas resolved env.request served.1 served.2)

/-- **A lost acknowledgement**: after an interruption at publication, the caller reads the head.
The act was applied when the head's entry follows the expected head with the request's action. -/
def applied (cas : σ) (name : String) (expected : Head Digest) (a : Action) : Bool :=
  match Port.root cas (rootName name) with
  | none => false
  | some root =>
    match entryAt cas root.head.digest with
    | .ok (.action parent _ a' _) => parent.digest = expected.digest && toVal a' == toVal a
    | _ => false

end Exchange

end Effect4.Tool
