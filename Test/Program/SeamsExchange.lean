import Effect4.Tool.Exchange
import Effect4.Laws.Tool.Exchange
import Test.Program.SeamsS4

/-!
# Sessions over the store: the controls (seams ST4)

Finite evaluations of `Exchange.apply` and `Exchange.load` over the actual store.

* **Tested: loop 5.** Open, edit and start under `Base.head "demo"`; each accepted action commits
  one entry and moves `session/demo`. A later load at the head gives the same run.
* **Tested: loop 6.** Two writers read one head. The second writer's act refuses `staleBase`; at
  the new head, its edit at the old snapshot is the tool's own `stale`, inside the reply. A fork
  starts `session/demo-b` from an entry.
* **Red (tested): stored chains.** A refused stored action, a false `after`, an unsupported
  version, an index out of parent order, a first action without an origin, and a missing parent
  each refuse loading at their place.
* **Control: engines.** A chain whose origin records another engine loads when it replays.
* **Tested: bases and acknowledgement.** A query at an exact entry changes nothing; an action there
  refuses `readOnly`. After a commit whose acknowledgement is lost, the caller finds its action at
  the head.

`load_own`, `apply_commits_once` and `apply_refuses` (`src/Effect4/Laws/Tool/Exchange.lean`) are
the laws.
-/

set_option autoImplicit false

namespace Test.Program.SeamsExchange

open Effect4 Effect4.Program Effect4.Program.Check Effect4.Store Effect4.Tool Effect4.Tool.Exchange
open Test.Program.SeamsS4 (app program sketch budget)

def engine : Digest := zeroDigest

/-- Serve one request at a base. -/
def ex (cas : Cas) (base : Base) (request : Request) :
    Except Exchange.Refusal (Reply × Option (Head Digest) × Cas) :=
  (apply Oracle.uncached engine cas ⟨base, request⟩).value

/-- An exchange's reply, head and store, or nothing. -/
def done (r : Except Exchange.Refusal (Reply × Option (Head Digest) × Cas)) :
    Option (Reply × Head Digest × Cas) :=
  match r with
  | .ok (reply, some head, cas) => some (reply, head, cas)
  | _ => none

def accepted (reply : Reply) : Bool := reply.result.toBool

def changed : NativeEff := .bind (.perform (.external 0) (.lit .unit)) (.succeed (.lit (.nat 1)))

/-! ## Loop 5: persist, stop, resume -/

def step1 := done (ex Cas.empty (.head "demo" none) (.act (.open_ "demo" app sketch)))
def edit (snap : Snap) : Request := .act (.edit snap (.commit [(.at_ [] program, .fill changed)] .keepExact))
def step2 := step1.bind fun (r, h, c) => r.now.bind fun snap =>
  done (ex c (.head "demo" (some h)) (edit snap))
def step3 := step2.bind fun (r, h, c) => r.now.bind fun snap =>
  done (ex c (.head "demo" (some h)) (.act (.start snap budget)))

-- Each accepted action commits one entry and moves the head once.
#guard step1.map (fun (r, h, _) => (accepted r, h.generation)) = some (true, 1)
#guard step2.map (fun (r, h, _) => (accepted r, h.generation)) = some (true, 2)
#guard step3.map (fun (r, h, _) => (accepted r, h.generation)) = some (true, 3)

-- A new process loads the chain at the head: three actions, and run 0 waits on `ask`.
def resumed : Option State := step3.bind fun (_, h, c) =>
  ((load Oracle.uncached c ⟨h.digest⟩).value).toOption
#guard resumed.map (·.transcript.length) = some 3
#guard (resumed.bind fun s => (s.raw.runs[0]?).map fun entry =>
  (entry.live.view.awaiting.map (·.await)).length) = some 1

-- A query at the head answers from the loaded state and publishes nothing.
#guard (step3.bind fun (_, h, c) => done (ex c (.head "demo" (some h)) (.ask .history))).map
  (fun (r, h', _) => (accepted r, h'.generation)) = some (true, 3)

/-! ## Loop 6: two writers -/

-- A starts at head 2; B, still at head 2, edits: the session head moved.
#guard match step2, step3 with
  | some (r, h2, _), some (_, h3, c3) =>
    match r.now with
    | some snap =>
      match ex c3 (.head "demo" (some h2)) (edit snap) with
      | .error (.staleBase "demo" (some expected) (some actual)) => expected == h2 && actual == h3
      | _ => false
    | none => false
  | _, _ => false

-- B reloads at head 3 and edits at its old snapshot: the document moved, inside the reply.
#guard match step1, step3 with
  | some (r1, _, _), some (_, h3, c3) =>
    match r1.now with
    | some snap =>
      match done (ex c3 (.head "demo" (some h3)) (edit snap)) with
      | some (reply, h, _) => !accepted reply && h == h3
      | none => false
    | none => false
  | _, _ => false

-- B forks from the first entry instead: a new session continues from it.
#guard match step1, step3 with
  | some (r1, h1, _), some (_, _, c3) =>
    match r1.now with
    | some snap =>
      match done (ex c3 (.fork ⟨h1.digest⟩ "demo-b") (.act (.start snap budget))) with
      | some (reply, h, c) => accepted reply && h.generation == 1 &&
          (c.store.root? (rootName "demo-b")).isSome
      | none => false
    | none => false
  | _, _ => false

/-! ## Exact entries and lost acknowledgements -/

-- A query at an exact entry changes nothing; an action there refuses `readOnly`.
#guard match step1 with
  | some (_, h1, c1) =>
    match ex c1 (.at_ ⟨h1.digest⟩) (.ask .history) with
    | .ok (reply, _, c) => accepted reply && c.store.nodes.length == c1.store.nodes.length
    | .error _ => false
  | none => false
#guard match step1 with
  | some (_, h1, c1) =>
    match ex c1 (.at_ ⟨h1.digest⟩) (.act .reset) with
    | .error .readOnly => true
    | _ => false
  | none => false

-- The acknowledgement of the start was lost: the head's entry follows head 2 with the start.
#guard match step2, step3 with
  | some (r, h2, _), some (_, _, c3) =>
    match r.now with
    | some snap => applied c3 "demo" h2 (.start snap budget) && !applied c3 "demo" h2 .reset
    | none => false
  | _, _ => false

/-! ## Stored chains that do not load -/

def origin (protocol : Nat := protocolVersion) (engine : Digest := engine) : SessionEntry :=
  .origin protocol codecVersion engine

def programRef : Ref NativeEff := address sketch.program

/-- Commit entries directly, with the schemas and the program they reference. -/
def forged (entries : List SessionEntry) : Option Cas :=
  match Cas.empty.commit ⟨[genesisNode, nodeOf (shape SessionEntry).document,
      nodeOf (shape NativeEff).document, nodeOf sketch.program] ++ entries.map nodeOf, []⟩ with
  | .ok (_, cas) => some cas
  | .error _ => none

def loadAt (entries : List SessionEntry) (head : SessionEntry) : Option (Except LoadRefusal State) :=
  (forged entries).map fun cas => (load Oracle.uncached cas (address head)).value

def opening (parent : SessionEntry) (after : Option (Ref NativeEff) := some programRef) :
    SessionEntry :=
  .action (address parent) 0 (.open_ "demo" app sketch) after

-- Control: the honest one-action chain loads, under another engine too.
#guard (loadAt [origin, opening origin] (opening origin)).map (·.toOption.isSome) = some true
#guard (loadAt [origin (engine := (address program).digest), opening (origin (engine := (address program).digest))]
  (opening (origin (engine := (address program).digest)))).map (·.toOption.isSome) = some true

-- A refused stored action refuses at its index.
#guard match loadAt [origin, .action (address origin) 0 .reset none] (.action (address origin) 0 .reset none) with
  | some (.error (.refused 0 .noDocument)) => true
  | _ => false
-- A false `after` refuses at its index.
#guard match loadAt [origin, opening origin none] (opening origin none) with
  | some (.error (.after 0)) => true
  | _ => false
-- An unsupported protocol version refuses.
#guard match loadAt [origin 2, opening (origin 2)] (opening (origin 2)) with
  | some (.error (.version 2 1)) => true
  | _ => false
-- An entry at index 1 whose parent is the origin reaches the origin while index 0 is owed.
#guard match loadAt [origin, .action (address origin) 1 .reset none] (.action (address origin) 1 .reset none) with
  | some (.error (.early d 0)) => d == (address origin).digest
  | _ => false
-- red (tested): a head recording index 5 over an action that records 0 where the walk expects 4
-- is out of order, named with both indices (it was the same `parent` refusal as the case above).
#guard match loadAt [origin, opening origin, .action (address (opening origin)) 0 .reset none,
    .action (address (.action (address (opening origin)) 0 .reset none)) 5 .reset none]
    (.action (address (.action (address (opening origin)) 0 .reset none)) 5 .reset none) with
  | some (.error (.outOfOrder d 4 0)) => d == (address (.action (address (opening origin)) 0 .reset none : SessionEntry)).digest
  | _ => false
-- A first action whose parent is another action names no origin.
#guard match loadAt [origin, opening origin, .action (address (opening origin)) 0 .reset none]
    (.action (address (opening origin)) 0 .reset none) with
  | some (.error (.noOrigin d)) => d == (address (opening origin)).digest
  | _ => false
-- A missing parent does not read.
#guard match (forged [origin]).map fun cas => (load Oracle.uncached cas (address (opening origin))).value with
  | some (.error (.unreadable _ (.missing _))) => true
  | _ => false

end Test.Program.SeamsExchange
