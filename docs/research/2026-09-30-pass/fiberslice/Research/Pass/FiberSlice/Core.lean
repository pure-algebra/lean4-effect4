import Effect4.Api.HostSession
import Effect4.Laws.Api.HostSession
import Effect4.Program.Profile

/-! Fiber slice of the external lane, the shared core: a prototype admission with derived fiber
declarations and one shape-and-handle recursion. Research evidence, outside the Test root.
Base `be15b062`. Nothing here is production code. The other probe files of this folder import
this module; `run.sh` builds its olean under `.build/` first.

Parts:
1. `envStep` / `envAt`: the environment the checker types a node in, read off the path.
2. `siteDecl` / `fiberDecl`: a fiber's declared type from its recorded site and the checker.
3. `fitsAt` / `fits`: shape and fiber declarations in one recursion, with a located refusal.
4. `admitD` / `acceptReplyD`: the old admission, then the declaration clause on the
   prepared value.
5. `preflightD` / `submitD` / `applyReplyD` / `applyPendingD`: the session steps over it.
6. `replayCheckedFromD`: the tape route over it (for the frontier scenarios). -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSlice
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Session Header Call Reply Key Result Phase BoundCall ReplySlot
  readReply storeReply retire)

/-! ## 1. The environment at a path

`Checker.check` extends the environment at exactly the children `Node.binders` counts
(`Program/Binders.lean`). `envStep` names the types it extends with, read through the
checker's own success projections (`effTy`, `termTy`); every other child keeps the parent's
environment, and a layer's effect body is closed (`Node.closedChild`). -/

def envStep (sig : Signature NativeOp) (env : TyEnv) : Node NativeOp → Nat → Option TyEnv
  | .eff (.bind first _), 1 => (effTy sig env first).map fun f => env ++ [f.answer]
  | .eff (.catchCause body _), 1 => (effTy sig env body).map fun b => env ++ [.causeOf b.error]
  | .eff (.catchIf _ body _), 1 => (effTy sig env body).map fun b => env ++ [b.error]
  | .eff (.select s d _ _), 0 => ((termTy sig env s).bind d.arms).map fun arms => env ++ arms.1
  | .eff (.select s d _ _), 1 => ((termTy sig env s).bind d.arms).map fun arms => env ++ arms.2
  | .eff (.matchCause body _ _), 1 => (effTy sig env body).map fun b => env ++ [b.answer]
  | .eff (.matchCause body _ _), 2 => (effTy sig env body).map fun b => env ++ [.causeOf b.error]
  | .eff (.onExit body _), 1 => (effTy sig env body).map fun b => env ++ [.exitOf b.answer b.error]
  | .eff (.iterate cursorTy initial _ _ _ _), 0 =>
    (termTy sig env initial).map fun c0 => env ++ [cursorTy.getD c0]
  | .eff (.acquireRelease acquire _), 1 =>
    (effTy sig env acquire).map fun a => env ++ [a.answer, .exitOf .unknown .unknown]
  | .stmts (.cons (.bindYield effect) _), 1 => (effTy sig env effect).map fun t => env ++ [t.answer]
  | .layer (.effect _ _), 0 => some []
  | .layer (.effectDiscard _), 0 => some []
  | _, _ => some env

/-- The environment the checker reaches the node at `path` with, from `env` at `n`. -/
def envAt (sig : Signature NativeOp) : Node NativeOp → TyEnv → List Nat → Option TyEnv
  | _, env, [] => some env
  | n, env, i :: rest =>
    match n.child i, envStep sig env n i with
    | some c, some env' => envAt sig c env' rest
    | _, _ => none

/-! ## 2. Declarations from sites -/

/-- The declared type of the fiber a source site forks: the checker's type of the site's
program child, in the environment the checker reaches the site with. Fork, `forkIn` and
`forkScoped` sites are action nodes (`Compile.lean:989-993`, `:1057`); a race entrant's site is
its list cell (`Compile.lean:1030`, `Fibers.lean:1864-1867`). Layer references are expanded
first, as `typeOfProgram` does; a site path the runtime stamps names the same node there. -/
def siteDecl (sig : Signature NativeOp) (root : NativeEff) (site : List Nat) : Option EffTy :=
  let program := root.expandRefs
  match envAt sig (.eff program) [] site, Node.at_ (.eff program) site with
  | some env, some (.action (.fork body _)) => effTy sig env body
  | some env, some (.action (.forkIn body _ _)) => effTy sig env body
  | some env, some (.action (.forkScoped body _)) => effTy sig env body
  | some env, some (.effs (.cons head _)) => effTy sig env head
  | _, _ => none

/-- A live fiber's declared type: the certified program type for the loaded root (fiber 0,
`Api.load`), its site's for a fork. `none` for no such fiber, for a root some other entry made
(`runFork`, `runCallback`: never in a session), and for a fork the runtime made for its own work:
finalizer forks and races without a source Point record `[]` (`Fibers.lean:969`, `:1864`), a
layer build of `merge`/`mergeAll` records the layer's path (`Compile.lean:1450-1455`), which
names no fork node. Nothing is stored: the declaration is a function of the machine's origin
record and the checked program. -/
def fiberDecl (sig : Signature NativeOp) (root : NativeEff) (m : NativeMachine) (id : FiberId) :
    Option EffTy :=
  match m.fiber? id with
  | none => none
  | some f =>
    match f.origin with
    | .root => if id = ⟨0⟩ then typeOfProgram sig root else none
    | .forked _ _ site => siteDecl sig root site

/-! ## 3. One recursion for shape and fiber declarations -/

inductive FitReason
  /-- The value does not have the type's shape (`Val.hasTy`'s verdict at this node). -/
  | shape (expected : Ty)
  /-- A fiber handle whose declaration does not fit the expected handle type. -/
  | fiberDecl (handle : FiberId) (declared : Option EffTy) (expected : Ty)
deriving DecidableEq

/-- A located refusal: the position in the value (child indices) and the reason. -/
structure FitRefusal where
  path : List Nat
  reason : FitReason
deriving DecidableEq

/-- A declaration fits `fiberOf a e` by covariance (`Ty.sub`, decisions row 55). An
undeclared fiber is read at the top: only a target above every type takes it. -/
def declFits (d : Option EffTy) (a e : Ty) : Bool :=
  match d with
  | some d => d.answer.sub a && d.error.sub e
  | none => Ty.sub .unknown a && Ty.sub .unknown e

/-- The first refusal of a list of positions. -/
def firstRefusal {α : Type} (f : α → Nat → Option FitRefusal) : List α → Nat → Option FitRefusal
  | [], _ => none
  | x :: xs, i =>
    match f x i with
    | some r => some r
    | none => firstRefusal f xs (i + 1)

/-- Shape and fiber declarations together over the encoding `Val.hasTy` reads: products as a
two-cell list, Results and exits as constructors, snapshots decoded. Every other type is
`Val.hasTy`'s verdict (scalars, today's number-only cells and deferreds, scopes, contexts,
external handles, causes, literals). Structural on the type. -/
def fitsAt (decl : FiberId → Option EffTy) (allocated : List String) (p : List Nat) (v : Val) :
    Ty → Option FitRefusal
  | .fiberOf a e =>
    match v with
    | Value.fiber id =>
      if declFits (decl ⟨id⟩) a e then none
      else some ⟨p, .fiberDecl ⟨id⟩ (decl ⟨id⟩) (.fiberOf a e)⟩
    | _ => some ⟨p, .shape (.fiberOf a e)⟩
  | .option inner =>
    match v with
    | .none => none
    | .some x => fitsAt decl allocated (p ++ [0]) x inner
    | _ => some ⟨p, .shape (.option inner)⟩
  | .prod ta tb =>
    match v with
    | .list [x, y] =>
      match fitsAt decl allocated (p ++ [0]) x ta with
      | some r => some r
      | none => fitsAt decl allocated (p ++ [1]) y tb
    | _ => some ⟨p, .shape (.prod ta tb)⟩
  | .except error value =>
    match v with
    | .ctor 0 [err] => fitsAt decl allocated (p ++ [0]) err error
    | .ctor 1 [val] => fitsAt decl allocated (p ++ [0]) val value
    | _ => some ⟨p, .shape (.except error value)⟩
  | .exitOf a e =>
    match v with
    | .ctor 0 [x] => fitsAt decl allocated (p ++ [0]) x a
    | .ctor 1 [w] =>
      if Val.hasTy (.ctor 1 [w]) (.exitOf a e) allocated then none
      else some ⟨p, .shape (.exitOf a e)⟩
    | _ => some ⟨p, .shape (.exitOf a e)⟩
  | .list ty =>
    match v with
    | .ctor 3 [_] =>
      match Val.snapshot? v with
      | some ids =>
        firstRefusal (fun (id : FiberId) i => fitsAt decl allocated (p ++ [0, i]) (Value.fiber id.value) ty) ids 0
      | none => some ⟨p, .shape (.list ty)⟩
    | .list values => firstRefusal (fun x i => fitsAt decl allocated (p ++ [i]) x ty) values 0
    | _ => some ⟨p, .shape (.list ty)⟩
  | .union l r =>
    match fitsAt decl allocated p v l with
    | none => none
    | some rl =>
      match fitsAt decl allocated p v r with
      | none => none
      | some rr => some (if rl.reason matches .shape _ then rr else rl)
  | ty => if Val.hasTy v ty allocated then none else some ⟨p, .shape ty⟩

/-- The Boolean judgment: no refusal. -/
def fits (decl : FiberId → Option EffTy) (allocated : List String) (v : Val) (ty : Ty) : Bool :=
  (fitsAt decl allocated [] v ty).isNone

/-! ## 4. Admission: the old check, then the declaration clause on the prepared value -/

/-- The declaration clause of an answer at its row. A success value is checked after
preparation (`externalValue`: an allocation request becomes its handle in the extended
table), in the prepared world; a delayed read is checked at the cell's present contents, as
`admitAnswer` does. Failures carry no handle (`valOfErr_keys`), so they have no clause. -/
def declClause (program : NativeEff) (table : RowTable) (m : NativeMachine) :
    NativeDecision → Option FitRefusal
  | .answerAsync fiber token answer =>
    match requestOf m fiber token with
    | some (.external i, _) =>
      match externalRow table i with
      | some row =>
        let decl := fiberDecl (nativeSignature table) program m
        match answer with
        | .ofExit (.success v) =>
          match externalValue row.answer m.state.externals.allocated v with
          | some (allocated, prepared) => fitsAt decl allocated [] prepared row.answer
          | none => none
        | .ofExit (.failure _) => none
        | .ofRefGet cell =>
          match m.state.refs[cell.index]? with
          | some v => fitsAt decl m.state.externals.allocated [] v row.answer
          | none => none
      | none => none
    | _ => none
  | _ => none

inductive RefusalD
  | admit (why : Refusal)
  | handleDecl (fiber : FiberId) (token : Nat) (why : FitRefusal)
deriving DecidableEq

/-- `admit`, then the declaration clause. -/
def admitD (program : NativeEff) (table : RowTable) (m : NativeMachine) (d : NativeDecision) :
    Option RefusalD :=
  match admit table m d with
  | some why => some (.admit why)
  | none =>
    match d with
    | .answerAsync fiber token _ => (declClause program table m d).map (.handleDecl fiber token)
    | _ => none

def EnvelopeD (program : NativeEff) (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Prop :=
  r.table = table ∧ requestOf m r.fiber r.token = some (r.op, r.request) ∧
    admitD program table m (.answerAsync r.fiber r.token r.completion) = none

instance (program : NativeEff) (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Decidable (EnvelopeD program table m r) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def acceptReplyD (program : NativeEff) (table : RowTable) (m : NativeMachine) (r : RecordedReply) :
    Option NativeDecision :=
  if EnvelopeD program table m r then some (.answerAsync r.fiber r.token r.completion) else none

/-! ## 5. The session steps over the prototype (copies of `HostSession`'s, one call changed) -/

def preflightD {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : Except Api.HostSession.Refusal NativeDecision :=
  if reply.version ≠ Api.HostSession.version then .error .version
  else if reply.session ≠ s.header.session then .error .session
  else match s.active.find? (fun bound => bound.key == reply.key) with
    | none => .error .noCall
    | some bound =>
      if reply.callId ≠ bound.call.callId then .error .callOrder
      else if requestOf s.machine bound.call.fiber bound.token = none then .error .staleCall
      else match acceptReplyD program table s.machine (bound.record reply) with
        | none => .error .envelope
        | some decision => .ok decision

def submitD {program : Api.Program} {table : RowTable} (s : Session program table)
    (reply : Reply) : Result program table :=
  if (readReply s.pending reply.key).isSome then ⟨.refused .pendingReply, s⟩
  else match preflightD s reply with
    | .error why => ⟨.refused why, s⟩
    | .ok _ =>
      if !(s.pending.any fun slot => slot.key == reply.key) then ⟨.refused .noCall, s⟩
      else if !Api.HostProtocol.allows (Api.HostProtocol.observe s.machine) (.submit reply.key)
          (Api.HostProtocol.observe s.machine) then ⟨.refused .protocol, s⟩
      else ⟨.preflight, { s with pending := storeReply s.pending reply }⟩

def applyReplyD {program : Api.Program} {table : RowTable} (s : Session program table)
    (key : Key) : Nat → Result program table
  | 0 => ⟨.frontier, s⟩
  | fuel + 1 =>
    match s.active.find? (fun bound => bound.key == key), readReply s.pending key with
    | some bound, some reply =>
      match preflightD s reply with
      | .error why => ⟨.refused why, s⟩
      | .ok decision =>
        let machine := steppedBy program (fuel + 1) table s.machine decision
        if !Api.HostProtocol.allows (Api.HostProtocol.observe s.machine) (.answer key)
            (Api.HostProtocol.observe machine) then ⟨.refused .protocol, s⟩
        else if requestOf machine bound.call.fiber bound.token = none then
          let next := { s with
            machine := machine
            active := s.active.filter (fun b => b.key != key)
            pending := s.pending.filter (fun slot => slot.key != key)
            applied := s.applied + 1
            consumed := s.consumed ++ [bound.call.callId] }
          ⟨.applied, retire next⟩
        else ⟨.frontier, { s with machine }⟩
    | _, _ => ⟨.refused .noCall, s⟩

def applyPendingD {program : Api.Program} {table : RowTable} (s : Session program table) :
    Nat → Result program table
  | 0 => ⟨.frontier, s⟩
  | fuel + 1 => match Api.HostSession.pendingReplies s with
    | [reply] => applyReplyD s reply.key (fuel + 1)
    | [] => ⟨.refused .noCall, s⟩
    | _ => ⟨.refused .selectionRequired, s⟩

/-! ## 6. The tape route over the prototype (a copy of `replayCheckedFrom`, one call changed) -/

def replayCheckedFromD (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) :
    NativeReplay ⊕ (Nat × NativeDecision × RefusalD × NativeMachine) :=
  letI := evaluatorFor program table
  match tape with
  | [] => .inl (replayEval (interpOf program table) fuel [] m)
  | decision :: rest =>
    match m.stuck with
    | some why => .inl (.stuck why m)
    | none =>
      match admitD program table m decision with
      | some why => .inr (position, decision, why, m)
      | none =>
        let r := stepDecisionState (interpOf program table) fuel m decision
        match oracleRefusal answers table r.1 with
        | some why => .inr (position, decision, .admit why, r.1)
        | none =>
          if r.2 then replayCheckedFromD program fuel answers table (position + 1) rest r.1
          else .inl (.frontier .fuel r.1)
termination_by tape

def replayCheckedD (program : Api.Program) (fuel : Nat) (tape : List Api.Decision)
    (answers : List (Completion Val Err Defect FiberId Ann) := [])
    (table : RowTable := []) : Api.Inspection ⊕ (Nat × Api.Decision × RefusalD × Api.Machine) :=
  match replayCheckedFromD program fuel answers table 0 tape (Api.load program fuel answers) with
  | .inr refusal => .inr refusal
  | .inl (.finished m) => .inl ⟨.finished, m, []⟩
  | .inl (.frontier why m) => .inl ⟨.frontier, m, Api.frontierReasons why m⟩
  | .inl (.stuck why m) => .inl ⟨.stuck why, m, []⟩

end Research.Pass.FiberSlice
