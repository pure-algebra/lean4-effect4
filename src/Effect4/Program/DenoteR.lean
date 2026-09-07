import Effect4.Program.Sched
import Effect4.Program.Agreement

/-!
# Structural denotation over stores and fibers (R2, restated by P2)

Contract: `Test/contracts/program-denote-r.contract.md`. Design and authorized
corrections: `docs/research/2026-09-06-w3-r2-continuation.md`,
`docs/research/2026-09-06-r3-r4-implementation.md` and the P2 phase model of
`docs/research/2026-09-06-p0-fable-record.md` §4.

`denoteR root e p` is structural on the existing `Eff` at a `Point`; `p.fuel` is
the only budget and is spent as `compileEff` spends it. A frontier carries the
residual point, never a failed exit. Loops and generators are not unfolded here:
they are the runtime operations `FiberOp.loop` and `FiberOp.gen`, whose later
iterations the evaluator runs inside the body's delivery through its saved slots,
with the compile's own navigation (`InterpR.walkR`). `inlineYield` records exactly
which yielded source forms expose an immediate exit before the iterator resumes.

The counted checkpoints the host spends where the term has no work of its own are
explicit: `suspend` in front of a suspension, a decided branch, a yieldable error's
failure and the generator and loop entries, and `sync` for a pure thunk's value.
Control erasure removes them with the boundary markers, so after erasure the
straight fragment restricts to `Denote.denote` when the compile budget covers its
depth. The raw terms retain handler and cleanup boundaries (`E4-SCHED-CE-004`).
Fiber nodes are the term scheduler's interface, not a handler semantics or a
simulation theorem. In particular the placeholder `rHandler` must not be used to
interpret a frontier as a finished result (`RDEN-FB-HANDLER`). Mask nodes carry
addressed or synthesized bodies; their execution and interruption rules live in the
evaluator (`RDEN-FB-SCHEDULER`). Program rows and acquisition/release remain
unsupported frontiers, as in `compileEff` (`RDEN-FB-UNSUPPORTED`).
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-- A live frontier at a point. -/
def pending (reason : FrontierReason) (at_ : Point) : RProgram :=
  .vis (.inr (.frontier reason at_)) Effects.Program.pure

/-- Value continuations short-circuit on a failed exit. -/
def seqR (k : Val → RProgram) : ExitV → RProgram
  | .success v => k v
  | .failure c => .pure (.failure c)

/-- Invoke a source callback against the completed exits visible at invocation.
The query is administrative and is consumed by `prepareR`, not the run loop. -/
def constructR (k : List (FiberId × ExitV) → RProgram) : RProgram :=
  .vis (.inr .construction) k

/-- Resolve construction queries in freshly built code, including the eager body
of a guard. Its saved exit callback is constructed only when that callback runs.
Counted operations retain their continuations untouched. -/
def prepareR (completed : List (FiberId × ExitV)) : RProgram → RProgram
  | .pure ex => .pure ex
  | .vis (.inr .construction) k => prepareR completed (k completed)
  | .vis (.inr (.guard_ kind)) k => .vis (.inr (.guard_ kind)) fun
    | none => prepareR completed (k none)
    | some ex => k (some ex)
  | .vis op k => .vis op k

/-- Retain a continuation boundary. The normal branch closes it explicitly;
an interrupted body resumes through the saved exit branch instead. -/
def guardR (kind : GuardKind) (body : RProgram) : RProgram :=
  .vis (.inr (.guard_ kind)) fun
    | none => body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure
    | some ex => .pure ex

/-- The optional cleanup effect returned by an OnExit callback follows the
same ordinary handlers as `Machine.finalizerCode` (`internal/effect.ts:4021-4029`). -/
def finalizerR (ex : ExitV) (cleanup : RProgram) : RProgram :=
    (guardR .onSuccess
      (match ex with
       | .success _ => cleanup
       | .failure _ => (guardR .onFailure cleanup).bind fun
           | .success v => .pure (.success v)
           | .failure c => .pure (Exit.restoreAfterFinalizer ex (.failure c)))).bind (seqR fun _ =>
      .vis (.inr (.finishFinalizer ex)) Effects.Program.pure)

/-- An exit finalizer has its own boundary, then restores the body's exit and mask.
The runtime implements the mask; erasure below removes only these control markers. -/
def onExitR (body : RProgram) (fin : ExitV → RProgram)
    (interruptible : Bool := false) : RProgram :=
  (guardR (.onExit interruptible) body).bind fun ex => finalizerR ex (fin ex)

/-- The counted checkpoint that returns code: `Suspend` at `p`. -/
def suspendR (p : Point) (body : RProgram) : RProgram :=
  .vis (.inr (.suspend p)) fun _ => body

/-- A store operation answering its value. -/
def storeR (op : SyncOp) : RProgram :=
  .vis (.inl op) fun v => .pure (.success v)

/-- A value-answering fiber operation answering its value. -/
def fiberValR (op : FiberOp) (h : op.answer = Val) : RProgram :=
  .vis (.inr op) fun v => .pure (.success (h ▸ v))

/-- Forget control boundaries and checkpoints for the store meaning, retaining every
other operation. This is an erasure, not a scheduler or a handler for interruption. -/
def controlErasure : Effects.Handler RSig (Effects.Program RSig) where
  handle
    | .inr .construction => .pure []
    | .inr (.guard_ _) => .pure none
    | .inr (.unguard ex) | .inr (.finishFinalizer ex) => .pure ex
    | .inr (.suspend _) => .pure Val.unit
    | .inr (.sync v) => .pure v
    | op => .vis op Effects.Program.pure

def eraseControl {A : Type} (program : Effects.Program RSig A) : Effects.Program RSig A :=
  Effects.interpret controlErasure program

theorem eraseControl_pure {A : Type} (a : A) :
    eraseControl (Effects.Program.pure a) = .pure a := rfl

theorem eraseControl_bind {A B : Type} (p : Effects.Program RSig A)
    (k : A → Effects.Program RSig B) :
    eraseControl (p.bind k) = (eraseControl p).bind (fun a => eraseControl (k a)) :=
  Effects.interpret_bind controlErasure p k

theorem eraseControl_guardR (kind : GuardKind) (body : RProgram) :
    eraseControl (guardR kind body) = eraseControl body := by
  change eraseControl (body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure) = _
  rw [eraseControl_bind]
  exact Effects.Program.bind_pure_right _

theorem eraseControl_onExitR (body : RProgram) (fin : ExitV → RProgram) (flag : Bool) :
    eraseControl (onExitR body fin flag) =
      (eraseControl body).bind fun ex => (eraseControl (fin ex)).bind fun fex =>
        .pure (Exit.restoreAfterFinalizer ex (finVoid fex)) := by
  simp only [onExitR, finalizerR, eraseControl_bind, eraseControl_guardR]
  congr 1
  funext ex
  cases ex with
  | success v =>
    congr 1
    funext fex
    cases fex <;> rfl
  | failure cause =>
    simp only [eraseControl_bind, eraseControl_guardR, Effects.Program.bind_assoc]
    congr 1
    funext fex
    cases fex <;> rfl

theorem eraseControl_suspendR (p : Point) (body : RProgram) :
    eraseControl (suspendR p body) = eraseControl body := rfl

theorem eraseControl_sync (v : Val) (k : Val → RProgram) :
    eraseControl (.vis (.inr (.sync v)) k) = eraseControl (k v) := rfl

theorem eraseControl_constructR (k : List (FiberId × ExitV) → RProgram) :
    eraseControl (constructR k) = eraseControl (k []) := rfl

/-- Race entrants use the same list-node addresses as `actionAt.entrants`. -/
def entrantPoints : Effs NativeOp → Point → List Point
  | .nil, _ => []
  | .cons _ rest, p => p.child 0 :: entrantPoints rest (p.child 1)

def racePoints (root : NativeEff) (p : Point) : List Point :=
  match Node.at_ (.eff root) p.path with
  | some (.eff (.withFiber (.raceAll es))) => entrantPoints es ((p.child 0).child 0)
  | _ => []

/-- The term of the fiber action `actionAt` answers at a point. Program-valued fields of
the action are represented by their source addresses, never stored as `Prim`. -/
def denoteFiberAction (root : NativeEff) (p : Point) : NAction → RProgram
  | .fork _ options =>
    .vis (.inr (.fork (.at_ ((p.child 0).child 0)) options)) fun v => .pure (.success v)
  | .forkIn _ options scope =>
    .vis (.inr (.forkIn ((p.child 0).child 0) options scope)) fun v => .pure (.success v)
  | .forkScoped _ options =>
    .vis (.inr (.forkScoped ((p.child 0).child 0) options)) Effects.Program.pure
  | .runIn target scope =>
    .vis (.inr (.runIn target scope)) fun v => .pure (.success v)
  | .interrupt target => .vis (.inr (.interrupt target)) fun v => .pure (.success v)
  | .interruptAs target who => .vis (.inr (.interruptAs target who)) fun v => .pure (.success v)
  | .interruptScoped target =>
    .vis (.inr (.interruptScoped target)) fun v => .pure (.success v)
  | .interruptAll targets who =>
    .vis (.inr (.interruptAll targets who)) fun v => .pure (.success v)
  | .awaitAll targets => .vis (.inr (.awaitAll targets)) fun v => .pure (.success v)
  | .awaitAllFailFast targets =>
    .vis (.inr (.awaitAllFailFast targets)) fun v => .pure (.success v)
  | .snapshotChildren => .vis (.inr .snapshotChildren) fun v => .pure (.success v)
  | .awaitNewChildren snapshot =>
    .vis (.inr (.awaitNewChildren snapshot)) fun v => .pure (.success v)
  | .raceAll _ => .vis (.inr (.raceAll (racePoints root p))) Effects.Program.pure
  | .setInterruptible _ flag =>
    .vis (.inr (.mask flag (.at_ (p.child 0)))) Effects.Program.pure
  | .setContext ctx => .vis (.inr (.setContext ctx)) fun v => .pure (.success v)
  | .getContext => .vis (.inr .getContext) fun v => .pure (.success v)
  | .getId => .vis (.inr .getId) fun v => .pure (.success v)
  | .closeScope scope ex => .vis (.inr (.closeScope scope ex)) Effects.Program.pure
  | .refuse cause => .vis (.inr (.refuse cause)) fun v => .pure (.success v)
  | .dropObservers token => .vis (.inr (.dropObservers token)) fun v => .pure (.success v)
  | .cancelRace race => .vis (.inr (.cancelRace race)) fun v => .pure (.success v)
  -- `forkScoped` is `flatMap(scope, scope => forkIn(self, scope, options))` (`:5381-5406`,
  -- §20): the counted service read, then `forkIn` on the handle it answered
  | .ambientScope =>
    match Node.at_ (.eff root) p.path with
    | some (.eff (.withFiber (.forkScoped _ options))) =>
      (guardR .onSuccess (fiberValR .ambientScope rfl)).bind (seqR fun
        | .scopeHandle s =>
          .vis (.inr (.forkIn ((p.child 0).child 0) options s)) fun v => .pure (.success v)
        | _ => .pure badShapeExit)
    | _ => .pure badShapeExit
  -- the parallel close's step is a store program, never a source node
  | .closePar _ => .pure badShapeExit

/-- The fiber action selected by the actual point lookup. A point that names no action is
the frame machine's `suspendBody` refusal after its counted step. -/
def denoteAction (root : NativeEff) (p : Point) : RProgram :=
  match actionAt root p with
  | none => suspendR p (.pure outsideExit)
  | some action => denoteFiberAction root p action

/-- Async registration answers with an exit; failure is not a successful error value.
The request and registration name retain the exact `Deferred.await` decoding. -/
def denoteAsync (request : Term) (p : Point) : RProgram :=
  match evalTerm p.env request with
  | none => .pure badShapeExit
  | some value =>
    match NativeOp.awaitCellOf value with
    | none => .pure badShapeExit
    | some cell => .vis (.inr (.async (.registerAwait cell) value)) Effects.Program.pure

/-- A yielded source form with an immediate `Prim.success` or `Prim.failure` head.
`sync`, `yieldError` with a valid argument, and compound frames are not inline exits;
`exit` of an immediate exit is that exit's success (`internal/effect.ts:3621-3622`), and
a loop never is (its compile is a `Suspend`). The definition inspects source data and the point's captured completed exits;
its compiler-head equation is checked below. -/
def inlineYield : NativeEff → Point → Option ExitV
  | e, p =>
    if p.fuel = 0 then none else
    match e with
    | .succeed t => some (match evalTerm p.env t with
      | some v => .success v | none => badShapeExit)
    | .fail t => some (match evalTerm p.env t with
      | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
    | .failCause t => some (match causeOf p.env t with
      | some c => .failure c | none => badShapeExit)
    | .yieldError t => match evalTerm p.env t with
      | some _ => none | none => some badShapeExit
    | .perform op request =>
      match (NativeOp.row op).kind with
      | .sync => match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
        | some _ => none | none => some badShapeExit
      | .async => match (evalTerm p.env request).bind NativeOp.awaitCellOf with
        | some _ => none | none => some badShapeExit
      | .program => none
    | .callback op request =>
      match (NativeOp.row op).kind with
      | .async => match (evalTerm p.env request).bind NativeOp.awaitCellOf with
        | some _ => none | none => some badShapeExit
      | _ => some badShapeExit
    | .awaitFiber target mode => match evalTerm p.env target with
      | some (.fiber id) => p.awaitExit id mode | _ => some badShapeExit
    | .exit b => (inlineYield b (p.child 0)).map fun ex => .success (reifyExitVal ex)
    | .choose _ left right => match p.tape with
      | true :: rest => inlineYield left { p with path := p.path ++ [0], tape := rest }
      | false :: rest => inlineYield right { p with path := p.path ++ [1], tape := rest }
      | [] => none
    | _ => none

/-- The structural denotation at an address. Every arm names the `compileEff` arm it
mirrors; the counted checkpoints are where the frame machine spends a primitive that the
term would otherwise elide. -/
def denoteR (root : NativeEff) : NativeEff → Point → RProgram
  | e, p =>
    match p.fuel with
    | 0 => pending .compileFuel p
    | _ + 1 =>
      match e with
      | .succeed t => .pure (match evalTerm p.env t with
        | some v => .success v | none => badShapeExit)
      | .fail t => .pure (match evalTerm p.env t with
        | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit)
      | .failCause t => .pure (match causeOf p.env t with
        | some c => .failure c | none => badShapeExit)
      -- `Prim.yieldableError`: one counted step, then the failure.
      | .yieldError t => match evalTerm p.env t with
        | some v => suspendR p (.pure (.failure (Cause.fail (errOf v))))
        | none => .pure badShapeExit
      -- `Prim.sync (pure p)`: the value through the `answered` phase.
      | .sync t => .vis (.inr (.sync ((evalTerm p.env t).getD Val.unit))) fun v => .pure (.success v)
      -- `Prim.suspend (body child)`: the counted step, then the body.
      | .suspend b => suspendR p (constructR fun completed =>
          denoteR root b ({ p with completed }.child 0))
      | .perform op request =>
        match (NativeOp.row op).kind with
        | .sync =>
          match (evalTerm p.env request).bind (NativeOp.syncOpOf op) with
          | some operation => .vis (.inl operation) fun v => .pure (.success v)
          | none => .pure badShapeExit
        | .async => denoteAsync request p
        | .program => pending .unsupported p
      | .bind a b => (guardR .onSuccess (denoteR root a (p.child 0))).bind
          (seqR fun v => constructR fun completed =>
            denoteR root b ({ p with completed }.childWith 1 v))
      -- `Prim.suspend (body p)`, decided by `suspendBodyAt`: the counted step, then the branch.
      | .branch test a b => suspendR p (constructR fun completed => match evalTerm p.env test with
          | some (.bool true) => denoteR root a ({ p with completed }.child 0)
          | some (.bool false) => denoteR root b ({ p with completed }.child 1)
          | _ => .pure badShapeExit)
      -- `Effect.exit` folds an immediate exit; otherwise the both-arm boundary.
      | .exit b =>
        match inlineYield b (p.child 0) with
        | some ex => .pure (.success (reifyExitVal ex))
        | none => (guardR .all (denoteR root b (p.child 0))).bind fun ex =>
            .pure (.success (reifyExitVal ex))
      | .catchCause b h => (guardR .onFailure (denoteR root b (p.child 0))).bind fun
        | .success v => .pure (.success v)
        | .failure c => constructR fun completed =>
            denoteR root h ({ p with completed }.childWith 1 (.exitErr c))
      | .matchCause b v c => (guardR .all (denoteR root b (p.child 0))).bind fun
        | .success x => constructR fun completed =>
            denoteR root v ({ p with completed }.childWith 1 x)
        | .failure cause => constructR fun completed =>
            denoteR root c ({ p with completed }.childWith 2 (.exitErr cause))
      | .onExit b f => onExitR (denoteR root b (p.child 0)) fun ex =>
          constructR fun completed => denoteR root f ({ p with completed }.childWith 1 (reifyExitVal ex))
      -- `Prim.suspend (body p)` then `Prim.iterator (gen p [] false) unit`: the entry.
      | .gen _ => suspendR p (.vis (.inr (.gen p)) Effects.Program.pure)
      -- `Prim.suspend (body p)` then `Prim.whileLoop (loop p) cursor`: the entry.
      | .whileLoop initial _ _ _ => suspendR p (match evalTerm p.env initial with
          | some cursor => .vis (.inr (.loop p cursor)) Effects.Program.pure
          | none => .pure badShapeExit)
      -- `Prim.yieldNowWith`: the park answers the void value, which the continuation passes
      -- on (the frame resumes with `success void`; an answer is never discarded)
      | .yieldNow priority => .vis (.inr (.yieldNow priority)) fun v => .pure (.success v)
      | .callback op request =>
        match (NativeOp.row op).kind with
        | .async => denoteAsync request p
        | _ => .pure badShapeExit
      | .awaitFiber target mode =>
        match evalTerm p.env target with
        | some (.fiber id) =>
          match p.awaitExit id mode with
          | some exit => .pure exit
          | none => match mode with
            | .joinEffect => .vis (.inr (.await id .joinEffect)) Effects.Program.pure
            | .awaitValue => .vis (.inr (.await id .awaitValue)) fun v => .pure (.success v)
        | _ => .pure badShapeExit
      | .uninterruptible _ | .interruptible _ | .withFiber _ => denoteAction root p
      -- `scoped` is one WithFiber whose eager body is child 0
      -- (`internal/effect.ts:3938-3948`). Context restoration is callback glue.
      | .scoped _ => .vis (.inr (.scoped (p.child 0))) Effects.Program.pure
      | .acquireRelease _ _ => pending .unsupported p
      | .choose _ left right =>
        match p.tape with
        | true :: rest => denoteR root left { p with path := p.path ++ [0], tape := rest }
        | false :: rest => denoteR root right { p with path := p.path ++ [1], tape := rest }
        | [] => pending .unansweredChoice p

/-! ## The address and frontier equations -/

theorem denoteR_zero (root e : NativeEff) (p : Point) (h : p.fuel = 0) :
    denoteR root e p = pending .compileFuel p := by
  unfold denoteR
  simp only [h]

theorem denoteR_bind (root : NativeEff) (a b : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.bind a b) p =
      (guardR .onSuccess (denoteR root a (p.child 0))).bind
        (seqR fun v => constructR fun completed =>
          denoteR root b ({ p with completed }.childWith 1 v)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_suspend (root : NativeEff) (b : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.suspend b) p = suspendR p (constructR fun completed =>
      denoteR root b ({ p with completed }.child 0)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_branch (root : NativeEff) (t : Term) (a b : NativeEff) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (.branch t a b) p =
      suspendR p (constructR fun completed => match evalTerm p.env t with
        | some (.bool true) => denoteR root a ({ p with completed }.child 0)
        | some (.bool false) => denoteR root b ({ p with completed }.child 1)
        | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

/-- The exit arm: an immediate exit folds (row D1 of the P0 record); otherwise the body
runs inside a both-arm boundary and its exit is reified. -/
theorem denoteR_exit (root : NativeEff) (b : NativeEff) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.exit b) p =
      match inlineYield b (p.child 0) with
      | some ex => .pure (.success (reifyExitVal ex))
      | none => (guardR .all (denoteR root b (p.child 0))).bind fun ex =>
          .pure (.success (reifyExitVal ex)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_choose (root : NativeEff) (site : Nat) (a b : NativeEff) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (.choose site a b) p =
      match p.tape with
      | true :: rest => denoteR root a { p with path := p.path ++ [0], tape := rest }
      | false :: rest => denoteR root b { p with path := p.path ++ [1], tape := rest }
      | [] => pending .unansweredChoice p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_withFiber (root : NativeEff) (action : ActionTerm NativeOp) (p : Point)
    (h : p.fuel ≠ 0) :
    denoteR root (.withFiber action) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_gen (root : NativeEff) (body : Stmts NativeOp) (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.gen body) p = suspendR p (.vis (.inr (.gen p)) Effects.Program.pure) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

theorem denoteR_whileLoop (root : NativeEff) (initial test step : Term) (body : NativeEff)
    (p : Point) (h : p.fuel ≠ 0) :
    denoteR root (.whileLoop initial test step body) p =
      suspendR p (match evalTerm p.env initial with
        | some cursor => .vis (.inr (.loop p cursor)) Effects.Program.pure
        | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]

/-- Only the two immediate exit constructors; all other heads require a machine step. -/
def headExit : NCode → Option ExitV
  | .success v => some (.success v)
  | .failure c => some (.failure c)
  | _ => none

theorem headExit_eq_asExit? (c : NCode) : headExit c = c.asExit? := by
  cases c <;> rfl

theorem inlineYield_eq_headExit (e : NativeEff) (p : Point) :
    inlineYield e p = headExit (compileEff e p) := by
  cases hf : p.fuel with
  | zero =>
    cases e <;> first
      | (simp only [inlineYield, compileEff, hf, ↓reduceIte, frontier, headExit]; done)
      | (rename_i a; cases a <;> simp only [inlineYield, compileEff, hf, ↓reduceIte, frontier, headExit])
  | succ f =>
    cases e with
    | choose site a b =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases ht : p.tape with
      | nil => rfl
      | cons choice rest =>
        cases choice <;> dsimp only
        · exact inlineYield_eq_headExit b _
        · exact inlineYield_eq_headExit a _
    | exit b =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      rw [inlineYield_eq_headExit b (p.child 0), headExit_eq_asExit? (compileEff b (p.child 0))]
      cases hx : (compileEff b (p.child 0)).asExit? <;> rfl
    | perform op request =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases hk : (NativeOp.row op).kind with
      | sync =>
        cases hv : evalTerm p.env request with
        | none => rfl
        | some value =>
          dsimp only [Option.bind]
          cases NativeOp.syncOpOf op value <;> rfl
      | async => cases (evalTerm p.env request).bind NativeOp.awaitCellOf <;> rfl
      | program => rfl
    | callback op request =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases hk : (NativeOp.row op).kind with
      | sync | program => rfl
      | async => cases (evalTerm p.env request).bind NativeOp.awaitCellOf <;> rfl
    | succeed t | fail t | yieldError t =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env t <;> rfl
    | failCause c =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases causeOf p.env c <;> rfl
    | awaitFiber target mode =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte]
      cases evalTerm p.env target with
      | none => rfl
      | some v =>
        cases v with
        | fiber id =>
          simp only
          cases hx : p.awaitExit id mode with
          | none => rfl
          | some ex => cases ex <;> rfl
        | _ => rfl
    -- a `forkScoped` node compiles to its wrapper's `OnSuccess` (§20); every other action
    -- to the `WithFiber`; neither is an immediate exit
    | withFiber a =>
      cases a <;> simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte, headExit]
    | sync _ | suspend _ | bind _ _ | gen _ | catchCause _ _ | matchCause _ _ _
    | onExit _ _ | uninterruptible _ | interruptible _ | branch _ _ _ | whileLoop _ _ _ _
    | yieldNow _ | «scoped» _ | acquireRelease _ _ =>
      simp only [inlineYield, compileEff, hf, Nat.succ_ne_zero, ↓reduceIte, headExit, frontier]
termination_by structural e

/-- A straight source form that `inlineYield` classifies as an immediate exit denotes to
exactly that exit: the fold of `denoteR`'s `exit` arm is the body's straight meaning. -/
theorem denote_of_inlineYield : ∀ (b : NativeEff) (q : Point) {exit : ExitV},
    Straight b = true → inlineYield b q = some exit → denote b q.env = Effects.Program.pure exit
  | .succeed t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .fail t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .failCause c, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · simp only [Option.some.injEq] at h
      subst h
      rfl
  | .yieldError t, q, exit, _, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · rcases hx : evalTerm q.env t with _ | x
      · simp only [hx, Option.some.injEq] at h
        subst h
        simp only [denote, hx]
        rfl
      · simp [hx] at h
  | .perform op r, q, exit, hs, h => by
    have hk := Straight.perform_sync hs
    simp only [inlineYield, hk] at h
    split at h
    · cases h
    · rcases hx : evalTerm q.env r with _ | x
      · simp only [hx, Option.bind, Option.some.injEq] at h
        subst h
        simp only [denote, hk, hx, Option.bind]
        rfl
      · rcases ho : NativeOp.syncOpOf op x with _ | o
        · simp only [hx, ho, Option.bind, Option.some.injEq] at h
          subst h
          simp only [denote, hk, hx, ho, Option.bind]
          rfl
        · simp [hx, ho] at h
  | .exit b, q, exit, hs, h => by
    simp only [inlineYield] at h
    split at h
    · cases h
    · rcases hy : inlineYield b (q.child 0) with _ | inner
      · simp [hy] at h
      · simp only [hy, Option.map, Option.some.injEq] at h
        subst h
        have hd : denote b q.env = Effects.Program.pure inner :=
          denote_of_inlineYield b (q.child 0) hs hy
        rw [denote, hd]
        rfl
  | .sync _, q, exit, _, h | .suspend _, q, exit, _, h | .bind _ _, q, exit, _, h
  | .branch _ _ _, q, exit, _, h | .catchCause _ _, q, exit, _, h
  | .matchCause _ _ _, q, exit, _, h | .onExit _ _, q, exit, _, h => by
    simp [inlineYield] at h
  | .gen _, _, _, hs, _ | .uninterruptible _, _, _, hs, _ | .interruptible _, _, _, hs, _
  | .whileLoop _ _ _ _, _, _, hs, _ | .yieldNow _, _, _, hs, _ | .callback _ _, _, _, hs, _
  | .awaitFiber _ _, _, _, hs, _ | .withFiber _, _, _, hs, _ | .«scoped» _, _, _, hs, _
  | .acquireRelease _ _, _, _, hs, _ | .choose _ _ _, _, _, hs, _ => by
    simp [Straight] at hs

/-! ## Restriction to the existing straight denotation -/

/-- The compile budget of a straight program is positive: its depth is. -/
theorem fuel_ne_zero_of_depth {e : NativeEff} {p : Point} (hp : Agreement.depth e ≤ p.fuel) :
    p.fuel ≠ 0 := by
  have := Agreement.depth_pos e
  omega

/-- After erasing the control markers and checkpoints, the straight fragment is the
store denotation whenever the compile budget covers its depth. -/
theorem denoteR_straight (root : NativeEff) : ∀ (e : NativeEff) (p : Point),
    Straight e = true → Agreement.depth e ≤ p.fuel →
    eraseControl (denoteR root e p) = Effects.Program.inl (denote e p.env)
  | .succeed t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => rw [denoteR, hf, denote]; rfl
  | .fail t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => rw [denoteR, hf, denote]; rfl
  | .failCause t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => rw [denoteR, hf, denote]; rfl
  | .yieldError t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      rw [denoteR, hf, denote]
      cases hx : evalTerm p.env t <;> rfl
  | .sync t, p, _, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f => rw [denoteR, hf, denote]; rfl
  | .suspend b, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      simp only [denoteR, hf]
      rw [eraseControl_suspendR, eraseControl_constructR, denote]
      exact denoteR_straight root b ({ p with fuel := f + 1, completed := [] }.child 0) hs
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
  | .perform op request, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hk := Straight.perform_sync hs
      simp only [denoteR, hf, denote, hk]
      cases (evalTerm p.env request).bind (NativeOp.syncOpOf op) <;> rfl
  | .bind a b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos (.bind a b); omega
    have hab := Straight.bind hs
    have ha := denoteR_straight root a (p.child 0) hab.1
      (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    rw [denoteR_bind root a b p hpos, eraseControl_bind, eraseControl_guardR,
      ha, denote, Effects.Program.inl_bind]
    congr 1
    funext ex
    cases ex with
    | failure c => rfl
    | success v =>
      exact denoteR_straight root b ({ p with completed := [] }.childWith 1 v) hab.2
        (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
  | .branch test a b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos (.branch test a b); omega
    have hab := Straight.branch hs
    rw [denoteR_branch root test a b p hpos, eraseControl_suspendR, eraseControl_constructR, denote]
    split
    · rename_i ht
      rw [ht]
      exact denoteR_straight root a ({ p with completed := [] }.child 0) hab.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    · rename_i ht
      rw [ht]
      exact denoteR_straight root b ({ p with completed := [] }.child 1) hab.2
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    · split
      · contradiction
      · contradiction
      · rfl
  | .exit b, p, hs, hp => by
    have hpos : p.fuel ≠ 0 := by have := Agreement.depth_pos (.exit b); omega
    have hb := denoteR_straight root b (p.child 0) hs
      (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
    rw [denoteR_exit root b p hpos]
    cases hy : inlineYield b (p.child 0) with
    | none =>
      dsimp only
      rw [eraseControl_bind, eraseControl_guardR, hb, denote, Effects.Program.inl_bind]
      rfl
    | some ex =>
      dsimp only
      have hd : denote b p.env = Effects.Program.pure ex :=
        denote_of_inlineYield b (p.child 0) hs hy
      rw [eraseControl_pure, denote, hd]
      rfl
  | .catchCause b h, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hbh := Straight.catchCause hs
      have hb := denoteR_straight root b (p.child 0) hbh.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      rw [denoteR, hf, eraseControl_bind, eraseControl_guardR,
        hb, denote, Effects.Program.inl_bind]
      congr 1
      funext ex
      cases ex with
      | success v => rfl
      | failure c =>
        exact denoteR_straight root h ({ p with fuel := f + 1, completed := [] }.childWith 1 (.exitErr c)) hbh.2
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
  | .matchCause b v c, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hparts := Straight.matchCause hs
      have hb := denoteR_straight root b (p.child 0) hparts.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      rw [denoteR, hf, eraseControl_bind, eraseControl_guardR,
        hb, denote, Effects.Program.inl_bind]
      congr 1
      funext ex
      cases ex with
      | success value =>
        exact denoteR_straight root v ({ p with fuel := f + 1, completed := [] }.childWith 1 value) hparts.2.1
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
      | failure cause =>
        exact denoteR_straight root c ({ p with fuel := f + 1, completed := [] }.childWith 2 (.exitErr cause)) hparts.2.2
          (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
  | .onExit b fin, p, hs, hp => by
    cases hf : p.fuel with
    | zero => exact (fuel_ne_zero_of_depth hp hf).elim
    | succ f =>
      have hparts := Straight.onExit hs
      have hb := denoteR_straight root b (p.child 0) hparts.1
        (by simp only [Agreement.depth] at hp; simp only [Point.child]; omega)
      rw [denoteR, hf, eraseControl_onExitR, hb, denote, Effects.Program.inl_bind]
      congr 1
      funext ex
      have hfin := denoteR_straight root fin ({ p with completed := [] }.childWith 1 (reifyExitVal ex)) hparts.2
        (by simp only [Agreement.depth] at hp; simp only [Point.childWith]; omega)
      simp only [hf] at hfin
      rw [eraseControl_constructR, hfin, Effects.Program.inl_bind]
      rfl
  | .gen _, _, hs, _ | .uninterruptible _, _, hs, _ | .interruptible _, _, hs, _
  | .whileLoop _ _ _ _, _, hs, _ | .yieldNow _, _, hs, _ | .callback _ _, _, hs, _
  | .awaitFiber _ _, _, hs, _ | .withFiber _, _, hs, _ | .«scoped» _, _, hs, _
  | .acquireRelease _ _, _, hs, _ | .choose _ _ _, _, hs, _ => by
    simp only [Straight, Bool.false_eq_true] at hs

theorem meaning_denoteR_straight (root : NativeEff) (e : NativeEff) (p : Point)
    (hs : Straight e = true) (hp : Agreement.depth e ≤ p.fuel) (stores : Stores) :
    (Effects.interpret rHandler (eraseControl (denoteR root e p))).run stores =
      meaning e p.env stores := by
  rw [denoteR_straight root e p hs hp]
  exact meaning_via_rsig e p.env stores

end Effect4.Program.Sched
