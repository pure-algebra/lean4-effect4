import Effect4.Semantics.Denotation
import Effect4.Flow.Region

/-!
# Semantics.RegionDenotation

Owner: the algebraic meaning of an admitted *region* flow (the remaining third
of packet D2 of `docs/research/2026-09-03-reification-plan.md`; the merged
failure runner and the `Scope` lemmas L1/L2 landed first, in
`Effect4/Flow/Region.lean`).

D1 read the plain runner as `interpret` of a program over `Sig ⊕ₛ DecSig`.
A region run performs three more things — it opens a region, it acquires a
resource inside one, and it closes one — and none of them is a function of the
block alone: each reads or writes the *stack of open regions*. So the region
denotation is a program over one more summand, and the handler of that summand
is the only part of the interpretation that is stateful.

Four decisions shape the module; each is forced by `Region.lean`, not by the
plan text.

* **The scope summand has four operations, not three.** `enter`, `acquire` and
  `leave` are the plan's three. The fourth is `fail`: when an operation fails,
  `regionLoop` calls `Flow.fail`, which closes *every* open region with the
  failure (`unwind`). That reads the whole stack, so it is a scope operation and
  not something the pure denotation can inline.
* **Two answers carry a refusal the denotation cannot see.** `regionLoop`'s
  `acquire` and `leave` arms both match on `stack` and fall through to the stuck
  frontier when it is empty. Emptiness is runtime state, so `acquire` answers
  `Option (Except Val Val)` and `leave` answers `Option Failures`, `none` being
  that refusal in both. (Region admission refuses an `acquire` or a `leave`
  outside every region. `Effect4/Semantics/RegionSafety.lean` now derives the
  frame-identity and parent-chain invariant from admission and proves these
  stuck arms unreachable for checked entry runs under the standard handler.
  The unrestricted denotation still retains both answers.)
* **`leave` answers the merged failure list.** `closeFrame` keeps every failing
  release, in close order (L2). `regionLoop` continues at the region's
  `continue_` block exactly when that list is empty, and otherwise fails with
  its head and carries its tail. The answer is therefore `Failures`, the
  runner's own carrier, and L1/L2 are literally the arm-level facts of the
  `leave` clause of `scopeHandler`.
* **The shape is `Handler.sum`, not `Handler.mapHom`.** The plan offers
  `interpret (scopeHandler.mapHom (MonadHom.stateT (interpretHom traceHandler)))`
  as an alternative. lean4-effects v0.3.1, the pinned revision, has no
  `MonadHom`, no `Handler.mapHom`, no `interpretHom` and no `interpret_mapHom`
  (`Effects/Hom.lean` does not exist), so that shape is not available and is not
  used. The sum shape is taken instead: the three summands are handled into one
  monad, `StateT (Stack alphabet) (RunM M)`, with the two stackless handlers
  lifted through `Handler.overStack`. This is a hand-rolled instance of exactly
  the transport `mapHom` would give.

The alphabet summand is *not* D1's. A `RegionService` answers `Except Val Val`,
where a `FlowService` answers `Val`, so `Fam` and `traceHandler` do not type
here; `RegionFam` and `regionTraceHandler` are their fallible twins. The
decision summand is D1's `DecSig`, lifted, unchanged.

The plan spells the scope requests `enter : RegionId`,
`acquire : Op × Val × Op` and `leave : RegionId × Val`. The two alphabet
operations of an `acquire` travel in the family *name* here rather than the
parameter, exactly as `Fam` puts its operation in the name and the wire value in
the parameter; that keeps every parameter and every answer in `Type 0`. And
`leave` takes only the value: `regionLoop` closes the frame the *stack* names,
never the one the terminator names, so the region identity in the request would
be decoration the runner does not read.

The fuel-free continuation is `Effect4/Semantics/RegionTotal.lean`.
`denoteRegionsGo` follows the erased graph with the lexicographic measure
`(tape.length, (raw.reachSet block).length)`, including the `enter`, `acquire`
and `leave` cases. `denoteRegionsFuel_eq_denoteRegionsWF` proves agreement
for every admitted region flow, tape, input and sufficient fuel, before any
handler is selected. The stack invariant mentioned above remains a separate
obligation; this equality does not assume it.
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val Outcome)

variable {Ty : Type uTy} {M : Type → Type}

/-! ## The alphabet summand of a region run

`Fam` denotes every answer as `Val`. A region service may fail, so its family
denotes every answer as `Except Val Val`; everything else is D1's. -/

/-- The flow alphabet as a named-operation family whose answers may fail: the
shape `RegionService.handle` already promised. -/
abbrev RegionFam (alphabet : FlowAlphabet Ty) : Family :=
  ⟨alphabet.Op, fun _ => Val, fun _ => Except Val Val⟩

/-- The signature of a region flow's own operations. -/
abbrev RegionOpSig (alphabet : FlowAlphabet Ty) : Signature := (RegionFam alphabet).toSignature

/-- A `RegionService` is already a `Family.Service` for `RegionFam`. -/
def RegionService.toService {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M) :
    (RegionFam alphabet).Service M :=
  service.handle

/-! ## The scope summand -/

/-- The stack of open regions a region run threads, innermost first. -/
abbrev Stack (alphabet : FlowAlphabet Ty) := List (Frame alphabet)

/-- The names of the scope summand. The two alphabet operations an `acquire`
names travel in the *name*, as they do in `Fam` (whose name is the operation
and whose parameter is the wire value); this keeps every parameter and every
answer in `Type 0` and the family in the same universe shape as `Fam`. -/
inductive ScopeName (alphabet : FlowAlphabet Ty) where
  /-- Open a region and push a frame for it. -/
  | enter
  /-- Perform `operation` inside the innermost region and register `release`
  for its answer. -/
  | acquire (operation release : alphabet.Op)
  /-- Close the innermost region with a value. -/
  | leave
  /-- Close every open region with a failure. -/
  | fail

/-- What a scope operation asks for. -/
abbrev ScopeName.Param {alphabet : FlowAlphabet Ty} : ScopeName alphabet → Type
  | .enter => RegionId
  | .acquire _ _ => Val
  | .leave => Val
  | .fail => Val

/-- What a scope operation answers.

`acquire` and `leave` answer an `Option`: `none` is `regionLoop`'s stuck arm on
an empty stack, which no pure denotation can predict. `leave` answers the
merged failure list of `closeFrame` — empty exactly when the close was clean —
and `fail` answers the merged failure list of `unwind`. -/
abbrev ScopeName.Answer {alphabet : FlowAlphabet Ty} : ScopeName alphabet → Type
  | .enter => Unit
  | .acquire _ _ => Option (Except Val Val)
  | .leave => Option Failures
  | .fail => Failures

/-- The scope summand as a named-operation family. -/
abbrev ScopeFam (alphabet : FlowAlphabet Ty) : Family :=
  ⟨ScopeName alphabet, ScopeName.Param, ScopeName.Answer⟩

/-- The signature of the scope summand. -/
abbrev ScopeSig (alphabet : FlowAlphabet Ty) : Signature := (ScopeFam alphabet).toSignature

/-- What a region run performs: the scope, the alphabet, and the decisions the
tape has already made. `⊕ₛ` is `infixl`, so the nesting is written out: the
right summand is D1's `FullSig` with the fallible alphabet, which is what lets
`regionHandler` reuse `decisionHandler` under one lift. -/
abbrev RegionSig (alphabet : FlowAlphabet Ty) : Signature :=
  ScopeSig alphabet ⊕ₛ (RegionOpSig alphabet ⊕ₛ DecSig)

/-- The monad a region run is interpreted into: the run monad under the stack
of open regions. -/
abbrev ScopeM (M : Type → Type) (alphabet : FlowAlphabet Ty) := StateT (Stack alphabet) (RunM M)

/-! ## The handlers -/

/-- Lift a stackless handler over the stack. This is the transport
`Handler.mapHom (MonadHom.stateT …)` would supply upstream; `StateT.lift` is a
monad morphism, so the two agree clause for clause. -/
def Handler.overStack [Monad M] {S : Signature.{u, 0}} {alphabet : FlowAlphabet Ty}
    (handler : Handler S (RunM M)) : Handler S (ScopeM M alphabet) :=
  ⟨fun operation => StateT.lift (handler.handle operation)⟩

/-- The traced fallible service: the operation runs and `logOperation` writes
its rows, or none at all if the service calls it pure. This is
`tracedFlowService` for a `RegionService`. -/
def regionTracedService [Monad M] {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) :
    (RegionFam alphabet).Service (RunM M) :=
  fun op request => do
    let result ← StateT.lift (service.handle op request)
    logOperation service nameOf op request result
    pure result

/-- The alphabet summand's handler. -/
def regionTraceHandler [Monad M] {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) :
    Handler (RegionOpSig alphabet) (RunM M) :=
  (regionTracedService service nameOf).toHandler

/-- **The scope handler.** Its `leave` arm is `closeFrame`, so L1 (`closeFrame_log`)
and L2 (`closeFrame_failure`, `closeFrame_failure_merge`,
`closeFrame_failure_closeResult`) are the arm-level facts of this handler; its
`fail` arm is `unwind`. -/
def scopeHandler [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) : Handler (ScopeSig alphabet) (ScopeM M alphabet) :=
  Family.Service.toHandler (F := ScopeFam alphabet) fun name =>
    match name with
    | .enter => fun region stack => do
        emit (.enter region.value)
        pure ((), ({ region := region, releases := [] } : Frame alphabet) :: stack)
    | .acquire op releaser => fun request stack =>
        match stack with
        | [] => pure (none, [])
        | frame :: rest => do
            let result ← StateT.lift (service.handle op request)
            logOperation service nameOf op request result
            match result with
            | .ok answer =>
                pure (some (.ok answer),
                  { frame with releases := (releaser, answer) :: frame.releases } :: rest)
            | .error error => pure (some (.error error), frame :: rest)
    | .leave => fun value stack =>
        match stack with
        | [] => pure (none, [])
        | frame :: rest => do
            let failures ← closeFrame service nameOf frame (.success value)
            pure (some failures, rest)
    | .fail => fun error stack => do
        let closing ← unwind service nameOf stack error
        pure (closing, stack)

/-- The handler a region run is interpreted under: the scope on the left, then
D1's two summands lifted over the stack. -/
def regionHandler [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) : Handler (RegionSig alphabet) (ScopeM M alphabet) :=
  (scopeHandler service nameOf).sum
    (Handler.overStack ((regionTraceHandler service nameOf).sum decisionHandler))

/-! ## The denotation

This module defines the fuelled approximation, as D1 defines `denoteFuel`.
`denoteRegions` below selects a supplied fuel. The separate continuation in
`Effect4/Semantics/RegionTotal.lean` defines and proves its fuel-free meaning
through `CyclesWF`; existing fuelled receipts and signatures stay unchanged. -/

/-- The injection of one alphabet operation. -/
abbrev performOp {alphabet : FlowAlphabet Ty} (op : alphabet.Op) (request : Val) :
    (RegionSig alphabet).Op := .inr (.inl ⟨op, request⟩)

/-- The injection of one decision. -/
abbrev decideOp {alphabet : FlowAlphabet Ty} (site : DecisionId) (branch : Bool) :
    (RegionSig alphabet).Op := .inr (.inr (site, branch))

/-- The injection of one scope operation. -/
abbrev scopeOp {alphabet : FlowAlphabet Ty} (name : ScopeName alphabet)
    (param : name.Param) : (RegionSig alphabet).Op := .inl ⟨name, param⟩

/-- The fuelled denotation of a region flow, structural on fuel, mirroring
`regionLoop` case for case. The second component of the result is the merged
failure the run collected, exactly as `runRegionsCause` reports it. -/
def denoteRegionsFuel {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty) :
    Nat → BlockId → Env → Tape →
      Program (RegionSig alphabet) ((RunResult × Tape) × Failures)
  | 0, block, _, tape => .pure ((.frontier (.fuel block), tape), [])
  | fuel + 1, block, env, tape =>
    match flow.block? block with
    | none => .pure ((.frontier (.stuck block), tape), [])
    | some current =>
      let stuck : Program (RegionSig alphabet) ((RunResult × Tape) × Failures) :=
        .pure ((.frontier (.stuck block), tape), [])
      match current.term with
      | .plain term =>
          let raw : RawBlock Ty := { id := current.id, params := current.params, term := term }
          match plan alphabet raw env tape with
          | .stuck => stuck
          | .ret value => .pure ((.done value, tape), [])
          | .jump target env' => denoteRegionsFuel flow fuel target env' tape
          | .perform op request target env' =>
              .vis (performOp op request) fun result : Except Val Val =>
                match result with
                | .ok answer => denoteRegionsFuel flow fuel target (env' ++ [answer]) tape
                | .error error =>
                    .vis (scopeOp .fail error) fun closing : Failures =>
                      .pure ((.failed error, tape), error :: ([] ++ closing))
          | .exhausted site => .pure ((.frontier (.unansweredDecision site), tape), [])
          | .mismatch expected actual => .pure ((.refused expected actual, tape), [])
          | .choose site branch target env' rest =>
              .vis (decideOp site branch) fun _ : Unit =>
                denoteRegionsFuel flow fuel target env' rest
      | .enter region body args =>
          match readArgs env args with
          | none => stuck
          | some values =>
              .vis (scopeOp .enter region) fun _ : Unit =>
                denoteRegionsFuel flow fuel body values tape
      | .acquire operation request release target args =>
          match alphabet.lookup operation, alphabet.lookup release, env[request.index]?,
              readArgs env args with
          | some op, some releaser, some requestValue, some values =>
              .vis (scopeOp (.acquire op releaser) requestValue)
                  fun result : Option (Except Val Val) =>
                match result with
                | none => stuck
                | some (.ok answer) =>
                    denoteRegionsFuel flow fuel target (values ++ [answer]) tape
                | some (.error error) =>
                    .vis (scopeOp .fail error) fun closing : Failures =>
                      .pure ((.failed error, tape), error :: ([] ++ closing))
          | _, _, _, _ => stuck
      | .leave value =>
          match env[value.index]?, current.region.bind flow.row? with
          | some v, some row =>
              .vis (scopeOp .leave v) fun result : Option Failures =>
                match result with
                | none => stuck
                | some [] => denoteRegionsFuel flow fuel row.continue_ [v] tape
                | some (error :: more) =>
                    .vis (scopeOp .fail error) fun closing : Failures =>
                      .pure ((.failed error, tape), error :: (more ++ closing))
          | _, _ => stuck

/-- The denotation of an admitted region flow from its entry with no open
region. -/
def denoteRegions [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (tape : Tape) (input : Val) :
    Program (RegionSig alphabet) ((RunResult × Tape) × Failures) :=
  denoteRegionsFuel flow.flow fuel flow.flow.entry [input] tape

/-! ## Closing a region run

`done` and `frontier` are not operations of any summand — they are a function
of the result the denotation returns — so D1's `outcomeRows` supplies them
unchanged, here over the failure-carrying pair. -/

/-- Append the outcome rows of a finished region run. -/
def closeCause [Monad M] (result : (RunResult × Tape) × Failures) :
    RunM M ((RunResult × Tape) × Failures) :=
  fun log => pure (result, log ++ outcomeRows result.1.1)

/-- The region runner read through the algebra, from a given stack: interpret
the denotation under `regionHandler`, discard the final stack, then append the
outcome rows. -/
def interpretRegionsFrom [Monad M] {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String)
    (stack : Stack alphabet)
    (program : Program (RegionSig alphabet) ((RunResult × Tape) × Failures)) :
    RunM M ((RunResult × Tape) × Failures) :=
  (interpret (regionHandler service nameOf) program).run stack >>= fun outcome =>
    closeCause outcome.1

/-- The region runner read through the algebra: `interpretRegionsFrom` with no
open region. -/
def interpretRegions [Monad M] {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String)
    (program : Program (RegionSig alphabet) ((RunResult × Tape) × Failures)) :
    RunM M ((RunResult × Tape) × Failures) :=
  interpretRegionsFrom service nameOf [] program


/-! ## What one operation does

Six lemmas, one per operation shape, each in the goal's own spelling.
`Signature.sum` and `Family.toSignature` are plain definitions upstream, so
`(RegionSig alphabet).Answer op` does not reduce at the transparency `rw` and
`simp` match at; these are the only place that reduction is needed. -/

section Interpretation

variable {alphabet : FlowAlphabet Ty}

theorem regionHandler_run_enter [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (region : RegionId) (stack : Stack alphabet)
    (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (scopeOp .enter region)).run stack).run log) =
      pure (((), ({ region := region, releases := [] } : Frame alphabet) :: stack),
        log ++ [Effects.Trace.Event.enter region.value]) := by
  show ((emit (M := M) (Effects.Trace.Event.enter region.value) >>= fun _ =>
      pure ((), ({ region := region, releases := [] } : Frame alphabet) :: stack)).run log) = _
  rw [StateT.run_bind, emit_run, pure_bind]
  rfl

theorem regionTracedService_run [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (op : alphabet.Op) (request : Val)
    (log : Effect4.Trace.Log) :
    (regionTracedService service nameOf op request).run log =
      service.handle op request >>= fun result =>
        pure (result, log ++ opRows service nameOf op request result) := by
  simp only [regionTracedService, StateT.run_bind, StateT.run_lift, logOperation_run,
    pure_bind, bind_assoc]
  rfl

theorem regionHandler_run_perform [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (op : alphabet.Op) (request : Val) (stack : Stack alphabet)
    (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (performOp op request)).run stack).run log) =
      service.handle op request >>= fun result =>
        pure ((result, stack), log ++ opRows service nameOf op request result) := by
  show ((regionTracedService service nameOf op request >>= fun answer =>
      pure (answer, stack)).run log) = _
  rw [StateT.run_bind, regionTracedService_run, bind_assoc]
  exact bind_congr fun result => pure_bind _ _

theorem regionHandler_run_decide [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (site : DecisionId) (branch : Bool) (stack : Stack alphabet)
    (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (decideOp site branch)).run stack).run log) =
      pure (((), stack), log ++ [Effects.Trace.Event.decide site.value branch]) := by
  show ((emit (M := M) (Effects.Trace.Event.decide site.value branch) >>= fun answer =>
      pure (answer, stack)).run log) = _
  rw [StateT.run_bind, emit_run, pure_bind]
  rfl

theorem regionHandler_run_acquire_cons [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String)
    (op releaser : alphabet.Op) (request : Val) (frame : Frame alphabet) (rest : Stack alphabet)
    (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (scopeOp (.acquire op releaser) request)).run
        (frame :: rest)).run log) =
      service.handle op request >>= fun result =>
        pure ((some result,
            match result with
            | .ok answer =>
                ({ frame with releases := (releaser, answer) :: frame.releases } :: rest :
                  Stack alphabet)
            | .error _ => frame :: rest),
          log ++ opRows service nameOf op request result) := by
  show (((StateT.lift (service.handle op request) >>= fun result =>
      logOperation service nameOf op request result >>= fun _ =>
        match result with
        | .ok answer =>
            (pure (some (Except.ok answer),
              ({ frame with releases := (releaser, answer) :: frame.releases } :: rest :
                Stack alphabet)) : RunM M (Option (Except Val Val) × Stack alphabet))
        | .error error => pure (some (Except.error error), (frame :: rest : Stack alphabet)))).run
      log) = _
  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
  refine bind_congr fun result => ?_
  rw [pure_bind, StateT.run_bind, logOperation_run, pure_bind]
  cases result <;> rfl

theorem regionHandler_run_leave_nil [Monad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (value : Val) (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (scopeOp .leave value)).run
      ([] : Stack alphabet)).run log) = pure ((none, []), log) := rfl

theorem regionHandler_run_leave_cons [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (value : Val)
    (frame : Frame alphabet) (rest : Stack alphabet) (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (scopeOp .leave value)).run
        (frame :: rest)).run log) =
      (closeFrame service nameOf frame (.success value)).run log >>= fun outcome =>
        pure ((some outcome.1, rest), outcome.2) := by
  show ((closeFrame service nameOf frame (Outcome.success value)).run log >>= fun outcome =>
    (pure ((some outcome.1, rest), outcome.2) : M _)) = _
  rfl

theorem regionHandler_run_acquire_nil [Monad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (op releaser : alphabet.Op) (request : Val)
    (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (scopeOp (.acquire op releaser) request)).run
      ([] : Stack alphabet)).run log) = pure ((none, []), log) := rfl

theorem regionHandler_run_fail [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (error : Val) (stack : Stack alphabet)
    (log : Effect4.Trace.Log) :
    ((((regionHandler service nameOf).handle (scopeOp .fail error)).run stack).run log) =
      (unwind service nameOf stack error).run log >>= fun outcome =>
        pure ((outcome.1, stack), outcome.2) := by
  show ((unwind service nameOf stack error).run log >>= fun outcome =>
    (pure ((outcome.1, stack), outcome.2) : M _)) = _
  rfl

theorem interpretRegionsFrom_run_pure [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (result : (RunResult × Tape) × Failures) (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack (.pure result)).run log =
      pure (result, log ++ outcomeRows result.1.1) := by
  show ((pure (result, stack) >>= fun outcome => closeCause outcome.1).run log) = _
  rw [StateT.run_bind]
  show ((pure ((result, stack), log) : M _) >>= _) = _
  rw [pure_bind]
  rfl

theorem interpretRegionsFrom_run_vis [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (operation : (RegionSig alphabet).Op)
    (next : (RegionSig alphabet).Answer operation →
      Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack (.vis operation next)).run log =
      ((((regionHandler service nameOf).handle operation).run stack).run log) >>= fun outcome =>
        (interpretRegionsFrom service nameOf outcome.1.2 (next outcome.1.1)).run outcome.2 := by
  show (((((regionHandler service nameOf).handle operation).run stack >>= fun answered =>
      (interpret (regionHandler service nameOf) (next answered.1)).run answered.2) >>=
        fun outcome => closeCause outcome.1).run log) = _
  rw [StateT.run_bind, StateT.run_bind, bind_assoc]
  refine bind_congr fun answered => ?_
  exact (StateT.run_bind (m := M)
    ((interpret (regionHandler service nameOf) (next answered.1.1)).run answered.1.2)
    (fun outcome => closeCause outcome.1) answered.2).symm

/-- One operation whose run is a `pure`: the arm reduces to the continuation.

`Signature.sum` and `Family.toSignature` are plain definitions upstream, so
`(RegionSig alphabet).Answer operation` does not reduce at `rw`'s transparency.
Taking the computed run as a hypothesis — with the dependent answer type on both
sides of it — is what keeps every arm lemma out of that thicket. -/
theorem interpretRegionsFrom_run_handled_pure [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (operation : (RegionSig alphabet).Op)
    (next : (RegionSig alphabet).Answer operation →
      Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (value : ((RegionSig alphabet).Answer operation × Stack alphabet) × Effect4.Trace.Log)
    (log : Effect4.Trace.Log)
    (agree : (((regionHandler service nameOf).handle operation).run stack).run log = pure value) :
    (interpretRegionsFrom service nameOf stack (.vis operation next)).run log =
      (interpretRegionsFrom service nameOf value.1.2 (next value.1.1)).run value.2 := by
  rw [interpretRegionsFrom_run_vis, agree, pure_bind]

/-- One operation whose run is an effect followed by a `pure`. -/
theorem interpretRegionsFrom_run_handled_bind [Monad M] [LawfulMonad M] {B : Type}
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (operation : (RegionSig alphabet).Op)
    (next : (RegionSig alphabet).Answer operation →
      Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (source : M B)
    (step : B → ((RegionSig alphabet).Answer operation × Stack alphabet) × Effect4.Trace.Log)
    (log : Effect4.Trace.Log)
    (agree : (((regionHandler service nameOf).handle operation).run stack).run log =
      source >>= fun b => pure (step b)) :
    (interpretRegionsFrom service nameOf stack (.vis operation next)).run log =
      source >>= fun b =>
        (interpretRegionsFrom service nameOf (step b).1.2 (next (step b).1.1)).run (step b).2 := by
  rw [interpretRegionsFrom_run_vis, agree, bind_assoc]
  exact bind_congr fun b => pure_bind _ _

theorem interpretRegionsFrom_run_perform [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (op : alphabet.Op) (request : Val)
    (next : Except Val Val → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack (.vis (performOp op request) next)).run log =
      service.handle op request >>= fun result =>
        (interpretRegionsFrom service nameOf stack (next result)).run
          (log ++ opRows service nameOf op request result) :=
  interpretRegionsFrom_run_handled_bind service nameOf stack (performOp op request) next
    (service.handle op request)
    (fun result => ((result, stack), log ++ opRows service nameOf op request result)) log
    (regionHandler_run_perform service nameOf op request stack log)

theorem interpretRegionsFrom_run_decide [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (site : DecisionId) (branch : Bool)
    (next : Unit → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack (.vis (decideOp site branch) next)).run log =
      (interpretRegionsFrom service nameOf stack (next ())).run
        (log ++ [Effects.Trace.Event.decide site.value branch]) :=
  interpretRegionsFrom_run_handled_pure service nameOf stack (decideOp site branch) next
    (((), stack), log ++ [Effects.Trace.Event.decide site.value branch]) log
    (regionHandler_run_decide service nameOf site branch stack log)

theorem interpretRegionsFrom_run_enter [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (region : RegionId)
    (next : Unit → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack (.vis (scopeOp .enter region) next)).run log =
      (interpretRegionsFrom service nameOf
        (({ region := region, releases := [] } : Frame alphabet) :: stack) (next ())).run
        (log ++ [Effects.Trace.Event.enter region.value]) :=
  interpretRegionsFrom_run_handled_pure service nameOf stack (scopeOp .enter region) next
    (((), ({ region := region, releases := [] } : Frame alphabet) :: stack),
      log ++ [Effects.Trace.Event.enter region.value]) log
    (regionHandler_run_enter service nameOf region stack log)

theorem interpretRegionsFrom_run_acquire_nil [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String)
    (op releaser : alphabet.Op) (request : Val)
    (next : Option (Except Val Val) → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf [] (.vis (scopeOp (.acquire op releaser) request) next)).run
        log =
      (interpretRegionsFrom service nameOf [] (next none)).run log :=
  interpretRegionsFrom_run_handled_pure service nameOf [] (scopeOp (.acquire op releaser) request)
    next ((none, []), log) log
    (regionHandler_run_acquire_nil service nameOf op releaser request log)

theorem interpretRegionsFrom_run_acquire_cons [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String)
    (op releaser : alphabet.Op) (request : Val) (frame : Frame alphabet) (rest : Stack alphabet)
    (next : Option (Except Val Val) → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf (frame :: rest)
        (.vis (scopeOp (.acquire op releaser) request) next)).run log =
      service.handle op request >>= fun result =>
        (interpretRegionsFrom service nameOf
          (match result with
            | .ok answer =>
                ({ frame with releases := (releaser, answer) :: frame.releases } :: rest :
                  Stack alphabet)
            | .error _ => frame :: rest)
          (next (some result))).run (log ++ opRows service nameOf op request result) :=
  interpretRegionsFrom_run_handled_bind service nameOf (frame :: rest)
    (scopeOp (.acquire op releaser) request) next (service.handle op request)
    (fun result =>
      ((some result,
        match result with
        | .ok answer =>
            ({ frame with releases := (releaser, answer) :: frame.releases } :: rest :
              Stack alphabet)
        | .error _ => frame :: rest),
        log ++ opRows service nameOf op request result)) log
    (regionHandler_run_acquire_cons service nameOf op releaser request frame rest log)

theorem interpretRegionsFrom_run_leave_nil [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (value : Val)
    (next : Option Failures → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf [] (.vis (scopeOp .leave value) next)).run log =
      (interpretRegionsFrom service nameOf [] (next none)).run log :=
  interpretRegionsFrom_run_handled_pure service nameOf [] (scopeOp .leave value) next
    ((none, []), log) log (regionHandler_run_leave_nil service nameOf value log)

theorem interpretRegionsFrom_run_leave_cons [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (value : Val)
    (frame : Frame alphabet) (rest : Stack alphabet)
    (next : Option Failures → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf (frame :: rest)
        (.vis (scopeOp .leave value) next)).run log =
      (closeFrame service nameOf frame (.success value)).run log >>= fun closed =>
        (interpretRegionsFrom service nameOf rest (next (some closed.1))).run closed.2 :=
  interpretRegionsFrom_run_handled_bind service nameOf (frame :: rest) (scopeOp .leave value) next
    ((closeFrame service nameOf frame (.success value)).run log)
    (fun closed => ((some closed.1, rest), closed.2)) log
    (regionHandler_run_leave_cons service nameOf value frame rest log)

theorem interpretRegionsFrom_run_fail [Monad M] [LawfulMonad M]
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (stack : Stack alphabet)
    (error : Val)
    (next : Failures → Program (RegionSig alphabet) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack (.vis (scopeOp .fail error) next)).run log =
      (unwind service nameOf stack error).run log >>= fun closing =>
        (interpretRegionsFrom service nameOf stack (next closing.1)).run closing.2 :=
  interpretRegionsFrom_run_handled_bind service nameOf stack (scopeOp .fail error) next
    ((unwind service nameOf stack error).run log)
    (fun closing => ((closing.1, stack), closing.2)) log
    (regionHandler_run_fail service nameOf error stack log)

theorem fail_eq_interpret [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : Stack alphabet) (error : Val) (rest : Failures)
    (tape : Tape) (log : Effect4.Trace.Log) :
    (fail service nameOf stack error rest tape).run log =
      (interpretRegionsFrom service nameOf stack
        (.vis (scopeOp .fail error) fun closing : Failures =>
          .pure ((.failed error, tape), error :: (rest ++ closing)))).run log := by
  rw [interpretRegionsFrom_run_fail]
  show ((unwind service nameOf stack error).run log >>= fun closing =>
      ((emit (Effects.Trace.Event.done (Outcome.failure error)) >>= fun _ =>
        pure ((RunResult.failed error, tape), error :: (rest ++ closing.1))).run closing.2)) = _
  refine bind_congr fun closing => ?_
  rw [interpretRegionsFrom_run_pure, StateT.run_bind, emit_run, pure_bind]
  rfl

theorem stuck_eq_interpret [Monad M] [LawfulMonad M] (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : Stack alphabet) (block : BlockId) (tape : Tape)
    (log : Effect4.Trace.Log) :
    (interpretRegionsFrom service nameOf stack
        (.pure ((RunResult.frontier (.stuck block), tape), []))).run log =
      pure (((RunResult.frontier (.stuck block), tape), []), log) := by
  rw [interpretRegionsFrom_run_pure]
  simp [outcomeRows]

/-- **T1 for regions.** The region runner, at every fuel, from every stack, is
`interpret` of the fuelled region denotation under `regionHandler`, closed by
D1's outcome rows. -/
theorem regionLoop_eq_interpret [Monad M] [LawfulMonad M] (flow : RegionFlow Ty)
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : Stack alphabet)
      (log : Effect4.Trace.Log),
      (regionLoop alphabet flow service nameOf fuel block env tape stack).run log =
        (interpretRegionsFrom service nameOf stack
          (denoteRegionsFuel flow fuel block env tape)).run log := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape stack log
      rw [denoteRegionsFuel, interpretRegionsFrom_run_pure]
      show ((emit (M := M) Effects.Trace.Event.frontier >>= fun _ =>
        pure ((RunResult.frontier (.fuel block), tape), [])).run log) = _
      rw [StateT.run_bind, emit_run, pure_bind]
      rfl
  | succ fuel ih =>
      intro block env tape stack log
      simp only [regionLoop, denoteRegionsFuel]
      cases found : flow.block? block with
      | none =>
          try simp only []
          rw [interpretRegionsFrom_run_pure]
          simp [outcomeRows]
      | some current =>
          try simp only []
          cases term : current.term with
          | plain rawTerm =>
              try simp only []
              cases planned :
                plan alphabet { id := current.id, params := current.params, term := rawTerm }
                  env tape with
              | stuck =>
                  try simp only []
                  exact (stuck_eq_interpret service nameOf stack block tape log).symm
              | ret value =>
                  try simp only []
                  rw [interpretRegionsFrom_run_pure]
                  show ((emit (M := M) (Effects.Trace.Event.done (Outcome.success value)) >>= fun _ =>
                    pure ((RunResult.done value, tape), [])).run log) = _
                  rw [StateT.run_bind, emit_run, pure_bind]
                  rfl
              | jump target env' => try simp only []; exact ih target env' tape stack log
              | perform op request target env' =>
                  try simp only []
                  rw [interpretRegionsFrom_run_perform]
                  show ((StateT.lift (service.handle op request) >>= fun result =>
                      logOperation service nameOf op request result >>= fun _ =>
                        match result with
                        | .ok answer =>
                            regionLoop alphabet flow service nameOf fuel target
                              (env' ++ [answer]) tape stack
                        | .error error => fail service nameOf stack error [] tape).run log) = _
                  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
                  refine bind_congr fun result => ?_
                  rw [pure_bind, StateT.run_bind, logOperation_run, pure_bind]
                  cases result with
                  | ok answer => exact ih target (env' ++ [answer]) tape stack _
                  | error error => exact fail_eq_interpret service nameOf stack error [] tape _
              | exhausted site =>
                  try simp only []
                  rw [interpretRegionsFrom_run_pure]
                  show ((emit (M := M) Effects.Trace.Event.frontier >>= fun _ =>
                    pure ((RunResult.frontier (.unansweredDecision site), tape), [])).run log) = _
                  rw [StateT.run_bind, emit_run, pure_bind]
                  rfl
              | mismatch expected actual =>
                  try simp only []
                  rw [interpretRegionsFrom_run_pure]
                  simp [outcomeRows]
              | choose site branch target env' rest =>
                  try simp only []
                  rw [interpretRegionsFrom_run_decide]
                  show ((emit (M := M) (Effects.Trace.Event.decide site.value branch) >>= fun _ =>
                    regionLoop alphabet flow service nameOf fuel target env' rest stack).run log) = _
                  rw [StateT.run_bind, emit_run, pure_bind]
                  exact ih target env' rest stack _
          | enter region body args =>
              try simp only []
              cases read : readArgs env args with
              | none =>
                  try simp only []
                  exact (stuck_eq_interpret service nameOf stack block tape log).symm
              | some values =>
                  try simp only []
                  rw [interpretRegionsFrom_run_enter]
                  show ((emit (M := M) (Effects.Trace.Event.enter region.value) >>= fun _ =>
                    regionLoop alphabet flow service nameOf fuel body values tape
                      ({ region := region, releases := [] } :: stack)).run log) = _
                  rw [StateT.run_bind, emit_run, pure_bind]
                  exact ih body values tape _ _
          | acquire operation request release target args =>
              try simp only []
              cases foundOp : alphabet.lookup operation with
              | none =>
                  try simp only []
                  exact (stuck_eq_interpret service nameOf stack block tape log).symm
              | some op =>
                  cases foundRelease : alphabet.lookup release with
                  | none =>
                      try simp only []
                      exact (stuck_eq_interpret service nameOf stack block tape log).symm
                  | some releaser =>
                      try simp only []
                      cases foundRequest : env[request.index]? with
                      | none =>
                          try simp only []
                          exact (stuck_eq_interpret service nameOf stack block tape log).symm
                      | some requestValue =>
                          try simp only []
                          cases read : readArgs env args with
                          | none =>
                              try simp only []
                              exact (stuck_eq_interpret service nameOf stack block tape log).symm
                          | some values =>
                              try simp only []
                              cases open_ : stack with
                              | nil =>
                                  rw [interpretRegionsFrom_run_acquire_nil]
                                  exact (stuck_eq_interpret service nameOf [] block tape log).symm
                              | cons frame rest =>
                                  rw [interpretRegionsFrom_run_acquire_cons]
                                  show ((StateT.lift (service.handle op requestValue) >>=
                                      fun result =>
                                        logOperation service nameOf op requestValue result >>=
                                          fun _ =>
                                            match result with
                                            | .ok answer =>
                                                regionLoop alphabet flow service nameOf fuel target
                                                  (values ++ [answer]) tape
                                                  ({ frame with
                                                      releases := (releaser, answer) ::
                                                        frame.releases } :: rest)
                                            | .error error =>
                                                fail service nameOf (frame :: rest) error []
                                                  tape).run log) = _
                                  rw [StateT.run_bind, StateT.run_lift, bind_assoc]
                                  refine bind_congr fun result => ?_
                                  rw [pure_bind, StateT.run_bind, logOperation_run, pure_bind]
                                  cases result with
                                  | ok answer => exact ih target (values ++ [answer]) tape _ _
                                  | error error =>
                                      exact fail_eq_interpret service nameOf (frame :: rest) error
                                        [] tape _
          | leave value =>
              try simp only []
              cases foundValue : env[value.index]? with
              | none =>
                  try simp only []
                  exact (stuck_eq_interpret service nameOf stack block tape log).symm
              | some v =>
                  cases foundRow : current.region.bind flow.row? with
                  | none =>
                      try simp only []
                      exact (stuck_eq_interpret service nameOf stack block tape log).symm
                  | some row =>
                      try simp only []
                      cases open_ : stack with
                      | nil =>
                          rw [interpretRegionsFrom_run_leave_nil]
                          exact (stuck_eq_interpret service nameOf [] block tape log).symm
                      | cons frame rest =>
                          rw [interpretRegionsFrom_run_leave_cons]
                          show (((closeFrame service nameOf frame (.success v)) >>= fun failures =>
                            match failures with
                            | [] => regionLoop alphabet flow service nameOf fuel row.continue_ [v]
                                tape rest
                            | error :: more => fail service nameOf rest error more tape).run log) = _
                          rw [StateT.run_bind]
                          refine bind_congr fun closed => ?_
                          cases closedFailures : closed.1 with
                          | nil => exact ih row.continue_ [v] tape rest _
                          | cons error more =>
                              exact fail_eq_interpret service nameOf rest error more tape _

/-! ## The region runner is `interpret` of the region denotation -/

/-- T1 for regions, at the cause-carrying face: `runRegionsCause` is
`interpret` of `denoteRegions` from the empty stack, closed by the outcome
rows. -/
theorem runRegionsCause_eq_interpret [Monad M] [LawfulMonad M] [DecidableEq Ty] (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (runRegionsCause fuel flow service nameOf tape input).run log =
      (interpretRegions service nameOf (denoteRegions fuel flow tape input)).run log :=
  regionLoop_eq_interpret flow.flow service nameOf fuel flow.flow.entry [input] tape [] log

/-- **T1 for regions, at the public face.** For every admitted region flow,
tape, input and fuel, the region runner is `interpret` of the region denotation
under `scopeHandler` summed with D1's alphabet and decision handlers, run from
the empty stack and closed by D1's outcome rows; the wire face projects the
merged failure to its first, which is what `runRegions` returns. -/
theorem runRegions_eq_interpret [Monad M] [LawfulMonad M] [DecidableEq Ty] (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (runRegions fuel flow service nameOf tape input).run log =
      (interpretRegions service nameOf (denoteRegions fuel flow tape input)).run log >>=
        fun outcome => pure (outcome.1.1, outcome.2) := by
  show ((runRegionsCause fuel flow service nameOf tape input >>= fun outcome =>
    pure outcome.fst).run log) = _
  rw [StateT.run_bind, runRegionsCause_eq_interpret]
  rfl

/-- The default run, read through the algebra. -/
theorem runRegionsDefault_eq_interpret [Monad M] [LawfulMonad M] [DecidableEq Ty]
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) :
    (runRegionsDefault flow service nameOf tape input).run log =
      (interpretRegions service nameOf
        (denoteRegions (fuelFor flow.flow.erase tape) flow tape input)).run log >>=
        fun outcome => pure (outcome.1.1, outcome.2) :=
  runRegions_eq_interpret _ flow service nameOf tape input log

/-! ## D1 and D2 agree where there are no regions -/

/-- A region flow with no regions: every declared block is `plain`, so the
region layer erases to the Flow v2 graph with nothing forgotten. -/
def AllPlain (flow : RegionFlow Ty) : Prop :=
  ∀ block ∈ flow.blocks, ∃ term, block.term = .plain term

/-- A `FlowService` as a `RegionService`: every operation succeeds. -/
def FlowService.toRegionService [Monad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) : RegionService alphabet M where
  handle op request := service.handle op request >>= fun answer => Pure.pure (Except.ok answer)
  pure := service.pure

theorem toRegionService_handle [Monad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (op : alphabet.Op) (request : Val) :
    service.toRegionService.handle op request =
      service.handle op request >>= fun answer => Pure.pure (Except.ok answer) := rfl

theorem toRegionService_pure [Monad M] {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet M) (op : alphabet.Op) :
    service.toRegionService.pure op = service.pure op := rfl

/-- Resolving a block in the erasure is resolving it in the region flow and
erasing the terminator. -/
theorem lookupBlock_erase_block (flow : RegionFlow Ty) (block : BlockId) :
    lookupBlock flow.erase block =
      (flow.block? block).map fun current =>
        { id := current.id, params := current.params, term := flow.eraseTerm current } := by
  show (flow.blocks.map _).find? _ = _
  rw [List.find?_map]
  rfl

/-- `block?` resolves by identity. -/
theorem block?_id {flow : RegionFlow Ty} {block : BlockId} {current : RegionBlock Ty}
    (found : flow.block? block = some current) : current.id = block :=
  of_decide_eq_true (List.find?_eq_some_iff_getElem.mp found).1

/-- `AllPlain` from a decidable check, so a concrete flow discharges it by
`decide`. -/
theorem allPlain_of_all {flow : RegionFlow Ty}
    (checked : flow.blocks.all (fun block =>
      match block.term with | .plain _ => true | _ => false) = true) : AllPlain flow := by
  intro block mem
  have holds := List.all_eq_true.mp checked block mem
  cases term : block.term with
  | plain rawTerm => exact ⟨rawTerm, rfl⟩
  | enter _ _ _ => rw [term] at holds; exact absurd holds (by simp)
  | acquire _ _ _ _ _ => rw [term] at holds; exact absurd holds (by simp)
  | leave _ => rw [term] at holds; exact absurd holds (by simp)

set_option linter.unusedSimpArgs false in
/-- The region runner on a region-free flow is the plain runner on its
erasure: the same result, the same unconsumed tape, the same log, and an empty
merged failure. -/
theorem regionLoop_erase [Monad M] [LawfulMonad M] (flow : RegionFlow Ty)
    (plain : AllPlain flow) (service : FlowService alphabet M) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log),
      (regionLoop alphabet flow service.toRegionService nameOf fuel block env tape []).run log =
        (loop alphabet flow.erase service nameOf fuel block env tape).run log >>= fun outcome =>
          pure ((outcome.1, ([] : Failures)), outcome.2) := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape log
      simp [regionLoop, loop, emit_run]
  | succ fuel ih =>
      intro block env tape log
      simp only [regionLoop, loop, lookupBlock_erase_block]
      cases found : flow.block? block with
      | none => simp
      | some current =>
          obtain ⟨rawTerm, isPlain⟩ := plain current (List.mem_of_find?_eq_some found)
          have idEq : current.id = block := block?_id found
          subst idEq
          simp only [Option.map_some, RegionFlow.eraseTerm, isPlain]
          cases planned :
            plan alphabet { id := current.id, params := current.params, term := rawTerm }
              env tape with
          | stuck => simp [step, planned]
          | ret value => simp [step, planned, emit_run]
          | jump target env' =>
              simp only [step, planned, StateT.run_bind, StateT.run_pure, pure_bind]
              exact ih target env' tape log
          | exhausted site => simp [step, planned, emit_run]
          | mismatch expected actual => simp [step, planned]
          | choose site branch target env' rest =>
              simp only [step, planned, emit_run, StateT.run_bind, StateT.run_pure, pure_bind]
              exact ih target env' rest _
          | perform op request target env' =>
              simp only [step, planned, toRegionService_handle, StateT.run_bind, StateT.run_lift,
                bind_assoc, pure_bind]
              refine bind_congr fun answer => ?_
              rw [logOperation_run, pure_bind]
              cases pureOp : service.pure op with
              | false =>
                  simp only [opRows, toRegionService_pure, pureOp, Bool.false_eq_true, if_false,
                    emit_run, StateT.run_bind, pure_bind, StateT.run_pure, List.append_assoc,
                    List.cons_append, List.nil_append]
                  exact ih target (env' ++ [answer]) tape _
              | true =>
                  simp only [opRows, toRegionService_pure, pureOp, if_true, List.append_nil,
                    StateT.run_pure, pure_bind]
                  exact ih target (env' ++ [answer]) tape log

/-- **The corollary D2 owes D1.** On a region flow with no regions the region
runner and the plain runner of `Effect4/Semantics/Runs.lean` agree — same
result, same unconsumed tape, same log — so D2's denotation restricted to the
`plain` fragment is D1's. -/
theorem runRegions_erase [Monad M] [LawfulMonad M] [DecidableEq Ty] (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (plain : AllPlain flow.flow)
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) :
    (runRegions fuel flow service.toRegionService nameOf tape input).run log =
      (runTape fuel flow.checked service nameOf tape input).run log := by
  show ((runRegionsCause fuel flow service.toRegionService nameOf tape input >>= fun outcome =>
    pure outcome.fst).run log) = _
  rw [StateT.run_bind]
  show ((regionLoop alphabet flow.flow service.toRegionService nameOf fuel flow.flow.entry [input]
    tape []).run log >>= _) = _
  rw [regionLoop_erase flow.flow plain service nameOf, bind_assoc]
  simp only [pure_bind]
  show (((loop alphabet flow.flow.erase service nameOf fuel flow.flow.entry [input] tape).run log)
    >>= fun outcome => (pure outcome : M ((RunResult × Tape) × Effect4.Trace.Log))) = _
  rw [bind_pure]
  show _ = ((loop alphabet flow.checked.erase service nameOf fuel flow.checked.erase.entry [input]
    tape).run log)
  rw [flow.erased]
  rfl

end Interpretation

end Effect4.Flow
