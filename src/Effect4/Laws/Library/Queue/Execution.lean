import Effect4.Laws.Library.Queue.Ops
import Effect4.Laws.Library.Queue.Conservation
import Effect4.Laws.Program.StoreExecution

/-!
# Queue attempts as native machine commands

Concept: translation-simulation R10, the command half of proposed `queue-expansion-agrees`.
Consumer: QueueWorkers `Assertions.jobs_step`.
Reach: actual compiled take and offer store rows on an arbitrary fiber, with their encoded first-profile cell.
The existing attempt laws give the reply, next cell and model notifications.
The native command commits that cell and preserves the caller stack and unfinished command suffix.
The model job laws account for the same committed transition.
Capture, source-position, cell membership and budget premises remain explicit.
These laws establish no whole-run closure, writer census, wrapper delivery, progress or outside-host behavior.
Decisions rows 233, 255 and 275 bound this fragment.
-/

set_option autoImplicit false

namespace Effect4.Queue.Execution

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules Effect4.Program.Typed
open Queue.Model

/-- The compiled take attempt commits the model's cell and job transition, retaining all pending commands. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem take_loop (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {w : Typed.World} (types : TyDecls.Within sig.types w.types) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.take id 1 1))
    (injective : tb.Injective) {idSrc hintSrc : TermSrc} {env : Env} {path : List Nat}
    {tys : List Ty} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Captured idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise (tb.handle id)))
    (readsHint : Captured hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise hint))
    (typesId : CapturedTy sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    (typesHint : CapturedTy sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    (m : Api.Machine) {q : RefKey} (held : refPeek m.state.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A))
    (root : NativeEff) (table : RowTable) (fiber : FiberId)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (term request : Term) (p : Point) (compileFuel : Nat) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (tree : takeStep A idSrc hintSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok term)
    (pointEnv : p.env = captured) (pointFuel : p.fuel = compileFuel + 1)
    (requestCell : evalTerm p.env request = some (.cell q))
    (found : m.fiber? fiber = some f)
    (site : (Node.eff root).at_ p.path = some (.eff (.perform (.refModifyWith term) request)))
    (current : f.frame.current = resolve root p)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    ∃ reply entered woken,
      takeReplyVal msg (Model.take s ⟨id, 1, 1⟩).2.1 = some reply ∧
      Notified s (Model.take s ⟨id, 1, 1⟩).1 (Model.take s ⟨id, 1, 1⟩).2.2 entered woken ∧
      driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
          (.loop fiber yielding) rest =
        (({ m with state := { m.state with refs := refPoke m.state.refs q (cellVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1) msg (Model.take s ⟨id, 1, 1⟩).1) } }).update
          { countOp f with frame := { f.frame with current := .success (Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
        Val.list (woken.map (takerVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1)))]) } },
         [.drainDue, .deliver fiber yielding] ++ rest) ∧
      ((∃ job, (Model.take s ⟨id, 1, 1⟩).2.1 = .got [job] ∧
        stateJobs s = job :: stateJobs (Model.take s ⟨id, 1, 1⟩).1) ∨
       ((Model.take s ⟨id, 1, 1⟩).2.1 = .wait ∧
        stateJobs (Model.take s ⟨id, 1, 1⟩).1 = stateJobs s)) := by
  have currentCompile : f.frame.current = compileEff (.perform (.refModifyWith term) request) p := by
    unfold resolve at current
    rw [site] at current
    exact current
  obtain ⟨term', reply, entered, woken, tree', encoded, notified, answer, _, _⟩ :=
    Queue.take_attempt sig atoms types A message tb msg s id hint profile requested injective
      depth tyDepth typedEnv readsId readsHint typesId typesHint held member
  have same : term' = term := Except.ok.inj (tree'.symm.trans tree)
  subst term'
  have answerPoint : syncOpStep (.refModify q term p.env) m.state =
      some ({ m.state with refs := refPoke m.state.refs q (cellVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1) msg (Model.take s ⟨id, 1, 1⟩).1) }, Val.tuple [reply, Val.list (entered.map (offerVal tb msg)),
        Val.list (woken.map (takerVal (tb.afterTake id hint (Model.take s ⟨id, 1, 1⟩).2.1)))]) := by
    rw [pointEnv]
    exact answer
  exact ⟨reply, entered, woken, encoded, notified,
    StoreExecution.modify_loop root table m fiber f term request p compileFuel q
      _ _ yielding rest found currentCompile pointFuel requestCell interrupt override budget answerPoint,
    take_jobs profile id⟩

/-- The compiled offer attempt commits the model's cell and job transition, retaining all pending commands. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem offer_loop (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {w : Typed.World} (types : TyDecls.Within sig.types w.types) (A : Ty)
    (message : MessageTy A) (tb : Table) (msg : Nat → Val) (s : State) (id a : Nat)
    (hint : DeferredKey) (profile : FirstProfile s) (requested : Requested s (.offer id a))
    (fresh : ∀ o ∈ s.offers, o.id ≠ id) {idSrc hintSrc messageSrc : TermSrc} {env : Env}
    {path : List Nat} {tys : List Ty} {captured : List Val}
    (depth : captured.length = env.names.length) (tyDepth : tys.length = env.names.length)
    (typedEnv : EnvTyped w tys captured)
    (readsId : Reads idSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise (tb.handle id)))
    (readsHint : Reads hintSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (Val.promise hint))
    (readsMessage : Reads messageSrc (env.push [env.mint "current"]) path
      (captured ++ [cellVal tb msg s]) (msg a))
    (typesId : TypesEach sig idSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) idTy)
    (typesHint : TypesEach sig hintSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) Queue.answerTy)
    (typesMessage : TypesEach sig messageSrc (env.push [env.mint "current"]) path
      (tys ++ [Queue.cellTy A]) A)
    (m : Api.Machine) {q : RefKey} (held : refPeek m.state.refs q = some (cellVal tb msg s))
    (member : Fits w (cellVal tb msg s) (Queue.cellTy A))
    (root : NativeEff) (table : RowTable) (fiber : FiberId)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (term request : Term) (p : Point) (compileFuel : Nat) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (tree : offerStep A idSrc hintSrc messageSrc (minted (env.mint "current")) (env.push [env.mint "current"]) path = .ok term)
    (pointEnv : p.env = captured) (pointFuel : p.fuel = compileFuel + 1)
    (requestCell : evalTerm p.env request = some (.cell q))
    (found : m.fiber? fiber = some f)
    (site : (Node.eff root).at_ p.path = some (.eff (.perform (.refModifyWith term) request)))
    (current : f.frame.current = resolve root p)
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield) :
    ∃ woken,
      Notified s (Model.offer s id a).1 (Model.offer s id a).2.2 [] woken ∧
      driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
          (.loop fiber yielding) rest =
        (({ m with state := { m.state with refs := refPoke m.state.refs q (cellVal (tb.afterOffer id hint (Model.offer s id a).2.1) msg (Model.offer s id a).1) } }).update
          { countOp f with frame := { f.frame with current := .success (Val.tuple [offerReplyVal (Model.offer s id a).2.1,
        Val.list (woken.map (takerVal (tb.afterOffer id hint (Model.offer s id a).2.1)))]) } },
         [.drainDue, .deliver fiber yielding] ++ rest) ∧
      stateJobs (Model.offer s id a).1 = stateJobs s ++ [a] := by
  have currentCompile : f.frame.current = compileEff (.perform (.refModifyWith term) request) p := by
    unfold resolve at current
    rw [site] at current
    exact current
  obtain ⟨term', woken, tree', notified, answer, _, _⟩ :=
    Queue.offer_attempt sig atoms types A message tb msg s id a hint profile requested fresh
      depth tyDepth typedEnv readsId readsHint readsMessage typesId typesHint typesMessage held member
  have same : term' = term := Except.ok.inj (tree'.symm.trans tree)
  subst term'
  have answerPoint : syncOpStep (.refModify q term p.env) m.state =
      some ({ m.state with refs := refPoke m.state.refs q (cellVal (tb.afterOffer id hint (Model.offer s id a).2.1) msg (Model.offer s id a).1) }, Val.tuple [offerReplyVal (Model.offer s id a).2.1,
        Val.list (woken.map (takerVal (tb.afterOffer id hint (Model.offer s id a).2.1)))]) := by
    rw [pointEnv]
    exact answer
  exact ⟨woken, notified,
    StoreExecution.modify_loop root table m fiber f term request p compileFuel q
      _ _ yielding rest found currentCompile pointFuel requestCell interrupt override budget answerPoint,
    offer_jobs profile id a⟩

end Effect4.Queue.Execution
