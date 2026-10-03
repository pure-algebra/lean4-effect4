import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Answer — fiber clauses that answer from the machine

Concept 4 of `docs/core/semantics.md` (`step-deliver-preserves`, `step-loop-preserves`): clauses of
`M6Ledger.step_deliver` / `step_loop` through `evaluate_keeps` (`Commands/Evaluate.lean`), each
`FiberClauseKeeps root rootTy op` for an operation whose evaluation answers a value read off the
machine and continues.

Not established: the other clauses (`Commands/Evaluate.lean`, `Clauses/*`), progress.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

/-- **`snapshotChildren`** (`Machine/Fibers.lean`, `FiberAction.snapshotChildren`): the fiber's
tracked children as fiber handles, each declared by `J` (`FiberTyped.children`), so the answer fits
the certificate the pre fixes, `List<Fiber<unknown, unknown>>` (`snapshotChildren_answers`). -/
theorem clause_snapshotChildren (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .snapshotChildren := by
  intro w m rest f y next ev hc
  have declared : ∀ c ∈ f.children, (w.Γ c).isSome = true :=
    (ev.typed.machine.fiber (rfiber?_mem ev.look)).children
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    ((interpR root.program).fibersValue f.children)
    (fun cert pre => by
      subst pre
      exact snapshotChildren_answers root w f.children declared))

/-- A context whose services fit is live: its value's handles are its service values'
(`Val.handles_context`), each live by `ServicesFit`'s second half (finding F-CTX). -/
theorem live_context_of_servicesFit {w : World} {ctx : Ctx} (h : ServicesFit w ctx.services) :
    Live w (Val.context ctx) := fun x hx =>
  flatMap_live h.2 x (by rw [Val.handles_context] at hx; exact hx)

/-- **`getContext`** (`FiberAction.getContext`): the fiber's context, whose services fit by `J`
(`RunFiberOk`'s service clause) and which is therefore live, answered as a context handle
(`getContext_answers`). -/
theorem clause_getContext (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .getContext := by
  intro w m rest f y next ev hc
  have c5 : ServicesFit w f.context.services :=
    (ev.typed.machine.fiber (rfiber?_mem ev.look)).ok.c5
  exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    ((interpR root.program).contextValue f.context)
    (fun cert pre => by
      subst pre
      exact getContext_answers root w f.context c5 (live_context_of_servicesFit c5)))

/-- **`interrupt`** (`:857`, D6b): the public interrupt installs `interruptAs(target, self)` over
the saved answer frame, typed at `unit` by its row's pre, the target's declaration, which this
row's pre gives (finding F-PRE); the frame carries the reply to the continuation. -/
theorem clause_interrupt (root : ProgramSource) (rootTy : EffTy) (target : FiberId) :
    FiberClauseKeeps root rootTy (.interrupt target) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.interrupt _ m (saveAnswerR f (seqR next)) y target))
  unfold FiberAction.interrupt
  refine ev.settle_continue { f.frame with
    current := fiberValR (.interruptAs target f.id) rfl, stack := .answer (seqR next) :: f.frame.stack }
    (fun ty declared => ?_)
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  refine ⟨⟨.unit, .never, Env.Requirement.empty⟩, ?_,
    hostStack_push (Evaluating.unitAnswerFrame typedNext) stack, ⟨prov.recorded, prov.deferred⟩⟩
  exact TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () pre (fun _ _ _ post => unitAnswer_typed root post)

end Effect4.Program.Typed
