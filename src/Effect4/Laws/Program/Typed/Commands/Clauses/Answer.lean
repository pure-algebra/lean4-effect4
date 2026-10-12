import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Answer — fiber clauses that answer from the machine

Concept 4 of `docs/core/semantics.md` (`step-deliver-preserves`, `step-loop-preserves`): clauses of
`deliver_preserves` / `step_loop` through `evaluate_keeps` (`Commands/Evaluate.lean`), each
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
    (fun _ cert pre => by
      subst pre
      exact snapshotChildren_answers root w f.children declared) (fun _ => rfl))

/-- **`getContext`** (`FiberAction.getContext`): the fiber's context, whose services fit by `J`
(`RunFiberOk`'s service clause) and cover the code's row, answered as a context handle
(`ambient_getContext_answers`); the continuation runs at the context's own keys (the operation's
input). -/
theorem clause_getContext (root : ProgramSource) (rootTy : EffTy) :
    FiberClauseKeeps root rootTy .getContext := by
  intro w m rest f y next ev hc
  have c5 : ServicesFit w f.context.services :=
    (ev.typed.machine.fiber (rfiber?_mem ev.look)).ok.c5
  refine ev.settle_continue
    { f.frame with current := next ((interpR root.program).contextValue f.context) }
    (fun ty declared => ?_)
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have continued := typedNext w (leHost_refl w) (Val.context f.context)
    (ambient_getContext_answers c5 covered pre)
  have input : ambientFiberInput row .getContext (Val.context f.context) =
      f.context.services.keysRow := by
    simp only [ambientFiberInput, Val.context?_context]
  rw [input] at continued
  exact ⟨f.context.services.keysRow, tin, flag,
    (Provision.satisfies_iff_subset_keysRow _ _).mpr (Row.subset_refl _), bit, continued, stack,
    ⟨prov.recorded, prov.deferred⟩⟩

/-- **`interrupt`** (`:857`, D6b): the public interrupt installs `interruptAs(target, self)` over
the saved answer frame, typed at `unit` at the fiber's row by its row's pre, the target's
declaration, which this row's pre gives (finding F-PRE); the frame carries the reply to the
continuation. -/
theorem clause_interrupt (root : ProgramSource) (rootTy : EffTy) (target : FiberId) :
    FiberClauseKeeps root rootTy (.interrupt target) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.interrupt _ m (saveAnswerR f (seqR next)) y target))
  unfold FiberAction.interrupt
  refine ev.settle_continue { f.frame with
    current := fiberValR (.interruptAs target f.id) rfl, stack := .answer (seqR next) :: f.frame.stack }
    (fun ty declared => ?_)
  obtain ⟨row, tin, flag, covered, bit, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, typedNext, entry, wf⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  refine ⟨row, ((((⟨.unit, .never, Env.Requirement.empty⟩ : EffTy), row, row) : AmbientPosition), tin.2),
    flag, covered, bit, ?_,
    .cons (.inl (Evaluating.unitAnswerFrame (fun w' o ans post => typedNext w' o ans post) entry wf))
      stack, ⟨prov.recorded, prov.deferred⟩⟩
  refine .fiber (op := .interruptAs target f.id) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () pre (fun w' _ ans post => ?_)
    ⟨Row.subset_refl _, Row.subset_refl _⟩
  change ans = Val.unit at post
  subst post
  exact .pure (ambientExit_const (strongExit_success w' _ _ trivial)) ⟨Row.subset_refl _, Row.subset_refl _⟩

end Effect4.Program.Typed
