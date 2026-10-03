import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Iter — the generator's entry clause

Concept 4 of `docs/core/semantics.md` (`step-deliver-preserves`, `step-loop-preserves`): the clause
of `M6Ledger.step_deliver` / `step_loop` (through `evaluate_keeps`, `Commands/Evaluate.lean`) for
`FiberOp.gen`, the generator's entry (`evaluateFiberR`, `Laws/Program/EvaluateR.lean`, the `gen`
arm; `Effect.gen`, `internal/effect.ts:1175-1196`): the answer frame saved, the walk's first step
(`interpRAt`'s `iterNext`, `walkR`) run from the body's start, and a resumed yield's code installed
over the generator's `iter` frame, or a finished walk's exit installed over the answer frame.

Decisions row 190 makes a hook frame's typing a protocol (`IteratorProtocol`, the greatest
invariant of `IteratorStep`, `Typed/Residual.lean`) and puts the source-derived invariant on the
producer. This module states the producer's obligation as one proposition, `GenProtocol`: a
generator entry at a point the checker types at `cert` is in the iterator protocol from
`⟨unit, cert.error, cert.requires⟩` to `cert`. `clause_gen_of` derives the clause from it; the
protocol's first step is exactly the entry's walk at the value `unit`.

`GenProtocol` itself is proved in `Clauses/Gen.lean` (`genProtocol`): coinduction over typed
generator positions, a position in the body with its enclosing blocks, its environment typed at the
checker's, and the reachability bits of `GenTy` covering the walk's fall-off (the checker repair is
seat M6E's `1343764b`, owner option (a)). `fiberPre`'s `gen` arm names the generator node (seat
M6E's third finding).

Not established: that a generator finishes.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Contracts

/-- **The generator producer's obligation** (decisions row 190): at a point the checker types at
`cert`, the generator's entry name, its body's start with nothing bound, is in the iterator
protocol from `⟨unit, cert.error, cert.requires⟩` (the entry is stepped at `unit`) to `cert`.
The premises are `DenotesTyped`'s (`Typed/Assembly.lean`; decisions rows 170, 175), which `J`
holds (`MachineTyped.sourceWF`, `MachineTyped.services`): a resumed yield is the denotation of the
yielded effect at its point, typed only at a well-formed source and the source's service table. -/
def GenProtocol (root : ProgramSource) : Prop :=
  root.program.layerRefsWF = true →
    ∀ (w : World), w.serviceTy = root.sig.serviceTy →
      ∀ (p : Point) (body : Stmts NativeOp) (cert : EffTy),
        Node.at_ (.eff root.program) p.path = some (.eff (.gen body)) → PointTyped root w p cert →
          IteratorProtocol root w ⟨.unit, cert.error, cert.requires⟩ cert (.gen p [] false)

/-- The `gen` arm of the evaluator, as the clause reads it. -/
theorem evaluateFiberR_gen (interp : RInterp) (m : RState) (f : RFiber) (y : Bool) (p : Point)
    (next : ExitV → RProgram) :
    evaluateFiberR interp m f y (.gen p) next =
      match (interp.iterNext (.gen p [] false) .unit).2 with
      | .done v => ⟨m, answerR (saveAnswerR f next) (.pure (.success v)), y, .continue_, []⟩
      | .halt c => ⟨m, answerR (saveAnswerR f next) (.pure (.failure c)), y, .continue_, []⟩
      | .resume code cont =>
        ⟨m, answerR (pushR (saveAnswerR f next) (.iter cont)) code, y, .continue_, []⟩ := rfl

/-- **`gen`** from the producer's obligation: the pre types the point at `cert` and names its
generator node (`fiberPre`'s `gen` arm; seat M6E's third finding: at a point of another node the
walk halts with `badName`, which no exit type admits), so the entry is in the protocol
(`GenProtocol`, at `J`'s source and service table); its first step at the evaluator's view, typed
by `J` (`Evaluating.view`), and the value `unit` answers a finished walk with an exit at `cert`,
installed over the answer frame, which carries it to the continuation at the post `ExitOk w' cert`;
a resumed yield's code is typed at an intermediate type and its `iter` frame accepted by the
protocol of its tail, from that type to `cert`, over the same answer frame. -/
theorem clause_gen_of (root : ProgramSource) (rootTy : EffTy) (producer : GenProtocol root)
    (p : Point) : FiberClauseKeeps root rootTy (.gen p) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, ⟨pre, body, hat⟩, typedNext⟩ := TypedProg.fiber_inv current
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have answer : FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w cert tin
      (.answer next) :=
    answerFrame_typed (post := fun w' ans => ExitOk w' cert ans) (fun _ _ _ hex => hex)
      (fun w' o ans post => typedNext w' o ans post)
  have below : HostStack root w (m.update f) f.id cert ty (.answer next :: f.frame.stack) :=
    hostStack_push answer stack
  obtain ⟨_, _, entry⟩ := IteratorProtocol.unfold
    (producer ev.typed.machine.sourceWF w ev.typed.machine.services p body cert hat pre)
  have step := entry w (leHost_refl w) m.completedExits ev.view .unit
    (show Fits w Val.unit Ty.unit from trivial)
  rw [evaluateFiberR_gen]
  revert step
  cases ((interpRAt root.program m.completedExits).iterNext (.gen p [] false) .unit).2 with
  | done v =>
    intro step
    exact ev.settle_continue
      { f.frame with current := .pure (.success v), stack := .answer next :: f.frame.stack }
      (fun ty' declared' => by
        have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
        subst same
        exact ⟨cert, TypedProg.pure step, below, ⟨prov.recorded, prov.deferred⟩⟩)
  | halt c =>
    intro step
    exact ev.settle_continue
      { f.frame with current := .pure (.failure c), stack := .answer next :: f.frame.stack }
      (fun ty' declared' => by
        have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
        subst same
        exact ⟨cert, TypedProg.pure step, below, ⟨prov.recorded, prov.deferred⟩⟩)
  | resume code cont =>
    intro step
    obtain ⟨tin', typedCode, tail⟩ := step
    exact ev.settle_continue
      { f.frame with current := code, stack := .iter cont :: .answer next :: f.frame.stack }
      (fun ty' declared' => by
        have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
        subst same
        exact ⟨tin', typedCode, hostStack_push (frameAccepts_iter tail) below,
          ⟨prov.recorded, prov.deferred⟩⟩)

end Effect4.Program.Typed
