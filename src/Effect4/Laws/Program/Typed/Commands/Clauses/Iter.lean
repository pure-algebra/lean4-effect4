import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Iter — the generator's entry clause

Concept 4 of `docs/core/semantics.md` (`step-deliver-preserves`, `step-loop-preserves`): the clause
of `deliver_preserves` / `step_loop` (through `evaluate_keeps`, `Commands/Evaluate.lean`) for
`FiberOp.gen`, the generator's entry (`evaluateFiberR`, `Laws/Program/EvaluateR.lean`, the `gen`
arm; `Effect.gen`, `internal/effect.ts:1175-1196`): the answer frame saved, the walk's first step
(`interpRAt`'s `iterNext`, `walkR`) run from the body's start, and a resumed yield's code installed
over the generator's `iter` frame, or a finished walk's exit installed over the answer frame.

Decisions row 190 makes a hook frame's typing a protocol and puts the source-derived invariant on
the producer; decisions row 349 types the machine's code by the row-indexed judgment, so the
protocol is the ambient one (`AmbientIteratorProtocol`, the greatest invariant of
`AmbientIteratorStep`, `Typed/Context.lean`), at the frame's success and failure rows. This module
states the producer's obligation as one proposition, `GenProtocol`: a generator entry at a point
the checker types at `cert`, entered at a row that holds `cert`'s requirement row and the
requirement rows of the programs the point's stack passes (`AmbientStackTyped`), is in the ambient
iterator protocol at that row from `⟨unit, cert.error, cert.requires⟩` to `cert`.
`clause_gen_of_stack` derives the clause from it and from the stack's rows at the entry; the
protocol's first step is exactly the entry's walk at the value `unit`.

`GenProtocol` itself is proved in `Clauses/Gen.lean` (`genProtocol`): coinduction over typed
generator positions. `fiberPre`'s `gen` arm names the generator node (seat M6E's third finding).

Not established here: `clause_gen_of` itself. The `gen` arm of `ambientFiberPre`
(`Typed/Residual.lean`) carries the point's type, its node and its requirement row, but not the
stack's rows, which M5 needs to type a yielded parameter's run (`param_arm`'s `required`,
`DenotesTyped`'s stack premise); M5's producer (`gen_arm`) holds them (`ChildDenotes`'s
`savedParams`) and drops them. `clause_gen_of_stack` takes them as its premise, so the clause is
this theorem once the arm carries them (seat A's receipt). Not established: that a generator
finishes.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched
open Contracts

/-- **The generator producer's obligation** (decisions rows 190 and 349): at a point the checker
types at `cert`, entered at a row `available` that holds `cert`'s requirement row and the
requirement rows of the programs the point's stack passes, the generator's entry name, its body's
start with nothing bound, is in the ambient iterator protocol at the frame rows `available`,
`available`, from `⟨unit, cert.error, cert.requires⟩` (the entry is stepped at `unit`) to `cert`.
The premises are `DenotesTyped`'s (`Typed/Assembly.lean`; decisions rows 170, 175 and 349), which
`J` holds (`MachineTyped.sourceWF`, `MachineTyped.services`) but for the stack's rows: a resumed
yield is the denotation of the yielded effect at its point, typed only at a well-formed source,
the source's service table, and a row holding the point's and its stack's requirement rows. -/
def GenProtocol (root : ProgramSource) : Prop :=
  SourceWF root →
    ∀ (w : World), w.serviceTy = root.sig.serviceTy →
      ∀ (available : Env.Requirement) (p : Point) (body : Stmts NativeOp) (cert : EffTy),
        Node.at_ (.eff root.program) p.path = some (.eff (.gen body)) → PointTyped root w p cert →
          Row.Subset cert.requires available →
          AmbientStackTyped root w available (scopeParams root.program p.path) p.params →
            AmbientIteratorProtocol root w available available ⟨.unit, cert.error, cert.requires⟩
              cert (.gen p [] false)

/-- The `gen` arm of the evaluator, as the clause reads it. -/
theorem evaluateFiberR_gen (interp : RInterp) (m : RState) (f : RFiber) (y : Bool) (p : Point)
    (next : ExitV → RProgram) :
    evaluateFiberR interp m f y (.gen p) next =
      match (interp.iterNext (.gen p [] false) .unit).2 with
      | .done v => ⟨m, answerR (saveAnswerR f next) (.pure (.success v)), y, .continue_, [], []⟩
      | .halt c => ⟨m, answerR (saveAnswerR f next) (.pure (.failure c)), y, .continue_, [], []⟩
      | .resume code cont =>
        ⟨m, answerR (pushR (saveAnswerR f next) (.iter cont)) code, y, .continue_, [], []⟩ := rfl

/-- **`gen`** from the producer's obligation and the stack's rows at the entry: the pre types the
point at `cert`, names its generator node (`fiberPre`'s `gen` arm; seat M6E's third finding: at a
point of another node the walk halts with `badName`, which no exit type admits) and holds `cert`'s
requirement row within the fiber's row; with the stack's rows there (`stacked`) the entry is in the
protocol at that row (`GenProtocol`, at `J`'s source and service table). Its first step at the
evaluator's view, typed by `J` (`Evaluating.view`), and the value `unit` answers a finished walk
with an exit at `cert`, installed at the row over the answer frame, which carries it to the
continuation at the post `ExitOk w' cert`; a resumed yield's code is typed at the row at an
intermediate type, and its `iter` frame is the protocol of its tail, from that type to `cert`, over
the same answer frame. Consumer: `clause_gen_of`, once `ambientFiberPre`'s `gen` arm carries the
stack's rows (seat A's receipt). -/
theorem clause_gen_of_stack (root : ProgramSource) (rootTy : EffTy) (producer : GenProtocol root)
    (p : Point)
    (stacked : ∀ (w : World) (row : Env.Requirement) (cert : FiberCert (.gen p)),
      ambientFiberPre root w row (.gen p) cert →
        AmbientStackTyped root w row (scopeParams root.program p.path) p.params) :
    FiberClauseKeeps root rootTy (.gen p) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨row, ⟨q, b⟩, final, covered, bit, current, stack, prov⟩ :=
    ev.code (by rw [hc]; rfl) ty declared
  change b = f.frame.interruptible at bit
  subst bit
  change AmbientProg root w row q f.frame.current at current
  rw [hc] at current
  obtain ⟨cert, pre, typedNext, _⟩ := ambientProg_fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have params := stacked w row cert pre
  obtain ⟨⟨hpt, body, hat⟩, coverage⟩ := pre
  change EffTy at cert
  have answer : MFrame root w (((cert, row, row) : AmbientPosition), f.frame.interruptible)
      (q, f.frame.interruptible) (.answer next) :=
    .answer next fun w' o ex hex => by
      rw [ambientInput_const]
      exact typedNext w' o ex hex.1
  have below : MHostStack root w (m.update f) f.id
      (((cert, row, row) : AmbientPosition), f.frame.interruptible) (finalPos ty final)
      (.answer next :: f.frame.stack) :=
    .cons (.inl answer) stack
  obtain ⟨_, _, entry⟩ := AmbientIteratorProtocol.unfold
    (producer ev.typed.machine.sourceWF w ev.typed.machine.services row p body cert hat hpt coverage
      params)
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
        exact ⟨row, (((cert, row, row) : AmbientPosition), f.frame.interruptible), final, covered,
          rfl, .pure (ambientExit_const step) ⟨Row.subset_refl _, Row.subset_refl _⟩, below,
          ⟨prov.recorded, prov.deferred⟩⟩)
  | halt c =>
    intro step
    exact ev.settle_continue
      { f.frame with current := .pure (.failure c), stack := .answer next :: f.frame.stack }
      (fun ty' declared' => by
        have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
        subst same
        exact ⟨row, (((cert, row, row) : AmbientPosition), f.frame.interruptible), final, covered,
          rfl, .pure (ambientExit_const step) ⟨Row.subset_refl _, Row.subset_refl _⟩, below,
          ⟨prov.recorded, prov.deferred⟩⟩)
  | resume code cont =>
    intro step
    obtain ⟨tin', typedCode, tail⟩ := step
    exact ev.settle_continue
      { f.frame with current := code, stack := .iter cont :: .answer next :: f.frame.stack }
      (fun ty' declared' => by
        have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
        subst same
        exact ⟨row, (((tin', row, row) : AmbientPosition), f.frame.interruptible), final, covered,
          rfl, typedCode,
          .cons (.inl (.iter cont (fun _ o => ambientIteratorProtocol_mono o tail)
            (Row.subset_refl _))) below,
          ⟨prov.recorded, prov.deferred⟩⟩)

end Effect4.Program.Typed
