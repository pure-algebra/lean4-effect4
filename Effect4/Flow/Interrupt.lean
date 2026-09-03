import Effect4.Flow.Region

/-!
# Flow.Interrupt

Owner: interruption as decisions (plan packet M2 of
`docs/research/2026-09-03-reification-plan.md`, after the A1 alphabet bump).

Interruption is not a new effect here: it is a *second decision family*. A run
has finitely many interruptible points, and a tape answers, at each one,
whether the interrupt is delivered there. That is the same shape as `choose`
(`Effect4/Flow/Decision.lean`) with three differences:

* **The site space is disjoint.** A `choose` site is a number the flow author
  wrote; an interrupt site is a number this module computes from the flow's own
  identifiers, offset by `interruptBase`. `Point.site_ne_choose` is the
  separation: no interrupt site is a site below the base, and `Point.site_inj`
  says the two shapes of point never collide with each other. A flow whose
  `choose` sites all lie below the base (`sitesSeparated`) can therefore carry
  both tapes on one wire without either answering the other's question.
* **Exhaustion is not a frontier.** A `choose` with no tape entry is an
  unanswered live frontier: the run cannot proceed. An interrupt point with no
  tape entry is answered, and the answer is *no*: the run proceeds. So the
  interrupt tape is written only where delivery happens, and the empty tape is
  the uninterrupted run.
* **A mask defers rather than refuses.** A delivered answer taken while any
  open region is masked is not dropped and not delivered: it is *pending*
  (rc.112's `_deferredInterrupt`, `Effect4/Runtime/Runtime.lean`), and the next
  point that is not masked delivers it. `interruptPoint_masked_defers` and
  `interruptPoint_unmasked_delivers` are the two halves.

**The points.** Before every `perform` of a plain block, and at every region
`leave`. `acquire` is not a point: rc.112 acquires uninterruptibly, and the
region contract already says a release is one operation by construction.

**Delivery.** Every open region closes innermost-first with
`Outcome.interrupted` — so each `leave` row and each `finalizer` row carries
`{"interrupted":true}` on the wire — and the run ends `done interrupted` with
`InterruptResult.interrupted`. This is the Lean producer of `Outcome.interrupted`
that A1 promised: before M2 only the P-T11 projection could build one.

`RunResult` (`Effect4/Semantics/Runs.lean`) is not touched: an interrupted run
is a fourth way to end that the region runner has no arm for, so this module
carries its own `InterruptResult` and its own runner, and every existing
theorem about `regionLoop` still speaks about the same function it did.

Rows `E4-FLOW-CE-022` (a delivery under a mask must defer) and
`E4-FLOW-CE-023` (a finalizer must see `interrupted`).
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val Outcome)

/-! ## 1. The site space

Interrupt sites are computed, never authored. Everything at or above
`interruptBase` is an interrupt site; a `choose` site below it can never be
answered by an interrupt tape entry, nor the other way round. -/

/-- The first site number reserved for interrupt points. -/
def interruptBase : Nat := 1000000

/-- An interruptible point of a run. -/
inductive Point where
  /-- Before the `perform` of a plain block. -/
  | perform (block : BlockId)
  /-- At the `leave` of a region. -/
  | leave (region : RegionId)
deriving DecidableEq, Repr

namespace Point

/-- The decision site of a point: `perform` sites are odd above the base,
`leave` sites even, so the two families never collide. -/
def site : Point → DecisionId
  | .perform block => ⟨interruptBase + 2 * block.value + 1⟩
  | .leave region => ⟨interruptBase + 2 * region.value⟩

theorem site_ge (point : Point) : interruptBase ≤ point.site.value := by
  cases point <;> simp [site] <;> omega

/-- The separation: a site below the base is not an interrupt site. Every
`choose` site of a flow admitted by `sitesSeparated` is such a site. -/
theorem site_ne_choose {point : Point} {choose : DecisionId}
    (below : choose.value < interruptBase) : point.site ≠ choose := by
  intro eq
  have ge := site_ge point
  rw [eq] at ge
  omega

/-- Distinct points have distinct sites. -/
theorem site_inj {left right : Point} (eq : left.site = right.site) : left = right := by
  cases left with
  | perform lb =>
      cases right with
      | perform rb =>
          obtain ⟨lb⟩ := lb; obtain ⟨rb⟩ := rb
          simp only [site, DecisionId.mk.injEq] at eq
          have same : lb = rb := by omega
          simp [same]
      | leave rr => simp only [site, DecisionId.mk.injEq] at eq; omega
  | leave lr =>
      cases right with
      | perform rb => simp only [site, DecisionId.mk.injEq] at eq; omega
      | leave rr =>
          obtain ⟨lr⟩ := lr; obtain ⟨rr⟩ := rr
          simp only [site, DecisionId.mk.injEq] at eq
          have same : lr = rr := by omega
          simp [same]

end Point

/-- Whether every `choose` site of a region flow lies below `interruptBase`, so
that the choice tape and the interrupt tape answer disjoint questions. -/
def sitesSeparated (flow : RegionFlow Ty) : Bool :=
  flow.blocks.all fun block =>
    match block.term with
    | .plain (.choose site _ _ _) => site.value < interruptBase
    | _ => true

/-! ## 2. The interrupt tape -/

/-- Read the interrupt tape at one point. The head entry is consumed only when
it names this point; otherwise the point is answered *not delivered* and the
tape is kept. Exhaustion is the same answer: an interrupt tape names the points
that deliver, and nothing else. -/
def interruptRead : Tape → DecisionId → Bool × Tape
  | [], _ => (false, [])
  | entry :: rest, site =>
      if entry.site = site then (entry.branch, rest) else (false, entry :: rest)

theorem interruptRead_nil (site : DecisionId) : interruptRead [] site = (false, []) := rfl

theorem interruptRead_hit (site : DecisionId) (branch : Bool) (rest : Tape) :
    interruptRead (⟨site, branch⟩ :: rest) site = (branch, rest) := by
  simp [interruptRead]

theorem interruptRead_miss {site other : DecisionId} (ne : other ≠ site) (branch : Bool)
    (rest : Tape) :
    interruptRead (⟨other, branch⟩ :: rest) site = (false, ⟨other, branch⟩ :: rest) := by
  simp [interruptRead, ne]

/-- The interrupt state of a run: the unread tape and the pending (deferred)
interrupt. `pending` is rc.112's `_deferredInterrupt`. -/
structure IState where
  itape : Tape
  pending : Bool
deriving DecidableEq, Repr

/-- The initial interrupt state of a run. -/
def IState.start (itape : Tape) : IState := { itape := itape, pending := false }

/-! ## 3. The runner -/

/-- How an interruptible run ends. `interrupted` is the arm the region runner
has no room for; the other four are `RunResult`'s, arm for arm. -/
inductive InterruptResult where
  | done (value : Val)
  | failed (error : Val)
  /-- Every open region closed with `Outcome.interrupted` and the run ended. -/
  | interrupted
  | frontier (reason : Frontier)
  | refused (expected actual : DecisionId)
deriving DecidableEq, Repr

/-- Whether the run is masked: any open region declared uninterruptible masks
every point inside it, its own `leave` included. -/
def isMasked {alphabet : FlowAlphabet Ty} (masked : List RegionId)
    (stack : List (Frame alphabet)) : Bool :=
  stack.any fun frame => masked.any fun region => decide (region = frame.region)

/-- Ask the tape at one interrupt point. The answer is always traced — one
`decide` row per point, at the point's own site — then folded into the pending
flag. While masked the fold is all that happens (the interrupt defers); while
unmasked a pending interrupt is delivered here and the flag is cleared. -/
def interruptPoint [Monad M] (masked : Bool) (point : Point) (state : IState) :
    RunM M (Bool × IState) := do
  let answered := interruptRead state.itape point.site
  emit (.decide point.site.value answered.fst)
  let pending := state.pending || answered.fst
  if masked then pure (false, { itape := answered.snd, pending := pending })
  else pure (pending, { itape := answered.snd, pending := false })

/-- Close every open region, innermost first, with `interrupted`. Each frame
logs `leave region interrupted` and one `finalizer region interrupted` before
each release's own rows (`closeFrame`). A release that fails while the run is
being interrupted does not change the outcome: the run is interrupted. -/
def unwindInterrupt [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) : List (Frame alphabet) → RunM M Unit
  | [] => pure ()
  | frame :: rest => do
      let _ ← closeFrame service nameOf frame .interrupted
      unwindInterrupt service nameOf rest

/-- Deliver the interrupt: unwind, then end the run `done interrupted`. -/
def deliverInterrupt [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (tape : Tape) :
    RunM M (InterruptResult × Tape) := do
  unwindInterrupt service nameOf stack
  emit (.done .interrupted)
  pure (.interrupted, tape)

/-- End the run with a failure after closing every open region with it; the
region runner's `fail`, at `InterruptResult`. -/
def failInterrupt [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (error : Val) (tape : Tape) :
    RunM M (InterruptResult × Tape) := do
  let _ ← unwind service nameOf stack error
  emit (.done (.failure error))
  pure (.failed error, tape)

/-- Spend one unit of fuel per block, keeping the region stack and the
interrupt state. This is `regionLoop` with an interrupt point before every
`perform` and at every `leave`; every other arm is the same walk. -/
def interruptLoop [Monad M] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (masked : List RegionId) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) :
    Nat → BlockId → Env → Tape → IState → List (Frame alphabet) →
      RunM M (InterruptResult × Tape)
  | 0, block, _, tape, _, _ => do
      emit .frontier
      pure (.frontier (.fuel block), tape)
  | fuel + 1, block, env, tape, state, stack =>
    match flow.block? block with
    | none => pure (.frontier (.stuck block), tape)
    | some current =>
      let stuck : RunM M (InterruptResult × Tape) := pure (.frontier (.stuck block), tape)
      match current.term with
      | .plain term =>
          let raw : RawBlock Ty := { id := current.id, params := current.params, term := term }
          match plan alphabet raw env tape with
          | .stuck => stuck
          | .ret value => do
              emit (.done (.success value))
              pure (.done value, tape)
          | .jump target env' =>
              interruptLoop alphabet flow masked service nameOf fuel target env' tape state stack
          | .perform op request target env' => do
              let point ← interruptPoint (isMasked masked stack) (.perform current.id) state
              if point.fst then deliverInterrupt service nameOf stack tape
              else do
                let result ← StateT.lift (service.handle op request)
                logOperation service nameOf op request result
                match result with
                | .ok answer =>
                    interruptLoop alphabet flow masked service nameOf fuel target
                      (env' ++ [answer]) tape point.snd stack
                | .error error => failInterrupt service nameOf stack error tape
          | .exhausted site => do
              emit .frontier
              pure (.frontier (.unansweredDecision site), tape)
          | .mismatch expected actual => pure (.refused expected actual, tape)
          | .choose site branch target env' rest => do
              emit (.decide site.value branch)
              interruptLoop alphabet flow masked service nameOf fuel target env' rest state stack
      | .enter region body args =>
          match readArgs env args with
          | none => stuck
          | some values => do
              emit (.enter region.value)
              interruptLoop alphabet flow masked service nameOf fuel body values tape state
                ({ region := region, releases := [] } :: stack)
      | .acquire operation request release target args =>
          match alphabet.lookup operation, alphabet.lookup release, env[request.index]?,
              readArgs env args, stack with
          | some op, some releaser, some requestValue, some values, frame :: rest => do
              let result ← StateT.lift (service.handle op requestValue)
              logOperation service nameOf op requestValue result
              match result with
              | .ok answer =>
                  interruptLoop alphabet flow masked service nameOf fuel target
                    (values ++ [answer]) tape state
                    ({ frame with releases := (releaser, answer) :: frame.releases } :: rest)
              | .error error => failInterrupt service nameOf stack error tape
          | _, _, _, _, _ => stuck
      | .leave value =>
          match env[value.index]?, stack, current.region.bind flow.row? with
          | some v, frame :: rest, some row => do
              let point ← interruptPoint (isMasked masked stack) (.leave frame.region) state
              if point.fst then do
                let _ ← closeFrame service nameOf frame .interrupted
                unwindInterrupt service nameOf rest
                emit (.done .interrupted)
                pure (.interrupted, tape)
              else do
                match ← closeFrame service nameOf frame (.success v) with
                | [] =>
                    interruptLoop alphabet flow masked service nameOf fuel row.continue_ [v] tape
                      point.snd rest
                | error :: _ => failInterrupt service nameOf rest error tape
          | _, _, _ => stuck

/-- Run an admitted region flow with an interrupt tape, from its entry with no
open region. -/
def runInterrupts [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (masked : List RegionId)
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (tape : Tape)
    (itape : Tape) (input : Val) : RunM M (InterruptResult × Tape) :=
  interruptLoop alphabet flow.flow masked service nameOf fuel flow.flow.entry [input] tape
    (IState.start itape) []

/-- Run with the fuel the erased graph allots. -/
def runInterruptsDefault [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (masked : List RegionId)
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) (tape : Tape)
    (itape : Tape) (input : Val) : RunM M (InterruptResult × Tape) :=
  runInterrupts (fuelFor flow.flow.erase tape) flow masked service nameOf tape itape input

/-! ## 4. Laws

The two halves of deferral, and the finalizer's view of an interrupted close.
Everything else about a run is a receipt (`Effect4Test/Flow/InterruptContract.lean`):
the three goldens' logs are `#guard`ed there, and the host agrees with them. -/

/-- **Deferral.** While masked, no point delivers, and a delivered answer is
not lost: it becomes the pending interrupt. -/
theorem interruptPoint_masked_defers [Monad M] [LawfulMonad M] (point : Point) (state : IState)
    (log : Effect4.Trace.Log) :
    (interruptPoint (M := M) true point state).run log =
      pure ((false, { itape := (interruptRead state.itape point.site).snd,
                      pending := state.pending || (interruptRead state.itape point.site).fst }),
        log ++ [.decide point.site.value (interruptRead state.itape point.site).fst]) := by
  simp [interruptPoint, emit_run]

/-- **Delivery.** While unmasked, a point delivers exactly when the interrupt
is already pending or the tape answers it here, and the flag is cleared. -/
theorem interruptPoint_unmasked_delivers [Monad M] [LawfulMonad M] (point : Point) (state : IState)
    (log : Effect4.Trace.Log) :
    (interruptPoint (M := M) false point state).run log =
      pure ((state.pending || (interruptRead state.itape point.site).fst,
             { itape := (interruptRead state.itape point.site).snd, pending := false }),
        log ++ [.decide point.site.value (interruptRead state.itape point.site).fst]) := by
  simp [interruptPoint, emit_run]

/-- **Finalizers observe `interrupted`.** An interrupted close writes
`leave region interrupted` and then, in the reified scope's close order, one
`finalizer region interrupted` row before each release's own rows. This is
`closeFrame_log` at the new outcome, and the reason `Outcome.interrupted` now
has a Lean producer. -/
theorem closeFrame_interrupted_log {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (frame : Frame alphabet) (log : Effect4.Trace.Log) (s : σ) :
    (((closeFrame service nameOf frame .interrupted).run log).run s).fst.snd =
      log ++ Effects.Trace.Event.leave frame.region.value .interrupted ::
        closeRows service nameOf frame.region.value .interrupted
          (Effect4.Scope.closeOrder frame.toScope) s :=
  closeFrame_log service nameOf frame .interrupted log s

/-- The reified `Exit` an interrupted close carries is the one-reason interrupt
cause with no interruptor: the wire drops the interruptor identity, and the
model has none to drop. -/
theorem frameExit_interrupted :
    frameExit .interrupted =
      Effect4.Exit.failure ⟨[.interrupt none Effect4.ReasonAnnotations.empty]⟩ := rfl

end Effect4.Flow
