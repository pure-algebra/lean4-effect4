import Effects.Flow.Checked
import Effect4.Flow.Decision
import Effect4.Semantics.Frontier
import Effect4.Semantics.Observation

/-!
# Semantics.Runs

Owner: the executable face of an admitted first-order flow (plan packet
P-T2). A run walks blocks with a positional environment (one value per block
parameter), asks a `FlowService` for every `perform`, answers every `choose`
from a finite tape, and logs the shared trace alphabet as it goes. It is the
second Lean emitter of that alphabet; agreement with the traced service over
the algebra is the internal oracle (`docs/TRACE-DAG.md`).

Control is separated from effect: `plan` is the pure decision of one block,
`step` runs it in the service's monad, `loop` spends one unit of fuel per
block. Fuel exhaustion and tape exhaustion end a run at a `Frontier`, never a
failure (DB-04); a tape entry for another site is a refusal (R6).

Flow v3 adds two terminators. A `performCatch` names a failure successor; the
plain service of this module cannot fail (`FlowService.handle` answers a `Val`),
so a plain run always takes its value edge and reads exactly as a `perform`.
The failure edge is taken by the region runner (`Effect4/Flow/Region.lean`),
whose service answers an `Except`. A `branch` is taken by the *value* of its
test operand and is still a decision *site*: the run reads the tape entry at
that site exactly as a `choose` does, and refuses when the tape disagrees with
the value, so the tape bound and `CyclesWF` are unchanged. That is one rule,
not two. Admission types the test operand `boolTy`, but the carrier claims no
boolean semantics (`Effects.Trace.Val` is untyped and a `FlowService` answers
an unconstrained `Val`), so a test operand may have no boolean reading at all;
such a run is refused like any other disagreement (`E4-FLOW-CE-029`). It is
`PlanSized.mismatch`, not a tape-only fallthrough, that keeps `stuck`
unreachable on an admitted flow (`plan_checked`).
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val)

/-- How a finite run ends. -/
inductive RunResult where
  | done (value : Val)
  /-- An operation failed and every open region was closed with the failure
  (region flows, `Effect4/Flow/Region.lean`); plain flows never fail. -/
  | failed (error : Val)
  | frontier (reason : Frontier)
  /-- The tape's next entry answers another site: the tape is not this flow's.
  A Flow v3 `branch` whose tape entry names its own site but disagrees with the
  test *value* refuses with that site twice: the entry is at the right site and
  still not this run's answer. -/
  | refused (expected actual : DecisionId)
deriving DecidableEq, Repr

namespace RunResult

def exhausted : RunResult → Bool
  | .frontier (.fuel _) => true
  | _ => false

def stuck : RunResult → Bool
  | .frontier (.stuck _) => true
  | _ => false

end RunResult

/-- What a run asks of the world: one handler per operation, and which
operations are pure atoms (run, but excluded from the trace). -/
structure FlowService (alphabet : FlowAlphabet Ty) (M : Type → Type) where
  handle : alphabet.Op → Val → M Val
  pure : alphabet.Op → Bool := fun _ => false

/-- The positional environment of a block: one value per parameter. -/
abbrev Env := List Val

/-- The run monad: the service's monad under the trace log. -/
abbrev RunM (M : Type → Type) := StateT Effect4.Trace.Log M

/-- Append one event to the log. -/
def emit [Monad M] (event : Effect4.Trace.Event) : RunM M Unit :=
  fun log => pure ((), log ++ [event])

theorem emit_run [Monad M] (event : Effect4.Trace.Event) (log : Effect4.Trace.Log) :
    (emit (M := M) event).run log = pure ((), log ++ [event]) := rfl

/-- Read an argument list from the environment. -/
def readArgs (env : Env) : List Var → Option (List Val)
  | [] => some []
  | v :: vs =>
    match env[v.index]?, readArgs env vs with
    | some value, some values => some (value :: values)
    | _, _ => none

/-- The pure control decision of one block, taken before any effect runs. -/
inductive Plan (alphabet : FlowAlphabet Ty) where
  | stuck
  | ret (value : Val)
  | jump (target : BlockId) (env : Env)
  | perform (operation : alphabet.Op) (request : Val) (target : BlockId) (env : Env)
  | exhausted (site : DecisionId)
  | mismatch (expected actual : DecisionId)
  | choose (site : DecisionId) (branch : Bool) (target : BlockId) (env : Env) (rest : Tape)
  /-- Flow v3's caught perform: the value edge's target and environment, then
  the failure edge's. A service that cannot fail never takes the second. -/
  | performCatch (operation : alphabet.Op) (request : Val) (target : BlockId) (env : Env)
      (onError : BlockId) (errorEnv : Env)

/-- The boolean reading of a `branch`'s test operand, when it has one. Nothing
in admission says a value of the alphabet's `boolTy` is a `Val.bool` (the
carrier claims no boolean semantics), so this is an `Option`, and a `none` is
a disagreement with every tape answer (`E4-FLOW-CE-029`). -/
def testValue (env : Env) (test : Var) : Option Bool :=
  match env[test.index]? with
  | some (.bool value) => some value
  | _ => none

/-- Decide what one block does. -/
def plan (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) (env : Env) (tape : Tape) :
    Plan alphabet :=
  match block.term with
  | .ret value =>
      match env[value.index]? with
      | some v => .ret v
      | none => .stuck
  | .jump target args =>
      match readArgs env args with
      | some values => .jump target values
      | none => .stuck
  | .perform operation request target args =>
      match alphabet.lookup operation, env[request.index]?, readArgs env args with
      | some op, some requestValue, some values => .perform op requestValue target values
      | _, _, _ => .stuck
  | .choose decision left right args =>
      match readArgs env args with
      | none => .stuck
      | some values =>
        match tape.read decision with
        | .exhausted => .exhausted decision
        | .mismatch expected actual => .mismatch expected actual
        | .answered branch rest =>
            .choose decision branch (if branch then left else right) values rest
  | .performCatch operation request target args onError errorArgs =>
      match alphabet.lookup operation, env[request.index]?, readArgs env args,
          readArgs env errorArgs with
      | some op, some requestValue, some values, some errorValues =>
          .performCatch op requestValue target values onError errorValues
      | _, _, _, _ => .stuck
  | .branch test site onTrue onFalse args =>
      match readArgs env args with
      | none => .stuck
      | some values =>
        match tape.read site with
        | .exhausted => .exhausted site
        | .mismatch expected actual => .mismatch expected actual
        | .answered answer rest =>
          if testValue env test = some answer then
            .choose site answer (if answer then onTrue else onFalse) values rest
          else .mismatch site site

/-- What one block transition yields. -/
inductive Next where
  | continue_ (block : BlockId) (env : Env) (tape : Tape)
  | finished (result : RunResult) (tape : Tape)

/-- Run one block: its plan, then its effects and events. -/
def step [Monad M] (alphabet : FlowAlphabet Ty) (service : FlowService alphabet M)
    (nameOf : alphabet.Op → String) (block : RawBlock Ty) (env : Env) (tape : Tape) :
    RunM M Next :=
  match plan alphabet block env tape with
  | .stuck => pure (.finished (.frontier (.stuck block.id)) tape)
  | .ret value => do
      emit (.done (.success value))
      pure (.finished (.done value) tape)
  | .jump target env' => pure (.continue_ target env' tape)
  | .perform op request target env' => do
      let answer ← StateT.lift (service.handle op request)
      if service.pure op then pure () else do
        emit (.op (nameOf op) request)
        emit (.answer (nameOf op) answer)
      pure (.continue_ target (env' ++ [answer]) tape)
  | .exhausted site => do
      emit .frontier
      pure (.finished (.frontier (.unansweredDecision site)) tape)
  | .mismatch expected actual => pure (.finished (.refused expected actual) tape)
  | .choose site branch target env' rest => do
      emit (.decide site.value branch)
      pure (.continue_ target env' rest)
  | .performCatch op request target env' _ _ => do
      let answer ← StateT.lift (service.handle op request)
      if service.pure op then pure () else do
        emit (.op (nameOf op) request)
        emit (.answer (nameOf op) answer)
      pure (.continue_ target (env' ++ [answer]) tape)

/-- Spend one unit of fuel per block. -/
def loop [Monad M] (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) :
    Nat → BlockId → Env → Tape → RunM M (RunResult × Tape)
  | 0, block, _, tape => do
      emit .frontier
      pure (.frontier (.fuel block), tape)
  | fuel + 1, block, env, tape =>
    match lookupBlock raw block with
    | none => pure (.frontier (.stuck block), tape)
    | some current => do
      match ← step alphabet service nameOf current env tape with
      | .finished result rest => pure (result, rest)
      | .continue_ next env' rest => loop alphabet raw service nameOf fuel next env' rest

/-- Enough fuel for every run of an admitted flow: between two decisions no
block repeats (every cycle chooses), so at most `blocks.length` blocks are
visited per tape entry, plus the final segment and the finishing block. -/
def fuelFor (raw : RawFlow Ty) (tape : Tape) : Nat :=
  (tape.length + 1) * raw.blocks.length + 1

/-- Run an admitted flow from its entry, returning the unconsumed tape. -/
def runTape [Monad M] {alphabet : FlowAlphabet Ty} (fuel : Nat) (flow : CheckedFlow alphabet)
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) : RunM M (RunResult × Tape) :=
  loop alphabet flow.erase service nameOf fuel flow.erase.entry [input] tape

/-- Run an admitted flow from its entry. -/
def run [Monad M] {alphabet : FlowAlphabet Ty} (fuel : Nat) (flow : CheckedFlow alphabet)
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) : RunM M RunResult :=
  (·.1) <$> runTape fuel flow service nameOf tape input

/-- Run with the fuel `fuelFor` allots. -/
def runDefault [Monad M] {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) : RunM M RunResult :=
  run (fuelFor flow.erase tape) flow service nameOf tape input

/-! ## Laws -/

private theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
private theorem idMap {α β : Type} (x : Id α) (f : α → β) : f <$> x = f x := rfl
private theorem idPure {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- A `choose` consumes exactly the head of the tape and logs the decision. -/
theorem step_choose_consumes_one [Monad M] (alphabet : FlowAlphabet Ty)
    (service : FlowService alphabet M) (nameOf : alphabet.Op → String)
    (id : BlockId) (params : List Ty) (decision : DecisionId) (left right : BlockId)
    (args : List Var) {env : Env} {values : List Val} (read : readArgs env args = some values)
    (branch : Bool) (rest : Tape) :
    step alphabet service nameOf ⟨id, params, .choose decision left right args⟩ env
        (⟨decision, branch⟩ :: rest) =
      (do emit (.decide decision.value branch)
          pure (.continue_ (if branch then left else right) values rest)) := by
  simp [step, plan, read, Tape.read]

theorem readArgs_of_bounded {env : Env} :
    ∀ {args : List Var}, (∀ v, v ∈ args → v.index < env.length) →
      ∃ values, readArgs env args = some values ∧ values.length = args.length
  | [], _ => ⟨[], rfl, rfl⟩
  | v :: vs, bounded => by
      obtain ⟨values, read, len⟩ :=
        readArgs_of_bounded (fun w mem => bounded w (List.mem_cons_of_mem _ mem))
      have lt := bounded v List.mem_cons_self
      have at_ : env[v.index]? = some env[v.index] := List.getElem?_eq_getElem lt
      exact ⟨env[v.index] :: values, by simp [readArgs, at_, read], by simp [len]⟩

/-- A plan whose every continuation resolves to a block of the environment's
size; `stuck` is not among its shapes. -/
inductive PlanSized (raw : RawFlow Ty) {alphabet : FlowAlphabet Ty} : Plan alphabet → Prop where
  | ret (value : Val) : PlanSized raw (.ret value)
  | exhausted (site : DecisionId) : PlanSized raw (.exhausted site)
  | mismatch (expected actual : DecisionId) : PlanSized raw (.mismatch expected actual)
  | jump {target : BlockId} {env' : Env} (targetBlock : RawBlock Ty)
      (found : lookupBlock raw target = some targetBlock)
      (sized : env'.length = targetBlock.params.length) :
      PlanSized raw (.jump target env')
  | perform {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
      (targetBlock : RawBlock Ty)
      (found : lookupBlock raw target = some targetBlock)
      (sized : env'.length + 1 = targetBlock.params.length) :
      PlanSized raw (.perform op request target env')
  | choose {site : DecisionId} {branch : Bool} {target : BlockId} {env' : Env} {rest : Tape}
      (targetBlock : RawBlock Ty)
      (found : lookupBlock raw target = some targetBlock)
      (sized : env'.length = targetBlock.params.length) :
      PlanSized raw (.choose site branch target env' rest)
  | performCatch {op : alphabet.Op} {request : Val} {target : BlockId} {env' : Env}
      {onError : BlockId} {errorEnv : Env}
      (targetBlock errorBlock : RawBlock Ty)
      (found : lookupBlock raw target = some targetBlock)
      (sized : env'.length + 1 = targetBlock.params.length)
      (foundError : lookupBlock raw onError = some errorBlock)
      (sizedError : errorEnv.length + 1 = errorBlock.params.length) :
      PlanSized raw (.performCatch op request target env' onError errorEnv)

/-- Admission makes `stuck` unreachable: on a well-formed flow, a block whose
environment has exactly its parameters plans a resolving, well-sized step. -/
theorem plan_checked {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty} (wf : FlowWF alphabet raw)
    {block : RawBlock Ty} (mem : block ∈ raw.blocks) {env : Env}
    (sized : env.length = block.params.length) (tape : Tape) :
    PlanSized raw (plan alphabet block env tape) := by
  have vars := wf.terms.1 block mem
  have arity := wf.terms.2.1 block mem
  have refs := wf.references block mem
  have ops := wf.operations block mem
  have resolve : ∀ (edge : Nat) (target : BlockId),
      block.term.successors[edge]? = some target →
      ∃ targetBlock, lookupBlock raw target = some targetBlock ∧
        targetBlock.params.length = block.term.arityAt edge := by
    intro edge target at_
    have isSome := refs target (List.mem_of_getElem? at_)
    have ar := arity edge target at_
    cases found : lookupBlock raw target with
    | none => rw [found] at isSome; cases isSome
    | some targetBlock => rw [found] at ar; exact ⟨targetBlock, rfl, ar⟩
  unfold plan
  cases termEq : block.term with
  | ret value =>
      dsimp only
      have lt : value.index < env.length := by
        rw [sized]; exact vars value (by rw [termEq]; exact List.mem_cons_self)
      rw [List.getElem?_eq_getElem lt]
      exact .ret _
  | jump target args =>
      dsimp only
      obtain ⟨values, read, len⟩ := readArgs_of_bounded (env := env) (args := args)
        (fun v vmem => by rw [sized]; exact vars v (by rw [termEq]; exact vmem))
      rw [read]
      obtain ⟨targetBlock, found, ar⟩ := resolve 0 target (by rw [termEq]; rfl)
      exact .jump targetBlock found (by rw [len, ar, termEq]; rfl)
  | perform operation request target args =>
      dsimp only
      have known : (alphabet.lookup operation).isSome = true := by
        have := ops; unfold OperationWF at this; rw [termEq] at this; exact this
      cases lookupEq : alphabet.lookup operation with
      | none => rw [lookupEq] at known; cases known
      | some op =>
        have lt : request.index < env.length := by
          rw [sized]; exact vars request (by rw [termEq]; exact List.mem_cons_self)
        rw [List.getElem?_eq_getElem lt]
        obtain ⟨values, read, len⟩ := readArgs_of_bounded (env := env) (args := args)
          (fun v vmem => by rw [sized]; exact vars v (by rw [termEq]; exact List.mem_cons_of_mem _ vmem))
        rw [read]
        obtain ⟨targetBlock, found, ar⟩ := resolve 0 target (by rw [termEq]; rfl)
        exact .perform targetBlock found (by rw [len, ar, termEq]; rfl)
  | choose decision left right args =>
      dsimp only
      obtain ⟨values, read, len⟩ := readArgs_of_bounded (env := env) (args := args)
        (fun v vmem => by rw [sized]; exact vars v (by rw [termEq]; exact vmem))
      rw [read]
      cases tape.read decision with
      | exhausted => exact .exhausted _
      | mismatch expected actual => exact .mismatch _ _
      | answered branch rest =>
          cases branch with
          | true =>
              obtain ⟨targetBlock, found, ar⟩ := resolve 0 left (by rw [termEq]; rfl)
              exact .choose targetBlock found (by rw [len, ar, termEq]; rfl)
          | false =>
              obtain ⟨targetBlock, found, ar⟩ := resolve 1 right (by rw [termEq]; rfl)
              exact .choose targetBlock found (by rw [len, ar, termEq]; rfl)
  | performCatch operation request target args onError errorArgs =>
      dsimp only
      have known : (alphabet.lookup operation).isSome = true := by
        have := ops; unfold OperationWF at this; rw [termEq] at this; exact this
      cases lookupEq : alphabet.lookup operation with
      | none => rw [lookupEq] at known; cases known
      | some op =>
        have lt : request.index < env.length := by
          rw [sized]; exact vars request (by rw [termEq]; exact List.mem_cons_self)
        rw [List.getElem?_eq_getElem lt]
        obtain ⟨values, read, len⟩ := readArgs_of_bounded (env := env) (args := args)
          (fun v vmem => by
            rw [sized]
            exact vars v (by
              rw [termEq]
              exact List.mem_cons_of_mem _ (List.mem_append_left _ vmem)))
        obtain ⟨errorValues, readError, lenError⟩ :=
          readArgs_of_bounded (env := env) (args := errorArgs)
            (fun v vmem => by
              rw [sized]
              exact vars v (by
                rw [termEq]
                exact List.mem_cons_of_mem _ (List.mem_append_right _ vmem)))
        rw [read, readError]
        obtain ⟨targetBlock, found, ar⟩ := resolve 0 target (by rw [termEq]; rfl)
        obtain ⟨errorBlock, foundError, arError⟩ := resolve 1 onError (by rw [termEq]; rfl)
        exact .performCatch targetBlock errorBlock found (by rw [len, ar, termEq]; rfl)
          foundError (by rw [lenError, arError, termEq]; rfl)
  | branch test site onTrue onFalse args =>
      dsimp only
      obtain ⟨values, read, len⟩ := readArgs_of_bounded (env := env) (args := args)
        (fun v vmem => by
          rw [sized]; exact vars v (by rw [termEq]; exact List.mem_cons_of_mem _ vmem))
      rw [read]
      obtain ⟨trueBlock, foundTrue, arTrue⟩ := resolve 0 onTrue (by rw [termEq]; rfl)
      obtain ⟨falseBlock, foundFalse, arFalse⟩ := resolve 1 onFalse (by rw [termEq]; rfl)
      cases tape.read site with
      | exhausted => exact .exhausted _
      | mismatch expected actual => exact .mismatch _ _
      | answered answer rest =>
          dsimp only
          by_cases agreed : testValue env test = some answer
          · rw [if_pos agreed]
            cases answer with
            | true => exact .choose trueBlock foundTrue (by rw [len, arTrue, termEq]; rfl)
            | false => exact .choose falseBlock foundFalse (by rw [len, arFalse, termEq]; rfl)
          · rw [if_neg agreed]
            exact .mismatch _ _

/-- The shape a checked step leaves behind: a finished run is not stuck, and a
continuation resolves to a block of the environment's size. -/
def NextSized (raw : RawFlow Ty) : Next → Prop
  | .finished result _ => result.stuck = false
  | .continue_ block env _ =>
      ∃ current, lookupBlock raw block = some current ∧ env.length = current.params.length

/-- One step of a checked flow over a state monad leaves a sized `Next`. -/
theorem step_checked {σ : Type} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) {block : RawBlock Ty} (mem : block ∈ raw.blocks)
    {env : Env} (sized : env.length = block.params.length) (tape : Tape)
    (log : Effect4.Trace.Log) (s : σ) :
    NextSized raw (((step alphabet service nameOf block env tape).run log).run s).1.1 := by
  have planned := plan_checked wf mem sized tape
  generalize planEq : plan alphabet block env tape = p at planned
  cases planned with
  | ret value =>
      simp [step, planEq, emit_run, NextSized, RunResult.stuck, StateT.run_bind, StateT.run_pure,
        idBind, idPure]
  | exhausted site =>
      simp [step, planEq, emit_run, NextSized, RunResult.stuck, StateT.run_bind, StateT.run_pure,
        idBind, idPure]
  | mismatch expected actual =>
      simp [step, planEq, NextSized, RunResult.stuck, StateT.run_bind, StateT.run_pure, idBind, idPure]
  | jump targetBlock found sizedTarget =>
      simp only [step, planEq, StateT.run_pure]
      exact ⟨targetBlock, found, sizedTarget⟩
  | perform targetBlock found sizedTarget =>
      simp only [step, planEq, StateT.run_bind, StateT.run_lift, StateT.run_pure, emit_run]
      cases service.pure _ <;> simp [NextSized, emit_run, StateT.run_bind, StateT.run_pure] <;>
        exact ⟨targetBlock, found, by simp [sizedTarget]⟩
  | choose targetBlock found sizedTarget =>
      simp only [step, planEq, StateT.run_bind, StateT.run_pure, emit_run]
      simp [NextSized]
      exact ⟨targetBlock, found, sizedTarget⟩
  | performCatch targetBlock _ found sizedTarget _ _ =>
      simp only [step, planEq, StateT.run_bind, StateT.run_lift, StateT.run_pure, emit_run]
      cases service.pure _ <;> simp [NextSized, emit_run, StateT.run_bind, StateT.run_pure] <;>
        exact ⟨targetBlock, found, by simp [sizedTarget]⟩

/-- Admission makes `stuck` unreachable for every fuel. -/
theorem loop_checked_not_stuck {σ : Type} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ)
      (current : RawBlock Ty), lookupBlock raw block = some current →
      env.length = current.params.length →
      (((loop alphabet raw service nameOf fuel block env tape).run log).run s).1.1.1.stuck = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape log s current _ _
      simp [loop, emit_run, RunResult.stuck, StateT.run_bind, StateT.run_pure, idBind, idPure]
  | succ fuel ih =>
      intro block env tape log s current found sized
      have mem : current ∈ raw.blocks := List.mem_of_find?_eq_some found
      have stepped := step_checked wf service nameOf mem sized tape log s
      simp only [loop, found, StateT.run_bind]
      generalize ((step alphabet service nameOf current env tape).run log).run s = outcome at stepped ⊢
      rcases outcome with ⟨⟨next, log'⟩, s'⟩
      cases next with
      | finished result rest =>
          simpa [idBind, idPure, NextSized, StateT.run_pure] using stepped
      | continue_ next env' rest =>
          obtain ⟨target, foundTarget, sizedTarget⟩ := stepped
          simpa [idBind] using ih next env' rest log' s' target foundTarget sizedTarget

/-- The public form of `loop_checked_not_stuck`: a checked run never reports
`stuck`. -/
theorem run_checked_not_stuck {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val)
    (log : Effect4.Trace.Log) (s : σ) :
    (((run fuel flow service nameOf tape input).run log).run s).1.1.stuck = false := by
  have wf := erase_wf flow
  have entry := wf.entry
  unfold EntryWF at entry
  cases found : lookupBlock flow.erase flow.erase.entry with
  | none => rw [found] at entry; cases entry
  | some current =>
      rw [found] at entry
      have sized : ([input] : Env).length = current.params.length := by rw [entry]; rfl
      have := loop_checked_not_stuck wf service nameOf fuel flow.erase.entry [input] tape log s
        current found sized
      unfold run runTape
      simpa [StateT.run_map, idMap] using this

/-- More fuel changes nothing about a run that did not exhaust its fuel. -/
theorem loop_fuel_mono {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ),
      (((loop alphabet raw service nameOf fuel block env tape).run log).run s).1.1.1.exhausted = false →
      ((loop alphabet raw service nameOf (fuel + 1) block env tape).run log).run s =
        ((loop alphabet raw service nameOf fuel block env tape).run log).run s := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape log s finished
      simp [loop, emit_run, RunResult.exhausted, StateT.run_bind, StateT.run_pure, idBind, idPure]
        at finished
  | succ fuel ih =>
      intro block env tape log s finished
      cases found : lookupBlock raw block with
      | none => simp [loop, found]
      | some current =>
          simp only [loop, found, StateT.run_bind] at finished ⊢
          generalize ((step alphabet service nameOf current env tape).run log).run s = outcome at finished ⊢
          rcases outcome with ⟨⟨next, log'⟩, s'⟩
          cases next with
          | finished result rest => rfl
          | continue_ next env' rest =>
              simp only [idBind] at finished ⊢
              exact ih next env' rest log' s' finished

theorem run_fuel_mono {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val)
    (log : Effect4.Trace.Log) (s : σ)
    (finished : (((run fuel flow service nameOf tape input).run log).run s).1.1.exhausted = false) :
    ((run (fuel + 1) flow service nameOf tape input).run log).run s =
      ((run fuel flow service nameOf tape input).run log).run s := by
  unfold run runTape at finished ⊢
  simp only [StateT.run_map, idMap] at finished
  simp only [StateT.run_map, idMap]
  rw [loop_fuel_mono alphabet flow.erase service nameOf fuel flow.erase.entry [input] tape log s
    (by simpa using finished)]

end Effect4.Flow
