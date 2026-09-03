import Effect4.Semantics.Runs
import Effect4.Semantics.Fuel
import Effect4.Flow.Region

/-!
# Semantics.Approximation

Owner: coherent finite approximations and colimits (DB-04).

A bounded run is an *approximation*, not a denotation. This module gives the
order in which one approximation refines another, proves that spending more
fuel climbs that order, and assembles the increasing chain of approximations
into its colimit.

The raw result of a bounded run is the pair `RunResult × Log`. Two of its bits
are not observations:

* the trailing `frontier` event a fuel-exhausted run logs is punctuation, and
* the `BlockId` inside `Frontier.fuel` is a resumption pointer.

`observe` drops both. Keeping the block id would break monotonicity: a flow
whose blocks jump in a cycle emits nothing, so fuel `n` and fuel `n + 1`
observe the same (empty) log while stopping at different blocks, and neither
raw pair could then be below the other. `Effect4Test/Semantics/ApproximationContract.lean`
carries that counterexample as an executable receipt, which is why `obsLe` is
antisymmetric only up to `observe` (`obsLe_antisymm`), and genuinely
antisymmetric on settled pairs (`obsLe_antisymm_terminal`).

What remains is a decidable partial order on `Observation`: `Observation.le`,
with `le_refl`, `le_trans`, `le_antisymm`. A live fuel frontier is below every
observation whose log extends its own; `done`, `failed`, `refused`,
`frontier (unansweredDecision _)` and `frontier (stuck _)` are maximal
(`terminal_maximal`).

The three DB-04 laws, for the plain runner (`loop`, `run`) and for the region
runner (`regionLoop`, `runRegions`) alike:

* monotonicity — `loop_obs_mono`, `run_obs_mono`, `region_obs_mono`,
  `runRegions_obs_mono`, with the chain forms `loop_obs_chain`,
  `run_obs_chain`, `region_obs_chain`. This strengthens `loop_fuel_mono`,
  which covers only a run that did not exhaust its fuel, to every run;
* compatibility — `Chain.stable`, `loop_fuel_stable` (the raw form: value,
  tape, log and state all unchanged), `run_obs_stable`,
  `runRegions_obs_stable`. A completing observation cannot later become an
  unrelated failure, and a live leaf is only ever refined;
* coherence — `Chain.colimit`: if the run settles below the bound then the
  least such fuel exists (`Chain.colimit_below`: every smaller fuel is a live
  fuel frontier whose log is a prefix of the colimit's), the colimit does not
  depend on the bound (`Chain.colimit_bound_mono`) nor on which settled fuel
  found it (`Chain.colimit_eq_of_settled`).

For an admitted plain flow the search is unnecessary: `run_fuelFor_finishes`
(`Effect4/Semantics/Fuel.lean`) proves that `fuelFor` suffices, so
`runColimitDefault` is a total `Observation`, `runColimitDefault_settled`
proves it settled, and `runColimit_eq_default` says the searched colimit
agrees with it. This is the "colimit is a partial function" statement of
DB-03/DB-04 for the deterministic fragment: with the tape fixed, the run is a
function of it. The region runner has its own allotment,
`regionFuelFor flow tape = fuelFor flow.erase tape`, and
`runRegions_fuelFor_finishes` proves it suffices, so
`runRegionsColimitDefault` is total as well; the searched `runRegionsColimit`
agrees with it above that fuel (`runRegionsColimit_eq_default`).

Nothing here claims a denotation for an unbounded or open program. The colimit
is taken over one fixed tape, one service, and one starting state; a run whose
tape runs out is settled at the unanswered frontier, which is a live frontier
of the *tape*, not of the fuel (`Effect4/Semantics/Fuel.lean`,
`run_fuelFor_answered`).
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val Outcome)

/-! ## Log prefixes

The order's only content is "one log extends another", so the prefix test is
decidable by construction. -/

/-- `logPrefix a b` decides whether the log `a` is an initial segment of `b`. -/
def logPrefix : Effect4.Trace.Log → Effect4.Trace.Log → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => decide (a = b) && logPrefix as bs

theorem logPrefix_append (a b : Effect4.Trace.Log) : logPrefix a (a ++ b) = true := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [logPrefix, ih]

theorem logPrefix_refl (a : Effect4.Trace.Log) : logPrefix a a = true := by
  simpa using logPrefix_append a []

theorem logPrefix_dest {a b : Effect4.Trace.Log} (h : logPrefix a b = true) :
    ∃ c, b = a ++ c := by
  induction a generalizing b with
  | nil => exact ⟨b, rfl⟩
  | cons x xs ih =>
    cases b with
    | nil => simp [logPrefix] at h
    | cons y ys =>
      simp only [logPrefix, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨rfl, tail⟩ := h
      obtain ⟨c, rfl⟩ := ih tail
      exact ⟨c, rfl⟩

theorem logPrefix_trans {a b c : Effect4.Trace.Log} (ab : logPrefix a b = true)
    (bc : logPrefix b c = true) : logPrefix a c = true := by
  obtain ⟨u, rfl⟩ := logPrefix_dest ab
  obtain ⟨v, rfl⟩ := logPrefix_dest bc
  simpa [List.append_assoc] using logPrefix_append a (u ++ v)

theorem logPrefix_antisymm {a b : Effect4.Trace.Log} (ab : logPrefix a b = true)
    (ba : logPrefix b a = true) : a = b := by
  obtain ⟨u, rfl⟩ := logPrefix_dest ab
  obtain ⟨v, hv⟩ := logPrefix_dest ba
  have len := congrArg List.length hv
  simp only [List.length_append] at len
  have : u = [] := by
    cases u with
    | nil => rfl
    | cons _ _ => simp only [List.length_cons] at len; omega
  simp [this]

/-! ## The observation of a bounded run -/

/-- Drop the trailing `frontier` event a fuel-exhausted run logs. The marker
says "this log is not finished"; the observation says it by being `live`. -/
def stripFrontier : Effect4.Trace.Log → Effect4.Trace.Log
  | [] => []
  | event :: rest =>
      match rest with
      | [] =>
        match event with
        | .frontier => []
        | _ => [event]
      | _ :: _ => event :: stripFrontier rest

theorem stripFrontier_concat (log : Effect4.Trace.Log) :
    stripFrontier (log ++ [Effects.Trace.Event.frontier]) = log := by
  induction log with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simpa [stripFrontier] using ih

/-- What a bounded run observed. A `live` observation may still be refined by
more fuel; a `terminal` one may not. -/
inductive Observation where
  /-- The fuel ran out: the log observed so far, without the marker. -/
  | live (log : Effect4.Trace.Log)
  /-- The run reached an outcome, an unanswered decision, a refusal, or a
  stuck block: nothing more can be observed. -/
  | terminal (result : RunResult) (log : Effect4.Trace.Log)
deriving DecidableEq, Repr

namespace Observation

/-- The log an observation exposes. -/
def log : Observation → Effect4.Trace.Log
  | .live l => l
  | .terminal _ l => l

/-- Whether more fuel may still refine this observation. -/
def isLive : Observation → Bool
  | .live _ => true
  | .terminal _ _ => false

/-- Whether this observation is final. -/
def settled (o : Observation) : Bool := !o.isLive

/-- The observation order: a live frontier is below every observation whose
log extends its own; a terminal observation is below only itself. -/
def le : Observation → Observation → Bool
  | .live l, other => logPrefix l other.log
  | .terminal result l, other => decide (other = .terminal result l)

theorem le_refl (o : Observation) : le o o = true := by
  cases o with
  | live l => simpa [le, log] using logPrefix_refl l
  | terminal result l => simp [le]

theorem le_trans {a b c : Observation} (ab : le a b = true) (bc : le b c = true) :
    le a c = true := by
  cases a with
  | live l =>
    cases b with
    | live l' =>
      simp only [le, log] at ab bc ⊢
      exact logPrefix_trans ab bc
    | terminal result l' =>
      simp only [le, decide_eq_true_eq] at bc
      subst bc
      simpa [le, log] using ab
  | terminal result l =>
    simp only [le, decide_eq_true_eq] at ab
    subst ab
    exact bc

theorem le_antisymm {a b : Observation} (ab : le a b = true) (ba : le b a = true) : a = b := by
  cases a with
  | live l =>
    cases b with
    | live l' =>
      simp only [le, log] at ab ba
      simpa using logPrefix_antisymm ab ba
    | terminal result l' => simp only [le, decide_eq_true_eq] at ba; exact ba
  | terminal result l =>
    simp only [le, decide_eq_true_eq] at ab
    exact ab.symm

/-- A settled observation is a terminal one. -/
theorem settled_terminal {o : Observation} (h : o.settled = true) :
    ∃ result l, o = .terminal result l := by
  cases o with
  | live l => simp [Observation.settled, Observation.isLive] at h
  | terminal result l => exact ⟨result, l, rfl⟩

/-- A terminal observation is maximal: nothing lies strictly above it. -/
theorem terminal_maximal {result : RunResult} {l : Effect4.Trace.Log} {o : Observation}
    (h : le (.terminal result l) o = true) : o = .terminal result l := by
  simpa [le] using h

/-- A live observation is below exactly the observations whose logs extend it. -/
theorem live_le_iff {l : Effect4.Trace.Log} {o : Observation} :
    le (.live l) o = logPrefix l o.log := rfl

end Observation

/-- The observation carried by a finished run: the fuel frontier's marker and
resumption block are dropped, everything else is terminal. -/
def observe (result : RunResult) (log : Effect4.Trace.Log) : Observation :=
  match result with
  | .frontier (.fuel _) => .live (stripFrontier log)
  | _ => .terminal result log

theorem observe_settled (result : RunResult) (log : Effect4.Trace.Log) :
    (observe result log).settled = !result.exhausted := by
  cases result with
  | done value => rfl
  | failed error => rfl
  | refusedSite expected actual => rfl
  | refusedValue site => rfl
  | frontier reason => cases reason <;> rfl

theorem observe_terminal {result : RunResult} (log : Effect4.Trace.Log)
    (h : result.exhausted = false) : observe result log = .terminal result log := by
  cases result with
  | done value => rfl
  | failed error => rfl
  | refusedSite expected actual => rfl
  | refusedValue site => rfl
  | frontier reason =>
    cases reason with
    | fuel block => simp [RunResult.exhausted] at h
    | unansweredDecision site => rfl
    | stuck block => rfl

theorem observe_fuel (block : BlockId) (log : Effect4.Trace.Log) :
    observe (.frontier (.fuel block)) (log ++ [Effects.Trace.Event.frontier]) =
      .live log := by
  simp [observe, stripFrontier_concat]

/-- The observation order on the runner's raw result pair. It is a preorder on
pairs and a partial order on the observations they induce: two fuel frontiers
that logged the same events but stopped at different blocks lie below each
other, because the block is not observed. -/
def obsLe (a b : RunResult × Effect4.Trace.Log) : Bool :=
  Observation.le (observe a.1 a.2) (observe b.1 b.2)

theorem obsLe_refl (a : RunResult × Effect4.Trace.Log) : obsLe a a = true :=
  Observation.le_refl _

theorem obsLe_trans {a b c : RunResult × Effect4.Trace.Log} (ab : obsLe a b = true)
    (bc : obsLe b c = true) : obsLe a c = true :=
  Observation.le_trans ab bc

theorem obsLe_antisymm {a b : RunResult × Effect4.Trace.Log} (ab : obsLe a b = true)
    (ba : obsLe b a = true) : observe a.1 a.2 = observe b.1 b.2 :=
  Observation.le_antisymm ab ba

/-- On a terminal pair the order is genuinely antisymmetric. -/
theorem obsLe_antisymm_terminal {a b : RunResult × Effect4.Trace.Log}
    (terminal : a.1.exhausted = false) (ab : obsLe a b = true) (ba : obsLe b a = true) :
    a = b := by
  have eq := obsLe_antisymm ab ba
  rw [observe_terminal a.2 terminal] at eq
  have := (Observation.terminal_maximal (o := observe b.1 b.2) (by rw [← eq]; exact Observation.le_refl _))
  cases a with
  | mk ra la =>
    cases b with
    | mk rb lb =>
      simp only at eq this
      cases rb with
      | done value => simp [observe] at this; simp [this.1, this.2]
      | failed error => simp [observe] at this; simp [this.1, this.2]
      | refusedSite expected actual => simp [observe] at this; simp [this.1, this.2]
      | refusedValue site => simp [observe] at this; simp [this.1, this.2]
      | frontier reason =>
        cases reason with
        | fuel block => simp [observe] at this
        | unansweredDecision site => simp [observe] at this; simp [this.1, this.2]
        | stuck block => simp [observe] at this; simp [this.1, this.2]

/-! ## The step and the loop extend the log -/

private theorem idBind {α β : Type} (x : Id α) (f : α → Id β) : x >>= f = f x := rfl
private theorem idMap {α β : Type} (x : Id α) (f : α → β) : f <$> x = f x := rfl
private theorem idPure {α : Type} (a : α) : (pure a : Id α) = a := rfl

/-- One step only appends to the log. -/
theorem step_log_extends {σ : Type} (alphabet : FlowAlphabet Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (block : RawBlock Ty) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ) :
    ∃ events,
      ((((step alphabet service nameOf block env tape).run log).run s)).1.2 = log ++ events := by
  generalize planEq : plan alphabet block env tape = p
  cases p with
  | stuck =>
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      simp only [step, planEq]
      rfl
  | ret value =>
      refine ⟨[.done (.success value)], ?_⟩
      simp only [step, planEq]
      rfl
  | jump target env' =>
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      simp only [step, planEq]
      rfl
  | perform op request target env' =>
      cases pureOp : service.pure op with
      | true =>
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          simp only [step, planEq, pureOp]
          rfl
      | false =>
          refine ⟨[.op (nameOf op) request,
            .answer (nameOf op) (((service.handle op request).run s).1)], ?_⟩
          simp only [step, planEq, pureOp, Bool.false_eq_true, if_false]
          show (log ++ [Effects.Trace.Event.op (nameOf op) request] ++
            [Effects.Trace.Event.answer (nameOf op) (((service.handle op request).run s).1)]) = _
          simp
  | exhausted site =>
      refine ⟨[.frontier], ?_⟩
      simp only [step, planEq]
      rfl
  | mismatch expected actual =>
      refine ⟨[], ?_⟩
      rw [List.append_nil]
      simp only [step, planEq]
      rfl
  | choose site branch target env' rest =>
      refine ⟨[.decide site.value branch], ?_⟩
      simp only [step, planEq]
      rfl
  | performCatch op request target env' onError errorEnv =>
      cases pureOp : service.pure op with
      | true =>
          refine ⟨[], ?_⟩
          rw [List.append_nil]
          simp only [step, planEq, pureOp]
          rfl
      | false =>
          refine ⟨[.op (nameOf op) request,
            .answer (nameOf op) (((service.handle op request).run s).1)], ?_⟩
          simp only [step, planEq, pureOp, Bool.false_eq_true, if_false]
          show (log ++ [Effects.Trace.Event.op (nameOf op) request] ++
            [Effects.Trace.Event.answer (nameOf op) (((service.handle op request).run s).1)]) = _
          simp

/-- A step never reports fuel exhaustion: only `loop` spends fuel. -/
theorem step_finished_not_exhausted {σ : Type} (alphabet : FlowAlphabet Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (block : RawBlock Ty) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ)
    {result : RunResult} {rest : Tape}
    (finished : ((((step alphabet service nameOf block env tape).run log).run s)).1.1 =
      .finished result rest) : result.exhausted = false := by
  generalize planEq : plan alphabet block env tape = p at finished
  cases p with
  | stuck =>
      simp only [step, planEq] at finished
      have h : Next.finished (RunResult.frontier (Frontier.stuck block.id)) tape =
          Next.finished result rest := finished
      injection h with h1 _
      rw [← h1]
      rfl
  | ret value =>
      simp only [step, planEq] at finished
      have h : Next.finished (RunResult.done value) tape = Next.finished result rest := finished
      injection h with h1 _
      rw [← h1]
      rfl
  | jump target env' =>
      simp only [step, planEq] at finished
      exact Next.noConfusion
        (show Next.continue_ target env' tape = Next.finished result rest from finished)
  | perform op request target env' =>
      cases pureOp : service.pure op with
      | true =>
          simp only [step, planEq, pureOp] at finished
          exact Next.noConfusion
            (show Next.continue_ target
                (env' ++ [(((service.handle op request).run s)).1]) tape =
              Next.finished result rest from finished)
      | false =>
          simp only [step, planEq, pureOp, Bool.false_eq_true, if_false] at finished
          exact Next.noConfusion
            (show Next.continue_ target
                (env' ++ [(((service.handle op request).run s)).1]) tape =
              Next.finished result rest from finished)
  | exhausted site =>
      simp only [step, planEq] at finished
      have h : Next.finished (RunResult.frontier (Frontier.unansweredDecision site)) tape =
          Next.finished result rest := finished
      injection h with h1 _
      rw [← h1]
      rfl
  | mismatch expected actual =>
      simp only [step, planEq] at finished
      have h : Next.finished (RunResult.refusal expected actual) tape =
          Next.finished result rest := finished
      injection h with h1 _
      rw [← h1]
      simp
  | choose site branch target env' rest' =>
      simp only [step, planEq] at finished
      exact Next.noConfusion
        (show Next.continue_ target env' rest' = Next.finished result rest from finished)
  | performCatch op request target env' onError errorEnv =>
      cases pureOp : service.pure op with
      | true =>
          simp only [step, planEq, pureOp] at finished
          exact Next.noConfusion
            (show Next.continue_ target
                (env' ++ [(((service.handle op request).run s)).1]) tape =
              Next.finished result rest from finished)
      | false =>
          simp only [step, planEq, pureOp, Bool.false_eq_true, if_false] at finished
          exact Next.noConfusion
            (show Next.continue_ target
                (env' ++ [(((service.handle op request).run s)).1]) tape =
              Next.finished result rest from finished)

/-! ## The observation of a fuelled run -/

/-- The full result of a fuelled loop over `StateT σ Id`. -/
def loopOut {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ) :
    ((RunResult × Tape) × Effect4.Trace.Log) × σ :=
  ((loop alphabet raw service nameOf fuel block env tape).run log).run s

/-- The observation a fuelled loop makes. -/
def loopObservation {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ) :
    Observation :=
  let out := loopOut alphabet raw service nameOf fuel block env tape log s
  observe out.1.1.1 out.1.2

theorem loopObservation_zero {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ) :
    loopObservation alphabet raw service nameOf 0 block env tape log s = .live log := by
  simp [loopObservation, loopOut, loop, emit_run, StateT.run_pure, idPure, observe,
    stripFrontier_concat]

/-- A block that does not resolve is a terminal `stuck` observation. -/
theorem loopObservation_succ_none {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) {block : BlockId} (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ)
    (found : lookupBlock raw block = none) :
    loopObservation alphabet raw service nameOf (fuel + 1) block env tape log s =
      .terminal (.frontier (.stuck block)) log := by
  simp only [loopObservation, loopOut, loop, found]
  rfl

/-- Every observation extends the log the run started from. -/
theorem loopObservation_extends {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ),
      logPrefix log (loopObservation alphabet raw service nameOf fuel block env tape log s).log
        = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape log s
      rw [loopObservation_zero]
      exact logPrefix_refl log
  | succ fuel ih =>
      intro block env tape log s
      cases found : lookupBlock raw block with
      | none =>
          rw [loopObservation_succ_none alphabet raw service nameOf fuel env tape log s found]
          exact logPrefix_refl log
      | some current =>
          obtain ⟨events, logEq⟩ :=
            step_log_extends alphabet service nameOf current env tape log s
          have notExhausted : ∀ (result : RunResult) (rest : Tape),
              (((step alphabet service nameOf current env tape).run log).run s).1.1 =
                Next.finished result rest → result.exhausted = false :=
            fun result rest h =>
              step_finished_not_exhausted alphabet service nameOf current env tape log s h
          simp only [loopObservation, loopOut, loop, found, StateT.run_bind]
          revert logEq notExhausted
          generalize ((step alphabet service nameOf current env tape).run log).run s = outcome
          rcases outcome with ⟨⟨next, log'⟩, s'⟩
          intro logEq notExhausted
          simp only at logEq
          cases next with
          | finished result rest =>
              have := notExhausted result rest rfl
              show logPrefix log (observe result log').log = true
              rw [observe_terminal log' this]
              simp only [Observation.log]
              rw [logEq]
              exact logPrefix_append log events
          | continue_ next env' rest =>
              simp only [idBind]
              refine logPrefix_trans (b := log') ?_ (ih next env' rest log' s')
              rw [logEq]
              exact logPrefix_append log events

/-! ## Monotonicity: more fuel climbs the order -/

/-- More fuel yields an observation above the smaller fuel's. This is the
DB-04 monotonicity law, and it strengthens `loop_fuel_mono` — which only
covers a run that did not exhaust its fuel — to every run. -/
theorem loop_obs_mono {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel k : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ),
      Observation.le (loopObservation alphabet raw service nameOf fuel block env tape log s)
        (loopObservation alphabet raw service nameOf (fuel + k) block env tape log s) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro k block env tape log s
      rw [Nat.zero_add, loopObservation_zero, Observation.live_le_iff]
      exact loopObservation_extends alphabet raw service nameOf k block env tape log s
  | succ fuel ih =>
      intro k block env tape log s
      rw [Nat.add_right_comm fuel 1 k]
      cases found : lookupBlock raw block with
      | none =>
          rw [loopObservation_succ_none alphabet raw service nameOf fuel env tape log s found,
            loopObservation_succ_none alphabet raw service nameOf (fuel + k) env tape log s found]
          exact Observation.le_refl _
      | some current =>
          simp only [loopObservation, loopOut, loop, found, StateT.run_bind]
          generalize ((step alphabet service nameOf current env tape).run log).run s = outcome
          rcases outcome with ⟨⟨next, log'⟩, s'⟩
          cases next with
          | finished result rest =>
              simp only [idBind, StateT.run_pure]
              exact Observation.le_refl _
          | continue_ next env' rest =>
              simp only [idBind]
              exact ih k next env' rest log' s'

/-- The chain form: observations along increasing fuel form a chain. -/
theorem loop_obs_chain {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    {i j : Nat} (le : i ≤ j) (block : BlockId) (env : Env) (tape : Tape)
    (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (loopObservation alphabet raw service nameOf i block env tape log s)
      (loopObservation alphabet raw service nameOf j block env tape log s) = true := by
  obtain ⟨k, rfl⟩ := Nat.le.dest le
  exact loop_obs_mono alphabet raw service nameOf i k block env tape log s

/-! ## Compatibility: a terminal observation is stable -/

/-- A run that did not exhaust its fuel gives exactly the same result — value,
tape, log and state — for every larger fuel. -/
theorem loop_fuel_stable {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) :
    ∀ (k : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ),
      (loopOut alphabet raw service nameOf fuel block env tape log s).1.1.1.exhausted = false →
      loopOut alphabet raw service nameOf (fuel + k) block env tape log s =
        loopOut alphabet raw service nameOf fuel block env tape log s := by
  intro k
  induction k with
  | zero => intro block env tape log s _; rfl
  | succ k ih =>
      intro block env tape log s settled
      have step := ih block env tape log s settled
      have settled' :
          (loopOut alphabet raw service nameOf (fuel + k) block env tape log s).1.1.1.exhausted
            = false := by rw [step]; exact settled
      have := loop_fuel_mono alphabet raw service nameOf (fuel + k) block env tape log s settled'
      show loopOut alphabet raw service nameOf (fuel + k + 1) block env tape log s = _
      unfold loopOut at this step ⊢
      rw [this, step]

/-- The same, as a statement about observations: a settled observation is the
observation of every larger fuel. A completing observation therefore cannot
later become an unrelated failure. -/
theorem loopObservation_stable {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel k : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ)
    (settled : (loopObservation alphabet raw service nameOf fuel block env tape log s).settled
      = true) :
    loopObservation alphabet raw service nameOf (fuel + k) block env tape log s =
      loopObservation alphabet raw service nameOf fuel block env tape log s := by
  have notExhausted :
      (loopOut alphabet raw service nameOf fuel block env tape log s).1.1.1.exhausted = false := by
    have := observe_settled
      (loopOut alphabet raw service nameOf fuel block env tape log s).1.1.1
      (loopOut alphabet raw service nameOf fuel block env tape log s).1.2
    simp only [loopObservation] at settled
    rw [settled] at this
    simpa using this.symm
  simp only [loopObservation]
  rw [loop_fuel_stable alphabet raw service nameOf fuel k block env tape log s notExhausted]

/-! ## Coherence: the least settling fuel, and the colimit -/

/-- The least `f ≤ bound` at which `p` holds, by downward recursion on the
bound. -/
def leastUpTo (p : Nat → Bool) : Nat → Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 =>
    match leastUpTo p n with
    | some f => some f
    | none => if p (n + 1) then some (n + 1) else none

theorem leastUpTo_none {p : Nat → Bool} :
    ∀ {n : Nat}, leastUpTo p n = none → ∀ g, g ≤ n → p g = false := by
  intro n
  induction n with
  | zero =>
      intro h g le
      have : g = 0 := Nat.le_zero.mp le
      subst this
      by_cases hp : p 0
      · simp [leastUpTo, hp] at h
      · simpa using hp
  | succ n ih =>
      intro h g le
      cases inner : leastUpTo p n with
      | some f => rw [leastUpTo, inner] at h; cases h
      | none =>
          rw [leastUpTo, inner] at h
          by_cases hp : p (n + 1)
          · simp [hp] at h
          · rcases Nat.lt_or_ge g (n + 1) with lt | ge
            · exact ih inner g (Nat.le_of_lt_succ lt)
            · have : g = n + 1 := Nat.le_antisymm le ge
              subst this
              simpa using hp

theorem leastUpTo_sound {p : Nat → Bool} :
    ∀ {n f : Nat}, leastUpTo p n = some f → p f = true := by
  intro n
  induction n with
  | zero =>
      intro f h
      by_cases hp : p 0
      · simp [leastUpTo, hp] at h; subst h; exact hp
      · simp [leastUpTo, hp] at h
  | succ n ih =>
      intro f h
      cases inner : leastUpTo p n with
      | some f' => rw [leastUpTo, inner] at h; cases h; exact ih inner
      | none =>
          rw [leastUpTo, inner] at h
          by_cases hp : p (n + 1)
          · simp [hp] at h; subst h; exact hp
          · simp [hp] at h

theorem leastUpTo_le {p : Nat → Bool} :
    ∀ {n f : Nat}, leastUpTo p n = some f → f ≤ n := by
  intro n
  induction n with
  | zero =>
      intro f h
      by_cases hp : p 0
      · simp [leastUpTo, hp] at h; omega
      · simp [leastUpTo, hp] at h
  | succ n ih =>
      intro f h
      cases inner : leastUpTo p n with
      | some f' =>
          rw [leastUpTo, inner] at h
          cases h
          exact Nat.le_succ_of_le (ih inner)
      | none =>
          rw [leastUpTo, inner] at h
          by_cases hp : p (n + 1)
          · simp [hp] at h; omega
          · simp [hp] at h

theorem leastUpTo_least {p : Nat → Bool} :
    ∀ {n f : Nat}, leastUpTo p n = some f → ∀ g, g < f → p g = false := by
  intro n
  induction n with
  | zero =>
      intro f h g lt
      by_cases hp : p 0
      · simp [leastUpTo, hp] at h; omega
      · simp [leastUpTo, hp] at h
  | succ n ih =>
      intro f h g lt
      cases inner : leastUpTo p n with
      | some f' => rw [leastUpTo, inner] at h; cases h; exact ih inner g lt
      | none =>
          rw [leastUpTo, inner] at h
          by_cases hp : p (n + 1)
          · simp [hp] at h
            subst h
            exact leastUpTo_none inner g (Nat.le_of_lt_succ lt)
          · simp [hp] at h

theorem leastUpTo_isSome {p : Nat → Bool} {n g : Nat} (holds : p g = true) (le : g ≤ n) :
    (leastUpTo p n).isSome = true := by
  cases h : leastUpTo p n with
  | some f => rfl
  | none => rw [leastUpTo_none h g le] at holds; cases holds

/-- The least fuel found below a larger bound is the same. -/
theorem leastUpTo_bound_mono {p : Nat → Bool} {n f : Nat} (found : leastUpTo p n = some f) :
    ∀ {m : Nat}, n ≤ m → leastUpTo p m = some f := by
  intro m
  induction m with
  | zero => intro le; rw [Nat.le_zero.mp le] at found; exact found
  | succ m ih =>
      intro le
      rcases Nat.lt_or_ge n (m + 1) with lt | ge
      · have inner := ih (Nat.le_of_lt_succ lt)
        rw [leastUpTo, inner]
      · have : n = m + 1 := Nat.le_antisymm le ge
        subst this
        exact found

/-! ### Chains of observations

Everything above the order is shared by both runners, so the colimit is stated
once, of an arbitrary fuel-indexed chain. -/

/-- A fuel-indexed chain of observations: what a bounded runner observes at
each fuel, carrying its own monotonicity proof. -/
structure Chain where
  /-- the observation at each fuel -/
  observation : Nat → Observation
  /-- more fuel climbs the order -/
  mono : ∀ {i j : Nat}, i ≤ j → Observation.le (observation i) (observation j) = true

namespace Chain

/-- A settled observation is the observation of every larger fuel. This is
DB-04's compatibility law -- a completing observation cannot later become an
unrelated failure -- and it follows from monotonicity alone, because a terminal
observation is maximal. -/
theorem stable (c : Chain) {fuel larger : Nat} (settled : (c.observation fuel).settled = true)
    (le : fuel ≤ larger) : c.observation larger = c.observation fuel := by
  obtain ⟨result, l, eq⟩ := Observation.settled_terminal settled
  have climbs := c.mono le
  rw [eq] at climbs ⊢
  exact Observation.terminal_maximal climbs

/-- The least fuel at which the chain settles, searched below `bound`. -/
def settledFuel (c : Chain) (bound : Nat) : Option Nat :=
  leastUpTo (fun fuel => (c.observation fuel).settled) bound

/-- The colimit of the chain below a bound: the settled observation the chain
reaches, if it reaches one. It is a partial function -- `none` records "not
settled below this bound", never divergence. -/
def colimit (c : Chain) (bound : Nat) : Option Observation :=
  (c.settledFuel bound).map c.observation

theorem colimit_settled {c : Chain} {bound : Nat} {o : Observation}
    (found : c.colimit bound = some o) : o.settled = true := by
  simp only [colimit, Option.map_eq_some_iff] at found
  obtain ⟨fuel, least, rfl⟩ := found
  exact leastUpTo_sound least

/-- Every fuel below the least settling one is a live approximation whose log
is a prefix of the colimit's log. -/
theorem colimit_below {c : Chain} {bound fuel : Nat} (least : c.settledFuel bound = some fuel)
    (g : Nat) (lt : g < fuel) :
    (c.observation g).isLive = true ∧
      logPrefix (c.observation g).log (c.observation fuel).log = true := by
  have live := leastUpTo_least least g lt
  refine ⟨by simpa [Observation.settled] using live, ?_⟩
  have climbs := c.mono (Nat.le_of_lt lt)
  cases smaller : c.observation g with
  | live l =>
      rw [smaller] at climbs
      simpa [Observation.live_le_iff, Observation.log] using climbs
  | terminal result l =>
      rw [smaller] at live
      simp [Observation.settled, Observation.isLive] at live

/-- The colimit is stable above the least settling fuel. -/
theorem colimit_above {c : Chain} {bound fuel : Nat} (least : c.settledFuel bound = some fuel)
    {larger : Nat} (le : fuel ≤ larger) : c.observation larger = c.observation fuel :=
  c.stable (leastUpTo_sound least) le

/-- The colimit does not depend on the bound: raising the bound cannot change
a colimit that already exists. -/
theorem colimit_bound_mono {c : Chain} {bound bound' : Nat} {o : Observation}
    (found : c.colimit bound = some o) (le : bound ≤ bound') : c.colimit bound' = some o := by
  simp only [colimit, Option.map_eq_some_iff] at found ⊢
  obtain ⟨fuel, least, rfl⟩ := found
  exact ⟨fuel, leastUpTo_bound_mono least le, rfl⟩

/-- If the chain settles at any fuel below the bound, the colimit exists. -/
theorem colimit_of_settles {c : Chain} {bound fuel : Nat}
    (settled : (c.observation fuel).settled = true) (le : fuel ≤ bound) :
    (c.colimit bound).isSome = true := by
  simp only [colimit, settledFuel, Option.isSome_map]
  exact leastUpTo_isSome settled le

/-- Any settled fuel below the bound identifies the colimit: the search finds
the least one, and stability makes its observation that settled one. The
colimit is therefore a function of the chain, not of how it was searched. -/
theorem colimit_eq_of_settled {c : Chain} {bound fuel : Nat}
    (settled : (c.observation fuel).settled = true) (le : fuel ≤ bound) :
    c.colimit bound = some (c.observation fuel) := by
  have isSome := colimit_of_settles settled le
  cases found : c.settledFuel bound with
  | none => simp only [colimit, found, Option.map_none] at isSome; cases isSome
  | some f =>
      have fle : f ≤ fuel := by
        rcases Nat.lt_or_ge fuel f with lt | ge
        · have := leastUpTo_least (p := fun fuel => (c.observation fuel).settled) found fuel lt
          rw [settled] at this
          cases this
        · exact ge
      simp only [colimit, found, Option.map_some]
      rw [colimit_above found fle]

end Chain

/-- The plain loop's chain of finite approximations. -/
def loopChain {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ) : Chain where
  observation fuel := loopObservation alphabet raw service nameOf fuel block env tape log s
  mono le := loop_obs_chain alphabet raw service nameOf le block env tape log s

/-! ## The same laws for `run` -/

/-- The full result of a fuelled run over `StateT σ Id`. -/
def runOut {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat) (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Effects.Trace.Val) (log : Effect4.Trace.Log) (s : σ) :
    (RunResult × Effect4.Trace.Log) × σ :=
  ((run fuel flow service nameOf tape input).run log).run s

/-- The observation a fuelled run makes. -/
def runObservation {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) : Observation :=
  let out := runOut fuel flow service nameOf tape input log s
  observe out.1.1 out.1.2

theorem runObservation_eq {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) :
    runObservation fuel flow service nameOf tape input log s =
      loopObservation alphabet flow.erase service nameOf fuel flow.erase.entry [input] tape log s := by
  simp [runObservation, runOut, loopObservation, loopOut, run, runTape, StateT.run_map, idMap]

/-- Monotonicity for the public runner. -/
theorem run_obs_mono {σ : Type} {alphabet : FlowAlphabet Ty} (fuel k : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (runObservation fuel flow service nameOf tape input log s)
      (runObservation (fuel + k) flow service nameOf tape input log s) = true := by
  rw [runObservation_eq, runObservation_eq]
  exact loop_obs_mono alphabet flow.erase service nameOf fuel k flow.erase.entry [input] tape log s

/-- The chain form for the public runner. -/
theorem run_obs_chain {σ : Type} {alphabet : FlowAlphabet Ty} {i j : Nat} (le : i ≤ j)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (runObservation i flow service nameOf tape input log s)
      (runObservation j flow service nameOf tape input log s) = true := by
  obtain ⟨k, rfl⟩ := Nat.le.dest le
  exact run_obs_mono i k flow service nameOf tape input log s

/-- A settled run observes the same thing for every larger fuel. -/
theorem run_obs_stable {σ : Type} {alphabet : FlowAlphabet Ty} (fuel k : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ)
    (settled : (runObservation fuel flow service nameOf tape input log s).settled = true) :
    runObservation (fuel + k) flow service nameOf tape input log s =
      runObservation fuel flow service nameOf tape input log s := by
  rw [runObservation_eq] at settled ⊢
  rw [runObservation_eq]
  exact loopObservation_stable alphabet flow.erase service nameOf fuel k flow.erase.entry [input]
    tape log s settled

/-- The chain of finite approximations of a public run. -/
def runChain {σ : Type} {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Effects.Trace.Val) (log : Effect4.Trace.Log) (s : σ) : Chain where
  observation fuel := runObservation fuel flow service nameOf tape input log s
  mono le := run_obs_chain le flow service nameOf tape input log s

/-- The colimit of a public run, searched below a bound. -/
def runColimit {σ : Type} {alphabet : FlowAlphabet Ty} (bound : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) : Option Observation :=
  (runChain flow service nameOf tape input log s).colimit bound

/-- The colimit of an admitted run: the settled observation reached at the fuel
`fuelFor` allots. This one is total, not `Option` -- `run_fuelFor_finishes`
(`Effect4/Semantics/Fuel.lean`) proves that fuel suffices, so the chain has
reached its top by then. It is the colimit DB-03 asks for on the deterministic
fragment: with the tape fixed, the run is a function of it. -/
def runColimitDefault {σ : Type} {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Effects.Trace.Val) (log : Effect4.Trace.Log) (s : σ) : Observation :=
  runObservation (fuelFor flow.erase tape) flow service nameOf tape input log s

/-- The colimit is settled: no more fuel can refine it. -/
theorem runColimitDefault_settled {σ : Type} {alphabet : FlowAlphabet Ty}
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) :
    (runColimitDefault flow service nameOf tape input log s).settled = true := by
  have finishes := run_fuelFor_finishes flow service nameOf tape input log s
  simp only [runColimitDefault, runObservation, runOut]
  rw [observe_settled, finishes]
  rfl

/-- Every smaller fuel is below the colimit. -/
theorem runColimitDefault_above {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) (le : fuel ≤ fuelFor flow.erase tape) :
    Observation.le (runObservation fuel flow service nameOf tape input log s)
      (runColimitDefault flow service nameOf tape input log s) = true :=
  run_obs_chain le flow service nameOf tape input log s

/-- Every larger fuel observes exactly the colimit. -/
theorem runColimitDefault_stable {σ : Type} {alphabet : FlowAlphabet Ty} {larger : Nat}
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) (le : fuelFor flow.erase tape ≤ larger) :
    runObservation larger flow service nameOf tape input log s =
      runColimitDefault flow service nameOf tape input log s :=
  (runChain flow service nameOf tape input log s).stable
    (runColimitDefault_settled flow service nameOf tape input log s) le

/-- The searched colimit and the colimit at the allotted fuel agree: below any
bound that reaches `fuelFor`, the search finds exactly this observation. -/
theorem runColimit_eq_default {σ : Type} {alphabet : FlowAlphabet Ty} {bound : Nat}
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Effects.Trace.Val)
    (log : Effect4.Trace.Log) (s : σ) (le : fuelFor flow.erase tape ≤ bound) :
    runColimit bound flow service nameOf tape input log s =
      some (runColimitDefault flow service nameOf tape input log s) :=
  Chain.colimit_eq_of_settled (c := runChain flow service nameOf tape input log s)
    (runColimitDefault_settled flow service nameOf tape input log s) le

/-! ## The region runner

`Effect4/Flow/Region.lean` runs an admitted region flow: `regionLoop` keeps a
stack of open regions, `enter` pushes one, `acquire` registers a release,
`leave` closes the innermost region latest-release-first, and a failing
operation unwinds every open region and ends the run `failed`. Packet D2 made
the failure carrier a *merged* list -- every failing release is kept, in close
order -- so a region run's raw value is `(RunResult × Tape) × Failures`, and
every law below is stated over that carrier. The merge is the one
`closeFrame_failure_merge` describes; the wire keeps only its head, and
`regionLoop_failed_head` is that projection.

The proofs do not repeat the plain runner's computation. They go through four
properties of a run computation, each closed under `bind`, so each law is one
structural walk over `regionLoop`'s branches:

* `Appends` -- the computation only appends to the log;
* `Sound` -- it appends, it punctuates a fuel frontier with the marker it
  emitted (which is what makes stripping the marker safe), a failing run's
  merged list is headed by the reported error, and a run that did not fail has
  an empty merged list;
* `Below` -- one computation observes below another at every log and state;
* `Settles` -- wherever the first did not exhaust its fuel, the second is the
  identical run.

What regions add over the plain runner -- failure, finalizers, the region
stack -- changes none of the laws: `RunResult.failed` is terminal, exactly
like `done` and `refused`, and fuel exhaustion still produces the *only* live
leaf (`regionLoop_frontier_live`).

The fuel argument transfers too, and exactly: an `enter` erases to a jump, an
`acquire` to a `perform`, a `leave` to a jump at the region's `continue_`, so
`regionLoop` spends one unit of fuel per block of `flow.erase` -- the very
graph `CyclesWF` constrains. `regionFuelFor flow tape = fuelFor flow.erase
tape = (tape.length + 1) * flow.blocks.length + 1` therefore suffices
(`runRegions_fuelFor_finishes`), and `runRegionsColimitDefault` is a total
`Observation`, not an `Option`. -/


/-! ## Three properties of a region-run computation -/

/-- A run computation only appends to the log: it never rewrites or drops a row
an earlier step emitted. -/
def Appends {σ : Type} {α : Type} (m : RunM (StateT σ Id) α) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ), ∃ events, ((m.run log).run s).1.2 = log ++ events

namespace Appends

theorem pure' {σ α : Type} (a : α) : Appends (σ := σ) (Pure.pure a) :=
  fun log _ => ⟨[], by simp only [List.append_nil]; rfl⟩

theorem emit' {σ : Type} (event : Effect4.Trace.Event) : Appends (σ := σ) (emit event) :=
  fun _ _ => ⟨[event], rfl⟩

theorem lift {σ α : Type} (x : StateT σ Id α) : Appends (σ := σ) (StateT.lift x) :=
  fun log _ => ⟨[], by simp only [List.append_nil]; rfl⟩

theorem bind {σ α β : Type} {m : RunM (StateT σ Id) α} {f : α → RunM (StateT σ Id) β}
    (hm : Appends m) (hf : ∀ a, Appends (f a)) : Appends (m >>= f) := by
  intro log s
  obtain ⟨events, eq⟩ := hm log s
  obtain ⟨events', eq'⟩ :=
    hf (((m.run log).run s)).1.1 (((m.run log).run s)).1.2 (((m.run log).run s)).2
  refine ⟨events ++ events', ?_⟩
  have run_eq : (((m >>= f).run log).run s)
      = ((f (((m.run log).run s)).1.1).run (((m.run log).run s)).1.2).run
          (((m.run log).run s)).2 := rfl
  rw [run_eq, eq', eq, List.append_assoc]

end Appends

theorem logOperation_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (op : alphabet.Op) (request : Val)
    (result : Except Val Val) : Appends (logOperation service nameOf op request result) := by
  unfold logOperation
  split
  · exact Appends.pure' ()
  · refine Appends.bind (Appends.emit' _) ?_
    intro _
    cases result with
    | ok answer => exact Appends.emit' _
    | error error => exact Appends.emit' _

theorem closeReleases_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (region : Nat) (exit : Outcome Val) :
    ∀ releases, Appends (closeReleases service nameOf region exit releases) := by
  intro releases
  induction releases with
  | nil => unfold closeReleases; exact Appends.pure' _
  | cons entry rest ih =>
      obtain ⟨release, resource⟩ := entry
      unfold closeReleases
      refine Appends.bind (Appends.emit' _) ?_
      intro _
      refine Appends.bind (Appends.lift _) ?_
      intro result
      refine Appends.bind (logOperation_appends _ _ _ _ _) ?_
      intro _
      refine Appends.bind ih ?_
      intro later
      cases result with
      | ok answer => exact Appends.pure' _
      | error error => exact Appends.pure' _

theorem closeFrame_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (frame : Frame alphabet) (exit : Outcome Val) :
    Appends (closeFrame service nameOf frame exit) := by
  unfold closeFrame
  refine Appends.bind (Appends.emit' _) ?_
  intro _
  exact closeReleases_appends _ _ _ _ _

theorem unwind_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (error : Val) :
    ∀ stack, Appends (unwind service nameOf stack error) := by
  intro stack
  induction stack with
  | nil => unfold unwind; exact Appends.pure' _
  | cons frame rest ih =>
      unfold unwind
      refine Appends.bind (closeFrame_appends _ _ _ _) ?_
      intro _
      refine Appends.bind ih ?_
      intro _
      exact Appends.pure' _

theorem fail_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (error : Val)
    (rest : Failures) (tape : Tape) :
    Appends (fail service nameOf stack error rest tape) := by
  unfold fail
  refine Appends.bind (unwind_appends _ _ _ _) ?_
  intro _
  refine Appends.bind (Appends.emit' _) ?_
  intro _
  exact Appends.pure' _

/-- The observation a finished region computation makes. -/
def obsOf {σ : Type} (m : RunM (StateT σ Id) ((RunResult × Tape) × Failures))
    (log : Effect4.Trace.Log) (s : σ) : Observation :=
  observe ((m.run log).run s).1.1.1.1 ((m.run log).run s).1.2

/-- What every region-run computation satisfies. -/
structure Sound {σ : Type} (m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Prop where
  appends : Appends m
  punctuates : ∀ (log : Effect4.Trace.Log) (s : σ),
    ((m.run log).run s).1.1.1.1.exhausted = true →
      ∃ events, ((m.run log).run s).1.2 = (log ++ events) ++ [Effects.Trace.Event.frontier]
  headed : ∀ (log : Effect4.Trace.Log) (s : σ) (error : Val),
    ((m.run log).run s).1.1.1.1 = .failed error →
      ∃ more, ((m.run log).run s).1.1.2 = error :: more
  clean : ∀ (log : Effect4.Trace.Log) (s : σ),
    (∀ error, ((m.run log).run s).1.1.1.1 ≠ .failed error) → ((m.run log).run s).1.1.2 = []

namespace Sound

theorem bind {σ α : Type} {m : RunM (StateT σ Id) α}
    {f : α → RunM (StateT σ Id) ((RunResult × Tape) × Failures)}
    (hm : Appends m) (hf : ∀ a, Sound (f a)) : Sound (m >>= f) := by
  have run_eq : ∀ (log : Effect4.Trace.Log) (s : σ), (((m >>= f).run log).run s)
      = ((f (((m.run log).run s)).1.1).run (((m.run log).run s)).1.2).run
          (((m.run log).run s)).2 := fun _ _ => rfl
  refine ⟨Appends.bind hm (fun a => (hf a).appends), ?_, ?_, ?_⟩
  · intro log s exhausted
    rw [run_eq] at exhausted ⊢
    obtain ⟨events, eq⟩ := hm log s
    obtain ⟨events', eq'⟩ := (hf _).punctuates _ _ exhausted
    exact ⟨events ++ events', by rw [eq', eq]; simp [List.append_assoc]⟩
  · intro log s error failed
    rw [run_eq] at failed ⊢
    exact (hf _).headed _ _ error failed
  · intro log s notFailed
    rw [run_eq] at notFailed ⊢
    exact (hf _).clean _ _ notFailed

/-- A settled leaf: the run stops here with a result that is neither a fuel
frontier nor a failure, and the merged failure list is empty. -/
theorem pure_settled {σ : Type} (result : RunResult) (tape : Tape)
    (notExhausted : result.exhausted = false) (notFailed : ∀ error, result ≠ .failed error) :
    Sound (σ := σ) (Pure.pure ((result, tape), ([] : Failures))) where
  appends := Appends.pure' _
  punctuates := by
    intro log s exhausted
    rw [show ((((Pure.pure ((result, tape), ([] : Failures)) :
      RunM (StateT σ Id) ((RunResult × Tape) × Failures)).run log).run s)).1.1.1.1 = result from rfl,
      notExhausted] at exhausted
    cases exhausted
  headed := by
    intro log s error failed
    exact absurd (show result = .failed error from failed) (notFailed error)
  clean := by intro log s _; rfl

/-- The failing leaf: the merged failure list is headed by the reported error. -/
theorem pure_failed {σ : Type} (error : Val) (tape : Tape) (more : Failures) :
    Sound (σ := σ) (Pure.pure ((RunResult.failed error, tape), error :: more)) where
  appends := Appends.pure' _
  punctuates := by
    intro log s exhausted
    rw [show ((((Pure.pure ((RunResult.failed error, tape), error :: more) :
      RunM (StateT σ Id) ((RunResult × Tape) × Failures)).run log).run s)).1.1.1.1
        = RunResult.failed error from rfl] at exhausted
    cases exhausted
  headed := by
    intro log s e failed
    have h : RunResult.failed error = RunResult.failed e := failed
    injection h with he
    subst he
    exact ⟨more, rfl⟩
  clean := by
    intro log s notFailed
    exact absurd (show RunResult.failed error = .failed error from rfl) (notFailed error)

/-- The fuel-frontier leaf: the marker is appended and the failure list is
empty. Fuel exhaustion is a live frontier, never a failure (DB-04). -/
theorem frontier_leaf {σ : Type} (block : BlockId) (tape : Tape) :
    Sound (σ := σ) (do emit Effects.Trace.Event.frontier
                       pure ((RunResult.frontier (Frontier.fuel block), tape), ([] : Failures)))
    where
  appends := fun _ _ => ⟨[Effects.Trace.Event.frontier], rfl⟩
  punctuates := by
    intro log s _
    refine ⟨[], ?_⟩
    show log ++ [Effects.Trace.Event.frontier]
      = (log ++ []) ++ [Effects.Trace.Event.frontier]
    rw [List.append_nil]
  headed := by
    intro log s error failed
    exact absurd (show RunResult.frontier (Frontier.fuel block) = .failed error from failed)
      (fun h => RunResult.noConfusion h)
  clean := by intro log s _; rfl

end Sound

theorem fail_sound {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (error : Val)
    (rest : Failures) (tape : Tape) : Sound (fail service nameOf stack error rest tape) := by
  unfold fail
  refine Sound.bind (unwind_appends _ _ _ _) ?_
  intro closing
  refine Sound.bind (Appends.emit' _) ?_
  intro _
  exact Sound.pure_failed error tape (rest ++ closing)

/-- A sound computation observes a log extending the one it started from. -/
theorem obsOf_extends {σ : Type} {m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)}
    (h : Sound m) (log : Effect4.Trace.Log) (s : σ) :
    logPrefix log (obsOf m log s).log = true := by
  obtain ⟨events, eq⟩ := h.appends log s
  cases exhausted : (((m.run log).run s)).1.1.1.1.exhausted with
  | false =>
      have terminal := observe_terminal (result := (((m.run log).run s)).1.1.1.1)
        (((m.run log).run s)).1.2 exhausted
      rw [obsOf, terminal]
      simp only [Observation.log]
      rw [eq]
      exact logPrefix_append log events
  | true =>
      obtain ⟨events', eq'⟩ := h.punctuates log s exhausted
      have fuel : ∃ block, (((m.run log).run s)).1.1.1.1 = .frontier (.fuel block) := by
        generalize (((m.run log).run s)).1.1.1.1 = result at exhausted
        cases result with
        | done value => cases exhausted
        | failed error => cases exhausted
        | refusedSite expected actual => cases exhausted
        | refusedValue site => cases exhausted
        | frontier reason =>
            cases reason with
            | fuel block => exact ⟨block, rfl⟩
            | unansweredDecision site => cases exhausted
            | stuck block => cases exhausted
      obtain ⟨block, isFuel⟩ := fuel
      rw [obsOf, isFuel, eq', observe_fuel]
      simp only [Observation.log]
      exact logPrefix_append log events'

/-- One region computation observes below another at every starting log and
state. -/
def Below {σ : Type} (m m' : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ), Observation.le (obsOf m log s) (obsOf m' log s) = true

namespace Below

theorem refl {σ : Type} (m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Below m m :=
  fun _ _ => Observation.le_refl _

theorem bind {σ α : Type} {m : RunM (StateT σ Id) α}
    {f g : α → RunM (StateT σ Id) ((RunResult × Tape) × Failures)} (h : ∀ a, Below (f a) (g a)) :
    Below (m >>= f) (m >>= g) := by
  intro log s
  exact h (((m.run log).run s)).1.1 (((m.run log).run s)).1.2 (((m.run log).run s)).2

/-- The fuel-zero computation is below every sound computation: the base case
of every monotonicity induction. -/
theorem frontier {σ : Type} {block : BlockId} {tape : Tape}
    {m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)} (h : Sound m) :
    Below (do emit Effects.Trace.Event.frontier
              pure ((RunResult.frontier (Frontier.fuel block), tape), ([] : Failures))) m := by
  intro log s
  have left : obsOf (σ := σ)
      (do emit Effects.Trace.Event.frontier
          pure ((RunResult.frontier (Frontier.fuel block), tape), ([] : Failures))) log s
        = .live log := by
    show observe (RunResult.frontier (Frontier.fuel block)) (log ++ [Effects.Trace.Event.frontier])
      = .live log
    exact observe_fuel block log
  rw [left, Observation.live_le_iff]
  exact obsOf_extends h log s

end Below

/-- One region computation is stable under another: wherever the first did not
exhaust its fuel, the second gives exactly the same run -- result, tape, merged
failure list, log and service state. -/
def Settles {σ : Type} (m m' : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ),
    ((m.run log).run s).1.1.1.1.exhausted = false → (m'.run log).run s = (m.run log).run s

namespace Settles

theorem refl {σ : Type} (m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Settles m m :=
  fun _ _ _ => rfl

theorem bind {σ α : Type} {m : RunM (StateT σ Id) α}
    {f g : α → RunM (StateT σ Id) ((RunResult × Tape) × Failures)} (h : ∀ a, Settles (f a) (g a)) :
    Settles (m >>= f) (m >>= g) := by
  intro log s settled
  exact h (((m.run log).run s)).1.1 (((m.run log).run s)).1.2 (((m.run log).run s)).2 settled

/-- The fuel-zero computation is stable under every computation, vacuously: it
did exhaust its fuel. -/
theorem frontier {σ : Type} {block : BlockId} {tape : Tape}
    {m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)} :
    Settles (do emit Effects.Trace.Event.frontier
                pure ((RunResult.frontier (Frontier.fuel block), tape), ([] : Failures))) m := by
  intro log s settled
  cases settled

end Settles

/-! ## The three inductions over `regionLoop` -/

theorem regionLoop_sound {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet)),
      Sound (regionLoop alphabet flow service nameOf fuel block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape stack
      exact Sound.frontier_leaf block tape
  | succ fuel ih =>
      intro block env tape stack
      unfold regionLoop
      cases hblock : flow.block? block with
      | none => exact Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h)
      | some current =>
          dsimp only
          cases hterm : current.term with
          | plain term =>
              dsimp only
              cases hplan : plan alphabet
                  { id := current.id, params := current.params, term := term } env tape with
              | stuck => exact Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h)
              | ret value =>
                  exact Sound.bind (Appends.emit' _)
                    (fun _ => Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h))
              | jump target env' => exact ih _ _ _ _
              | perform op request target env' =>
                  refine Sound.bind (Appends.lift _) ?_
                  intro result
                  refine Sound.bind (logOperation_appends _ _ _ _ _) ?_
                  intro _
                  cases result with
                  | ok answer => exact ih _ _ _ _
                  | error error => exact fail_sound _ _ _ _ _ _
              | exhausted site =>
                  exact Sound.bind (Appends.emit' _)
                    (fun _ => Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h))
              | mismatch expected actual =>
                  exact Sound.pure_settled _ _ (RunResult.exhausted_refusal _ _)
                    (fun _ h => absurd h (RunResult.refusal_ne_failed _ _ _))
              | choose site branch target env' rest =>
                  refine Sound.bind (Appends.emit' _) ?_
                  intro _
                  exact ih _ _ _ _
              | performCatch op request target env' onError errorEnv =>
                  refine Sound.bind (Appends.lift _) ?_
                  intro result
                  refine Sound.bind (logOperation_appends _ _ _ _ _) ?_
                  intro _
                  cases result with
                  | ok answer => exact ih _ _ _ _
                  | error error => exact ih _ _ _ _
          | enter region body args =>
              dsimp only
              cases hargs : readArgs env args with
              | none => exact Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h)
              | some values =>
                  refine Sound.bind (Appends.emit' _) ?_
                  intro _
                  exact ih _ _ _ _
          | acquire operation request release target args =>
              dsimp only
              cases hop : alphabet.lookup operation <;> cases hrelease : alphabet.lookup release <;>
                cases hrequest : env[request.index]? <;> cases hargs : readArgs env args <;>
                cases hstack : stack <;> dsimp only <;>
                first
                  | exact Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h)
                  | (refine Sound.bind (Appends.lift _) ?_
                     intro result
                     refine Sound.bind (logOperation_appends _ _ _ _ _) ?_
                     intro _
                     cases result with
                     | ok answer => exact ih _ _ _ _
                     | error error => exact fail_sound _ _ _ _ _ _)
          | leave value =>
              dsimp only
              cases hvalue : env[value.index]? <;> cases hstack : stack <;>
                cases hrow : current.region.bind flow.row? <;> dsimp only <;>
                first
                  | exact Sound.pure_settled _ _ rfl (fun _ h => RunResult.noConfusion h)
                  | (refine Sound.bind (closeFrame_appends _ _ _ _) ?_
                     intro failures
                     cases failures with
                     | nil => exact ih _ _ _ _
                     | cons error more => exact fail_sound _ _ _ _ _ _)

theorem regionLoop_below {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel k : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet)),
      Below (regionLoop alphabet flow service nameOf fuel block env tape stack)
        (regionLoop alphabet flow service nameOf (fuel + k) block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k block env tape stack
      rw [Nat.zero_add]
      show Below (do emit Effects.Trace.Event.frontier
                     pure ((RunResult.frontier (Frontier.fuel block), tape), ([] : Failures))) _
      exact Below.frontier (regionLoop_sound flow service nameOf k block env tape stack)
  | succ fuel ih =>
      intro k block env tape stack
      rw [Nat.add_right_comm fuel 1 k]
      unfold regionLoop
      cases hblock : flow.block? block with
      | none => exact Below.refl _
      | some current =>
          dsimp only
          cases hterm : current.term with
          | plain term =>
              dsimp only
              cases hplan : plan alphabet
                  { id := current.id, params := current.params, term := term } env tape with
              | stuck => exact Below.refl _
              | ret value => exact Below.refl _
              | jump target env' => exact ih _ _ _ _ _
              | perform op request target env' =>
                  refine Below.bind ?_
                  intro result
                  refine Below.bind ?_
                  intro _
                  cases result with
                  | ok answer => exact ih _ _ _ _ _
                  | error error => exact Below.refl _
              | performCatch op request target env' onError errorEnv =>
                  refine Below.bind ?_
                  intro result
                  refine Below.bind ?_
                  intro _
                  cases result with
                  | ok answer => exact ih _ _ _ _ _
                  | error error => exact ih _ _ _ _ _
              | exhausted site => exact Below.refl _
              | mismatch expected actual => exact Below.refl _
              | choose site branch target env' rest =>
                  refine Below.bind ?_
                  intro _
                  exact ih _ _ _ _ _
          | enter region body args =>
              dsimp only
              cases hargs : readArgs env args with
              | none => exact Below.refl _
              | some values =>
                  refine Below.bind ?_
                  intro _
                  exact ih _ _ _ _ _
          | acquire operation request release target args =>
              dsimp only
              cases hop : alphabet.lookup operation <;> cases hrelease : alphabet.lookup release <;>
                cases hrequest : env[request.index]? <;> cases hargs : readArgs env args <;>
                cases hstack : stack <;> dsimp only <;>
                first
                  | exact Below.refl _
                  | (refine Below.bind ?_
                     intro result
                     refine Below.bind ?_
                     intro _
                     cases result with
                     | ok answer => exact ih _ _ _ _ _
                     | error error => exact Below.refl _)
          | leave value =>
              dsimp only
              cases hvalue : env[value.index]? <;> cases hstack : stack <;>
                cases hrow : current.region.bind flow.row? <;> dsimp only <;>
                first
                  | exact Below.refl _
                  | (refine Below.bind ?_
                     intro failures
                     cases failures with
                     | nil => exact ih _ _ _ _ _
                     | cons error more => exact Below.refl _)

theorem regionLoop_settles {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel k : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet)),
      Settles (regionLoop alphabet flow service nameOf fuel block env tape stack)
        (regionLoop alphabet flow service nameOf (fuel + k) block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro k block env tape stack
      rw [Nat.zero_add]
      show Settles (do emit Effects.Trace.Event.frontier
                       pure ((RunResult.frontier (Frontier.fuel block), tape), ([] : Failures))) _
      exact Settles.frontier
  | succ fuel ih =>
      intro k block env tape stack
      rw [Nat.add_right_comm fuel 1 k]
      unfold regionLoop
      cases hblock : flow.block? block with
      | none => exact Settles.refl _
      | some current =>
          dsimp only
          cases hterm : current.term with
          | plain term =>
              dsimp only
              cases hplan : plan alphabet
                  { id := current.id, params := current.params, term := term } env tape with
              | stuck => exact Settles.refl _
              | ret value => exact Settles.refl _
              | jump target env' => exact ih _ _ _ _ _
              | perform op request target env' =>
                  refine Settles.bind ?_
                  intro result
                  refine Settles.bind ?_
                  intro _
                  cases result with
                  | ok answer => exact ih _ _ _ _ _
                  | error error => exact Settles.refl _
              | performCatch op request target env' onError errorEnv =>
                  refine Settles.bind ?_
                  intro result
                  refine Settles.bind ?_
                  intro _
                  cases result with
                  | ok answer => exact ih _ _ _ _ _
                  | error error => exact ih _ _ _ _ _
              | exhausted site => exact Settles.refl _
              | mismatch expected actual => exact Settles.refl _
              | choose site branch target env' rest =>
                  refine Settles.bind ?_
                  intro _
                  exact ih _ _ _ _ _
          | enter region body args =>
              dsimp only
              cases hargs : readArgs env args with
              | none => exact Settles.refl _
              | some values =>
                  refine Settles.bind ?_
                  intro _
                  exact ih _ _ _ _ _
          | acquire operation request release target args =>
              dsimp only
              cases hop : alphabet.lookup operation <;> cases hrelease : alphabet.lookup release <;>
                cases hrequest : env[request.index]? <;> cases hargs : readArgs env args <;>
                cases hstack : stack <;> dsimp only <;>
                first
                  | exact Settles.refl _
                  | (refine Settles.bind ?_
                     intro result
                     refine Settles.bind ?_
                     intro _
                     cases result with
                     | ok answer => exact ih _ _ _ _ _
                     | error error => exact Settles.refl _)
          | leave value =>
              dsimp only
              cases hvalue : env[value.index]? <;> cases hstack : stack <;>
                cases hrow : current.region.bind flow.row? <;> dsimp only <;>
                first
                  | exact Settles.refl _
                  | (refine Settles.bind ?_
                     intro failures
                     cases failures with
                     | nil => exact ih _ _ _ _ _
                     | cons error more => exact Settles.refl _)


/-! ## The region runner's laws -/

/-- The full result of a fuelled region loop over `StateT σ Id`: the run
result, the unconsumed tape, the merged failure list, the log and the service
state. -/
def regionOut {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) :
    (((RunResult × Tape) × Failures) × Effect4.Trace.Log) × σ :=
  ((regionLoop alphabet flow service nameOf fuel block env tape stack).run log).run s

/-- **The region analogue of `step_log_extends`.** The region runner has no
separable `step`: one block's worth of fuel is `regionLoop` at `fuel + 1`. It
only appends to the log -- `enter`, `op`, `answer`, `decide`, `leave`,
`finalizer`, `failed` and `done` rows are added, never rewritten or dropped. -/
theorem regionStep_log_extends {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) :
    ∃ events, (regionOut flow service nameOf (fuel + 1) block env tape stack log s).1.2
      = log ++ events :=
  (regionLoop_sound flow service nameOf (fuel + 1) block env tape stack).appends log s

/-- **Fuel stability, raw form.** Once a region run at fuel `i` has finished --
with a value, a failure, a refusal, an unanswered decision or a stuck block --
every fuel `j ≥ i` gives exactly the same run: the same result, the same
unconsumed tape, the same *merged failure list*, the same log and the same
service state. -/
theorem regionLoop_fuel_stable {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    {i j : Nat} (le : i ≤ j) (block : BlockId) (env : Env) (tape : Tape)
    (stack : List (Frame alphabet)) (log : Effect4.Trace.Log) (s : σ)
    (settled : (regionOut flow service nameOf i block env tape stack log s).1.1.1.1.exhausted
      = false) :
    regionOut flow service nameOf j block env tape stack log s =
      regionOut flow service nameOf i block env tape stack log s := by
  obtain ⟨k, rfl⟩ := Nat.le.dest le
  exact regionLoop_settles flow service nameOf i k block env tape stack log s settled

/-- **A fuel frontier is exactly a live observation.** When a region run stops
at the fuel bound its result is a `fuel` frontier -- never `failed`, never
`refused` -- and the merged failure list is untouched: it is empty. This is
DB-04's "fuel exhaustion is a live frontier, never a failure, never a
refusal" for the region runner, stated over the D2 failure carrier. -/
theorem regionLoop_frontier_live {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ)
    (exhausted : (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1.exhausted
      = true) :
    (∃ resume, (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1
        = .frontier (.fuel resume)) ∧
      (∀ error, (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1
        ≠ .failed error) ∧
      (∀ expected actual, (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1
        ≠ .refusal expected actual) ∧
      (regionOut flow service nameOf fuel block env tape stack log s).1.1.2 = [] := by
  have sound := regionLoop_sound flow service nameOf fuel block env tape stack
  have isFuel : ∃ resume,
      (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1
        = .frontier (.fuel resume) := by
    generalize (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1 = result
      at exhausted
    cases result with
    | done value => cases exhausted
    | failed error => cases exhausted
    | refusedSite expected actual => cases exhausted
    | refusedValue site => cases exhausted
    | frontier reason =>
        cases reason with
        | fuel resume => exact ⟨resume, rfl⟩
        | unansweredDecision site => cases exhausted
        | stuck resume => cases exhausted
  obtain ⟨resume, isFuelEq⟩ := isFuel
  refine ⟨⟨resume, isFuelEq⟩, ?_, ?_, ?_⟩
  · intro error failed
    rw [isFuelEq] at failed
    exact RunResult.noConfusion failed
  · intro expected actual refused
    rw [isFuelEq] at refused
    unfold RunResult.refusal at refused
    split at refused <;> exact RunResult.noConfusion refused
  · have unfolded :
        (((regionLoop alphabet flow service nameOf fuel block env tape stack).run log).run
          s).1.1.1.1 = .frontier (.fuel resume) := isFuelEq
    refine sound.clean log s ?_
    intro error failed
    rw [unfolded] at failed
    exact RunResult.noConfusion failed

/-- **The merged failure carrier.** A failing region run reports the head of
its merged failure list, and that list is empty on every run that did not
fail. The list is the close-order merge `closeFrame_failure_merge` describes:
a failing release under a failing body keeps both, body failure first. -/
theorem regionLoop_failed_head {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) (error : Val)
    (failed : (regionOut flow service nameOf fuel block env tape stack log s).1.1.1.1
      = .failed error) :
    ∃ more, (regionOut flow service nameOf fuel block env tape stack log s).1.1.2
      = error :: more :=
  (regionLoop_sound flow service nameOf fuel block env tape stack).headed log s error failed

/-- The observation a fuelled region run makes. -/
def regionObservation {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (fuel : Nat)
    (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) : Observation :=
  obsOf (regionLoop alphabet flow service nameOf fuel block env tape stack) log s

/-- **Monotonicity.** The region analogue of `loop_obs_mono`: more fuel yields
an observation above the smaller fuel's. -/
theorem region_obs_mono {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel k : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (regionObservation flow service nameOf fuel block env tape stack log s)
      (regionObservation flow service nameOf (fuel + k) block env tape stack log s) = true :=
  regionLoop_below flow service nameOf fuel k block env tape stack log s

/-- **The chain law.** Observations along increasing fuel form a chain. -/
theorem region_obs_chain {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    {i j : Nat} (le : i ≤ j) (block : BlockId) (env : Env) (tape : Tape)
    (stack : List (Frame alphabet)) (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (regionObservation flow service nameOf i block env tape stack log s)
      (regionObservation flow service nameOf j block env tape stack log s) = true := by
  obtain ⟨k, rfl⟩ := Nat.le.dest le
  exact region_obs_mono flow service nameOf i k block env tape stack log s

/-- The region loop's chain of finite approximations. -/
def regionChain {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) : Chain where
  observation fuel := regionObservation flow service nameOf fuel block env tape stack log s
  mono le := region_obs_chain flow service nameOf le block env tape stack log s

/-- **Compatibility.** A settled region observation is the observation of every
larger fuel. -/
theorem regionObservation_stable {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    {fuel larger : Nat} (block : BlockId) (env : Env) (tape : Tape)
    (stack : List (Frame alphabet)) (log : Effect4.Trace.Log) (s : σ)
    (settled : (regionObservation flow service nameOf fuel block env tape stack log s).settled
      = true) (le : fuel ≤ larger) :
    regionObservation flow service nameOf larger block env tape stack log s =
      regionObservation flow service nameOf fuel block env tape stack log s :=
  (regionChain flow service nameOf block env tape stack log s).stable settled le

/-! ## The same laws for `runRegions` -/

/-- The observation a fuelled run of an admitted region flow makes. -/
def runRegionsObservation {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) : Observation :=
  obsOf (runRegionsCause fuel flow service nameOf tape input) log s

/-- The observation is the *wire* runner's: `runRegions` projects the merged
failure list away and keeps result, tape and log, so it observes exactly what
`runRegionsCause` observes. -/
theorem runRegionsObservation_wire {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (fuel : Nat) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    runRegionsObservation fuel flow service nameOf tape input log s =
      observe (((runRegions fuel flow service nameOf tape input).run log).run s).1.1.1
        (((runRegions fuel flow service nameOf tape input).run log).run s).1.2 := rfl

theorem runRegionsObservation_eq {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (fuel : Nat) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    runRegionsObservation fuel flow service nameOf tape input log s =
      regionObservation flow.flow service nameOf fuel flow.flow.entry [input] tape [] log s := rfl

/-- Monotonicity for the public region runner. -/
theorem runRegions_obs_mono {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel k : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (runRegionsObservation fuel flow service nameOf tape input log s)
      (runRegionsObservation (fuel + k) flow service nameOf tape input log s) = true :=
  region_obs_mono flow.flow service nameOf fuel k flow.flow.entry [input] tape [] log s

/-- The chain form for the public region runner. -/
theorem runRegions_obs_chain {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty} {i j : Nat}
    (le : i ≤ j) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (runRegionsObservation i flow service nameOf tape input log s)
      (runRegionsObservation j flow service nameOf tape input log s) = true :=
  region_obs_chain flow.flow service nameOf le flow.flow.entry [input] tape [] log s

/-- The chain of finite approximations of an admitted region run. -/
def runRegionsChain {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) : Chain where
  observation fuel := runRegionsObservation fuel flow service nameOf tape input log s
  mono le := runRegions_obs_chain le flow service nameOf tape input log s

/-- A settled region run observes the same thing for every larger fuel. -/
theorem runRegions_obs_stable {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {fuel larger : Nat} (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ)
    (settled : (runRegionsObservation fuel flow service nameOf tape input log s).settled = true)
    (le : fuel ≤ larger) :
    runRegionsObservation larger flow service nameOf tape input log s =
      runRegionsObservation fuel flow service nameOf tape input log s :=
  (runRegionsChain flow service nameOf tape input log s).stable settled le

/-- The colimit of an admitted region run, searched below a bound. -/
def runRegionsColimit {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (bound : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) : Option Observation :=
  (runRegionsChain flow service nameOf tape input log s).colimit bound

theorem runRegionsColimit_settled {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {bound : Nat} {flow : CheckedRegionFlow alphabet}
    {service : RegionService alphabet (StateT σ Id)} {nameOf : alphabet.Op → String} {tape : Tape}
    {input : Val} {log : Effect4.Trace.Log} {s : σ} {o : Observation}
    (found : runRegionsColimit bound flow service nameOf tape input log s = some o) :
    o.settled = true :=
  Chain.colimit_settled found

theorem runRegionsColimit_eq_of_settled {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {bound fuel : Nat} {flow : CheckedRegionFlow alphabet}
    {service : RegionService alphabet (StateT σ Id)} {nameOf : alphabet.Op → String} {tape : Tape}
    {input : Val} {log : Effect4.Trace.Log} {s : σ}
    (settled : (runRegionsObservation fuel flow service nameOf tape input log s).settled = true)
    (le : fuel ≤ bound) :
    runRegionsColimit bound flow service nameOf tape input log s =
      some (runRegionsObservation fuel flow service nameOf tape input log s) :=
  Chain.colimit_eq_of_settled (c := runRegionsChain flow service nameOf tape input log s) settled le


/-! ## The fuel an admitted region flow needs -/

/-- The v2 block a region block erases to. -/
def eraseBlock (flow : RegionFlow Ty) (block : RegionBlock Ty) : RawBlock Ty :=
  { id := block.id, params := block.params, term := flow.eraseTerm block }

private theorem find?_map_erase (flow : RegionFlow Ty) (id : BlockId) :
    ∀ (bs : List (RegionBlock Ty)),
      (bs.map (eraseBlock flow)).find? (fun block => block.id = id)
        = (bs.find? (fun block => block.id = id)).map (eraseBlock flow)
  | [] => rfl
  | b :: bs => by
      have head : (eraseBlock flow b).id = b.id := rfl
      simp only [List.map_cons, List.find?_cons, head]
      by_cases h : b.id = id
      · simp [h]
      · simp [h, find?_map_erase flow id bs]

/-- Resolving a block in the erased graph is resolving it in the region graph
and erasing: erasure is name-preserving and table-preserving. -/
theorem lookupBlock_erase (flow : RegionFlow Ty) (id : BlockId) :
    lookupBlock flow.erase id = (flow.block? id).map (eraseBlock flow) :=
  find?_map_erase flow id flow.blocks

/-- A block resolved in the erased graph came from a region block with the same
parameter list. -/
theorem block?_of_lookup_erase {flow : RegionFlow Ty} {id : BlockId} {target : RawBlock Ty}
    (found : lookupBlock flow.erase id = some target) :
    ∃ block, flow.block? id = some block ∧ block.params = target.params := by
  rw [lookupBlock_erase] at found
  cases hb : flow.block? id with
  | none => rw [hb] at found; cases found
  | some block =>
      rw [hb, Option.map_some] at found
      injection found with erased
      exact ⟨block, rfl, by rw [← erased]; rfl⟩

/-- Walking a non-`choose` edge: the segment since the last decision grows by
one block and one unit of fuel pays for it. -/
theorem LoopBudget.advance {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) {block next : BlockId} {tape : Tape} {visited : List BlockId}
    {fuel : Nat} {current : RawBlock Ty} (found : lookupBlock raw block = some current)
    (edge : EdgeNoChoose raw block next)
    (budget : LoopBudget raw block tape visited (fuel + 1)) :
    LoopBudget raw next tape (block :: visited) fuel where
  nodup := List.nodup_cons.mpr ⟨budget.fresh, budget.nodup⟩
  fresh := by
    intro inSegment
    have reachBack : ReachableNoChoose raw next block := by
      rcases List.mem_cons.mp inSegment with eq | inVisited
      · cases eq; exact .refl _
      · exact budget.reaches next inVisited
    exact wf.cycles block next edge reachBack
  declared := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mem_blockIds_of_lookup found
    · exact budget.declared x hx
  reaches := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .step (.refl _) edge
    · exact .step (budget.reaches x hx) edge
  covers := by
    have covers := budget.covers
    simp only [List.length_cons]
    omega

/-- Answering a decision: one tape entry is consumed and the segment restarts,
paid for by the `blocks.length` the segment could not exceed. -/
theorem LoopBudget.consume {raw : RawFlow Ty} {block next : BlockId} {tape rest : Tape}
    {visited : List BlockId} {fuel : Nat}
    (bound : visited.length + 1 ≤ raw.blocks.length)
    (consumed : rest.length + 1 = tape.length)
    (budget : LoopBudget raw block tape visited (fuel + 1)) :
    LoopBudget raw next rest [] fuel where
  nodup := List.nodup_nil
  fresh := List.not_mem_nil
  declared := fun _ hx => absurd hx List.not_mem_nil
  reaches := fun _ hx => absurd hx List.not_mem_nil
  covers := by
    have covers := budget.covers
    have expand : (tape.length + 1) * raw.blocks.length
        = (rest.length + 1) * raw.blocks.length + raw.blocks.length := by
      rw [← consumed]
      simp [Nat.add_mul]
    simp only [List.length_nil]
    omega

/-- A region computation that does not stop at the fuel bound. -/
def NotExhausted {σ : Type} (m : RunM (StateT σ Id) ((RunResult × Tape) × Failures)) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ), ((m.run log).run s).1.1.1.1.exhausted = false

namespace NotExhausted

theorem bind {σ α : Type} {m : RunM (StateT σ Id) α}
    {f : α → RunM (StateT σ Id) ((RunResult × Tape) × Failures)} (hf : ∀ a, NotExhausted (f a)) :
    NotExhausted (m >>= f) := fun _ _ => hf _ _ _

theorem leaf {σ : Type} {result : RunResult} (tape : Tape) (failures : Failures)
    (h : result.exhausted = false) :
    NotExhausted (σ := σ) (Pure.pure ((result, tape), failures)) := fun _ _ => h

end NotExhausted

theorem fail_not_exhausted {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (stack : List (Frame alphabet)) (error : Val) (rest : Failures) (tape : Tape) :
    NotExhausted (fail service nameOf stack error rest tape) := by
  unfold fail
  refine NotExhausted.bind ?_
  intro _
  refine NotExhausted.bind ?_
  intro _
  exact NotExhausted.leaf _ _ rfl

/-- **The region fuel argument.** A region run walked under `LoopBudget` never
stops at the fuel bound. The region layer changes nothing about the count: an
`enter` erases to a jump, an `acquire` to a `perform` and a `leave` to a jump
at the region's `continue_`, so `regionLoop` spends exactly one unit of fuel
per block of the *erased* graph, which is the graph `CyclesWF` constrains. A
failing operation, a failing release and every unresolved shape end the run
earlier still. -/
theorem regionLoop_budget_not_exhausted {σ : Type} {alphabet : FlowAlphabet Ty}
    {flow : RegionFlow Ty} (wf : FlowWF alphabet flow.erase)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (visited : List BlockId)
      (stack : List (Frame alphabet)) (current : RegionBlock Ty),
      flow.block? block = some current →
      env.length = current.params.length →
      LoopBudget flow.erase block tape visited fuel →
      NotExhausted (regionLoop alphabet flow service nameOf fuel block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape visited stack current found _ budget
      exfalso
      have foundErase : lookupBlock flow.erase block = some (eraseBlock flow current) := by
        rw [lookupBlock_erase, found]; rfl
      have bound := budget.segment_lt foundErase
      have covers := budget.covers
      have pos : flow.erase.blocks.length ≤ (tape.length + 1) * flow.erase.blocks.length :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega
  | succ fuel ih =>
      intro block env tape visited stack current found sized budget
      have foundErase : lookupBlock flow.erase block = some (eraseBlock flow current) := by
        rw [lookupBlock_erase, found]; rfl
      have bound := budget.segment_lt foundErase
      have memErase : eraseBlock flow current ∈ flow.erase.blocks :=
        List.mem_of_find?_eq_some foundErase
      have idEq : current.id = block := lookupBlock_id foundErase
      have sizedErase : env.length = (eraseBlock flow current).params.length := sized
      have planned := plan_checked wf memErase sizedErase tape
      have shaped := plan_shape alphabet (eraseBlock flow current) env tape
      -- Walking a declared non-`choose` edge of the erased graph.
      have advance : ∀ (next : BlockId) (env' : Env) (stack' : List (Frame alphabet))
          (target : RawBlock Ty), lookupBlock flow.erase next = some target →
          env'.length = target.params.length → EdgeNoChoose flow.erase block next →
          NotExhausted (regionLoop alphabet flow service nameOf fuel next env' tape stack') := by
        intro next env' stack' target foundTarget sizedTarget edge
        obtain ⟨rb, foundRb, paramsEq⟩ := block?_of_lookup_erase foundTarget
        exact ih next env' tape (block :: visited) stack' rb foundRb
          (by rw [paramsEq]; exact sizedTarget) (LoopBudget.advance wf foundErase edge budget)
      -- Answering one decision.
      have consume : ∀ (next : BlockId) (env' : Env) (rest : Tape)
          (stack' : List (Frame alphabet)) (target : RawBlock Ty),
          lookupBlock flow.erase next = some target → env'.length = target.params.length →
          rest.length + 1 = tape.length →
          NotExhausted (regionLoop alphabet flow service nameOf fuel next env' rest stack') := by
        intro next env' rest stack' target foundTarget sizedTarget consumed
        obtain ⟨rb, foundRb, paramsEq⟩ := block?_of_lookup_erase foundTarget
        exact ih next env' rest [] stack' rb foundRb (by rw [paramsEq]; exact sizedTarget)
          (LoopBudget.consume bound consumed budget)
      unfold regionLoop
      rw [found]
      dsimp only
      cases hterm : current.term with
      | plain term =>
          have erasedEq : eraseBlock flow current
              = { id := current.id, params := current.params, term := term } := by
            simp [eraseBlock, RegionFlow.eraseTerm, hterm]
          rw [erasedEq] at planned shaped memErase
          dsimp only
          cases hplan : plan alphabet
              { id := current.id, params := current.params, term := term } env tape with
          | stuck => exact NotExhausted.leaf _ _ rfl
          | ret value =>
              exact NotExhausted.bind (fun _ => NotExhausted.leaf _ _ rfl)
          | jump target env' =>
              rw [hplan] at planned shaped
              simp only [PlanShape] at shaped
              cases planned with
              | jump targetBlock foundTarget sizedTarget =>
                  exact advance target env' stack targetBlock foundTarget sizedTarget
                    ⟨_, memErase, idEq, shaped.1, shaped.2⟩
          | perform op request target env' =>
              rw [hplan] at planned shaped
              simp only [PlanShape] at shaped
              cases planned with
              | perform targetBlock foundTarget sizedTarget =>
                  refine NotExhausted.bind ?_
                  intro result
                  refine NotExhausted.bind ?_
                  intro _
                  cases result with
                  | ok answer =>
                      exact advance target (env' ++ [answer]) stack targetBlock foundTarget
                        (by simpa using sizedTarget) ⟨_, memErase, idEq, shaped.1, shaped.2⟩
                  | error error => exact fail_not_exhausted _ _ _ _ _ _
          | performCatch op request target env' onError errorEnv =>
              rw [hplan] at planned shaped
              simp only [PlanShape] at shaped
              cases planned with
              | performCatch targetBlock errorBlock foundTarget sizedTarget foundError
                  sizedError =>
                  refine NotExhausted.bind ?_
                  intro result
                  refine NotExhausted.bind ?_
                  intro _
                  cases result with
                  | ok answer =>
                      exact advance target (env' ++ [answer]) stack targetBlock foundTarget
                        (by simpa using sizedTarget) ⟨_, memErase, idEq, shaped.1, shaped.2.1⟩
                  | error error =>
                      exact advance onError (errorEnv ++ [error]) stack errorBlock foundError
                        (by simpa using sizedError) ⟨_, memErase, idEq, shaped.1, shaped.2.2⟩
          | exhausted site =>
              exact NotExhausted.bind (fun _ => NotExhausted.leaf _ _ rfl)
          | mismatch expected actual =>
              exact NotExhausted.leaf _ _ (RunResult.exhausted_refusal _ _)
          | choose site branch target env' rest =>
              rw [hplan] at planned shaped
              simp only [PlanShape] at shaped
              cases planned with
              | choose targetBlock foundTarget sizedTarget =>
                  refine NotExhausted.bind ?_
                  intro _
                  exact consume target env' rest stack targetBlock foundTarget sizedTarget shaped
      | enter region body args =>
          have erasedEq : eraseBlock flow current
              = { id := current.id, params := current.params, term := .jump body args } := by
            simp [eraseBlock, RegionFlow.eraseTerm, hterm]
          rw [erasedEq] at planned shaped memErase
          dsimp only
          cases hargs : readArgs env args with
          | none => exact NotExhausted.leaf _ _ rfl
          | some values =>
              have planEq : plan alphabet
                  { id := current.id, params := current.params, term := RawTerm.jump body args }
                  env tape = .jump body values := by
                simp [plan, hargs]
              rw [planEq] at planned shaped
              simp only [PlanShape] at shaped
              cases planned with
              | jump targetBlock foundTarget sizedTarget =>
                  refine NotExhausted.bind ?_
                  intro _
                  exact advance body values _ targetBlock foundTarget sizedTarget
                    ⟨_, memErase, idEq, shaped.1, shaped.2⟩
      | acquire operation request release target args =>
          have erasedEq : eraseBlock flow current
              = { id := current.id, params := current.params,
                  term := .perform operation request target args } := by
            simp [eraseBlock, RegionFlow.eraseTerm, hterm]
          rw [erasedEq] at planned shaped memErase
          dsimp only
          cases hop : alphabet.lookup operation <;> cases hrelease : alphabet.lookup release <;>
            cases hrequest : env[request.index]? <;> cases hargs : readArgs env args <;>
            cases hstack : stack <;> dsimp only <;>
            first
              | exact NotExhausted.leaf _ _ rfl
              | (rename_i op releaser requestValue values frame rest
                 have planEq : plan alphabet
                     { id := current.id, params := current.params,
                       term := RawTerm.perform operation request target args } env tape
                     = .perform op requestValue target values := by
                   simp [plan, hop, hrequest, hargs]
                 rw [planEq] at planned shaped
                 simp only [PlanShape] at shaped
                 cases planned with
                 | perform targetBlock foundTarget sizedTarget =>
                     refine NotExhausted.bind ?_
                     intro result
                     refine NotExhausted.bind ?_
                     intro _
                     cases result with
                     | ok answer =>
                         exact advance target (values ++ [answer]) _ targetBlock foundTarget
                           (by simpa using sizedTarget) ⟨_, memErase, idEq, shaped.1, shaped.2⟩
                     | error error => exact fail_not_exhausted _ _ _ _ _ _)
      | leave value =>
          dsimp only
          cases hvalue : env[value.index]? <;> cases hstack : stack <;>
            cases hrow : current.region.bind flow.row? <;> dsimp only <;>
            first
              | exact NotExhausted.leaf _ _ rfl
              | (rename_i v frame rest row
                 have erasedEq : eraseBlock flow current
                     = { id := current.id, params := current.params,
                         term := .jump row.continue_ [value] } := by
                   simp [eraseBlock, RegionFlow.eraseTerm, hterm, hrow]
                 rw [erasedEq] at planned shaped memErase
                 have planEq : plan alphabet
                     { id := current.id, params := current.params,
                       term := RawTerm.jump row.continue_ [value] } env tape
                     = .jump row.continue_ [v] := by
                   simp [plan, readArgs, hvalue]
                 rw [planEq] at planned shaped
                 simp only [PlanShape] at shaped
                 cases planned with
                 | jump targetBlock foundTarget sizedTarget =>
                     refine NotExhausted.bind ?_
                     intro failures
                     cases failures with
                     | nil =>
                         exact advance row.continue_ [v] rest targetBlock foundTarget sizedTarget
                           ⟨_, memErase, idEq, shaped.1, shaped.2⟩
                     | cons error more => exact fail_not_exhausted _ _ _ _ _ _)


/-- Enough fuel for every run of an admitted region flow: the fuel its erasure
needs. `regionLoop` spends one unit per block of `flow.erase` and the region
boundaries are blocks of that graph, so the region layer adds nothing to the
count -- `regionFuelFor flow tape = (tape.length + 1) * flow.blocks.length + 1`
(`regionFuelFor_blocks`). -/
def regionFuelFor (flow : RegionFlow Ty) (tape : Tape) : Nat := fuelFor flow.erase tape

/-- The region flow's own block table gives the same allotment: erasure is one
block per block. -/
theorem regionFuelFor_blocks (flow : RegionFlow Ty) (tape : Tape) :
    regionFuelFor flow tape = (tape.length + 1) * flow.blocks.length + 1 := by
  simp [regionFuelFor, fuelFor, RegionFlow.erase]

/-- The admitted region flow's erasure carries the v2 evidence. -/
theorem regionFlow_erase_wf [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) : FlowWF alphabet flow.flow.erase :=
  flow.erased ▸ erase_wf flow.checked

/-- **DB-04 for the region runner, with the merged failure carrier.** Running
an admitted region flow with the fuel `regionFuelFor` allots never ends at the
fuel frontier. With `regionLoop_frontier_live` this says a fuel frontier is
never what an admitted region run reports at its own allotment. -/
theorem runRegionsCause_fuelFor_finishes {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) :
    ((((runRegionsCause (regionFuelFor flow.flow tape) flow service nameOf tape
      input).run log).run s)).1.1.1.1.exhausted = false := by
  have wf := regionFlow_erase_wf flow
  have entry := wf.entry
  unfold EntryWF at entry
  cases found : lookupBlock flow.flow.erase flow.flow.erase.entry with
  | none => rw [found] at entry; cases entry
  | some erased =>
      rw [found] at entry
      obtain ⟨current, foundCurrent, paramsEq⟩ := block?_of_lookup_erase found
      have sized : ([input] : Env).length = current.params.length := by
        rw [paramsEq, entry]; rfl
      exact regionLoop_budget_not_exhausted wf service nameOf (regionFuelFor flow.flow tape)
        flow.flow.entry [input] tape [] [] current foundCurrent sized
        { nodup := List.nodup_nil
          fresh := List.not_mem_nil
          declared := fun _ hx => absurd hx List.not_mem_nil
          reaches := fun _ hx => absurd hx List.not_mem_nil
          covers := by simp [regionFuelFor, fuelFor] } log s

/-- The wire form: the public region runner at its own allotment never ends at
the fuel frontier. -/
theorem runRegions_fuelFor_finishes {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) :
    ((((runRegions (regionFuelFor flow.flow tape) flow service nameOf tape
      input).run log).run s)).1.1.1.exhausted = false :=
  runRegionsCause_fuelFor_finishes flow service nameOf tape input log s

/-- `runRegionsDefault` is `runRegions` at exactly that fuel, so it too always
finishes. -/
theorem runRegionsDefault_finishes {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) :
    ((((runRegionsDefault flow service nameOf tape input).run log).run s)).1.1.1.exhausted
      = false :=
  runRegions_fuelFor_finishes flow service nameOf tape input log s

/-- The colimit of an admitted region run: the settled observation reached at
the fuel `regionFuelFor` allots. Total, not `Option`. -/
def runRegionsColimitDefault {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) : Observation :=
  runRegionsObservation (regionFuelFor flow.flow tape) flow service nameOf tape input log s

/-- The region colimit is settled: no more fuel can refine it. -/
theorem runRegionsColimitDefault_settled {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) :
    (runRegionsColimitDefault flow service nameOf tape input log s).settled = true := by
  have finishes := runRegionsCause_fuelFor_finishes flow service nameOf tape input log s
  simp only [runRegionsColimitDefault, runRegionsObservation, obsOf]
  rw [observe_settled, finishes]
  rfl

/-- Every smaller fuel is below the region colimit. -/
theorem runRegionsColimitDefault_above {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (fuel : Nat) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) (le : fuel ≤ regionFuelFor flow.flow tape) :
    Observation.le (runRegionsObservation fuel flow service nameOf tape input log s)
      (runRegionsColimitDefault flow service nameOf tape input log s) = true :=
  runRegions_obs_chain le flow service nameOf tape input log s

/-- Every larger fuel observes exactly the region colimit. -/
theorem runRegionsColimitDefault_stable {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {larger : Nat} (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ)
    (le : regionFuelFor flow.flow tape ≤ larger) :
    runRegionsObservation larger flow service nameOf tape input log s =
      runRegionsColimitDefault flow service nameOf tape input log s :=
  (runRegionsChain flow service nameOf tape input log s).stable
    (runRegionsColimitDefault_settled flow service nameOf tape input log s) le

/-- The searched region colimit and the colimit at the allotted fuel agree. -/
theorem runRegionsColimit_eq_default {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {bound : Nat} (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ)
    (le : regionFuelFor flow.flow tape ≤ bound) :
    runRegionsColimit bound flow service nameOf tape input log s =
      some (runRegionsColimitDefault flow service nameOf tape input log s) :=
  Chain.colimit_eq_of_settled (c := runRegionsChain flow service nameOf tape input log s)
    (runRegionsColimitDefault_settled flow service nameOf tape input log s) le

end Effect4.Flow
