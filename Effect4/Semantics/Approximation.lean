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
function of it. The region runner has no fuel-sufficiency theorem yet, so
`runRegionsColimit` stays an `Option`; `Chain.colimit_of_settles` is the way to
conclude it is `some`.

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
  | refused expected actual => rfl
  | frontier reason => cases reason <;> rfl

theorem observe_terminal {result : RunResult} (log : Effect4.Trace.Log)
    (h : result.exhausted = false) : observe result log = .terminal result log := by
  cases result with
  | done value => rfl
  | failed error => rfl
  | refused expected actual => rfl
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
      | refused expected actual => simp [observe] at this; simp [this.1, this.2]
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
      have h : Next.finished (RunResult.refused expected actual) tape =
          Next.finished result rest := finished
      injection h with h1 _
      rw [← h1]
      rfl
  | choose site branch target env' rest' =>
      simp only [step, planEq] at finished
      exact Next.noConfusion
        (show Next.continue_ target env' rest' = Next.finished result rest from finished)

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
operation unwinds every open region and ends the run `failed`. The laws
transfer, and the transfer is stated below as theorems rather than as a
promise.

The proofs do not repeat the plain runner's computation. They go through three
properties of a run computation, each closed under `bind`, so each law is one
structural walk over `regionLoop`'s branches:

* `Appends` -- the computation only appends to the log;
* `Punctuates` -- when it reports a fuel frontier, its log ends with the marker
  it appended (this is what makes stripping the marker safe);
* `Below` -- one computation observes below another at every log and state.

`closeFrame` and `unwind` iterate over releases and frames, so `Appends.forIn`
carries the property through a `for` loop. What regions add over the plain
runner -- failure, finalizers, the region stack -- changes none of the laws:
`RunResult.failed` is terminal, exactly like `done` and `refused`. The one
thing regions do not yet have is a fuel-sufficiency theorem
(`Effect4/Semantics/Fuel.lean` covers `loop` only, and `regionLoop` spends fuel
on region boundaries as well), so the region colimit stays an `Option` where
`runColimitDefault` is total. -/

/-- A run computation only appends to the log: it never rewrites or drops a row
an earlier step emitted. -/
def Appends {σ : Type} {α : Type} (m : RunM (StateT σ Id) α) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ), ∃ events, ((m.run log).run s).1.2 = log ++ events

namespace Appends

theorem pure {σ α : Type} (a : α) : Appends (σ := σ) (Pure.pure a) :=
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

theorem forIn {σ : Type} {α : Type u} {β : Type} (body : α → β → RunM (StateT σ Id) (ForInStep β))
    (hbody : ∀ a b, Appends (body a b)) :
    ∀ (xs : List α) (init : β), Appends (ForIn.forIn xs init body) := by
  intro xs
  induction xs with
  | nil => intro init; simpa using Appends.pure init
  | cons x rest ih =>
      intro init
      simp only [List.forIn_cons]
      refine Appends.bind (hbody x init) ?_
      intro step
      cases step with
      | done b => simpa using Appends.pure b
      | yield b => simpa using ih b

end Appends


theorem logOperation_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (op : alphabet.Op) (request : Val)
    (result : Except Val Val) : Appends (logOperation service nameOf op request result) := by
  unfold logOperation
  split
  · exact Appends.pure ()
  · refine Appends.bind (Appends.emit' _) ?_
    intro _
    cases result with
    | ok answer => exact Appends.emit' _
    | error error => exact Appends.emit' _

theorem closeFrame_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (frame : Frame alphabet) (exit : Outcome Val) :
    Appends (closeFrame service nameOf frame exit) := by
  unfold closeFrame
  refine Appends.bind (Appends.emit' _) ?_
  intro _
  refine Appends.bind (Appends.forIn _ ?_ _ _) ?_
  · intro x acc
    cases x with
    | mk release resource =>
        refine Appends.bind (Appends.emit' _) ?_
        intro _
        refine Appends.bind (Appends.lift _) ?_
        intro result
        refine Appends.bind (logOperation_appends service nameOf release resource result) ?_
        intro _
        cases result with
        | ok answer => exact Appends.pure _
        | error error =>
            dsimp only
            by_cases isNone : acc.isNone = true
            · rw [if_pos isNone]; exact Appends.pure _
            · rw [if_neg isNone]; exact Appends.pure _
  · intro b
    exact Appends.pure b

theorem unwind_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (stack : List (Frame alphabet)) (error : Val) :
    Appends (unwind service nameOf stack error) := by
  unfold unwind
  refine Appends.bind (Appends.forIn _ ?_ _ _) ?_
  · intro frame acc
    refine Appends.bind (closeFrame_appends service nameOf frame (.failure error)) ?_
    intro _
    exact Appends.pure _
  · intro _
    exact Appends.pure _

theorem fail_appends {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (stack : List (Frame alphabet)) (error : Val) (tape : Tape) :
    Appends (fail service nameOf stack error tape) := by
  unfold fail
  refine Appends.bind (unwind_appends service nameOf stack error) ?_
  intro _
  refine Appends.bind (Appends.emit' _) ?_
  intro _
  exact Appends.pure _

/-- The observation a finished run computation makes from a starting log and
state. -/
def obsOf {σ : Type} (m : RunM (StateT σ Id) (RunResult × Tape)) (log : Effect4.Trace.Log)
    (s : σ) : Observation :=
  observe (((m.run log).run s)).1.1.1 (((m.run log).run s)).1.2

/-- A run computation punctuates its fuel frontier: whenever it reports one,
its log ends with the marker `loop` appended. -/
def Punctuates {σ : Type} (m : RunM (StateT σ Id) (RunResult × Tape)) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ),
    (((m.run log).run s)).1.1.1.exhausted = true →
      ∃ events, (((m.run log).run s)).1.2 = (log ++ events) ++ [Effects.Trace.Event.frontier]

/-- One run computation observes below another at every starting log and
state. -/
def Below {σ : Type} (m m' : RunM (StateT σ Id) (RunResult × Tape)) : Prop :=
  ∀ (log : Effect4.Trace.Log) (s : σ), Observation.le (obsOf m log s) (obsOf m' log s) = true

namespace Punctuates

theorem pure_of_settled {σ : Type} {result : RunResult} {tape : Tape}
    (settled : result.exhausted = false) : Punctuates (σ := σ) (Pure.pure (result, tape)) := by
  intro log s exhausted
  rw [show (((Pure.pure (result, tape) :
      RunM (StateT σ Id) (RunResult × Tape)).run log).run s).1.1.1 = result from rfl] at exhausted
  rw [settled] at exhausted
  cases exhausted

theorem bind {σ α : Type} {m : RunM (StateT σ Id) α} {f : α → RunM (StateT σ Id) (RunResult × Tape)}
    (hm : Appends m) (hf : ∀ a, Punctuates (f a)) : Punctuates (m >>= f) := by
  intro log s exhausted
  obtain ⟨events, eq⟩ := hm log s
  have run_eq : (((m >>= f).run log).run s)
      = ((f (((m.run log).run s)).1.1).run (((m.run log).run s)).1.2).run
          (((m.run log).run s)).2 := rfl
  rw [run_eq] at exhausted ⊢
  obtain ⟨events', eq'⟩ :=
    hf (((m.run log).run s)).1.1 (((m.run log).run s)).1.2 (((m.run log).run s)).2 exhausted
  exact ⟨events ++ events', by rw [eq', eq]; simp [List.append_assoc]⟩

end Punctuates

/-- A computation that only appends and punctuates its frontier observes a log
extending the one it started from. -/
theorem obsOf_extends {σ : Type} {m : RunM (StateT σ Id) (RunResult × Tape)} (ha : Appends m)
    (hp : Punctuates m) (log : Effect4.Trace.Log) (s : σ) :
    logPrefix log (obsOf m log s).log = true := by
  obtain ⟨events, eq⟩ := ha log s
  cases exhausted : (((m.run log).run s)).1.1.1.exhausted with
  | false =>
      have terminal := observe_terminal (result := (((m.run log).run s)).1.1.1)
        (((m.run log).run s)).1.2 exhausted
      rw [obsOf, terminal]
      simp only [Observation.log]
      rw [eq]
      exact logPrefix_append log events
  | true =>
      obtain ⟨events', eq'⟩ := hp log s exhausted
      have fuel : ∃ block, (((m.run log).run s)).1.1.1 = .frontier (.fuel block) := by
        generalize (((m.run log).run s)).1.1.1 = result at exhausted
        cases result with
        | done value => cases exhausted
        | failed error => cases exhausted
        | refused expected actual => cases exhausted
        | frontier reason =>
            cases reason with
            | fuel block => exact ⟨block, rfl⟩
            | unansweredDecision site => cases exhausted
            | stuck block => cases exhausted
      obtain ⟨block, isFuel⟩ := fuel
      rw [obsOf, isFuel, eq', observe_fuel]
      simp only [Observation.log]
      exact logPrefix_append log events'

namespace Below

theorem refl {σ : Type} (m : RunM (StateT σ Id) (RunResult × Tape)) : Below m m :=
  fun _ _ => Observation.le_refl _

theorem bind {σ α : Type} {m : RunM (StateT σ Id) α}
    {f g : α → RunM (StateT σ Id) (RunResult × Tape)} (h : ∀ a, Below (f a) (g a)) :
    Below (m >>= f) (m >>= g) := by
  intro log s
  exact h (((m.run log).run s)).1.1 (((m.run log).run s)).1.2 (((m.run log).run s)).2

/-- The fuel-zero computation is below every computation that only appends and
punctuates: that is the base case of every monotonicity induction. -/
theorem frontier {σ : Type} {block : BlockId} {tape : Tape}
    {m : RunM (StateT σ Id) (RunResult × Tape)} (ha : Appends m) (hp : Punctuates m) :
    Below (do emit Effects.Trace.Event.frontier;
              pure (RunResult.frontier (Frontier.fuel block), tape)) m := by
  intro log s
  have left : obsOf (σ := σ)
      (do emit Effects.Trace.Event.frontier;
          pure (RunResult.frontier (Frontier.fuel block), tape)) log s = .live log := by
    show observe (RunResult.frontier (Frontier.fuel block)) (log ++ [Effects.Trace.Event.frontier])
      = .live log
    exact observe_fuel block log
  rw [left, Observation.live_le_iff]
  exact obsOf_extends ha hp log s

end Below


theorem regionLoop_appends {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet)),
      Appends (regionLoop alphabet flow service nameOf fuel block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape stack
      unfold regionLoop
      exact Appends.bind (Appends.emit' _) (fun _ => Appends.pure _)
  | succ fuel ih =>
      intro block env tape stack
      unfold regionLoop
      split
      · exact Appends.pure _
      · dsimp only
        split
        · split
          · exact Appends.pure _
          · exact Appends.bind (Appends.emit' _) (fun _ => Appends.pure _)
          · exact ih _ _ _ _
          · refine Appends.bind (Appends.lift _) ?_
            intro result
            refine Appends.bind (logOperation_appends _ _ _ _ _) ?_
            intro _
            split
            · exact ih _ _ _ _
            · exact fail_appends _ _ _ _ _
          · exact Appends.bind (Appends.emit' _) (fun _ => Appends.pure _)
          · exact Appends.pure _
          · refine Appends.bind (Appends.emit' _) ?_
            intro _
            exact ih _ _ _ _
        · split
          · exact Appends.pure _
          · refine Appends.bind (Appends.emit' _) ?_
            intro _
            exact ih _ _ _ _
        · split
          · refine Appends.bind (Appends.lift _) ?_
            intro result
            refine Appends.bind (logOperation_appends _ _ _ _ _) ?_
            intro _
            split
            · exact ih _ _ _ _
            · exact fail_appends _ _ _ _ _
          · exact Appends.pure _
        · split
          · refine Appends.bind (closeFrame_appends _ _ _ _) ?_
            intro outcome
            split
            · exact ih _ _ _ _
            · exact fail_appends _ _ _ _ _
          · exact Appends.pure _

theorem fail_punctuates {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (stack : List (Frame alphabet)) (error : Val) (tape : Tape) :
    Punctuates (fail service nameOf stack error tape) := by
  unfold fail
  refine Punctuates.bind (unwind_appends service nameOf stack error) ?_
  intro _
  refine Punctuates.bind (Appends.emit' _) ?_
  intro _
  exact Punctuates.pure_of_settled rfl

theorem regionLoop_punctuates {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet)),
      Punctuates (regionLoop alphabet flow service nameOf fuel block env tape stack) := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape stack log s _
      refine ⟨[], ?_⟩
      show log ++ [Effects.Trace.Event.frontier]
        = (log ++ []) ++ [Effects.Trace.Event.frontier]
      simp
  | succ fuel ih =>
      intro block env tape stack
      unfold regionLoop
      split
      · exact Punctuates.pure_of_settled rfl
      · dsimp only
        split
        · split
          · exact Punctuates.pure_of_settled rfl
          · exact Punctuates.bind (Appends.emit' _) (fun _ => Punctuates.pure_of_settled rfl)
          · exact ih _ _ _ _
          · refine Punctuates.bind (Appends.lift _) ?_
            intro result
            refine Punctuates.bind (logOperation_appends _ _ _ _ _) ?_
            intro _
            split
            · exact ih _ _ _ _
            · exact fail_punctuates _ _ _ _ _
          · exact Punctuates.bind (Appends.emit' _) (fun _ => Punctuates.pure_of_settled rfl)
          · exact Punctuates.pure_of_settled rfl
          · refine Punctuates.bind (Appends.emit' _) ?_
            intro _
            exact ih _ _ _ _
        · split
          · exact Punctuates.pure_of_settled rfl
          · refine Punctuates.bind (Appends.emit' _) ?_
            intro _
            exact ih _ _ _ _
        · split
          · refine Punctuates.bind (Appends.lift _) ?_
            intro result
            refine Punctuates.bind (logOperation_appends _ _ _ _ _) ?_
            intro _
            split
            · exact ih _ _ _ _
            · exact fail_punctuates _ _ _ _ _
          · exact Punctuates.pure_of_settled rfl
        · split
          · refine Punctuates.bind (closeFrame_appends _ _ _ _) ?_
            intro outcome
            split
            · exact ih _ _ _ _
            · exact fail_punctuates _ _ _ _ _
          · exact Punctuates.pure_of_settled rfl

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
      show Below (do emit Effects.Trace.Event.frontier;
                     pure (RunResult.frontier (Frontier.fuel block), tape)) _
      exact Below.frontier (regionLoop_appends flow service nameOf k block env tape stack)
        (regionLoop_punctuates flow service nameOf k block env tape stack)
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
                     intro outcome
                     cases outcome with
                     | none => exact ih _ _ _ _ _
                     | some error => exact Below.refl _)

/-- The observation a fuelled region run makes. -/
def regionObservation {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (fuel : Nat)
    (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) : Observation :=
  obsOf (regionLoop alphabet flow service nameOf fuel block env tape stack) log s

/-- Monotonicity for the region loop: the same law as `loop_obs_mono`, proved
by the same induction over the same three properties. -/
theorem region_obs_mono {σ : Type} {alphabet : FlowAlphabet Ty} (flow : RegionFlow Ty)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (fuel k : Nat) (block : BlockId) (env : Env) (tape : Tape) (stack : List (Frame alphabet))
    (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (regionObservation flow service nameOf fuel block env tape stack log s)
      (regionObservation flow service nameOf (fuel + k) block env tape stack log s) = true :=
  regionLoop_below flow service nameOf fuel k block env tape stack log s

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

/-- The observation a fuelled run of an admitted region flow makes. -/
def runRegionsObservation {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) : Observation :=
  obsOf (runRegions fuel flow service nameOf tape input) log s

theorem runRegionsObservation_eq {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (fuel : Nat) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    runRegionsObservation fuel flow service nameOf tape input log s =
      regionObservation flow.flow service nameOf fuel flow.flow.entry [input] tape [] log s := rfl

/-- The chain of finite approximations of an admitted region run. -/
def runRegionsChain {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log)
    (s : σ) : Chain where
  observation fuel := runRegionsObservation fuel flow service nameOf tape input log s
  mono le := region_obs_chain flow.flow service nameOf le flow.flow.entry [input] tape [] log s

theorem runRegions_obs_mono {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel k : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    Observation.le (runRegionsObservation fuel flow service nameOf tape input log s)
      (runRegionsObservation (fuel + k) flow service nameOf tape input log s) = true :=
  region_obs_mono flow.flow service nameOf fuel k flow.flow.entry [input] tape [] log s

/-- A settled region observation is the observation of every larger fuel. -/
theorem runRegions_obs_stable {σ : Type} [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    {fuel larger : Nat} (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ)
    (settled : (runRegionsObservation fuel flow service nameOf tape input log s).settled = true)
    (le : fuel ≤ larger) :
    runRegionsObservation larger flow service nameOf tape input log s =
      runRegionsObservation fuel flow service nameOf tape input log s :=
  (runRegionsChain flow service nameOf tape input log s).stable settled le

/-- The colimit of an admitted region run, searched below a bound. It stays an
`Option`: `Effect4/Semantics/Fuel.lean` proves that `fuelFor` suffices for the
plain runner only, and the region loop spends fuel on region boundaries too, so
no fuel is yet known to suffice for it. -/
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

end Effect4.Flow
