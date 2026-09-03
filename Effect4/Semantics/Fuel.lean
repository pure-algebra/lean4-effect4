import Effect4.Semantics.Runs

/-!
# Semantics.Fuel

Owner: the termination argument for the fuel `fuelFor` allots to a checked
flow (plan packet P-T2, law row `run_fuelFor_finishes`).

`fuelFor raw tape = (tape.length + 1) * raw.blocks.length + 1`. The docstring
of `fuelFor` argues informally: between two decisions no block repeats,
because a repeat would be a cycle of the successor graph through non-`choose`
blocks, which `CyclesWF` refuses; every `choose` consumes one tape entry; so
at most `blocks.length` blocks are visited per tape entry, plus one final
segment. This module turns that paragraph into a theorem.

The invariant carried through `loop` is `LoopBudget`: the blocks already
stepped through since the last decision form a duplicate-free list of declared
identities, none of them the current block, each reaching the current block
through non-`choose` edges, and the remaining fuel plus that list's length
covers `(tape.length + 1) * blocks.length + 1`. A non-`choose` step grows the
list by one and spends one fuel; a `choose` step shortens the tape by one and
resets the list, paid for by the `blocks.length` the list could not exceed.
-/

namespace Effect4.Flow

open Effects
open Effects.Trace (Val)

/-! ## Two list facts, proved by induction

`List.Nodup.length_le_of_subset` is in scope but depends on `Classical.choice`;
the trace lane's ceiling is `propext` and `Quot.sound`, so the pigeonhole step
is reproved here by structural induction, as `Effects.RawFlow` does privately
for its own saturation bound. -/

private theorem length_filter_ne {α : Type} [DecidableEq α] {a : α} :
    ∀ {l : List α}, a ∈ l → (l.filter fun x => decide (x ≠ a)).length + 1 ≤ l.length
  | [], mem => absurd mem List.not_mem_nil
  | b :: bs, mem => by
      by_cases eq : b = a
      · subst eq
        rw [List.filter_cons_of_neg (p := fun x => decide (x ≠ b))
          (by rw [decide_eq_false (fun h => h rfl)]; exact Bool.false_ne_true)]
        rw [List.length_cons]
        exact Nat.succ_le_succ (List.length_filter_le _ _)
      · rw [List.filter_cons_of_pos (p := fun x => decide (x ≠ a)) (decide_eq_true eq),
          List.length_cons, List.length_cons]
        have tailMem : a ∈ bs := by
          rcases List.mem_cons.mp mem with h | h
          · exact absurd h.symm eq
          · exact h
        have ih := length_filter_ne tailMem
        omega

/-- A duplicate-free list is no longer than any list containing it. -/
private theorem length_le_of_nodup_subset {α : Type} [DecidableEq α] :
    ∀ {l₁ l₂ : List α}, l₁.Nodup → l₁ ⊆ l₂ → l₁.length ≤ l₂.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, l₂, nodup, sub => by
      have ⟨notMem, nodupTail⟩ := List.nodup_cons.mp nodup
      have aMem : a ∈ l₂ := sub List.mem_cons_self
      have tailSub : l ⊆ l₂.filter fun x => decide (x ≠ a) := by
        intro x hx
        have ne : x ≠ a := fun eq => notMem (eq ▸ hx)
        exact List.mem_filter.mpr ⟨sub (List.mem_cons_of_mem _ hx), decide_eq_true ne⟩
      have ih := length_le_of_nodup_subset nodupTail tailSub
      have bound := length_filter_ne aMem
      rw [List.length_cons]
      omega

/-- A resolved block carries the identity it was looked up by. -/
theorem lookupBlock_id {raw : RawFlow Ty} {id : BlockId} {block : RawBlock Ty}
    (found : lookupBlock raw id = some block) : block.id = id := by
  unfold lookupBlock at found
  have matched := List.find?_some found
  simpa using matched

/-- A resolved identity is one of the declared block identities. -/
theorem mem_blockIds_of_lookup {raw : RawFlow Ty} {id : BlockId} {block : RawBlock Ty}
    (found : lookupBlock raw id = some block) :
    id ∈ raw.blocks.map RawBlock.id :=
  lookupBlock_id found ▸ List.mem_map_of_mem (List.mem_of_find?_eq_some found)

/-! ## What a plan says about the graph and the tape

`plan_checked` already says every continuation of a checked block resolves to
a block of the environment's size. The termination argument needs the two
facts `PlanSized` deliberately forgets: a `jump` or a `perform` leaves the
block along a declared non-`choose` edge, and a `choose` consumes exactly one
tape entry. Both are structural: no admission clause is used. -/

/-- The graph and tape shape of a plan, read off the block's terminator. -/
def PlanShape (term : RawTerm) (tape : Tape) {alphabet : FlowAlphabet Ty} :
    Plan alphabet → Prop
  | .jump target _ => term.isChoose = false ∧ target ∈ term.successors
  | .perform _ _ target _ => term.isChoose = false ∧ target ∈ term.successors
  | .performCatch _ _ target _ onError _ =>
      term.isChoose = false ∧ target ∈ term.successors ∧ onError ∈ term.successors
  | .choose _ _ _ _ rest => rest.length + 1 = tape.length
  | _ => True

/-- Every plan of a block has that block's shape: a non-decision continuation
travels a declared non-`choose` edge, and a decision consumes one tape entry. -/
theorem plan_shape (alphabet : FlowAlphabet Ty) (block : RawBlock Ty) (env : Env) (tape : Tape) :
    PlanShape block.term tape (plan alphabet block env tape) := by
  unfold plan
  cases block.term with
  | ret value =>
      dsimp only
      cases env[value.index]? <;> trivial
  | jump target args =>
      dsimp only
      cases readArgs env args <;>
        simp [PlanShape, RawTerm.isChoose, RawTerm.successors]
  | perform operation request target args =>
      dsimp only
      cases alphabet.lookup operation <;> cases env[request.index]? <;>
        cases readArgs env args <;>
        simp [PlanShape, RawTerm.isChoose, RawTerm.successors]
  | choose decision left right args =>
      dsimp only
      cases readArgs env args with
      | none => trivial
      | some values =>
        dsimp only
        cases readEq : tape.read decision with
        | exhausted => trivial
        | mismatch expected actual => trivial
        | answered branch rest =>
            exact Tape.read_answered_length readEq
  | performCatch operation request target args onError errorArgs =>
      dsimp only
      cases alphabet.lookup operation <;> cases env[request.index]? <;>
        cases readArgs env args <;> cases readArgs env errorArgs <;>
        simp [PlanShape, RawTerm.isChoose, RawTerm.successors]
  | branch test site onTrue onFalse args =>
      dsimp only
      cases readArgs env args with
      | none => trivial
      | some values =>
        dsimp only
        cases readEq : tape.read site with
        | exhausted => trivial
        | mismatch expected actual => trivial
        | answered answer rest =>
            dsimp only
            by_cases agreed : testValue env test = some answer
            · rw [if_pos agreed]; exact Tape.read_answered_length readEq
            · rw [if_neg agreed]; trivial

/-! ## One step of a checked flow makes measurable progress -/


/-- What one checked step leaves behind for the fuel argument: a finished run
never reports fuel exhaustion (only `loop` can), and a continuation either
travels a declared non-`choose` edge leaving the tape untouched, or consumes
exactly one tape entry. Either way it resolves to a well-sized block. -/
def NextProgress (raw : RawFlow Ty) (source : BlockId) (tape : Tape) : Next → Prop
  | .finished result _ => result.exhausted = false
  | .continue_ next env' rest =>
      (∃ current, lookupBlock raw next = some current ∧ env'.length = current.params.length) ∧
      ((rest = tape ∧ EdgeNoChoose raw source next) ∨ rest.length + 1 = tape.length)

/-- One step of a checked flow over a state monad makes progress. -/
theorem step_progress {σ : Type} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) {block : RawBlock Ty} (mem : block ∈ raw.blocks)
    {env : Env} (sized : env.length = block.params.length) (tape : Tape)
    (log : Effect4.Trace.Log) (s : σ) :
    NextProgress raw block.id tape
      (((step alphabet service nameOf block env tape).run log).run s).1.1 := by
  have planned := plan_checked wf mem sized tape
  have shaped := plan_shape alphabet block env tape
  generalize planEq : plan alphabet block env tape = p at planned shaped
  cases planned with
  | ret value =>
      simp [step, planEq, emit_run, NextProgress, RunResult.exhausted, StateT.run_pure, idPure]
  | exhausted site =>
      simp [step, planEq, emit_run, NextProgress, RunResult.exhausted, StateT.run_pure, idPure]
  | mismatch expected actual =>
      simp [step, planEq, NextProgress, RunResult.exhausted_refusal, StateT.run_pure, idPure]
  | jump targetBlock found sizedTarget =>
      simp only [PlanShape] at shaped
      simp only [step, planEq, StateT.run_pure]
      exact ⟨⟨targetBlock, found, sizedTarget⟩,
        Or.inl ⟨rfl, ⟨block, mem, rfl, shaped.1, shaped.2⟩⟩⟩
  | perform targetBlock found sizedTarget =>
      simp only [PlanShape] at shaped
      simp only [step, planEq, StateT.run_bind, StateT.run_lift, StateT.run_pure]
      cases service.pure _ <;>
        simp only [NextProgress, StateT.run_pure, if_true] <;>
        exact ⟨⟨targetBlock, found, by simp [sizedTarget]⟩,
          Or.inl ⟨rfl, ⟨block, mem, rfl, shaped.1, shaped.2⟩⟩⟩
  | choose targetBlock found sizedTarget =>
      simp only [PlanShape] at shaped
      simp only [step, planEq, StateT.run_bind, StateT.run_pure, emit_run]
      exact ⟨⟨targetBlock, found, sizedTarget⟩, Or.inr shaped⟩
  | performCatch targetBlock _ found sizedTarget _ _ =>
      simp only [PlanShape] at shaped
      simp only [step, planEq, StateT.run_bind, StateT.run_lift, StateT.run_pure]
      cases service.pure _ <;>
        simp only [NextProgress, StateT.run_pure, if_true] <;>
        exact ⟨⟨targetBlock, found, by simp [sizedTarget]⟩,
          Or.inl ⟨rfl, ⟨block, mem, rfl, shaped.1, shaped.2.1⟩⟩⟩

/-! ## The allotted fuel always suffices -/

/-- The loop invariant of the fuel argument. `visited` is the list of blocks
already stepped through since the last decision: duplicate-free, all declared,
none of them the block about to run, each reaching it through non-`choose`
edges. `covers` is the budget: the fuel still in hand plus the blocks already
walked in this segment covers `fuelFor`'s allotment for the remaining tape. -/
structure LoopBudget (raw : RawFlow Ty) (block : BlockId) (tape : Tape)
    (visited : List BlockId) (fuel : Nat) : Prop where
  nodup : visited.Nodup
  fresh : block ∉ visited
  declared : ∀ x, x ∈ visited → x ∈ raw.blocks.map RawBlock.id
  reaches : ∀ x, x ∈ visited → ReachableNoChoose raw x block
  covers : (tape.length + 1) * raw.blocks.length + 1 ≤ fuel + visited.length

/-- A segment between two decisions can never have walked every declared
block: the current block is declared and is not among the ones already
walked. -/
theorem LoopBudget.segment_lt {raw : RawFlow Ty} {block : BlockId} {tape : Tape}
    {visited : List BlockId} {fuel : Nat} {current : RawBlock Ty}
    (found : lookupBlock raw block = some current)
    (budget : LoopBudget raw block tape visited fuel) :
    visited.length + 1 ≤ raw.blocks.length := by
  have nodup : (block :: visited).Nodup := List.nodup_cons.mpr ⟨budget.fresh, budget.nodup⟩
  have sub : (block :: visited) ⊆ raw.blocks.map RawBlock.id := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mem_blockIds_of_lookup found
    · exact budget.declared x hx
  have counted := length_le_of_nodup_subset nodup sub
  simpa [List.length_cons, List.length_map] using counted

/-- The fuel argument: a checked flow walked under `LoopBudget` never
exhausts its fuel. Every non-`choose` step spends one unit and grows the
duplicate-free segment by one; `CyclesWF` keeps the segment shorter than the
block table, so every `choose` step buys back the whole `blocks.length` it
spends against one tape entry. -/
theorem loop_budget_not_exhausted {σ : Type} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (visited : List BlockId)
      (log : Effect4.Trace.Log) (s : σ) (current : RawBlock Ty),
      lookupBlock raw block = some current →
      env.length = current.params.length →
      LoopBudget raw block tape visited fuel →
      (((loop alphabet raw service nameOf fuel block env tape).run log).run s).1.1.1.exhausted
        = false := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape visited log s current found _ budget
      exfalso
      have bound := budget.segment_lt found
      have covers := budget.covers
      have pos : raw.blocks.length ≤ (tape.length + 1) * raw.blocks.length :=
        Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
      omega
  | succ fuel ih =>
      intro block env tape visited log s current found sized budget
      have bound := budget.segment_lt found
      have mem : current ∈ raw.blocks := List.mem_of_find?_eq_some found
      have idEq : current.id = block := lookupBlock_id found
      have stepped := step_progress wf service nameOf mem sized tape log s
      rw [idEq] at stepped
      simp only [loop, found, StateT.run_bind]
      generalize ((step alphabet service nameOf current env tape).run log).run s = outcome
        at stepped ⊢
      rcases outcome with ⟨⟨next, log'⟩, s'⟩
      cases next with
      | finished result rest =>
          simpa [idBind, idPure, NextProgress, StateT.run_pure] using stepped
      | continue_ nextBlock env' rest =>
          obtain ⟨⟨target, foundTarget, sizedTarget⟩, progress⟩ := stepped
          simp only [idBind]
          rcases progress with ⟨rfl, edge⟩ | consumed
          · -- a non-`choose` edge: the tape is untouched and the segment grows
            refine ih nextBlock env' rest (block :: visited) log' s' target foundTarget
              sizedTarget ⟨?_, ?_, ?_, ?_, ?_⟩
            · exact List.nodup_cons.mpr ⟨budget.fresh, budget.nodup⟩
            · intro inSegment
              have reachBack : ReachableNoChoose raw nextBlock block := by
                rcases List.mem_cons.mp inSegment with eq | inVisited
                · cases eq; exact .refl _
                · exact budget.reaches nextBlock inVisited
              exact wf.cycles block nextBlock edge reachBack
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact mem_blockIds_of_lookup found
              · exact budget.declared x hx
            · intro x hx
              rcases List.mem_cons.mp hx with rfl | hx
              · exact .step (.refl _) edge
              · exact .step (budget.reaches x hx) edge
            · have covers := budget.covers
              simp only [List.length_cons]
              omega
          · -- a `choose`: one tape entry is consumed and the segment restarts
            refine ih nextBlock env' rest [] log' s' target foundTarget sizedTarget
              ⟨List.nodup_nil, List.not_mem_nil, ?_, ?_, ?_⟩
            · intro x hx; cases hx
            · intro x hx; cases hx
            · have covers := budget.covers
              have expand : (tape.length + 1) * raw.blocks.length
                  = (rest.length + 1) * raw.blocks.length + raw.blocks.length := by
                rw [← consumed]
                simp [Nat.add_mul]
              simp only [List.length_nil]
              omega

/-- The fuel `fuelFor` allots to a checked flow always suffices: a run at that
fuel never ends at the fuel frontier. -/
theorem loop_fuelFor_not_exhausted {σ : Type} {alphabet : FlowAlphabet Ty} {raw : RawFlow Ty}
    (wf : FlowWF alphabet raw) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (block : BlockId) (env : Env) (tape : Tape)
    (log : Effect4.Trace.Log) (s : σ) (current : RawBlock Ty)
    (found : lookupBlock raw block = some current)
    (sized : env.length = current.params.length) :
    (((loop alphabet raw service nameOf (fuelFor raw tape) block env tape).run log).run s).1.1.1.exhausted
      = false :=
  loop_budget_not_exhausted wf service nameOf (fuelFor raw tape) block env tape [] log s current
    found sized
    { nodup := List.nodup_nil
      fresh := List.not_mem_nil
      declared := fun _ hx => absurd hx List.not_mem_nil
      reaches := fun _ hx => absurd hx List.not_mem_nil
      covers := by simp [fuelFor] }

/-- The public form: running an admitted flow with the fuel `fuelFor` allots
never ends at the fuel frontier. With `run_checked_not_stuck` this leaves an
admitted run exactly three kinds of end: a value, a refusal (a foreign tape or
a branch the value disagrees with), or an unanswered decision. -/
theorem run_fuelFor_finishes {σ : Type} {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s).1.1.exhausted
      = false := by
  have wf := erase_wf flow
  have entry := wf.entry
  unfold EntryWF at entry
  cases found : lookupBlock flow.erase flow.erase.entry with
  | none => rw [found] at entry; cases entry
  | some current =>
      rw [found] at entry
      have sized : ([input] : Env).length = current.params.length := by rw [entry]; rfl
      have finished := loop_fuelFor_not_exhausted wf service nameOf flow.erase.entry [input] tape
        log s current found sized
      unfold run runTape
      simpa [StateT.run_map, idMap] using finished

/-- `runDefault` is `run` at exactly that fuel, so it too always finishes. -/
theorem runDefault_finishes {σ : Type} {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    (((runDefault flow service nameOf tape input).run log).run s).1.1.exhausted = false :=
  run_fuelFor_finishes flow service nameOf tape input log s

/-- Any fuel at least `fuelFor`'s allotment also finishes: `run_fuel_mono`
carries the result up, one unit at a time. -/
theorem run_fuel_ge_finishes {σ : Type} {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    ∀ (extra : Nat),
      (((run (fuelFor flow.erase tape + extra) flow service nameOf tape input).run log).run s).1.1.exhausted
        = false := by
  intro extra
  induction extra with
  | zero => simpa using run_fuelFor_finishes flow service nameOf tape input log s
  | succ extra ih =>
      have step := run_fuel_mono (fuelFor flow.erase tape + extra) flow service nameOf tape input
        log s ih
      have shift : fuelFor flow.erase tape + (extra + 1) = fuelFor flow.erase tape + extra + 1 := rfl
      rw [shift, step]
      exact ih

/-! ## The plain runner never fails

`RunResult.failed` belongs to the region runner (`Effect4/Flow/Region.lean`):
only a `RegionService` can report an aborting operation. The plain `step` has
no shape that produces it, and `loop` only forwards what `step` finished
with. -/

/-- A step of the plain runner never finishes with a failure. -/
def NextNotFailed : Next → Prop
  | .finished result _ => ∀ error, result ≠ .failed error
  | .continue_ .. => True

theorem step_not_failed {σ : Type} {alphabet : FlowAlphabet Ty}
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String)
    (block : RawBlock Ty) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ) :
    NextNotFailed (((step alphabet service nameOf block env tape).run log).run s).1.1 := by
  unfold step
  cases plan alphabet block env tape with
  | stuck => simp [NextNotFailed, StateT.run_pure, idPure]
  | ret value => simp [NextNotFailed, emit_run, StateT.run_pure, idPure]
  | jump target env' => simp [NextNotFailed, StateT.run_pure, idPure]
  | perform op request target env' =>
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure]
      cases service.pure op <;> simp [NextNotFailed, emit_run, StateT.run_pure, idBind, idPure]
  | exhausted site =>
      simp [NextNotFailed, emit_run, StateT.run_pure, idPure]
  | mismatch expected actual => simp [NextNotFailed, StateT.run_pure, idPure]
  | choose site branch target env' rest =>
      simp [NextNotFailed, emit_run, StateT.run_pure, idPure]
  | performCatch op request target env' onError errorEnv =>
      simp only [StateT.run_bind, StateT.run_lift, StateT.run_pure]
      cases service.pure op <;> simp [NextNotFailed, emit_run, StateT.run_pure, idBind, idPure]

theorem loop_not_failed {σ : Type} (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) :
    ∀ (fuel : Nat) (block : BlockId) (env : Env) (tape : Tape) (log : Effect4.Trace.Log) (s : σ)
      (error : Val),
      (((loop alphabet raw service nameOf fuel block env tape).run log).run s).1.1.1
        ≠ .failed error := by
  intro fuel
  induction fuel with
  | zero =>
      intro block env tape log s error
      simp [loop, emit_run, StateT.run_pure, idPure]
  | succ fuel ih =>
      intro block env tape log s error
      cases found : lookupBlock raw block with
      | none => simp [loop, found, StateT.run_pure, idPure]
      | some current =>
          have notFailed := step_not_failed service nameOf current env tape log s
          simp only [loop, found, StateT.run_bind]
          generalize ((step alphabet service nameOf current env tape).run log).run s = outcome
            at notFailed ⊢
          rcases outcome with ⟨⟨next, log'⟩, s'⟩
          cases next with
          | finished result rest =>
              simpa [idBind, idPure, NextNotFailed, StateT.run_pure] using notFailed error
          | continue_ nextBlock env' rest =>
              simpa [idBind] using ih nextBlock env' rest log' s' error

/-- The public form: a plain run never reports a failure. -/
theorem run_not_failed {σ : Type} {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedFlow alphabet) (service : FlowService alphabet (StateT σ Id))
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val)
    (log : Effect4.Trace.Log) (s : σ) (error : Val) :
    (((run fuel flow service nameOf tape input).run log).run s).1.1 ≠ .failed error := by
  have notFailed := loop_not_failed alphabet flow.erase service nameOf fuel flow.erase.entry
    [input] tape log s error
  unfold run runTape
  simpa [StateT.run_map, idMap] using notFailed

/-- What is left. With `run_checked_not_stuck` ruling out `stuck`, `run_not_failed`
ruling out the region runner's failure, and
`run_fuelFor_finishes` ruling out the fuel frontier, an admitted run at the
allotted fuel ends in exactly one of four ways: a value, the unanswered
decision frontier, a foreign tape refused at its site, or a Flow v3 `branch`
refused because the value disagrees with the tape's own entry. The tape, not
the fuel, is the only remaining source of a live frontier. -/
theorem run_fuelFor_answered {σ : Type} {alphabet : FlowAlphabet Ty} (flow : CheckedFlow alphabet)
    (service : FlowService alphabet (StateT σ Id)) (nameOf : alphabet.Op → String) (tape : Tape)
    (input : Val) (log : Effect4.Trace.Log) (s : σ) :
    (∃ value,
        (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s).1.1
          = .done value) ∨
      (∃ site,
        (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s).1.1
          = .frontier (.unansweredDecision site)) ∨
      (∃ expected actual,
        (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s).1.1
          = .refusedSite expected actual) ∨
      (∃ site,
        (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s).1.1
          = .refusedValue site) := by
  have notExhausted := run_fuelFor_finishes flow service nameOf tape input log s
  have notStuck := run_checked_not_stuck (fuelFor flow.erase tape) flow service nameOf tape input
    log s
  have notFailed := fun error => run_not_failed (fuelFor flow.erase tape) flow service nameOf tape
    input log s error
  generalize (((run (fuelFor flow.erase tape) flow service nameOf tape input).run log).run s).1.1
    = result at notExhausted notStuck notFailed ⊢
  cases result with
  | done value => exact Or.inl ⟨value, rfl⟩
  | failed error => exact absurd rfl (notFailed error)
  | refusedSite expected actual => exact Or.inr (Or.inr (Or.inl ⟨expected, actual, rfl⟩))
  | refusedValue site => exact Or.inr (Or.inr (Or.inr ⟨site, rfl⟩))
  | frontier reason =>
      cases reason with
      | fuel block => simp [RunResult.exhausted] at notExhausted
      | unansweredDecision site => exact Or.inr (Or.inl ⟨site, rfl⟩)
      | stuck block => simp [RunResult.stuck] at notStuck

end Effect4.Flow
