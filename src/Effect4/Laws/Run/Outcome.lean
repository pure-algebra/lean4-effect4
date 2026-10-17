import Effect4.Laws.Api.SessionMeaningLoop
import Effect4.Laws.Program.CallChain

/-!
# Run.Outcome — a session's outcome is its call chain's

`Effect4.Program.Chain` (`src/Effect4/Laws/Program/CallChain.lean`) reads a behaviour as a chain
of finite call trees, with three outcomes under a host: it finishes, waits or diverges. This
module reads the loop session theorems as outcomes of the program's chain (`effChain`) under the
session's host:

- a driven run that exits is the chain finishing (`runWith_finishes`, from `runWith_denotesB`);
- a call the run waits on, which the host leaves unanswered, is the chain waiting
  (`frontier_waits`, from `rows_loop_frontier_host`);
- so a diverging chain has no exiting run and no such wait (`runWith_exit_of_diverges`,
  `frontier_of_diverges`);
- an equivalent program finishes where the run exits (`effEquiv_runWith`).

The converse, that a run which neither exits nor waits at every budget is a diverging chain, is
the planned goal `rows_divergence_adequate`.

Placement (`AGENTS.md`, five points), shared by the theorems below:

1. Concept `host-session-protocol` (concept 9 of `docs/core/semantics.md`), the property that the
   session's outcome under its host is its call chain's outcome.
2. Questions: the proposed claim `rows-loop-outcome` (R6, R12) and the planned goal
   `rows-divergence-adequate` (R12).
3. Reach: the row fragment with loops (`LoopedRows`, `LoopedDataRows`), a reactor inside the
   envelope that answers with exits, every budget, every round count.
4. Does not establish: that a drive finishes, that its rounds or budget suffice, or anything of a
   fork, a scope or an interruption. The host boundary stays where `docs/core/host-boundary.md`
   puts it.
5. Unlocks: R12's divergence adequacy at the driver, and rewrites of a program that keep its
   session theorems.
-/

set_option autoImplicit false

namespace Effect4.Run

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-- **A driven run's exit is its chain's finish.** Open a program of the row fragment with
loops and drive it with a reactor inside the envelope that answers with exits. When the run is
funded, at rest and its root exited, the program's chain finishes under the reactor read as a
host, with the root's exit, the run's stores and the drive's state. Placement: concept
`host-session-protocol`, the proposed claim `rows-loop-outcome`, role simulation; requirement
R6. Route: `runWith_denotesB` at its lower bound. Consumer: `runWith_exit_of_diverges` and
`effEquiv_runWith`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem runWith_finishes {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.app) (hexits : r.ExitsOnly)
    (hroot : LoopedRows b.program = true) (hfrag : LoopedDataRows b.table b.program = true)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r st id budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b r st id budget rounds).1.exit = some ex) :
    (effChain b.table b.program []).Finishes (rowsHost (reactorHost b.table r))
      (Stores.empty, st) ex
      ((Run.runWith b r st id budget rounds).1.machine.state, (Run.runWith b r st id budget rounds).2) := by
  obtain ⟨lower, hlow⟩ :=
    runWith_denotesB b r st id budget rounds henv hexits hroot hfrag hfund hrest ex hex
  exact ⟨lower, hlow lower (Nat.le_refl lower)⟩

/-- **A diverging chain has no exiting run**: under any budget and round count, a funded run at
rest whose program's chain diverges under the reactor has no exit. Placement: concept
`host-session-protocol`, the proposed claim `rows-loop-outcome`, role safety; requirement R12.
Route: an exit is the chain's finish (`runWith_finishes`), and a finish excludes divergence
(`Chain.Finishes.not_diverges`). It does not establish that such a run exists. Consumer: R12's
divergence adequacy, with the planned goal `rows_divergence_adequate`. -/
@[semantics "host-session-protocol" (requirement := R12)]
theorem runWith_exit_of_diverges {σ : Type} (b : Api.Built) (r : Reactor σ) (st : σ)
    (id : String) (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.app)
    (hexits : r.ExitsOnly) (hroot : LoopedRows b.program = true)
    (hfrag : LoopedDataRows b.table b.program = true)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r st id budget rounds).1 = true)
    (hdiv : (effChain b.table b.program []).Diverges (rowsHost (reactorHost b.table r))
      (Stores.empty, st)) :
    (Run.runWith b r st id budget rounds).1.exit = none := by
  rcases hex : (Run.runWith b r st id budget rounds).1.exit with _ | ex
  · rfl
  · exact absurd hdiv
      (runWith_finishes b r st id budget rounds henv hexits hroot hfrag hfund hrest ex hex).not_diverges

/-- A wait of the detailed observation is a wait of the budgeted run under the host. -/
theorem hostRunB_none_of_waiting {σ : Type} {table : RowTable}
    (host : Effects.Comodel (RowSig table) σ) (k : Nat) (e : NativeEff) (env : List Val)
    (s : Stores) (st : σ) {row : Nat} {request : Val} {s' : Stores} {st' : σ}
    (h : observeRows host (denoteRowsB table k e env) s st = ⟨.waiting row request, s', st'⟩) :
    hostRunB host k e env s st = none := by
  have hp := observeRows_project host (denoteRowsB table k e env) s st
  rw [h] at hp
  have hm : meaningUnderB host k e env s st = none := hp
  rw [meaningUnderB_eq_hostRunB] at hm
  rcases hr : hostRunB host k e env s st with _ | x
  · rfl
  · rw [hr] at hm
    cases hm

/-- **A frontier is the chain's wait.** For a recorded run of the row fragment with loops that
is funded, at rest and driven by a host, under any host whose answers are the run's: each call
the machine waits on is a host row, and where the host leaves it unanswered the program's chain
waits. Placement: concept `host-session-protocol`, the proposed claim `rows-loop-outcome`, role
simulation; requirement R12. Route: `rows_loop_frontier_host`, then the projection of a wait
(`hostRunB_none_of_waiting`). Consumer: `frontier_of_diverges`. -/
@[semantics "host-session-protocol" (requirement := R12)]
theorem frontier_waits (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hroot : LoopedRows s.built.program = true)
    (hfrag : LoopedDataRows s.built.table s.built.program = true) {σ : Type}
    (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st') :
    ∀ a ∈ Program.awaits s.machine, ∃ row, a.op = .external row ∧
      ((∀ (hrow : row < s.built.table.length), host.answer ⟨⟨row, hrow⟩, a.request⟩ st' = none) →
        (effChain s.built.table s.built.program []).Waits (rowsHost host) (Stores.empty, st)) := by
  intro a ha
  obtain ⟨row, hop, hwait⟩ :=
    rows_loop_frontier_host s hreach hfund hrest hhost hroot hfrag host st st' hA a ha
  refine ⟨row, hop, fun hnone => ?_⟩
  obtain ⟨lower, hlow⟩ := hwait hnone
  exact ⟨lower, hostRunB_none_of_waiting host lower _ [] Stores.empty st (hlow lower (Nat.le_refl _))⟩

/-- **A diverging chain leaves no call unanswered**: under the premises of `frontier_waits`, if
the program's chain diverges under the host, the host answers every call the machine waits on.
Placement: concept `host-session-protocol`, the proposed claim `rows-loop-outcome`, role safety;
requirement R12. Route: a frontier is the chain's wait (`frontier_waits`), and a wait excludes
divergence (`Chain.Waits.not_diverges`). Consumer: R12's separation of a frontier from
divergence. -/
@[semantics "host-session-protocol" (requirement := R12)]
theorem frontier_of_diverges (s : Run) (hreach : Run.Reached s) (hfund : funded s = true)
    (hrest : atRest s = true) (hhost : hostDriven s = true)
    (hroot : LoopedRows s.built.program = true)
    (hfrag : LoopedDataRows s.built.table s.built.program = true) {σ : Type}
    (host : Effects.Comodel (RowSig s.built.table) σ) (st st' : σ)
    (hA : HostAnswered s.built.table host s.built.program s.budget.fuel (tapeOf s)
      (Api.load s.built.program s.budget.compileFuel) st st')
    (hdiv : (effChain s.built.table s.built.program []).Diverges (rowsHost host) (Stores.empty, st)) :
    ∀ a ∈ Program.awaits s.machine, ∃ row, a.op = .external row ∧
      ¬ ∀ (hrow : row < s.built.table.length), host.answer ⟨⟨row, hrow⟩, a.request⟩ st' = none := by
  intro a ha
  obtain ⟨row, hop, hw⟩ := frontier_waits s hreach hfund hrest hhost hroot hfrag host st st' hA a ha
  exact ⟨row, hop, fun hnone => (hw hnone).not_diverges hdiv⟩

/-- **An equivalent program finishes where the run exits.** If the built program is equivalent
at its table to `e` (`EffEquiv`), a driven run that exits carries its exit, stores and drive
state to `e`'s chain under the same reactor host. Placement: concept `host-session-protocol`, the
proposed claim `call-chain-equivalence`, role simulation; requirement R6. Route:
`runWith_finishes`, then `Chain.Equiv.finishes_iff`. It does not establish that `e` has a
session of its own. Consumer: rewrites of an authored program that keep the driver theorem, such
as the closed entry of `effChain_bind_succeed`. -/
@[semantics "host-session-protocol" (requirement := R6)]
theorem effEquiv_runWith {σ : Type} (b : Api.Built) (e : NativeEff)
    (hequiv : EffEquiv b.table b.program e) (r : Reactor σ) (st : σ) (id : String)
    (budget : Api.Budget) (rounds : Nat) (henv : r.Envelops b.app) (hexits : r.ExitsOnly)
    (hroot : LoopedRows b.program = true) (hfrag : LoopedDataRows b.table b.program = true)
    (hfund : funded (Run.runWith b r st id budget rounds).1 = true)
    (hrest : atRest (Run.runWith b r st id budget rounds).1 = true)
    (ex : ExitV) (hex : (Run.runWith b r st id budget rounds).1.exit = some ex) :
    (effChain b.table e []).Finishes (rowsHost (reactorHost b.table r)) (Stores.empty, st) ex
      ((Run.runWith b r st id budget rounds).1.machine.state, (Run.runWith b r st id budget rounds).2) :=
  ((hequiv []).finishes_iff _ _ _ _).mp
    (runWith_finishes b r st id budget rounds henv hexits hroot hfrag hfund hrest ex hex)

/-- **Divergence adequacy at the driver, on loops** (planned goal): a program whose driven run,
at every budget, neither exits nor waits on a call has a diverging chain under the reactor.
Placement: concept `host-session-protocol`, the proposed claim `rows-divergence-adequate`, role
adequacy; requirement R12, the system map's open part "divergence is witnessed by compatible
finite prefixes". Reach: the row fragment with loops, a reactor inside the envelope that answers
with exits, a fixed round count. Route: at a budget `k`, case on the chain's run under the
reactor host. A cut is the goal. A finish or a wait needs a session budget at which the drive is
funded and at rest; that is the open claim `embedded-budget-sufficient`. Then `runWith_finishes`'s
converse direction (H9 on loops) gives an exit, and `frontier_waits` a wait, against the premise.
It establishes no progress and no fairness. Consumer: R12's divergence adequacy, with
`runWith_exit_of_diverges` its other direction. -/
@[semantics "host-session-protocol" (requirement := R12)]
proof_goal rows_divergence_adequate (σ : Type) (b : Api.Built) (r : Reactor σ) (st : σ)
    (id : String) (rounds : Nat) (henv : r.Envelops b.app) (hexits : r.ExitsOnly)
    (hroot : LoopedRows b.program = true) (hfrag : LoopedDataRows b.table b.program = true) :
    (∀ budget : Api.Budget, (Run.runWith b r st id budget rounds).1.exit = none ∧
      Program.awaits (Run.runWith b r st id budget rounds).1.machine = []) →
    (effChain b.table b.program []).Diverges (rowsHost (reactorHost b.table r)) (Stores.empty, st)

end Effect4.Run
