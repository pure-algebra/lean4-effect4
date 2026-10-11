import Effect4.Laws.Program.RuntimeR
import Effect4.Laws.Auto.Semantics

/-!
# Program.Table.Agreement — the raw statement at a row table (DI-57)

Slice H5 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310). The frame
machine and the reference machine agree at every row table: `run_eq_ref_table`. `run_eq_ref`
(`Laws/Program/RuntimeR.lean`) is its instance at the empty row table. Its proof is the packet's
slice H6a (decisions row 314). A host answer is a decision on both machines, and no load holds an
answer (DI-23), so the statement has no case of preloaded answers.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program

/-- The proposition of `run_eq_ref_table` (the 2026-10-03 note's S1): the frame machine and the
reference agree at every row table, on every decision tape. A host answer is a decision of the
tape, the only route by which an answer reaches either machine (DI-23). -/
def RunEqRefTable : Prop :=
  ∀ (e : NativeEff) (table : RowTable) (fuel : Nat) (tape : List Api.Decision)
    (compileFuel : Nat),
    (Api.replay e fuel tape table compileFuel).outcome =
        classify (replayR e fuel tape compileFuel table) ∧
      obs (Api.replay e fuel tape table compileFuel).machine =
        obsR (replayR e fuel tape compileFuel table).machine

/-- **The frame machine and the reference machine agree at every row table** (DI-57). On every
program, row table, decision tape and pair of budgets, the two replays end in the same class,
and they have the same observation `obs`: every fiber's exit and the whole stores, the external
allocations included. It is `Machine.Book`'s replay theorem at the two instances at the table:
`stepAgrees` and `hooksAgree_of` hold at every row table under the store invariant `StoresOk`,
whose clause `externals` holds at the empty row table alone; the registration arm answers
nothing on both machines, since a host answer is a decision (DI-23). Reach: no premise on the
tape, so an answer that no session admits is in reach. It does not establish reply admission,
the typing of a reply, a host's conformance or the session's ledger. `run_eq_ref` is its
instance at the empty row table. Concept `translation-simulation`, claim `run-eq-ref-table`,
role simulation; requirement R6. Consumer: `session_eq_ref`. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem run_eq_ref_table : RunEqRefTable := by
  intro e table fuel tape compileFuel
  rw [replay_outcome, replay_machine]
  exact replayRel_classify_obs (replay_rel (table := table) e compileFuel fuel tape)


/-- An element of the left list of a related pair has a related partner in the right list. A
step of `replay_origin`. -/
theorem listRel_mem_left {α β : Type _} {R : α → β → Prop} {l₁ : List α} {l₂ : List β}
    (h : ListRel R l₁ l₂) {a : α} (ha : a ∈ l₁) : ∃ b ∈ l₂, R a b := by
  induction h with
  | nil => cases ha
  | cons hab _ ih =>
    rcases List.mem_cons.mp ha with rfl | ha'
    · exact ⟨_, List.mem_cons_self, hab⟩
    · obtain ⟨b, hb, hr⟩ := ih ha'
      exact ⟨b, List.mem_cons_of_mem _ hb, hr⟩

/-- **A parked call's address names its call** (decisions row 323). In every machine that the
frame machine replays from a program's load, at any row table and any tape, a fiber whose
current code is an external registration keeps the address of a call of that operation in the
program. The simulation carries it: the related reference code is `CodeMeans.asyncForeign`,
whose address holds the call (`asyncRoute_means`). Concept `host-session-protocol`; a step of
the claim `reply-at-call-instance`; consumer: `Run.origin_addresses_call`. It does not say that
the expansion of the program's layer references keeps the call at that address. -/
theorem replay_origin (e : NativeEff) (table : RowTable) (cfuel fuel : Nat)
    (tape : List Api.Decision) (f : FRun)
    (hf : f ∈ (replayEval (evaluator := evaluatorFor e table) (interpOf e table) fuel tape
      (Api.load e cfuel)).machine.fibers)
    {op : NativeOp} {request : Val} {origin : List Nat} {signal : Bool} {cancel : Option EffName}
    (hc : f.frame.current = .async (.external op request origin) signal cancel) :
    ∃ r, Node.at_ (.eff e) origin = some (.eff (.perform op r)) := by
  letI := evaluatorFor e table
  letI := termEvaluatorFor e table
  obtain ⟨f₂, _, hfm⟩ :=
    listRel_mem_left (replay_rel (table := table) e cfuel fuel tape).machine.1 hf
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hcode, -⟩ := hfm
  rw [hc] at hcode
  generalize f₂.frame.current = c₂ at hcode
  cases hcode with
  | asyncForeign _ _ _ hnode _ _ => exact hnode

end Effect4.Program.Sched
