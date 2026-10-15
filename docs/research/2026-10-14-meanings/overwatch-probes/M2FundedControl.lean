import Effect4.Laws.Run.CallTree
import Effect4.Laws.Api.SessionMeaningBlocks
import Effect4.Author
import Effect4.Laws.Auto.KernelRfl

/-!
# Overwatch control: `hostDriven` without `funded` admits the interruption

Concept: translation-simulation, R6. Claim: `recorded-call-tree-prefix` widened to `BlockRows`
(decisions rows 388 and 390), role inversion: the boundary control of its history premise.
Consumer: the statement of slice M2, which ranges over host-driven histories.

Question. Codex's control (`MeaningsPrefixProbe.prefix_conclusion_refuted`) is excluded by
`hostDriven`. `hostDriven` reads `tapeOf`, and `tapeOf` stops at the first row cut by the budget.
Does a cut interruption escape `hostDriven` and still run the finalizer to its call?

Reach. Codex's program and command script at command budget 5 (compile budget 100): the
evaluation completes; the interruption's decision ends at a frontier after the finalizer parks.

Not established. No universal statement; it shows that the widened claim needs `funded` (as
`H9Blocks` takes it) or a history premise read from the whole journal.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Overwatch.M2FundedControl
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote Effect4.Laws.Auto Effect4.Run.CallTree
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)

/-- Codex's two-row table and program (`MeaningsPrefixProbe`), unchanged. -/
def table : RowTable := RowDef.table
  [Row.host "body" .unit .unit .never "prefix-control",
   Row.host "finalizer" .unit .unit .never "prefix-control"]
def body : NativeEff := .onExit (.perform (.external 0) (.lit .unit))
  (.perform (.external 1) (.lit .unit))
def program : NativeEff := .defs [] .nil body .nil
def admitted : Api.AdmittedProgram program ⟨table, []⟩ where
  ty := ⟨.unit, .never, .empty⟩
  typed := by cbv
  formed := (Effect4.Program.Formation.checkInput_eq_none_iff _ _).mp (by decide +kernel)
  signature := by decide +kernel
  columnsType := by decide +kernel

def built : Api.Built := ⟨table, program, admitted, []⟩
/-- The only change from Codex's script: command budget 5. -/
def initial : Run := Run.open built "prefix-control" ⟨5, 100⟩
def waiting : Run := initial.control Api.evaluate
def interrupted : Run := waiting.control (.interruptFrom none .empty Api.root)
def finalizerCall : Call := Call.claim interrupted ⟨Api.root, 1⟩ (.external 1) .unit
def recorded : Run := interrupted.step (.bind finalizerCall 1)

theorem fragment_admitted : BlockRows table program = true := by decide
theorem evaluation_progressed : waiting.phases = [.progressed] := by kernel_rfl
theorem interruption_cut : interrupted.phases = [.progressed, .frontier] := by kernel_rfl
theorem finalizer_request : requestOf interrupted.machine Api.root 1 = some (.external 1, .unit) := by
  kernel_rfl
theorem recorded_reached : Run.Reached recorded :=
  Run.Reached.step interrupted (.bind finalizerCall 1)
    (Run.Reached.play waiting _
      (Run.Reached.play initial _ (Run.Reached.open built "prefix-control" ⟨5, 100⟩)))
theorem finalizer_binding_accepted :
    (Command.bind finalizerCall 1, .bound) ∈ recorded.journal.zip recorded.phases := by
  decide +kernel
/-- The recorded run meets the widened claim's history premise. -/
theorem recorded_host_driven : Effect4.Run.hostDriven recorded = true := by kernel_rfl
/-- It is not funded: the interruption's row is cut. -/
theorem recorded_not_funded : Effect4.Run.funded recorded = false := by kernel_rfl

def blockWaits (k : Nat) (tape : ReplyTape) : RowsStop :=
  (observeRows (admittedTapeHost table)
    (denoteBlockB table (bodiesOf program) k [] program emptyCtx []) Stores.empty tape).stop

theorem tree_waits_first (k : Nat) : blockWaits k [] = .waiting 0 .unit := by
  cases k <;> rfl

theorem no_submitted_reply (reply : Reply) : Command.submit reply ∉ recorded.journal := by
  change Command.submit reply ∉
    [Command.control Api.evaluate, Command.control (.interruptFrom none .empty Api.root),
      Command.bind finalizerCall 1]
  simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, or_self, not_false_eq_true]

theorem submitted_tape_empty (tape : ReplyTape)
    (submitted : ∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ recorded.journal ∧
      reply.completion = .ofExit ex) : tape = [] := by
  cases tape with
  | nil => rfl
  | cons ex rest =>
    obtain ⟨reply, member, _⟩ := submitted ex List.mem_cons_self
    exact False.elim (no_submitted_reply reply member)

/-- **The control.** A reached, host-driven `BlockRows` run binds a call that no budget and no
submitted-reply tape of the block tree explains. -/
theorem host_driven_conclusion_refuted :
    Effect4.Run.hostDriven recorded = true ∧
      (Command.bind finalizerCall 1, .bound) ∈ recorded.journal.zip recorded.phases ∧
      ¬ ∃ (k : Nat) (tape : ReplyTape),
        (∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ recorded.journal ∧
          reply.completion = .ofExit ex) ∧
        blockWaits k tape = .waiting 1 .unit := by
  refine ⟨recorded_host_driven, finalizer_binding_accepted, ?_⟩
  rintro ⟨k, tape, submitted, observed⟩
  rw [submitted_tape_empty tape submitted, tree_waits_first] at observed
  cases observed

end Overwatch.M2FundedControl
