import Effect4.Laws.Run.CallTree
import Effect4.Author
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: translation-simulation R6, boundary of `recorded-call-tree-prefix`.
Counterexample E4-HOST-CE-011.
Consumer: repair the internal `request_leads` fragment before proving Routing's original clause.
A submitted cell read produces a second request without any submitted exit.
This checked control concerns the general helper; the actual Routing program allocates no cell.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Counterexamples.HostRefPrefix
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote Effect4.Laws.Auto Effect4.Run.CallTree
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)

def table : RowTable := RowDef.table
  [Row.host "cell-input" .unit .nat .never "cell-prefix-control",
   Row.host "cell-output" .nat .unit .never "cell-prefix-control"]
def program : NativeEff := .bind (.perform .refMake (.lit (.nat 17)))
  (.bind (.perform (.external 0) (.lit .unit)) (.perform (.external 1) (.var 1)))
def admitted : Api.AdmittedProgram program (.ofTable table) where
  ty := ⟨.unit, .never, .empty⟩
  typed := by cbv
  formed := (Effect4.Program.Formation.checkInput_eq_none_iff _ _).mp (by decide +kernel)
  signature := by decide +kernel
  columnsType := by decide +kernel

def built : Api.Built := ⟨table, program, admitted, []⟩
def initial : Run := Run.open built "cell-prefix" ⟨100, 100⟩
def waiting : Run := initial.control Api.evaluate
def answered : Run := waiting.answer ⟨Api.root, 0⟩ (.ofRefGet ⟨0⟩)

theorem fragment_admitted : StraightRows table program = true := by decide
theorem no_cause_handler : NoCauseHandler program = true := by decide
theorem no_clock_read : NoClockRead program = true := by decide
theorem external_only_refused : SourceScope.ExternalOnly program → False := by
  unfold SourceScope.ExternalOnly
  decide
theorem first_request : requestOf waiting.machine Api.root 0 = some (.external 0, .unit) := by kernel_rfl
theorem second_request : requestOf answered.machine Api.root 1 = some (.external 1, .nat 17) := by kernel_rfl
theorem reply_tree_request : treeWaits table program [] = .waiting 0 .unit := by kernel_rfl

theorem answered_reached : Run.Reached answered :=
  Run.Reached.play waiting _ (Run.Reached.play initial _ (Run.Reached.open built "cell-prefix" ⟨100, 100⟩))

def call0 : Call := ⟨version, "cell-prefix", table, 0, Api.root, .external 0, .unit⟩
def reply0 : Reply := ⟨version, "cell-prefix", 0, ⟨Api.root, 0⟩, .ofRefGet ⟨0⟩⟩

theorem journal_shape : answered.journal =
    [.control Api.evaluate, .bind call0 0, .submit reply0, .apply ⟨Api.root, 0⟩] := by
  kernel_rfl

theorem no_submitted_exit (reply : Reply) (ex : ExitV)
    (member : Command.submit reply ∈ answered.journal) : reply.completion ≠ .ofExit ex := by
  rw [journal_shape] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with impossible | impossible | same | impossible
  · cases impossible
  · cases impossible
  · cases same
    intro impossible
    cases impossible
  · cases impossible

theorem submitted_tape_empty (tape : ReplyTape)
    (submitted : ∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ answered.journal ∧
      reply.completion = .ofExit ex) : tape = [] := by
  cases tape with
  | nil => rfl
  | cons ex rest =>
    obtain ⟨reply, member, completion⟩ := submitted ex List.mem_cons_self
    exact False.elim (no_submitted_exit reply ex member completion)

theorem prefix_conclusion_refuted :
    ¬ ∃ tape : ReplyTape,
      (∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ answered.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits table program tape = .waiting 1 (.nat 17) := by
  rintro ⟨tape, submitted, waitingAt⟩
  rw [submitted_tape_empty tape submitted, reply_tree_request] at waitingAt
  cases waitingAt

end Test.Counterexamples.HostRefPrefix
