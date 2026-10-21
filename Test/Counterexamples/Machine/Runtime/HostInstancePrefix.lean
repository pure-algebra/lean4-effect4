import Effect4.Laws.Run.CallTree
import Effect4.Author
import Effect4.Laws.Auto.KernelRfl

/-!
Counterexample E4-HOST-CE-012.
Concept: translation-simulation R6, boundary of `recorded-call-tree-prefix`.
Consumer: the concrete reply-column premise of the internal Routing call-prefix helper.
The session admits a generic row's checked instance; the table-only tape refuses that exit.
The actual Routing columns contain no parameter. Its original statement stays unchanged.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Counterexamples.HostInstancePrefix
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote Effect4.Laws.Auto Effect4.Run.CallTree
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)

def table : RowTable := RowDef.table
  [Row.host "generic-input" (.var 0) (.var 0) .never "instance-prefix-control",
   Row.host "generic-output" .nat .unit .never "instance-prefix-control"]
def program : NativeEff :=
  .bind (.perform (.external 0) (.lit (.nat 17))) (.perform (.external 1) (.var 0))
def admitted : Api.AdmittedProgram program (.ofTable table) where
  ty := ⟨.unit, .never, .empty⟩
  typed := by cbv
  formed := (Effect4.Program.Formation.checkInput_eq_none_iff _ _).mp (by decide +kernel)
  signature := by decide +kernel
  columnsType := by decide +kernel

def built : Api.Built := ⟨table, program, admitted⟩
def initial : Run := Run.open built "instance-prefix" ⟨100, 100⟩
def waiting : Run := initial.control Api.evaluate
def answered : Run := waiting.answer ⟨Api.root, 0⟩ (.ofExit (.success (.nat 17)))

theorem fragment_admitted : StraightRows table program = true := by decide
theorem no_cause_handler : NoCauseHandler program = true := by decide
theorem external_only : SourceScope.ExternalOnly program := by
  unfold SourceScope.ExternalOnly
  decide

theorem concrete_refused : SourceScope.ConcreteReplies table → False := by
  unfold SourceScope.ConcreteReplies
  decide

theorem first_request : requestOf waiting.machine Api.root 0 = some (.external 0, .nat 17) := by kernel_rfl
theorem second_request : requestOf answered.machine Api.root 1 = some (.external 1, .nat 17) := by kernel_rfl
theorem reply_tree_empty : treeWaits table program [] = .waiting 0 (.nat 17) := by kernel_rfl
theorem reply_tree_submitted (rest : ReplyTape) :
    treeWaits table program (.success (.nat 17) :: rest) = .waiting 0 (.nat 17) := by kernel_rfl

def call0 : Call := ⟨version, "instance-prefix", table, 0, Api.root, .external 0, .nat 17⟩
def reply0 : Reply := ⟨version, "instance-prefix", 0, ⟨Api.root, 0⟩, .ofExit (.success (.nat 17))⟩

theorem journal_shape : answered.journal =
    [.control Api.evaluate, .bind call0 0, .submit reply0, .apply ⟨Api.root, 0⟩] := by kernel_rfl

theorem only_submitted_exit (reply : Reply) (ex : ExitV)
    (member : Command.submit reply ∈ answered.journal)
    (completion : reply.completion = .ofExit ex) : ex = .success (.nat 17) := by
  rw [journal_shape] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with impossible | impossible | same | impossible
  · cases impossible
  · cases impossible
  · cases same
    cases completion
    rfl
  · cases impossible

theorem prefix_conclusion_refuted :
    ¬ ∃ tape : ReplyTape,
      (∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ answered.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits table program tape = .waiting 1 (.nat 17) := by
  rintro ⟨tape, submitted, waitingAt⟩
  cases tape with
  | nil => rw [reply_tree_empty] at waitingAt; cases waitingAt
  | cons ex rest =>
    obtain ⟨reply, member, completion⟩ := submitted ex List.mem_cons_self
    rw [only_submitted_exit reply ex member completion, reply_tree_submitted] at waitingAt
    cases waitingAt

theorem answered_reached : Run.Reached answered :=
  Run.Reached.play waiting _ (Run.Reached.play initial _
    (Run.Reached.open built "instance-prefix" ⟨100, 100⟩))

end Test.Counterexamples.HostInstancePrefix
