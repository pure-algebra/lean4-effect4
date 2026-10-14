import Effect4.Laws.Run.CallTree
import Effect4.Laws.Api.SessionMeaningBlocks
import Effect4.Author
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: translation-simulation, R6. Claim: recorded-call-tree-prefix, role inversion.
Consumer: the M2 route decision in the meanings receipt.
Reach: one admitted block, two external rows, one interruption, no submitted reply.
The finite controls test whether a reply-only tree covers every recorded command prefix.
They establish no general simulation or outside-host agreement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Test.MeaningsPrefixProbe
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote Effect4.Laws.Auto Effect4.Run.CallTree
open Effect4.Api.HostSession
open Effect4.Api.Runner (Command)

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
def initial : Run := Run.open built "prefix-control" ⟨100, 100⟩
def waiting : Run := initial.control Api.evaluate
def interrupted : Run := waiting.control (.interruptFrom none .empty Api.root)
def finalizerCall : Call := Call.claim interrupted ⟨Api.root, 1⟩ (.external 1) .unit
def recorded : Run := interrupted.step (.bind finalizerCall 1)

theorem fragment_admitted : BlockRows table program = true := by decide
theorem external_only_body : SourceScope.ExternalOnly body := by
  unfold SourceScope.ExternalOnly
  decide
theorem old_source_restriction_refuses_block : ¬ SourceScope.ExternalOnly program := by
  unfold SourceScope.ExternalOnly
  decide
theorem concrete_replies : SourceScope.ConcreteReplies table := by
  unfold SourceScope.ConcreteReplies
  decide
theorem first_request : requestOf waiting.machine Api.root 0 = some (.external 0, .unit) := by
  kernel_rfl
theorem finalizer_request : requestOf interrupted.machine Api.root 1 = some (.external 1, .unit) := by
  kernel_rfl
theorem interrupted_reached : Run.Reached interrupted :=
  Run.Reached.play waiting _
    (Run.Reached.play initial _ (Run.Reached.open built "prefix-control" ⟨100, 100⟩))
theorem recorded_reached : Run.Reached recorded :=
  Run.Reached.step interrupted (.bind finalizerCall 1) interrupted_reached
theorem finalizer_binding_accepted :
    (Command.bind finalizerCall 1, .bound) ∈ recorded.journal.zip recorded.phases := by
  decide +kernel
theorem waiting_has_no_exit : waiting.exit = none := by kernel_rfl
theorem interrupted_not_host_driven : Run.hostDriven interrupted = false := by kernel_rfl

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

theorem prefix_conclusion_refuted :
    ¬ ∃ (k : Nat) (tape : ReplyTape),
      (∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ recorded.journal ∧
        reply.completion = .ofExit ex) ∧
      blockWaits k tape = .waiting 1 .unit := by
  rintro ⟨k, tape, submitted, observed⟩
  rw [submitted_tape_empty tape submitted, tree_waits_first] at observed
  cases observed

end Test.MeaningsPrefixProbe
