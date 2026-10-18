import Effect4.Program.Check
import Effect4.Laws.Program.Typing.Restrict
import Effect4.Laws.Program.Typing.Rebase
import Effect4.Laws.Auto.Obligations
/-!
Placement for the V1 checking connectors:
Concept: initial-algebras-folds; checker-base-natural and source-annotation-agrees, R14.
Question: exact checker decomposition and signature-extension compatibility.
Reach: all module keys for combine_deps; positive part answers for run_part_extends.
Exclusions: program admission, negative extension hits, progress, and native execution.
Consumer: Checked.ask_value, SourceSession.feed, and Check.extension.
The combine_deps pointer is a planned goal. No core constructor depends on that goal.
-/
set_option autoImplicit false
namespace Effect4.Program.Check
open Effect4 Effect4.Program Conform.Effect4.Typing Internal
theorem run_placed (d : SigData) (env : TyEnv) (q : NativeEff) (base : List Nat) :
    place base (run (.part d env q)) =
      ⟨(Annotate.check d.signature env base q).2,
        (Annotate.check d.signature env base q).1⟩ := by
  simp only [place, run, Annotate.check_eq]
  have ht := tableAt_rebase d.signature (some (.env env)) (.eff q) base []
  have hr := Checker.check_rebase d.signature base env [] q
  simp only [List.append_nil] at ht hr
  exact congr (congrArg Verdict.mk hr.symm) ht.symm

theorem run_part_extends {a b : SigData} (env : TyEnv) (q : NativeEff) (t : EffTy)
    (he : a.extendsB b = true) (hp : (run (.part a env q)).result = .ok t) :
    run (.part a env q) = run (.part b env q) := by
  have hc : Checker.check a.signature env [] q = .ok t := by
    simpa only [run, Annotate.check_eq] using hp
  have support := hasTy_sigProgram (check_sound a.signature q env [] t hc)
  have same := Annotate.check_restrict (SigData.extends_of_extendsB he) support env []
  exact (congrArg (fun out : List Table.Entry × Except TypeRefusal EffTy =>
    (⟨out.2, out.1⟩ : Verdict)) same).symm


@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal combine_deps (i : CheckInput) : combine i ((deps i).map (fun d => run d.input)) = run i

/-- The unchanged exact observation of ask; module decomposition remains its stated premise. -/
@[semantics "host-session-protocol" (requirement := R14)]
theorem Checked.ask_value (o : Oracle) (i : CheckInput) : (Checked.ask o i).value = run i := by
  rw [Oracle.eq_uncached o]
  cases i with
  | part sig env program => rfl
  | module app holes program =>
    change combine (.module app holes program)
      (((deps (.module app holes program)).map (fun d => (d.input, run d.input))).map Prod.snd) = _
    rw [List.map_map]
    exact combine_deps _
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_module (app : SigApp) (holes : RowTable) (program : NativeEff) :
    run (.module app holes program) =
      ⟨({ program,holes } : Sketch).sourceCheck app,({ program,holes } : Sketch).sourceAnnotate app⟩ := rfl

@[semantics "initial-algebras-folds" (requirement := R14)]
theorem run_part (sig : SigData) (env : TyEnv) (program : NativeEff) :
    run (.part sig env program) =
      ⟨(Annotate.check sig.signature env [] program).2,(Annotate.check sig.signature env [] program).1⟩ := rfl

/-- Placement: initial-algebras-folds, run_part_extends helper, positive part support, R14.
Consumer: positive extension-hit retention. This establishes no negative-answer or module reuse. -/
theorem support_of_positive {Op : Type} (sig : Signature Op) (program : Eff Op)
    (env : TyEnv) (ty : EffTy) (hp : Checker.check sig env [] program = .ok ty) :
    supportB sig program = true := by
  rw [supportB_eq]
  exact hasTy_sigProgram (check_sound sig program env [] ty hp)

theorem extension_hit_retains_positive (a b : SigData) (env : TyEnv) (q : NativeEff) (t : EffTy)
    (he : a.extendsB b = true) (hp : (run (.part a env q)).result = .ok t) :
    extension.hit (.part b env q) (.part a env q, run (.part a env q)) = true := by
  have hc : Checker.check a.signature env [] q = .ok t := by
    simpa only [run, Annotate.check_eq] using hp
  have hs := support_of_positive a.signature q env t hc
  have pos : (run (.part a env q)).result.toBool = true := by rw [hp]; rfl
  simp only [extension, extensionHit, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨True.intro,True.intro⟩,he⟩,pos⟩,hs⟩

def ExplanationReplays (input key : CheckInput) (why : TypeRefusal) : Prop :=
  match input with
  | .part .. => key = input ∧ (run key).result = .error why
  | .module .. => ∃ dependency ∈ Internal.deps input,
      dependency.input = key ∧ locatedResult dependency (run key) = .error why

@[semantics "initial-algebras-folds" (requirement := R14)]
proof_goal explain_replays (o : Oracle) (input : CheckInput) (explanation : Explanation)
    (key : CheckInput) (he : (explain o input).value = some explanation)
    (hp : explanation.part = some key) : ExplanationReplays input key explanation.refusal

end Effect4.Program.Check
