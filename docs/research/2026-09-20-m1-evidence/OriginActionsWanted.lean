def M1Origin.spawn_rel (root : NativeEff) {i₁ : FInterp} {i₂ : RInterp} (_hb : i₁.budgetOf = i₂.budgetOf)
    {m₁ : FMachine} {m₂ : RState}
    (_hok : MachineOk StoresOk m₁) (_hm : BMeans root m₁ m₂) {p₁ : FRun} {p₂ : RFiber}
    (_hp : FMeans root p₁ p₂) {prog₁ : NCode} {prog₂ : RProgram} (_hprog : CodeMeans root prog₁ prog₂)
    (options : Supervision.ForkOptions) (site : List Nat := []) : ProofGraph.Obligation (TripleRel root Eq (spawn i₁ m₁ p₁ prog₁ options site) (spawn i₂ m₂ p₂ prog₂ options site)) := ⟨⟩
#proof_wanted M1Origin.spawn_rel

def M1Origin.beginRace_rel (root : NativeEff) (c : List (FiberId × ExitV)) {m₁ : FMachine} {m₂ : RState}
    (_hok : MachineOk StoresOk m₁) (_hm : BMeans root m₁ m₂) {f₁ : FRun} {f₂ : RFiber}
    (_hf : FMeans root f₁ f₂) (y : Bool) {e₁ : List NCode} {e₂ : List RProgram}
    (_he : ListRel (CodeMeans root) e₁ e₂) (site : Option (List Nat) := none) : ProofGraph.Obligation (IterRel root (beginRace (interpAt root c) m₁ f₁ y e₁ site) (beginRace (interpRAt root c) m₂ f₂ y e₂ site)) := ⟨⟩
#proof_wanted M1Origin.beginRace_rel

def M1Origin.fork_rel {p₁ : NCode} {p₂ : RProgram} (_hp : CodeMeans root p₁ p₂)
    (options : Supervision.ForkOptions) {a₁ : FAnswer} {a₂ : RAnswer} (ha : AnswerRel root a₁ a₂) (site : List Nat := []) : ProofGraph.Obligation (IterRel root (FiberAction.fork (interpAt root c) m₁ f₁ y p₁ options a₁ site)
      (FiberAction.fork (interpRAt root c) m₂ f₂ y p₂ options a₂ site)) := ⟨⟩
#proof_wanted M1Origin.fork_rel

def M1Origin.forkIn_rel {p₁ : NCode} {p₂ : RProgram} (_hp : CodeMeans root p₁ p₂)
    (options : Supervision.ForkOptions) (scope : Nat) {a₁ : FAnswer} {a₂ : RAnswer}
    (ha : AnswerRel root a₁ a₂) (site : List Nat := []) : ProofGraph.Obligation (IterRel root (FiberAction.forkIn (interpAt root c) m₁ f₁ y p₁ options scope a₁ site)
      (FiberAction.forkIn (interpRAt root c) m₂ f₂ y p₂ options scope a₂ site)) := ⟨⟩
#proof_wanted M1Origin.forkIn_rel

def M1Origin.raceAll_rel {e₁ : List NCode} {e₂ : List RProgram} (_he : ListRel (CodeMeans root) e₁ e₂) (site : Option (List Nat) := none) : ProofGraph.Obligation (IterRel root (FiberAction.raceAll (interpAt root c) m₁ f₁ y e₁ site)
      (FiberAction.raceAll (interpRAt root c) m₂ f₂ y e₂ site)) := ⟨⟩
#proof_wanted M1Origin.raceAll_rel

