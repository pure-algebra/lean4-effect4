import Cas.Core.Admission
import Cas.IR.Word
import Cas.Lang.Ops

/-!
# Interpretation — one step calls the admission judgment

`step` consumes exactly one operation over the store word. Admission is
NOT re-derived here: the put case calls `Cas.put` — the proved sound and
complete judgment — and maps its outcomes onto the word. A conflict
(the explicit Level-0 collision witness) surfaces as a refusal, never
argued away. `run` is iterated `step` with fuel.

The ledger rows carried here: L5 (the put case agrees with the
judgment, and a fresh admission is `Store.set` through the bridge),
L6 (the load case answers exactly the projected store), and L7 (running
preserves word admission — the interpreter cannot un-close a store).

The LLM extension interprets by monad morphism: `handleLlm` folds the
oracle's answers into a pure store program, so one store interpreter
serves every composed language. The oracle's nondeterminism enters only
as the recorded answer; admission remains the only gate.
-/

namespace Cas.Lang

/-- Clause-named refusals, mirroring the runtime error family. -/
inductive Refusal where
  | notWellFormed
  | dangling (missing : Addr32)
  | wrongKind (ref : Addr32) (expected actual : UInt8)
  | collision (addr : Addr32)
  | noObject (addr : Addr32)
  | failed (reason : String)

/-- Admission's clauses, as refusals. -/
def Refusal.ofAdmission : AdmissionError → Refusal
  | .dangling a => .dangling a
  | .wrongKind a exp act => .wrongKind a exp act

/-- Where a program stands after some steps. -/
inductive Status (S : Sig) (A : Type) where
  | done (value : A)
  | running (rest : Prog S A)
  | refused (why : Refusal)

def Status.isDone : Status S A → Bool
  | .done _ => true
  | _ => false

def Status.isRefused : Status S A → Bool
  | .refused _ => true
  | _ => false

/-- Still suspended — the only status a fuelled run reports that says
nothing about the program. The word gate's precondition is that this is
`false`. -/
def Status.isRunning : Status S A → Bool
  | .running _ => true
  | _ => false

section Interp

variable (H : Bytes → Addr32)

/-- Consume exactly one operation. The put case is the admission
judgment, called: well-formedness is the decidable gate, `Cas.put`
judges, and each outcome maps onto the word — fresh appends, duplicate
is the identity, conflict and every admission clause refuse. -/
def step : Prog CasSig A → Word → Status CasSig A × Word
  | .pure a, w => (.done a, w)
  | .vis (.put n) k, w =>
    if h : n.WF then
      match _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ with
      | .error e => (.refused (.ofAdmission e), w)
      | .ok (.fresh a _) =>
        (.running (k a), w ++ [Binding.mk a n])
      | .ok (.duplicate a) => (.running (k a), w)
      | .ok (.conflict a _) => (.refused (.collision a), w)
    else (.refused .notWellFormed, w)
  | .vis (.load a) k, w =>
    match Word.find w a with
    | some n => (.running (k n), w)
    | none => (.refused (.noObject a), w)
  | .vis (.fail reason) _, w => (.refused (.failed reason), w)

/-- Ledger L6: the load case answers exactly the projected store. -/
theorem step_load_agrees (a : Addr32) (k : Node → Prog CasSig A)
    (w : Word) :
    step H (.vis (.load a) k) w
      = match Word.toStore w a with
        | some n => (.running (k n), w)
        | none => (.refused (.noObject a), w) := rfl

/-- Ledger L5, fresh half: when the judgment admits fresh, the step
continues with the judged address, and the appended word projects to
the judgment's successor store — the commuting square. -/
theorem step_put_fresh {A} {n : Node} (h : n.WF)
    (k : Addr32 → Prog CasSig A) {w : Word} {a : Addr32} {σ' : Store}
    (hput : _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ = .ok (.fresh a σ')) :
    step H (.vis (.put n) k) w =
        (.running (k a), w ++ [Binding.mk a n])
      ∧ Word.toStore (w ++ [Binding.mk a n]) = σ' := by
  obtain ⟨_, hfresh, _, hσ'⟩ := put_fresh_spec hput
  refine ⟨?_, ?_⟩
  · simp only [step, dif_pos h, hput]
  · rw [hσ']
    exact Word.toStore_snoc n hfresh

/-- Ledger L5, refusal half: the step refuses exactly when the
judgment rejects, clause for clause. -/
theorem step_put_error {A} {n : Node} (h : n.WF)
    (k : Addr32 → Prog CasSig A) {w : Word} {e : AdmissionError}
    (hput : _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ = .error e) :
    step H (.vis (.put n) k) w = (.refused (.ofAdmission e), w) := by
  simp only [step, dif_pos h, hput]

/-- Ledger L7, one step: the interpreter preserves word admission. -/
theorem step_preserves_wf {A} (p : Prog CasSig A) {w : Word}
    (hw : Word.wf w = true) : Word.wf (step H p w).2 = true := by
  match p with
  | .pure a => exact hw
  | .vis (.fail reason) k => exact hw
  | .vis (.load a) k =>
    unfold step
    cases hf : Word.find w a <;> simp [hf, hw]
  | .vis (.put n) k =>
    by_cases h : n.WF
    · cases hc : _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ with
      | error e => simp [step, dif_pos h, hc, hw]
      | ok outcome =>
        cases outcome with
        | fresh a σ' =>
          simp only [step, dif_pos h, hc]
          obtain ⟨hok, _, _, _⟩ := put_fresh_spec hc
          refine Word.wf_snoc hw ?_
          intro r hr
          rcases hok r hr with ⟨m, hm, ht⟩
          exact Word.resolvesIn_iff.mpr ⟨m, hm, ht⟩
        | duplicate a => simp [step, dif_pos h, hc, hw]
        | conflict a occ => simp [step, dif_pos h, hc, hw]
    · simp [step, dif_neg h, hw]

/-- Iterated `step` — an operation with indeterminate end, so it
carries fuel. Out of fuel reports the program still `running`. -/
def run (fuel : Nat) (p : Prog CasSig A) (w : Word) :
    Status CasSig A × Word :=
  match fuel with
  | 0 => (.running p, w)
  | fuel + 1 =>
    match step H p w with
    | (.running rest, w') => run fuel rest w'
    | halted => halted

/-- A step that continues just spends one fuel. -/
theorem run_step_running {A} {p rest : Prog CasSig A} {w w' : Word}
    (h : step H p w = (.running rest, w')) (fuel : Nat) :
    run H (fuel + 1) p w = run H fuel rest w' := by
  simp only [run, h]

/-- Ledger L7: running preserves word admission — through the bridge,
the interpreter cannot un-close a store. -/
theorem run_preserves_wf (fuel : Nat) (p : Prog CasSig A) {w : Word}
    (hw : Word.wf w = true) :
    Word.wf (run H fuel p w).2 = true := by
  induction fuel generalizing p w with
  | zero => exact hw
  | succ f ih =>
    unfold run
    have hstep := step_preserves_wf H p hw
    cases hs : step H p w with
    | mk st w' =>
      rw [hs] at hstep
      cases st with
      | running rest => exact ih rest hstep
      | done a => exact hstep
      | refused why => exact hstep

end Interp

/-- Interpret the LLM extension by monad morphism: fold the oracle's
answers in, leaving a pure store program. One store interpreter serves
every composed language. -/
def Prog.handleLlm (oracle : String → String) : Prog AgentSig A → Prog CasSig A
  | .pure a => .pure a
  | .vis (Sum.inl e) k => .vis e (fun r => (k r).handleLlm oracle)
  | .vis (Sum.inr (.infer p)) k => (k (oracle p)).handleLlm oracle

/-- Run an agent program: handle inference, then interpret the store. -/
def runAgent (H : Bytes → Addr32) (oracle : String → String) (fuel : Nat)
    (p : Prog AgentSig A) (w : Word) : Status CasSig A × Word :=
  run H fuel (p.handleLlm oracle) w

end Cas.Lang
