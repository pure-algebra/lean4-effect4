import Effect4.Program.Admit
import Effect4.Laws.Machine.Handles

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The executable lookup reads exactly the handle kinds counted by `MintedIn`. -/
theorem handleLive_eq (m : NativeMachine) (code : UInt8 × Nat) :
    handleLive m code =
      match Handle.ofCode code with
      | some h => h.existsIn m.world
      | none => true := by
  unfold handleLive Handle.ofCode
  cases hk : HandleKind.ofByte? code.1 with
  | none => rfl
  | some kind =>
    cases kind <;> simp [Handle.existsIn, RunMachine.world] <;> rfl

/-- Every recognized handle in the value is live, in the existing judgment. -/
theorem mintedIn_iff_MintedIn (m : NativeMachine) (v : Val) :
    mintedIn m v = true ↔ MintedIn m v.keys := by
  constructor
  · intro hm handle hh
    rw [Val.keys_eq_handles] at hh
    obtain ⟨code, hc, hd⟩ := List.mem_filterMap.mp hh
    have hv := List.all_eq_true.mp hm code hc
    rw [handleLive_eq, hd] at hv
    exact hv
  · intro hm
    apply List.all_eq_true.mpr
    intro code hc
    rw [handleLive_eq]
    cases hd : Handle.ofCode code with
    | none => rfl
    | some handle =>
      apply hm handle
      rw [Val.keys_eq_handles]
      exact List.mem_filterMap.mpr ⟨code, hc, hd⟩

/-- A successful decision check identifies the row of the actual guard token. -/
theorem admitted_row (table : RowTable) (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann)
    (h : admit table m (.answerAsync fiber token answer) = none) :
    ∃ i request row, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧ admitAnswer row m fiber token answer = none := by
  simp only [admit] at h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  split at h <;> try cases h
  exact ⟨_, _, _, by assumption, by assumption, h⟩

/-- A success admitted for the parked row inhabits that row's answer type. -/
theorem external_answer_typed (table : RowTable) (m : NativeMachine)
    (fiber : FiberId) (token : Nat) (value : Val)
    (h : admit table m (.answerAsync fiber token (.ofExit (.success value))) = none) :
    ∃ i request row, requestOf m fiber token = some (.external i, request) ∧
      externalRow table i = some row ∧ Val.hasTy value row.answer = true := by
  obtain ⟨i, request, row, hp, hr, ha⟩ := admitted_row table m fiber token _ h
  refine ⟨i, request, row, hp, hr, ?_⟩
  cases ht : Val.hasTy value row.answer with
  | true => rfl
  | false => simp [admitAnswer, ht] at ha

/-- An oracle success taken at registration has the same answer-type obligation. -/
theorem external_oracle_typed (table : RowTable) (i : Nat) (value : Val)
    (h : externalAdmits table i (.ofExit (.success value)) = true) :
    ∃ row, externalRow table i = some row ∧ Val.hasTy value row.answer = true := by
  cases hr : externalRow table i with
  | some row =>
    simp only [externalAdmits, hr] at h
    exact ⟨row, rfl, (Bool.and_eq_true_iff.mp h).1⟩
  | none => simp [externalAdmits, hr] at h

/-- A successful oracle registration resumes with the head value itself, and that
value inhabits the row's answer type. This connects admission to the actual code. -/
theorem external_registration_typed (program : NativeEff) (table : RowTable)
    (i : Nat) (request : Val) (row : Row) (fiber : FiberId) (token : Nat)
    (before after : Stores) (value : Val)
    (rest : List (Completion Val Err Defect FiberId Ann)) (code : NCode)
    (hrow : externalRow table i = some row)
    (hhead : before.externals.answers = .ofExit (.success value) :: rest)
    (hreg : (interpOf program table).registerAsync (.external (.external i) request)
      fiber token before = (after, some code)) :
    code = .success value ∧ Val.hasTy value row.answer = true := by
  by_cases ha : externalAdmits table i (.ofExit (.success value)) = true
  · have ht := ha
    simp only [externalAdmits, hrow, Bool.and_eq_true_iff] at ht
    simp only [interpOf, hrow, Option.isNone_some, Bool.false_eq_true, if_false,
      hhead, ha, if_true] at hreg
    have hc := congrArg Prod.snd hreg
    simp only [Option.some.injEq] at hc
    exact ⟨hc.symm, ht.1⟩
  · simp only [interpOf, hrow, Option.isNone_some, Bool.false_eq_true, if_false,
      hhead, ha] at hreg
    have hc := congrArg Prod.snd hreg
    cases hc

/-- Every accepted completion names only handles present before the answer. -/
theorem admitAnswer_minted (row : Row) (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann)
    (h : admitAnswer row m fiber token answer = none) : MintedIn m answer.keys := by
  cases answer with
  | ofExit exit =>
    cases exit with
    | success value =>
      cases ht : Val.hasTy value row.answer with
      | false => simp [admitAnswer, ht] at h
      | true =>
        cases hm : mintedIn m value with
        | false => simp [admitAnswer, ht, hm] at h
        | true => exact (mintedIn_iff_MintedIn m value).mp hm
    | failure cause => simp [Completion.keys, exitKeys, MintedIn, Ok]
  | ofRefGet cell =>
    cases hc : m.state.refs[cell.index]? with
    | none => simp [admitAnswer, hc] at h
    | some value =>
      obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.mp hc
      simp [Completion.keys, MintedIn, Ok, Handle.existsIn, RunMachine.world, hlt]

/-- Admission strengthens the existing tape premise at each inspected decision. -/
theorem admitted_decision_minted (table : RowTable) (m : NativeMachine) (d : NativeDecision)
    (h : admit table m d = none) :
    (match d with
      | .answerAsync _ _ answer => decide (MintedIn m answer.keys)
      | _ => true) = true := by
  cases d with
  | answerAsync fiber token answer =>
    obtain ⟨_, _, row, _, _, ha⟩ := admitted_row table m fiber token answer h
    exact decide_eq_true (admitAnswer_minted row m fiber token answer ha)
  | _ => rfl

/-- A checked replay which returns a run satisfies `AnswersValidAt`'s exact walk,
including its stopping rules at a stuck machine or exhausted driver fuel. -/
theorem replayCheckedFrom_answersValid (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) (r : NativeReplay)
    (h : replayCheckedFrom program fuel answers table position tape m = .inl r) :
    letI := evaluatorFor program table
    AnswersValidAt (interpOf program table) fuel tape m := by
  letI := evaluatorFor program table
  change answersValid (interpOf program table) fuel tape m = true
  induction tape generalizing position m r with
  | nil => rfl
  | cons decision rest ih =>
    cases hs : m.stuck with
    | some why => simp [answersValid, hs]
    | none =>
      cases ha : admit table m decision with
      | some why => simp only [replayCheckedFrom, hs, ha] at h; cases h
      | none =>
        simp only [answersValid, hs]
        apply Bool.and_eq_true_iff.mpr
        constructor
        · have hd := admitted_decision_minted table m decision ha
          cases decision <;> exact hd
        ·
          generalize he : stepDecisionState (interpOf program table) fuel m decision = next at h ⊢
          rcases next with ⟨m', continued⟩
          cases continued with
          | false => rfl
          | true =>
            simp only [replayCheckedFrom, hs, ha, he, if_true] at h
            cases ho : oracleRefusal answers table m' with
            | some why => simp only [ho] at h; cases h
            | none =>
              simp only [ho] at h
              exact ih (position + 1) m' r h

/-- Successful checking returns the very run obtained by the original tape walker. -/
theorem replayCheckedFrom_eq_replay (program : NativeEff) (fuel : Nat)
    (answers : List (Completion Val Err Defect FiberId Ann)) (table : RowTable)
    (position : Nat) (tape : List NativeDecision) (m : NativeMachine) (r : NativeReplay)
    (h : replayCheckedFrom program fuel answers table position tape m = .inl r) :
    letI := evaluatorFor program table
    r = replayEval (interpOf program table) fuel tape m := by
  letI := evaluatorFor program table
  induction tape generalizing position m r with
  | nil =>
    simp only [replayCheckedFrom] at h
    exact Sum.inl.inj h.symm
  | cons decision rest ih =>
    cases hs : m.stuck with
    | some why =>
      simp only [replayCheckedFrom, hs] at h
      cases h
      simp only [replayEval, hs]
    | none =>
      cases ha : admit table m decision with
      | some why => simp only [replayCheckedFrom, hs, ha] at h; cases h
      | none =>
        simp only [replayCheckedFrom, hs, ha] at h
        simp only [replayEval, hs]
        generalize he : stepDecisionState (interpOf program table) fuel m decision = next at h ⊢
        rcases next with ⟨m', continued⟩
        cases ho : oracleRefusal answers table m' with
        | some why => simp only [ho] at h; cases h
        | none =>
          simp only [ho] at h
          cases continued with
          | false => exact Sum.inl.inj h.symm
          | true =>
            simp only [if_true] at h ⊢
            exact ih (position + 1) m' r h

end Effect4.Program
