
/-! ### Control histories: a program with no host row receives no answer

With an empty row table the session accepts no reply: `admit` refuses every answer
(`externalRow [] i = none`), and so does the instance check. So the shop's machine moves by
controls alone. The general law of section 4 and the stages of section 5 are stated over these
histories: the typed state (M6) carries host answers only under `AdmittedTape`, whose link to the
session's executable admission is open (`admit_sound`, decisions rows 97 to 99). -/

/-- A decision that is no host answer. -/
def IsControl : NativeDecision → Prop
  | .answerAsync _ _ _ => False
  | _ => True

/-- **A control history**: the load stepped by controls only. -/
def ControlHistory (b : Api.Built) (compileFuel : Nat) (m : NativeMachine) : Prop :=
  ∃ history : List (Nat × NativeDecision), (∀ x ∈ history, IsControl x.2) ∧
    m = history.foldl (stepBy b) (Api.load b.program compileFuel)

/-- The empty table has no external row. -/
theorem externalRow_nil (i : Nat) : externalRow [] i = none := rfl

/-- With the empty table `admit` refuses every answer. -/
theorem admit_nil_answer (m : NativeMachine) (f : FiberId) (t : Nat)
    (a : Completion Val Err Defect FiberId Ann) : admit [] m (.answerAsync f t a) ≠ none := by
  unfold admit
  split
  · exact Option.some_ne_none _
  · split
    · exact Option.some_ne_none _
    · split
      · exact Option.some_ne_none _
      · split
        · rename_i i _ _
          rw [externalRow_nil]
          exact Option.some_ne_none _
        · exact Option.some_ne_none _

/-- **With the empty table every accepted decision is a control.** -/
theorem accepted_nil_control {calls : List (List Nat × CallInstance NativeOp)} {m : NativeMachine}
    {d : NativeDecision} (h : Accepted [] calls m d) : IsControl d := by
  cases d with
  | answerAsync f t a =>
    obtain ⟨r, hr | hr⟩ := h
    · have henv := acceptReply_envelope [] m r _ hr
      have hd := acceptReply_decision [] m r _ hr
      cases hd
      exact absurd henv.2.2 (admit_nil_answer m _ _ _)
    · unfold acceptAtInstance at hr
      split at hr
      · split at hr
        · rename_i i origin _ _
          rw [externalRow_nil] at hr
          cases hr
        · cases hr
      · cases hr
  | fire _ => trivial
  | flush => trivial
  | evaluate _ => trivial
  | yieldVerdict _ _ => trivial
  | interruptFrom _ _ _ => trivial
  | installMiddleware => trivial
  | advance _ => trivial

/-- **A program with no host row has control histories only.** -/
theorem history_control {b : Api.Built} {compileFuel : Nat} {m : NativeMachine}
    (htable : b.table = []) (h : HistoryOf b compileFuel m) : ControlHistory b compileFuel m := by
  obtain ⟨history, adm, rfl⟩ := h
  refine ⟨history, ?_, rfl⟩
  have go : ∀ (xs : List (Nat × NativeDecision)) (m₀ : NativeMachine),
      Lift.Admitted (W := Unit) (fun _ _ => True)
        (fun _ m x => Accepted b.table (Api.HostSession.callTable b.program b.table) m x.2)
        (stepBy b) m₀ xs → ∀ x ∈ xs, IsControl x.2 := by
    intro xs
    induction xs with
    | nil => intro _ _ x hx; exact absurd hx List.not_mem_nil
    | cons y ys ih =>
      intro m₀ hadm x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · have hy := hadm.1 () trivial
        rw [htable] at hy
        exact accepted_nil_control hy
      · exact ih _ hadm.2 x hx
  exact go history _ adm

/-- The shop has no host row. -/
theorem shop_table {b : Api.Built} (hb : Effect4.Api.Author.build (shop .none) = .ok b) :
    b.table = [] :=
  (build_elaborates hb).2

/-- **The machine of every script's run on the shop is a control history.** -/
theorem scenario_control (b : Api.Built) (hb : Effect4.Api.Author.build (shop .none) = .ok b)
    (moves : List Move) :
    ControlHistory b budget.compileFuel (Test.Dogfood.Scenario.play (opened b) moves).machine :=
  history_control (shop_table hb) (scenario_history b moves)
