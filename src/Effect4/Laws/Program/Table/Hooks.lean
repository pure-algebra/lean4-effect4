import Effect4.Laws.Program.Simulation.Fibers

/-!
# Program.Table.Hooks — the reference machine's prepared answer agrees at a row table

Slice H5 of `docs/research/2026-10-07-packet-host-meaning.md` (decisions row 310; DI-57). The
three hook lemmas of the probe of 2026-10-03 (`docs/research/2026-10-03-di57-slice/probe/`),
proved again at this tree: related machines prepare the same store and related code for an
answer, at any row table. They are steps of `run_eq_ref_table`
(`Laws/Program/Table/Agreement.lean`); their consumer is `hooksAgree_of` at a row table (the
packet's slice H6). The file stands above the simulation's fibers and below its drive.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote


/-- The frame's external row, read off its current code as `prepareExternalAnswer` reads it. -/
def frameIndex : Option NCode → Option Nat
  | some (.async (.external (.external i) _) _ _) => some i
  | _ => none

/-- Related current codes wait on the same external row (`CodeMeans.asyncForeign`). -/
theorem index_agree (root : NativeEff) {c₁ : NCode} {c₂ : RProgram} (h : CodeMeans root c₁ c₂) :
    frameIndex (some c₁) = externalIndexR (some c₂) := by
  cases h with
  | asyncForeign op request k hk => cases op <;> rfl
  | _ => rfl

/-- The frame's prepared answer is `prepareAtR`'s at the frame's row, up to the code each
machine writes for a completion. -/
theorem prepare_agree (root : NativeEff) (table : RowTable) (cur : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (state : Stores) :
    (prepareExternalAnswer table cur answer state).1 =
        (prepareAtR table (frameIndex cur) answer state).1 ∧
      CodeMeans root (prepareExternalAnswer table cur answer state).2
        (prepareAtR table (frameIndex cur) answer state).2 := by
  unfold prepareExternalAnswer prepareAtR
  by_cases ht : table.isEmpty = true
  · rw [if_pos ht, if_pos ht]
    exact ⟨rfl, answerCode_means (table := table) root answer⟩
  · rw [if_neg ht, if_neg ht]
    split
    · rename_i i _ _ _ value
      simp only [frameIndex]
      cases hr : externalRow table i with
      | none => dsimp only; exact ⟨rfl, CodeMeans.success value⟩
      | some row =>
        dsimp only
        cases hv : externalValue row.answer state.externals.allocated value with
        | none => dsimp only; exact ⟨rfl, CodeMeans.success value⟩
        | some p => dsimp only; exact ⟨rfl, CodeMeans.success _⟩
    · rename_i hnot
      split
      · rename_i i value hidx
        exfalso
        unfold frameIndex at hidx
        split at hidx
        · rename_i j request withSignal cancel
          exact hnot j request withSignal cancel value rfl rfl
        · cases hidx
      · exact ⟨rfl, answerCode_means (table := table) root _⟩

theorem frame_prepareAnswer (root : NativeEff) (table : RowTable) :
    (interpOf root table).prepareAnswer = prepareExternalAnswer table := rfl

theorem term_prepareAnswer (root : NativeEff) (table : RowTable) :
    (interpR root table).prepareAnswer = fun current answer state =>
      prepareAtR table (externalIndexR current) answer state := rfl

/-- **The prepared-answer clause of `HooksAgree`, at any row table** (less its `StoresOk`
half): related machines prepare the same store and related code. -/
theorem prepareAsync_agree (root : NativeEff) (table : RowTable) (a : FMachine) (b : RState)
    (h : BookMeans (CodeMeans root) (Means root) a b) (id : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    (prepareAsyncAnswer (interpOf root table) a id token answer).1 =
        (prepareAsyncAnswer (interpR root table) b id token answer).1 ∧
      CodeMeans root (prepareAsyncAnswer (interpOf root table) a id token answer).2
        (prepareAsyncAnswer (interpR root table) b id token answer).2 := by
  unfold prepareAsyncAnswer
  by_cases hs : b.stuck.isSome = true
  · have hs' : a.stuck.isSome = true := by rw [h.stuck]; exact hs
    rw [if_pos hs, if_pos hs']
    exact ⟨h.state, answerCode_means (table := table) root answer⟩
  · have hs' : ¬ a.stuck.isSome = true := by rw [h.stuck]; exact hs
    rw [if_neg hs, if_neg hs', frame_prepareAnswer, term_prepareAnswer, h.state]
    rcases book_fiber?_cases h id with ⟨h₁, h₂⟩ | ⟨f₁, f₂, h₁, h₂, hf⟩
    · rw [h₁, h₂]
      exact prepare_agree root table none answer b.state
    · rw [h₁, h₂]
      have hc := hf.1
      unfold controlOf at hc
      injection hc with _ hpark
      have hcode : CodeMeans root f₁.frame.current f₂.frame.current :=
        hf.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      dsimp only
      rw [hpark]
      split
      · have := prepare_agree root table (some f₁.frame.current) answer b.state
        rw [index_agree root hcode] at this
        exact this
      · exact prepare_agree root table none answer b.state

/-- **A prepared answer keeps the store invariant**, at any row table: it writes the external
allocations alone, and at the empty row table it writes nothing. A step of the prepared-answer
clause of `hooksAgree_of` (slice H6a). -/
theorem prepareExternalAnswer_ok (table : RowTable) (cur : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) {s : Stores} (hs : StoresOk table s) :
    StoresOk table (prepareExternalAnswer table cur answer s).1 := by
  dsimp only [prepareExternalAnswer]
  split
  · exact hs
  · rename_i ht
    have hne : table ≠ [] := fun h => ht (by rw [h]; rfl)
    split
    · split
      · exact hs
      · split
        · exact hs
        · exact ⟨hs.keysFresh, fun h => absurd h hne, hs.answers⟩
    · exact hs

/-- The frame's prepared answer keeps the store invariant (`prepareExternalAnswer_ok`). -/
theorem prepareAsync_ok (root : NativeEff) (table : RowTable) (a : FMachine) (id : FiberId)
    (token : Nat) (answer : Completion Val Err Defect FiberId Ann) (hs : StoresOk table a.state) :
    StoresOk table (prepareAsyncAnswer (interpOf root table) a id token answer).1 := by
  unfold prepareAsyncAnswer
  split
  · exact hs
  · exact prepareExternalAnswer_ok table _ answer hs

end Effect4.Program.Sched
