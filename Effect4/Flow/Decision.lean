import Effects.Flow.Block

/-!
# Flow.Decision

Owner: explicit replay decisions (ruling R6 of the trace lane).

A `choose` block is answered by a *choice tape*, consumed by occurrence: the
head entry must name the site being decided. A mismatch is a refusal (the tape
was written for another flow), exhaustion is a live frontier (the run is not
over, it is unanswered). The scheduler's tape is a different object and is
fixed to the single-fiber preset in this phase.
-/

namespace Effect4.Flow

open Effects

/-- One replayed decision: the site it answers and the branch taken. -/
structure Decision where
  site : DecisionId
  branch : Bool
deriving DecidableEq, Repr

/-- A finite choice tape, consumed front to back. -/
abbrev Tape := List Decision

/-- Reading one decision off the tape at a site. -/
inductive TapeRead where
  | exhausted
  | mismatch (expected actual : DecisionId)
  | answered (branch : Bool) (rest : Tape)
deriving DecidableEq, Repr

/-- Consume the head entry for `site`; the site must match. -/
def Tape.read : Tape → DecisionId → TapeRead
  | [], _ => .exhausted
  | decision :: rest, site =>
      if decision.site = site then .answered decision.branch rest
      else .mismatch site decision.site

/-- The wire projection of a tape, as goldens and receipts record it. -/
def Tape.wire (tape : Tape) : List (Nat × Bool) :=
  tape.map fun decision => (decision.site.value, decision.branch)

namespace Tape

theorem read_nil (site : DecisionId) : Tape.read [] site = .exhausted := rfl

theorem read_cons_eq (site : DecisionId) (branch : Bool) (rest : Tape) :
    Tape.read (⟨site, branch⟩ :: rest) site = .answered branch rest := by
  simp [Tape.read]

theorem read_cons_ne {expected actual : DecisionId} (ne : actual ≠ expected)
    (branch : Bool) (rest : Tape) :
    Tape.read (⟨actual, branch⟩ :: rest) expected = .mismatch expected actual := by
  simp [Tape.read, ne]

/-- A tape read never refuses a site against itself: `Tape.read` reports a
mismatch only when the head entry names *another* site. This is what makes
`expected = actual` an unambiguous marker of the Flow v3 value refusal
(`Effect4.Flow.RunResult.refusal`, `E4-FLOW-CE-029`). -/
theorem read_mismatch_ne {tape : Tape} {site expected actual : DecisionId}
    (read : Tape.read tape site = .mismatch expected actual) :
    expected = site ∧ actual ≠ expected := by
  cases tape with
  | nil => cases read
  | cons decision rest =>
      by_cases same : decision.site = site
      · simp only [Tape.read, if_pos same] at read
        cases read
      · simp only [Tape.read, if_neg same] at read
        obtain ⟨rfl, rfl⟩ := TapeRead.mismatch.inj read
        exact ⟨rfl, fun eq => same (by rw [eq])⟩

/-- An answered read consumed exactly one entry. -/
theorem read_answered_length {tape : Tape} {site : DecisionId} {branch : Bool} {rest : Tape}
    (answered : Tape.read tape site = .answered branch rest) :
    rest.length + 1 = tape.length := by
  cases tape with
  | nil => cases answered
  | cons decision more =>
      by_cases same : decision.site = site
      · simp only [Tape.read, if_pos same] at answered
        obtain ⟨-, rfl⟩ := TapeRead.answered.inj answered
        rfl
      · simp only [Tape.read, if_neg same] at answered
        cases answered

end Tape

end Effect4.Flow
