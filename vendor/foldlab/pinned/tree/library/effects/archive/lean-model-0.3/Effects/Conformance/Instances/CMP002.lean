import Effects.Conformance.Schema.Distinctness
import Effects.Replay.Run

/-!
# CMP-002 — identical requests remain separate occurrences

DISTINCTNESS over the solicited record-mode call pair: an emission is one
lawful invoke/recorded pair, which claims the current position and
advances it, so two emissions — even with byte-identical invocation
content and outcome — carry distinct occurrence positions. Position is
the occurrence identity; the store deduplicates request nodes while the
history keeps entries distinct. The carrier is the clean active
record-mode sub-state — no outstanding delegation — which the solicited
pair returns to.
-/

namespace Effects.Conformance

open Effects.Replay

/-- A clean active record-mode session: the states a solicited call pair
acts on, closed under the pair. -/
private abbrev Rec :=
  { s : SessionState String String String String //
      s.status = .active ∧ s.mode = .record ∧ s.pending = none }

private abbrev EmitIn := Invocation String String × Outcome String String

private def emitOccurrence (s : Rec) (io : EmitIn) : Nat × Rec :=
  (s.val.cursor,
    ⟨(run s.val (soliciting [io])).1, by
      have h := SES_003_solicited_run_appends_in_order [io] s.val
        s.property.1 s.property.2.1 s.property.2.2
      exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩)

private def start : Rec := ⟨⟨.record, .active, [], 0, none⟩, rfl, rfl, rfl⟩

private def sameCall : EmitIn :=
  (⟨"acme/Rates/get", 1, "req-0"⟩, .success "ok")

/-- CMP-002: identical invocation content never collapses occurrences. -/
def cmp002 : Distinctness Rec EmitIn Nat EmitIn where
  id := "CMP-002"
  sentence := "Two occurrences with identical invocation content remain distinct occurrence positions — the store deduplicates request nodes while the history keeps entries distinct; position is the occurrence identity, and every solicited call pair claims a fresh one."
  contentOf := id
  emit := emitOccurrence
  law := fun s i i' _ => by
    have h1 := SES_003_solicited_run_appends_in_order [i] s.val
      s.property.1 s.property.2.1 s.property.2.2
    simp only [emitOccurrence]
    rw [h1.2.1]
    simp only [List.length_cons, List.length_nil]
    omega
  posState := start
  posInput := sameCall
  posInput' := sameCall
  pos_content := rfl

end Effects.Conformance
