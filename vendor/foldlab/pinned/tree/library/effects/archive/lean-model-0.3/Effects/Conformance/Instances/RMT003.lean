import Effects.Conformance.Schema.TraceExcludes
import Effects.Conformance.Rider
import Effects.Conformance.Instances.RemoteKit
import Effects.Remote.Laws

/-!
# RMT-003 — integrity is terminal for those bytes

TRACE-EXCLUDES over the remote client machine at the identifier-dropped
projection: the guarded mode is "this key-content pair stands
integrity-rejected" — membership in the set-valued terminal-integrity
memory, which only ever grows — and the excluded decision is issuing an
upload command for that pair under any operation identifier. The
backing theorems are temporal: the per-step exclusion composes with
rejection-set monotonicity into the whole-run corollary, and both are
carried structurally by the sentence riders below. The negative kit is
the same request from a state with no rejection on record, which does
issue.
-/

namespace Effects.Conformance

open Effects.Remote

private abbrev MSt := MachineState Nat (List UInt8)
private abbrev MIn := MInput Nat (List UInt8)
private abbrev MDec := RDecision Nat (List UInt8)

private def rejectedState : MSt :=
  { rmtEmpty with
    rejected := (∅ : Std.HashSet (Nat × List UInt8)).insert (2, [7, 9]) }

/-- RMT-003: an integrity failure is terminal for those bytes — no wire
attempt ever repeats unchanged content. -/
def rmt003 : TraceExcludes MSt MIn MDec Bool where
  id := "RMT-003"
  sentence := "When a key-content pair stands integrity-rejected, no step ever issues an upload command carrying that key and that exact content again, under any operation identifier — the rejection memory only grows, so an integrity failure is terminal for those bytes over the whole run, and only changed content can try the wire."
  modeOf := fun s => s.rejected.contains (2, [7, 9])
  guarded := true
  decisions := fun s i =>
    ((Effects.Remote.step rmtParams s i).decisions).map Prod.snd
  bad := .issued (.upload 2 [7, 9])
  law := fun s i hm => by
    intro hmem
    simp only [List.mem_map] at hmem
    obtain ⟨p, hp, hpd⟩ := hmem
    obtain ⟨pid, pd⟩ := p
    cases hpd
    exact RMT_003_no_repeat_after_integrity rmtParams s i 2 [7, 9]
      (Std.HashSet.contains_iff_mem.mp hm) pid hp
  posState := rejectedState
  posInput := .request 1 (.upload 2 [7, 9])
  pos_mode := by simp [rejectedState]
  negState := rmtEmpty
  negInput := .request 1 (.upload 2 [7, 9])
  neg_mode := by simp [rmtEmpty]
  neg_bad := by simp [Effects.Remote.step, rmtEmpty, rmtParams]

/-- "The rejection memory only grows": per-step monotonicity of the
terminal-integrity set, over every machine instantiation. -/
def rmt003MonotoneRider : SentenceRider :=
  .of "RMT-003" "the rejection memory only grows"
    (@RMT_003_rejection_monotone)

/-- "Terminal over the whole run": the per-step exclusion composed with
monotonicity into the run corollary. -/
def rmt003RunRider : SentenceRider :=
  .of "RMT-003"
    "an integrity failure is terminal for those bytes over the whole run"
    (@RMT_003_terminal_over_run)

end Effects.Conformance
