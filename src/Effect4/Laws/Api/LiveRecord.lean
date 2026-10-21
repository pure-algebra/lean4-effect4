import Effect4.Run.LiveRecord
import Effect4.Laws.Api.Live
import Effect4.Laws.Program.CheckedTyping
import Effect4.Laws.Api.Built

/-!
# Laws.Api.LiveRecord — restoration and byte round-trip of a saved live session

Slice E of the authoring plan (`docs/research/2026-10-17-proof-scout/README.md` §7.5).

* **A saved live session restores to the same run** (`restore_save`): `LiveRecord.restore` accepts
  `LiveRecord.save l` and replays its journal to `l.run`.
* **An unknown format version is refused** (`restore_unsupportedVersion`): `LiveRecord.restore`
  returns `.error (.unsupportedVersion r.version)` when `r.version ≠ LiveRecord.currentVersion`.

The record's bytes are its generated `Canonical` instance's, whose round trip is the codec laws'.
-/

set_option autoImplicit false

namespace Effect4.LiveRecord

open Effect4 Effect4.Program Effect4.Store

/-- **A saved live session restores to the same run** (E1). Saving a `Live` session and restoring
it through `LiveRecord.restore` succeeds and produces a `Live` whose `run` is `l.run`, including
its journal, phases, waiting calls and row spellings.

Placement:
1. Concept: `host-session-protocol`, property `typed-replay-session`.
2. Question: proposed claim `live-session-persists` (role compatibility), extending
   `Live.journal_replays` at R13; consumer: the tool's `restore` action and its run record query (`Tool.Internal.action`, `Tool.Internal.query`).
3. Reach: every `Live`. Composes `admitProgram_eq_ok`, `Live.feedAll_wire` and
   `Live.journal_replays`.
4. What it does not establish: that another host's journal replays, host reconnection, external
   resources, or that side effects run at most once.
5. Unlocks: R13 and R6 for persistent authoring sessions. -/
@[semantics "host-session-protocol" (requirement := R13)]
theorem restore_save (l : Live) :
    ∃ l', restore (save l) = .ok l' ∧ l'.run = l.run := by
  refine ⟨(Live.open l.run.built l.run.id l.run.budget l.run.profile).feedAll
    (l.run.journal.map .wire), ?_, ?_⟩
  · unfold restore save
    dsimp only [ne_eq, not_true_eq_false, ↓reduceIte]
    unfold Object.open Object.ofBuilt
    rw [Api.Built.ofProgram_of_admitted _ _ l.run.built.admitted]
    rfl
  · rw [Live.feedAll_wire]
    exact Live.journal_replays l

/-- **An unknown format version is refused by `restore`.**

Placement:
1. Concept: `host-session-protocol`, property `typed-replay-session`.
2. Question: helper step of `live-session-persists`; consumer: the tool's `restore` refusal path (`Tool.Refusal.restore`).
3. Reach: every `LiveRecord` with `r.version ≠ currentVersion`.
4. What it does not establish: admission of a record at `currentVersion`.
5. Unlocks: R13. -/
theorem restore_unsupportedVersion (r : LiveRecord) (h : r.version ≠ currentVersion) :
    restore r = .error (.unsupportedVersion r.version) := by
  unfold restore
  simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]

end Effect4.LiveRecord
