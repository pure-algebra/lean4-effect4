import Effect4.Api.RunnerBytes
import Effect4.Laws.Api.Runner

/-!
# Laws of the runner at the byte boundary

A journal of rows means what the journal of commands it spells means, and nothing else:

* a row that reads is the one spelling of its command (`commandOf_exact`), and a well-formed
  command's row reads back (`commandOf_commandBytes`);
* playing a row is playing its command (`stepRow_command`); an unreadable row leaves the
  runner alone (`stepRow_unreadable`);
* rows act on runners as commands do: `replayRows` distributes over concatenation
  (`replayRows_append`);
* a journal whose rows all read replays exactly as `Runner.replay` of the commands
  (`replayRows_eq_replay`), so every law of `Laws/Api/Runner.lean` holds at the boundary.
-/

set_option autoImplicit false

namespace Effect4.Api.Runner

open Effect4 Effect4.Store
open Effect4.Api.HostSession (Phase)

/-- A row that reads is exactly its command's bytes, and the command is well-formed. -/
theorem commandOf_exact {row : Bytes} {c : Command} (h : commandOf row = some c) :
    row = commandBytes c ∧ (Canonical.toVal c).WF :=
  Canonical.decode_exact h

/-- A well-formed command's row reads back. -/
theorem commandOf_commandBytes (c : Command) (h : (Canonical.toVal c).WF) :
    commandOf (commandBytes c) = some c :=
  Canonical.decode_encode c h

/-- Two rows that read as one command are one row. -/
theorem row_unique {a b : Bytes} {c : Command} (ha : commandOf a = some c)
    (hb : commandOf b = some c) : a = b := by
  rw [(commandOf_exact ha).1, (commandOf_exact hb).1]

/-- Playing a row is playing its command. -/
theorem stepRow_command (p : Runner) {row : Bytes} {c : Command} (h : commandOf row = some c) :
    stepRow p row = ((step p c).1, some (step p c).2) := by
  unfold stepRow
  rw [h]

/-- A row that is not a command changes nothing, and its verdict says so. -/
theorem stepRow_unreadable (p : Runner) {row : Bytes} (h : commandOf row = none) :
    stepRow p row = (p, none) := by
  unfold stepRow
  rw [h]

/-- The written row of a well-formed command plays as the command. -/
theorem stepRow_commandBytes (p : Runner) (c : Command) (h : (Canonical.toVal c).WF) :
    stepRow p (commandBytes c) = ((step p c).1, some (step p c).2) :=
  stepRow_command p (commandOf_commandBytes c h)

theorem replayRows_nil (p : Runner) : replayRows p [] = (p, []) := rfl

theorem replayRows_cons (p : Runner) (row : Bytes) (rest : List Bytes) :
    replayRows p (row :: rest) =
      ((replayRows (stepRow p row).1 rest).1,
        (stepRow p row).2 :: (replayRows (stepRow p row).1 rest).2) := rfl

/-- Rows act on runners: a journal played in two parts is the journal played whole. -/
theorem replayRows_append (p : Runner) (a b : List Bytes) :
    replayRows p (a ++ b) =
      ((replayRows (replayRows p a).1 b).1,
        (replayRows p a).2 ++ (replayRows (replayRows p a).1 b).2) := by
  induction a generalizing p with
  | nil => rfl
  | cons row rest ih =>
    rw [List.cons_append, replayRows_cons, replayRows_cons, ih]
    rfl

/-- A journal whose rows all read replays as the journal of commands it spells. -/
theorem replayRows_eq_replay (p : Runner) (rows : List Bytes) (commands : List Command)
    (h : rows.mapM commandOf = some commands) :
    replayRows p rows = ((replay p commands).1, (replay p commands).2.map some) := by
  induction rows generalizing p commands with
  | nil =>
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    rfl
  | cons row rest ih =>
    simp only [List.mapM_cons, bind, Option.bind_eq_some_iff, pure, Option.some.injEq] at h
    obtain ⟨c, hc, cs, hcs, hx⟩ := h
    subst hx
    rw [replayRows_cons, stepRow_command p hc, ih (step p c).1 cs hcs, replay_cons]
    rfl

/-- The written journal of well-formed commands replays as the commands. -/
theorem replayRows_commandBytes (p : Runner) (commands : List Command)
    (h : ∀ c ∈ commands, (Canonical.toVal c).WF) :
    replayRows p (commands.map commandBytes) =
      ((replay p commands).1, (replay p commands).2.map some) := by
  apply replayRows_eq_replay
  induction commands with
  | nil => rfl
  | cons c rest ih =>
    rw [List.map_cons, List.mapM_cons, commandOf_commandBytes c (h c (List.mem_cons_self ..)),
      ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]
    rfl

#print axioms commandOf_exact
#print axioms row_unique
#print axioms stepRow_command
#print axioms replayRows_append
#print axioms replayRows_eq_replay
#print axioms replayRows_commandBytes

end Effect4.Api.Runner
