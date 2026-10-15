import Test.Dogfood.Scenario
import Test.Dogfood.Scenario.Timeout.Model
import Effect4.Laws.Run.Journal

/-!
# Host journal readers for the timeout observation

The concept is `host-session-protocol`, requirement R6.
The helpers serve the existing `timeout` claim through `stale_never_applies`.
The proved reader covers its first three clauses for every built program and every script.
The fourth clause concerns the timeout program's answer provenance and remains open.
The host boundary stays at `docs/core/host-boundary.md`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
namespace Test.Dogfood.Proofs.HostJournal
open Effect4 Effect4.Machine Effect4.Program Effect4.Run
open Effect4.Api.HostSession (Key)
open Test.Dogfood.Scenario (Move Seen)
open Test.Dogfood.Scenario.Timeout

theorem filterMap_map_sublist {α β γ : Type} (l : List α) (f : α → Option β)
    (g : α → Option γ) (k : β → γ) (h : ∀ a b, f a = some b → g a = some (k b)) :
    ((l.filterMap f).map k).Sublist (l.filterMap g) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a rest ih =>
    cases hf : f a with
    | none =>
      rw [List.filterMap_cons_none hf]
      cases hg : g a with
      | none =>
        rw [List.filterMap_cons_none hg]
        exact ih
      | some c =>
        rw [List.filterMap_cons_some hg]
        exact List.Sublist.cons c ih
    | some b =>
      rw [List.filterMap_cons_some hf, List.filterMap_cons_some (h a b hf), List.map_cons]
      exact List.Sublist.cons_cons (k b) ih

theorem filterMap_map_sublist_map {α β γ : Type} (l : List α) (f : α → Option β)
    (g : α → γ) (k : β → γ) (h : ∀ a b, f a = some b → g a = k b) :
    ((l.filterMap f).map k).Sublist (l.map g) := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a rest ih =>
    rw [List.map_cons]
    cases hf : f a with
    | none =>
      rw [List.filterMap_cons_none hf]
      exact List.Sublist.cons (g a) ih
    | some b =>
      rw [List.filterMap_cons_some hf, List.map_cons, h a b hf]
      exact List.Sublist.cons_cons (k b) ih

/-- A held call that `seenAt` finds carries the key it was asked for. -/
theorem seenAt_key (s : Run) (key : Key) (seen : Seen)
    (h : Test.Dogfood.Scenario.seenAt s key = some seen) : seen.key = key := by
  have hfound := List.find?_some h
  exact beq_iff_eq.mp hfound

/-- The receipts' keys are among the accepted receipt rows' keys. -/
theorem receipts_sublist (s : Run) :
    ((Test.Dogfood.Scenario.receipts s).map (·.key)).Sublist (submittedKeys s) := by
  refine filterMap_map_sublist _ _ _ _ (fun row seen hf => ?_)
  obtain ⟨c, ph⟩ := row
  cases c with
  | submit reply =>
    cases ph with
    | preflight =>
      show some reply.key = some seen.key
      rw [seenAt_key s reply.key seen hf]
    | bound => cases hf
    | applied => cases hf
    | progressed => cases hf
    | frontier => cases hf
    | refused _ => cases hf
  | bind _ _ => cases hf
  | apply _ => cases hf
  | control _ => cases hf

/-- The applications' keys are among the applied rows' keys. -/
theorem applications_sublist (s : Run) :
    ((Test.Dogfood.Scenario.applications s).map (·.key)).Sublist (appliedKeys s) := by
  refine filterMap_map_sublist _ _ _ _ (fun row seen hf => ?_)
  obtain ⟨c, ph⟩ := row
  cases c with
  | apply key =>
    cases ph with
    | applied =>
      show some key = some seen.key
      rw [seenAt_key s key seen hf]
    | bound => cases hf
    | preflight => cases hf
    | progressed => cases hf
    | frontier => cases hf
    | refused _ => cases hf
  | bind _ _ => cases hf
  | submit _ => cases hf
  | control _ => cases hf

/-- The observed retired calls' keys are among the session's retired keys. -/
theorem retired_sublist (s : Run) :
    ((Test.Dogfood.Scenario.retired s).map (·.1.key)).Sublist (retiredKeys s) := by
  refine filterMap_map_sublist_map _ _ _ _ (fun call entry hf => ?_)
  unfold Test.Dogfood.Scenario.seenOf at hf
  cases hrow : s.rowOf call.bound.call.op with
  | none =>
    rw [hrow] at hf
    cases hf
  | some row =>
    rw [hrow] at hf
    cases hf
    rfl

/-- **Clauses one to three of `stale_never_applies`, for every program.** On every run that a
script reaches from an opened program, the observation's retired keys have no application, and
its receipts and applications name each key once. Read through `session_keys_once`. -/
theorem stale_clauses (b : Api.Built) (moves : List Move) :
    (Test.Dogfood.Scenario.Timeout.observe (Test.Dogfood.Scenario.play (opened b) moves)).retired.all
        (fun entry => !(Test.Dogfood.Scenario.Timeout.observe (Test.Dogfood.Scenario.play (opened b) moves)).applications.contains
          entry.1) = true ∧
      decide (Test.Dogfood.Scenario.Timeout.observe (Test.Dogfood.Scenario.play (opened b) moves)).receipts.Nodup = true ∧
      decide (Test.Dogfood.Scenario.Timeout.observe (Test.Dogfood.Scenario.play (opened b) moves)).applications.Nodup = true := by
  have hreach : Run.Reached (Test.Dogfood.Scenario.play (opened b) moves) :=
    Test.Dogfood.Scenario.reached_play _ moves (Run.Reached.opened _ _ _ _)
  obtain ⟨-, hsub, happ, hret⟩ := session_keys_once _ hreach
  refine ⟨List.all_eq_true.mpr (fun entry hentry => ?_), decide_eq_true
    ((receipts_sublist _).nodup hsub), decide_eq_true ((applications_sublist _).nodup happ)⟩
  refine not_contains_iff.mpr (fun hin => ?_)
  have hr : entry.1 ∈ retiredKeys (Test.Dogfood.Scenario.play (opened b) moves) := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hentry
    exact (retired_sublist _).subset (List.mem_map.mpr ⟨e, he, rfl⟩)
  exact hret _ hr ((applications_sublist _).subset hin)


end Test.Dogfood.Proofs.HostJournal
