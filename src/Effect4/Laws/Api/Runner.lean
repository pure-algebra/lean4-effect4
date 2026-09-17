import Effect4.Api.Runner

/-!
# Laws.Api.Runner: refusal is a verdict, and journals act on runners

* `step_refused`: a row whose phase is a refusal leaves the runner exactly as it was. Each
  checked transition of `HostSession` answers its refusals with the session it was given, so a
  journal may hold refused rows and still replay to the same runner.
* `replay_append`: playing `a ++ b` is playing `a`, then `b` from the runner `a` reached, with
  the phases concatenated. Journals under concatenation act on runners, which is what lets a
  holder stop at any row and another instance take the rest.
* `replay_nil`, `replay_cons`: the unfolding.
-/

set_option autoImplicit false

namespace Effect4.Api.Runner

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Api.HostSession (Session Call Reply Key Result)

section refusals

variable {program : Api.Program} {table : RowTable} (s : Session program table)

theorem bindCall_refused (call : Call) (token : Nat) (why : HostSession.Refusal) :
    (HostSession.bindCall s call token).phase = .refused why →
      (HostSession.bindCall s call token).session = s := by
  unfold HostSession.bindCall
  dsimp only
  repeat' split
  all_goals intro h; cases h <;> rfl

theorem submit_refused (reply : Reply) (why : HostSession.Refusal) :
    (HostSession.submit s reply).phase = .refused why →
      (HostSession.submit s reply).session = s := by
  unfold HostSession.submit
  repeat' split
  all_goals intro h; cases h <;> rfl

theorem applyReply_refused (key : Key) (fuel : Nat) (why : HostSession.Refusal) :
    (HostSession.applyReply s key fuel).phase = .refused why →
      (HostSession.applyReply s key fuel).session = s := by
  cases fuel with
  | zero => intro h; simp only [HostSession.applyReply] at h; cases h
  | succ fuel =>
    unfold HostSession.applyReply
    dsimp only
    repeat' split
    all_goals intro h; cases h <;> rfl

theorem advance_refused (fuel : Nat) (decision : NativeDecision) (why : HostSession.Refusal) :
    (HostSession.advance s fuel decision).phase = .refused why →
      (HostSession.advance s fuel decision).session = s := by
  unfold HostSession.advance
  dsimp only
  repeat' split
  all_goals intro h; cases h <;> rfl

end refusals

/-- A refused row leaves the runner unchanged. -/
theorem step_refused (p : Runner) (c : Command) (why : HostSession.Refusal)
    (h : (step p c).2 = .refused why) : (step p c).1 = p := by
  have hs : (result p c).session = p.session := by
    cases c with
    | bind call token => exact bindCall_refused p.session call token why h
    | submit reply => exact submit_refused p.session reply why h
    | apply key => exact applyReply_refused p.session key p.fuel why h
    | control decision => exact advance_refused p.session p.fuel decision why h
  show ({ p with session := (result p c).session } : Runner) = p
  rw [hs]

theorem replay_nil (p : Runner) : replay p [] = (p, []) := rfl

theorem replay_cons (p : Runner) (c : Command) (rest : List Command) :
    replay p (c :: rest) =
      ((replay (step p c).1 rest).1, (step p c).2 :: (replay (step p c).1 rest).2) := rfl

/-- Journals act on runners: a concatenation plays as its parts, in order. -/
theorem replay_append (p : Runner) (a b : List Command) :
    replay p (a ++ b) =
      ((replay (replay p a).1 b).1, (replay p a).2 ++ (replay (replay p a).1 b).2) := by
  induction a generalizing p with
  | nil => rfl
  | cons c rest ih =>
    rw [List.cons_append, replay_cons, replay_cons, ih]
    rfl

/-- The runner a journal reaches is reached through any split of it. -/
theorem replay_append_player (p : Runner) (a b : List Command) :
    (replay p (a ++ b)).1 = (replay (replay p a).1 b).1 := by
  rw [replay_append]

/-! ## The algebra

`step` is a Mealy machine on runners: a coalgebra `Runner → (Command → Runner × Phase)`.
Three structures follow from it, and nothing else about a holder needs proving.

1. **Journals act.** A `Play` is a runner transformer that also writes phases (a Kleisli arrow
   of the writer over `List Phase`). Plays form a monoid under `Play.comp` with unit `Play.id`
   (`Play.id_comp`, `Play.comp_id`, `Play.comp_assoc`), and `replayPlay` is a monoid
   homomorphism into it from journals under concatenation (`replayPlay_nil`,
   `replayPlay_append`).
2. **`replay` is the only such map.** Journals are the free monoid on commands, so a
   homomorphism is fixed by what it does on single rows: `replay_unique`.
3. **Behaviour.** `behaviour p` is what a runner can be observed to do, the phases of every
   journal. It unfolds along `step` (`behaviour_cons`), which makes it the map into the final
   Mealy machine; two instances that agree on it are the same runner to every holder.

One law joins the refusal to the algebra: a refused row is the unit. It can be dropped from a
journal without changing the runner reached or any later phase (`replay_skip_refused`,
`behaviour_skip_refused`), so a journal has a normal form with no refused rows, which is what
a compaction may keep. -/

/-- A runner transformer that writes the phases it passes through. -/
abbrev Play := Runner → Runner × List HostSession.Phase

/-- The play that does nothing. -/
def Play.id : Play := fun p => (p, [])

/-- One play, then another from the runner the first reached; phases in order. -/
def Play.comp (f g : Play) : Play := fun p =>
  ((g (f p).1).1, (f p).2 ++ (g (f p).1).2)

theorem Play.id_comp (f : Play) : Play.comp Play.id f = f := by
  funext p
  simp only [Play.comp, Play.id, List.nil_append]

theorem Play.comp_id (f : Play) : Play.comp f Play.id = f := by
  funext p
  simp only [Play.comp, Play.id, List.append_nil]

theorem Play.comp_assoc (f g h : Play) :
    Play.comp (Play.comp f g) h = Play.comp f (Play.comp g h) := by
  funext p
  simp only [Play.comp, List.append_assoc]

/-- A journal as a play. -/
def replayPlay (journal : List Command) : Play := fun p => replay p journal

theorem replayPlay_nil : replayPlay [] = Play.id := rfl

/-- Journals under concatenation map to plays under composition. -/
theorem replayPlay_append (a b : List Command) :
    replayPlay (a ++ b) = Play.comp (replayPlay a) (replayPlay b) := by
  funext p
  exact replay_append p a b

/-- One row as a play. -/
def stepPlay (c : Command) : Play := fun p => ((step p c).1, [(step p c).2])

theorem replayPlay_single (c : Command) : replayPlay [c] = stepPlay c := rfl

/-- Journals are the free monoid on commands: a homomorphism into plays that sends a single
row to its step is `replay`. -/
theorem replay_unique (h : List Command → Play) (hnil : h [] = Play.id)
    (hsingle : ∀ c, h [c] = stepPlay c)
    (happend : ∀ a b, h (a ++ b) = Play.comp (h a) (h b)) :
    ∀ journal, h journal = replayPlay journal
  | [] => hnil
  | c :: rest => by
    have hc : c :: rest = [c] ++ rest := rfl
    rw [hc, happend, hsingle, replay_unique h hnil hsingle happend rest, replayPlay_append,
      replayPlay_single]

/-- What a runner can be observed to do: the phases of every journal. -/
def behaviour (p : Runner) (journal : List Command) : List HostSession.Phase :=
  (replay p journal).2

theorem behaviour_nil (p : Runner) : behaviour p [] = [] := rfl

/-- Behaviour unfolds along `step`: the first phase, then the behaviour of the next runner. -/
theorem behaviour_cons (p : Runner) (c : Command) (rest : List Command) :
    behaviour p (c :: rest) = (step p c).2 :: behaviour (step p c).1 rest := rfl

/-- A refused row is the unit of the action: dropping it reaches the same runner. -/
theorem replay_skip_refused (p : Runner) (c : Command) (rest : List Command)
    (why : HostSession.Refusal) (h : (step p c).2 = .refused why) :
    (replay p (c :: rest)).1 = (replay p rest).1 := by
  rw [replay_cons, step_refused p c why h]

/-- And every later phase is what it would have been without the refused row. -/
theorem behaviour_skip_refused (p : Runner) (c : Command) (rest : List Command)
    (why : HostSession.Refusal) (h : (step p c).2 = .refused why) :
    behaviour p (c :: rest) = .refused why :: behaviour p rest := by
  rw [behaviour_cons, step_refused p c why h, h]

end Effect4.Api.Runner
