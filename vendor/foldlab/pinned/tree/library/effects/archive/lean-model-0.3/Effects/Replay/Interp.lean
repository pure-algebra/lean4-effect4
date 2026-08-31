import Effects.Replay.Program
import Effects.Replay.Reducer

/-!
# Interpreting reified programs through the reducer

The interpretation carrier is Lean's own `EStateM`: its `Result` is
ok-with-state or error-with-state — the error carries the state it
stopped at, which is exactly the threading the compositionality
obligation demands (an `ExceptT`-over-`StateT` stack would drop the
state on failure; `EStateM` is the built-in that keeps it).

A leaf interprets as one reducer step on the session state, so the
interpretation inherits the reducer's semantics rather than restating
them: substitution hands the envelope to the continuation with the
consumed state; a typed rejection halts with the aborted state; a leaf
under an already-aborted session halts as absorbed — a totality case,
not a behavior (the interpreter split never starts a program on an
aborted session). The `replay_invoke_result` lemma pins that these
three are the only reachable leaf results in replay mode.

The state carrier is the replay-mode sub-carrier of the session state:
the reducer never changes the mode, so it is closed under every step.
-/

namespace Effects.Replay

variable {Op Req Val Err : Type} {α β : Type}

/-- The reducer never changes the session mode. -/
theorem reduce_preserves_mode [DecidableEq Op] [DecidableEq Req]
    (s : SessionState Op Req Val Err) (i : Input Op Req Val Err) :
    (reduce s i).state.mode = s.mode := by
  unfold reduce
  split
  · rfl
  · split <;>
      simp only [invokeRecord, appendRecord, abortRecord, completeStep,
        invokeReplay, rejectStep, absorb] <;>
      (try split) <;> (try split) <;> (try split) <;> (try split) <;> rfl

/-- Replay-mode session states: the interpretation's threaded state,
closed under every reducer step because the mode never changes. -/
abbrev ReplayState (Op Req Val Err : Type) :=
  { s : SessionState Op Req Val Err // s.mode = .replay }

/-- Why an interpretation stopped short of a value: the program's own
typed failure, the session's typed rejection at a position, or a leaf
reached under an already-aborted session. -/
inductive Halt (Err : Type) where
  | failed (e : Err)
  | rejected (category : MismatchCategory) (pos : Nat)
  | absorbed
  deriving DecidableEq

/-- Interpret a reified program: each leaf is one reducer step on the
session state. The codomain is Lean's `EStateM` over the replay-mode
carrier — success threads the state, every halt carries the state it
stopped at. -/
def interpE [DecidableEq Op] [DecidableEq Req] :
    Prog Op Req Val Err α →
      EStateM (Halt Err) (ReplayState Op Req Val Err) α
  | .pure a, s => .ok a s
  | .fail e, s => .error (.failed e) s
  | .invoke inv k, s =>
    have hm : (reduce s.val (.invoke inv)).state.mode = .replay :=
      (reduce_preserves_mode s.val (.invoke inv)).trans s.property
    match (reduce s.val (.invoke inv)).result with
    | .substituted out => interpE (k out) ⟨(reduce s.val (.invoke inv)).state, hm⟩
    | .rejected c pos => .error (.rejected c pos) ⟨(reduce s.val (.invoke inv)).state, hm⟩
    | _ => .error .absorbed ⟨(reduce s.val (.invoke inv)).state, hm⟩

/-- In replay mode an invocation step substitutes, rejects, or is
absorbed — never delegation, an append, or a completion result. The
interpretation's catch-all arm is reachable only as absorption. -/
theorem replay_invoke_result [DecidableEq Op] [DecidableEq Req]
    (s : SessionState Op Req Val Err) (inv : Invocation Op Req)
    (hm : s.mode = .replay) :
    (∃ out, (reduce s (.invoke inv)).result = .substituted out) ∨
      (∃ c pos, (reduce s (.invoke inv)).result = .rejected c pos) ∨
      (reduce s (.invoke inv)).result = .absorbed := by
  cases hst : s.status with
  | aborted =>
    have hr : reduce s (.invoke inv) = absorb s := by
      unfold reduce; rw [hst]
    rw [hr]; exact .inr (.inr rfl)
  | active =>
    have hr : reduce s (.invoke inv) = invokeReplay s inv := by
      unfold reduce; rw [hst, hm]
    rw [hr]; unfold invokeReplay
    split
    · exact .inr (.inl ⟨_, _, rfl⟩)
    · split
      · split
        · split
          · exact .inl ⟨_, rfl⟩
          · exact .inr (.inl ⟨_, _, rfl⟩)
        · exact .inr (.inl ⟨_, _, rfl⟩)
      · exact .inr (.inl ⟨_, _, rfl⟩)

/-- CMP-001, return half: interpreting a returned value is `EStateM`'s
own `pure` — it consumes nothing and threads the state unchanged. -/
theorem CMP_001_interp_pure [DecidableEq Op] [DecidableEq Req]
    (a : α) (s : ReplayState Op Req Val Err) :
    interpE (Prog.pure a) s = .ok a s := rfl

/-- CMP-001, bind half: interpretation is a monad morphism into
`EStateM` — interpreting a sequential composition is `EStateM`'s own
bind of the interpretations, so a nested program continues from exactly
the state its prefix reached: success threads it, and every halt
short-circuits carrying it. The cursor neither resets nor forks. -/
theorem CMP_001_interp_bind [DecidableEq Op] [DecidableEq Req]
    (p : Prog Op Req Val Err α) (f : α → Prog Op Req Val Err β)
    (s : ReplayState Op Req Val Err) :
    interpE (p.bind f) s =
      match interpE p s with
      | .ok a s' => interpE (f a) s'
      | .error e s' => .error e s' := by
  induction p generalizing s with
  | pure a => rfl
  | fail e => rfl
  | invoke inv k ih =>
    simp only [Prog.bind, interpE]
    split
    · exact ih _ _
    · rfl
    · rfl

end Effects.Replay
