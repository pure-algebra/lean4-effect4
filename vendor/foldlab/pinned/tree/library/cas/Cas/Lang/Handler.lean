import Cas.Lang.Interp

/-!
# Handlers — one syntax, every semantics an instance

The general account of effectful computation this language commits to
(EFFECTS-BACKEND R10): `Prog S` is SYNTAX — a free monad over the
signature, meaning nothing by itself. A semantics is a `Handler S M` —
one meaning per operation in a target monad — and `interpret` is the
monad morphism it induces. Every interface the estate has built is an
instance:

- the REFERENCE semantics (`referenceHandler`): the admission judgment
  in `StateT Word (Except Refusal)` — Lean's pure meaning, the
  semantic oracle every realization is claimed against;
- the production Effect adapter (slice 2's generated programs): the
  same operations handled into `Effect<_, CasError, R>` — fibers,
  interruption, and the error channel are the target monad's
  contribution, never the language's;
- replay: the degenerate handler whose answers come from a recorded
  word — the oracle-from-content direction;
- a transport (CLI, daemon, HTTP): handler COMPOSITION — a signature
  translation into a wire language whose handler lives across a
  process seam, and the seam's own effects (failure, cancellation,
  backpressure) are operations of their own signature, never smuggled.

Because `Prog` is finite (the HITrees-honest carrier, R1), `interpret`
lands in ANY monad by structural recursion — no iteration requirement
on the target. ITrees' `MonadIter` obligation returns exactly when F3
adds loops, and will be taken then, not smuggled now.

`interpret_bind` is the monad-morphism law, proved once for every
handler. The agreement of `interpretRef` (big-step) with the fueled
small-step `run` — R10's named obligation of the F3 increment — is
DISCHARGED below (`run_interpretRef_agree`); see that section's note
for the shape triage forced on it.
-/

namespace Cas.Lang

/-- A semantics: one meaning per operation, in a target monad. -/
structure Handler (S : Sig) (M : Type → Type v) where
  handle : (op : S.Op) → M (S.Ans op)

/-- The monad morphism a handler induces. Total by structural
recursion — finite syntax interprets into any monad. -/
def interpret [Monad M] (h : Handler S M) : Prog S A → M A
  | .pure a => pure a
  | .vis op k => h.handle op >>= fun answer => interpret h (k answer)

/-- The monad-morphism law: interpretation respects `bind`, for every
handler into every (lawful) target. One proof, all semantics. -/
theorem interpret_bind [Monad M] [LawfulMonad M] (h : Handler S M)
    (p : Prog S A) (f : A → Prog S B) :
    interpret h (p.bind f) = interpret h p >>= fun a => interpret h (f a) := by
  induction p with
  | pure a => simp [interpret, Prog.bind]
  | vis op k ih =>
    simp only [interpret, Prog.bind, bind_assoc]
    exact bind_congr fun answer => ih answer

/-- Handlers compose across a signature sum: handle either side. -/
def Handler.sum (h : Handler S M) (g : Handler T M) : Handler (S ⊕ₛ T) M where
  handle
    | .inl op => h.handle op
    | .inr op => g.handle op

section Reference

variable (H : Bytes → Addr32)

/-- The reference target: the store word threaded, refusal terminal. -/
abbrev RefM := StateT Word (Except Refusal)

/-- THE reference semantics: the admission judgment, per operation —
the same clauses as `step`, packaged as a handler. Meaning lives here;
every other interface is an adapter claimed against it. -/
def referenceHandler : Handler CasSig (RefM) where
  handle
    | .put n => fun w =>
      if h : n.WF then
        match _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ with
        | .error e => .error (.ofAdmission e)
        | .ok (.fresh a _) => .ok (a, w ++ [Binding.mk a n])
        | .ok (.duplicate a) => .ok (a, w)
        | .ok (.conflict a _) => .error (.collision a)
      else .error .notWellFormed
    | .load a => fun w =>
      match Word.find w a with
      | some n => .ok (n, w)
      | none => .error (.noObject a)
    | .fail reason => fun _ => .error (.failed reason)

/-- Big-step reference interpretation: a program's meaning over a
word — no fuel, total, the denotation `run` approximates step-wise. -/
def interpretRef (p : Prog CasSig A) (w : Word) :
    Except Refusal (A × Word) :=
  interpret (referenceHandler H) p w

/-! ### The bridge — big-step meaning against the fueled run

R10's named F3 obligation, discharged here. Statement triage found two
facts about its shape, stated rather than papered over.

**The refusal word.** The two sides carry DIFFERENT information when a
program refuses. `run` reports `(.refused r, w)` — the PARTIAL word,
every binding admitted before the refusing operation — while
`interpretRef` lands in `Except Refusal (A × Word)`, whose error branch
has no word slot at all. The divergence is in the TYPES, not in an
accident of the clauses, so no theorem can relate the words: on refusal
the two sides agree on the REFUSAL and on nothing else. The statements
below say exactly that, and the asymmetry propagates honestly into the
`ObsEq` corollaries (`Representation.lean`).

**The fuel.** Soundness needs no bound — a halted run is right at every
fuel. Completeness needs one, and it is EXISTENTIAL rather than a
program size, because `Prog`'s continuations are host functions: there
is no structural measure to quantify over (`Prog.vis` branches over an
answer type that is `Addr32`, not a finite index). `run_of_interpretRef`
therefore PRODUCES the fuel by structural induction and closes it
upward, so "enough fuel" is a conclusion, not a hypothesis. The
defunctionalized fragment, where a size does exist, keeps its exact
bound instead (`Defun.runP_embed_agree`, fuel `p.length + 1`) — this
bridge is the general statement that fragment is a special case of. -/

/-- One operation, small-step side: `step` IS the reference handler's
clause, reified into `Status`. The handler's answer continues the
program at the handler's word; the handler's refusal is `step`'s
refusal, at the word the step was reached with. Every clause — put (the
admission judgment), load (`Word.find`), fail — by the same equation. -/
theorem step_handle (op : CasSig.Op) (k : CasSig.Ans op → Prog CasSig A)
    (w : Word) :
    step H (.vis op k) w
      = match (referenceHandler H).handle op w with
        | .ok (ans, w') => (.running (k ans), w')
        | .error r => (.refused r, w) := by
  cases op with
  | put n =>
    by_cases h : n.WF
    · cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ with
      | error e => simp [step, referenceHandler, dif_pos h, hp]
      | ok o => cases o <;> simp [step, referenceHandler, dif_pos h, hp]
    · simp [step, referenceHandler, dif_neg h]
  | load a => cases hf : Word.find w a <;> simp [step, referenceHandler, hf]
  | fail reason => simp [step, referenceHandler]

/-- One operation, big-step side: interpretation consumes the handler's
clause and continues at its word, or stops at its refusal. -/
theorem interpretRef_vis (op : CasSig.Op) (k : CasSig.Ans op → Prog CasSig A)
    (w : Word) :
    interpretRef H (.vis op k) w
      = match (referenceHandler H).handle op w with
        | .ok (ans, w') => interpretRef H (k ans) w'
        | .error r => .error r := by
  cases h : (referenceHandler H).handle op w with
  | ok aw =>
    obtain ⟨ans, w'⟩ := aw
    simp [interpretRef, interpret, bind, StateT.bind, Except.bind, h]
  | error r =>
    simp [interpretRef, interpret, bind, StateT.bind, Except.bind, h]

/-- SOUNDNESS, done half: a run that has finished reports exactly the
reference meaning — value AND word. No fuel bound: this holds at every
fuel a run happens to halt at. -/
theorem interpretRef_of_run_done {A} :
    ∀ (fuel : Nat) {p : Prog CasSig A} {w w' : Word} {a : A},
      run H fuel p w = (.done a, w') → interpretRef H p w = .ok (a, w')
  | 0, p, w, w', a, h => by simp [run] at h
  | fuel + 1, p, w, w', a, h => by
    cases p with
    | pure a₀ =>
      simp only [run, step, Prod.mk.injEq, Status.done.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rfl
    | vis op k =>
      rw [run] at h
      rw [step_handle H op k w] at h
      cases hh : (referenceHandler H).handle op w with
      | error r => simp only [hh] at h; simp at h
      | ok aw =>
        obtain ⟨ans, w''⟩ := aw
        simp only [hh] at h
        rw [interpretRef_vis H op k w, hh]
        exact interpretRef_of_run_done fuel h

/-- SOUNDNESS, refused half: a run that has refused reports exactly the
reference's refusal — and NOTHING about the word, which is where the
two representations part company. -/
theorem interpretRef_of_run_refused {A} :
    ∀ (fuel : Nat) {p : Prog CasSig A} {w w' : Word} {r : Refusal},
      run H fuel p w = (.refused r, w') → interpretRef H p w = .error r
  | 0, p, w, w', r, h => by simp [run] at h
  | fuel + 1, p, w, w', r, h => by
    cases p with
    | pure a₀ => simp [run, step] at h
    | vis op k =>
      rw [run] at h
      rw [step_handle H op k w] at h
      cases hh : (referenceHandler H).handle op w with
      | error r₀ =>
        simp only [hh, Prod.mk.injEq, Status.refused.injEq] at h
        rw [interpretRef_vis H op k w, hh, h.1]
      | ok aw =>
        obtain ⟨ans, w''⟩ := aw
        simp only [hh] at h
        rw [interpretRef_vis H op k w, hh]
        exact interpretRef_of_run_refused fuel h

/-- COMPLETENESS, with the fuel PRODUCED rather than assumed: for every
program and starting word there is a fuel past which the run reports
the reference outcome — value and word on success; on refusal the
refusal together with SOME word, the partial history the `Except` side
does not carry. -/
theorem run_of_interpretRef (p : Prog CasSig A) (w : Word) :
    ∃ fuel : Nat, ∀ f, fuel ≤ f →
      match interpretRef H p w with
      | .ok (a, w') => run H f p w = (.done a, w')
      | .error r => ∃ w', run H f p w = (.refused r, w') := by
  induction p generalizing w with
  | pure a =>
    refine ⟨1, fun f hf => ?_⟩
    obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
    show (match interpretRef H (Prog.pure a) w with
      | .ok (a, w') => run H (f' + 1) (Prog.pure a) w = (.done a, w')
      | .error r => ∃ w', run H (f' + 1) (Prog.pure a) w = (.refused r, w'))
    have hi : interpretRef H (Prog.pure a) w = .ok (a, w) := rfl
    rw [hi]
    simp [run, step]
  | vis op k ih =>
    cases hh : (referenceHandler H).handle op w with
    | error r =>
      refine ⟨1, fun f hf => ?_⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      rw [interpretRef_vis H op k w, hh]
      refine ⟨w, ?_⟩
      rw [run, step_handle H op k w, hh]
    | ok aw =>
      obtain ⟨ans, w'⟩ := aw
      obtain ⟨fuel, hfuel⟩ := ih ans w'
      refine ⟨fuel + 1, fun f hf => ?_⟩
      obtain ⟨f', rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
      have hstep : step H (.vis op k) w = (.running (k ans), w') := by
        rw [step_handle H op k w, hh]
      rw [interpretRef_vis H op k w, hh, run_step_running H hstep f']
      exact hfuel f' (by omega)

/-- THE BRIDGE (EFFECTS-BACKEND R10's named F3 obligation, discharged):
the fueled small-step `run` and the big-step reference interpretation
are ONE semantics. Past a fuel this theorem produces, the run answers
`done` with a value and word exactly when the reference answers `ok`
with that value and word, and refuses with a reason exactly when the
reference errors with that reason — the run's partial word left
existential, because it is information `Except Refusal (A × Word)` has
nowhere to hold. -/
theorem run_interpretRef_agree (p : Prog CasSig A) (w : Word) :
    ∃ fuel : Nat, ∀ f, fuel ≤ f →
      (∀ (a : A) (w' : Word),
          run H f p w = (.done a, w') ↔ interpretRef H p w = .ok (a, w'))
        ∧ (∀ r : Refusal,
          (∃ w', run H f p w = (.refused r, w'))
            ↔ interpretRef H p w = .error r) := by
  obtain ⟨fuel, hfuel⟩ := run_of_interpretRef H p w
  refine ⟨fuel, fun f hf => ⟨fun a w' => ⟨interpretRef_of_run_done H f, ?_⟩,
    fun r => ⟨fun ⟨w', hw'⟩ => interpretRef_of_run_refused H f hw', ?_⟩⟩⟩
  · intro hok
    have := hfuel f hf
    rw [hok] at this
    exact this
  · intro herr
    have := hfuel f hf
    rw [herr] at this
    exact this

end Reference

/-- Replay: the recorded word is the oracle. A put must answer the
next recorded binding for its exact node — recorded history handled as
a semantics, the co-direction of recording. -/
def replayHandler :
    Handler CasSig (StateT Word (Except Refusal)) where
  handle
    | .put n => fun w =>
      match w with
      | [] => .error (.failed "replay: word exhausted")
      | b :: rest =>
        if b.node == n then .ok (b.address, rest)
        else .error (.failed "replay: put differs from the recorded binding")
    | .load a => fun w =>
      match Word.find w a with
      | some n => .ok (n, w)
      | none => .error (.noObject a)
    | .fail reason => fun _ => .error (.failed reason)

end Cas.Lang
