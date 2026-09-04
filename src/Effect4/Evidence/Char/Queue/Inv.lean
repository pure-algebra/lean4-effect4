import Effect4.Evidence.Char.Queue.Machine

/-!
# Char.Queue.Inv: the representation invariant and its one induction

Hand-authored part 3 of the five, first half: `QInv` with five named clauses,
transliterated from `QueueInv`
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/RtInvariants.lean:25-36`),
and its single `Inductive` witness, `qInv_inductive`, per
`workshop/Char/01-model/02-qinv-clauses.md`. The queue lemmas of
`RtReachable.lean:524-790` are each one arm of this witness. No second induction
over `Reach` is written here or anywhere in the component; every reachable-state
fact goes through `Inductive.reach` or `Machine.reach_ind`.

`Queue.ts` citations are at rc.112, `vendor/effect-4.0.0-rc.112/src/Queue.ts`,
SHA-256 `dc355d1a…`.
-/

set_option autoImplicit false

namespace Effect4.Char.Queue

open Effect4.Char

/-- The queue's representation invariant at capacity `cap`. Five clauses, one
per proof site. -/
structure QInv (cap : Nat) (s : QState) : Prop where
  /-- A parked taker is cleared by `shutdown` and by `takeExit`; it can coexist
  with a non-empty buffer, because `offer` appends and only *schedules* the
  release (`Queue.ts:666-667`, `:1969-1975`). -/
  takerLive : s.taker = true → s.status ≠ .shutdown
  /-- `fail` finishes an empty buffer at once; `takeAll` finishes a drained
  `closing` queue in the same step (`Queue.ts:2042-2046`). -/
  doneEmpty : ∀ e, s.status = .done e → s.buffer = []
  /-- `fail` keeps a non-empty buffer; nothing empties it without finishing.
  This is why an empty `closing` queue never exists. -/
  closingNonempty : ∀ e, s.status = .closing e → s.buffer ≠ []
  /-- `shutdown` clears the buffer and the taker together (`Queue.ts:1191-1210`). -/
  shutdownClear : s.status = .shutdown → s.buffer = [] ∧ s.taker = false
  /-- `offer` admits only below capacity. -/
  capacity : s.buffer.length ≤ cap

/-- The one induction. Only `offer` (for `capacity`) and `takeExit` (for
`shutdownClear`, through `doneEmpty`) consume a clause of the incoming
invariant; every other arm re-establishes the clauses from its own guard.
Elaboration: the 28-arm `simp_all` is about 60 percent of this module's wall
time (`workshop/Char/01-model/06-guarded-graded.md` section 3). -/
theorem qInv_inductive (cap : Nat) : Inductive (queue cap) (QInv cap) where
  init := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all [queue]
  step := by
    intro s s' l hi hstep
    obtain ⟨tl, dE, cN, sC, cp⟩ := hi
    cases l <;> cases hs : s.status <;>
      simp only [queue, hs] at hstep <;>
      (try split at hstep) <;>
      first
        | (injection hstep with heq
           subst heq
           refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> intros <;> simp_all <;> omega)
        | injection hstep

/-- Every reachable state satisfies `QInv`; the bootstrap for the corollaries
of a later slice. -/
theorem qInv_reach (cap : Nat) {s : QState} (h : Machine.Reach (queue cap) s) : QInv cap s :=
  (qInv_inductive cap).reach h

end Effect4.Char.Queue
