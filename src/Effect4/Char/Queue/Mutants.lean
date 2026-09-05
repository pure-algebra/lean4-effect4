import Effect4.Char.Queue.Tests

/-!
# Char.Queue.Mutants: the three mutants, the receipts, and the kept refutations

Hand-authored part 5 of the five, from `docs/research/2026-09-05-workshop-char/01-model/04-mutants.md`.
Quarantined by layout: this module imports the model and nothing imports it.
Each mutant replaces one arm of `queue 2` and inherits every other, which is the
parametric-hole discipline. A survivor is a build failure, because the kills are
`decide`d theorems; no kill rate is published.

`Q-W1` is the mutant the frame laws could not exclude
(`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/ApplyLaws.lean:171-175`),
and it is visible in the local balance table: its `takeAll` row reads
`b ++ [] = [b.head] ++ b.tail`, true only for one-element buffers.

The `Refute` namespace keeps the design report's uncorrected `takeExit` arm
refutable (`docs/research/2026-09-04-semantic-api-type-design.md:1637`), per the
estate's rule for a post-freeze correction.

`Queue.ts` citations are at rc.112, `vendor/effect-4.0.0-rc.112/src/Queue.ts`,
SHA-256 `dc355d1a…`.
-/

set_option autoImplicit false

namespace Effect4.Char.Queue

open Effect4.Char

/-! ## The mutants -/

/-- Q-W1: `takeAll` drains one element instead of the whole buffer. -/
def queueW1 : Machine QState QLabel where
  init := (queue 2).init
  step := fun s l =>
    match l, s.status with
    | .takeAll c, .opened =>
        if s.buffer ≠ [] ∧ c = s.buffer.take 1 then
          some { s with buffer := s.buffer.drop 1 } else none
    | _, _ => (queue 2).step s l

/-- Q-W2: `fail` discards a non-empty buffer and finishes at once, instead of
becoming `closing e` and keeping it (`Queue.ts:1006-1014`, `EffectQueue.lean:84`). -/
def queueW2 : Machine QState QLabel where
  init := (queue 2).init
  step := fun s l =>
    match l, s.status with
    | .fail e, .opened => some { s with buffer := [], status := .done e }
    | _, _ => (queue 2).step s l

/-- Q-W3: `shutdown` keeps the buffer instead of discarding it
(`Queue.ts:1196` `MutableList.clear`, `EffectQueue.lean:89`). Deliberately
violates `QInv.shutdownClear`: the carrier must be able to express the grade's
failure. -/
def queueW3 : Machine QState QLabel where
  init := (queue 2).init
  step := fun s l =>
    match l, s.status with
    | .shutdown, _ => some { s with status := .shutdown, taker := false }
    | _, _ => (queue 2).step s l

/-- The register. `attacks` names the obligation each mutant attacks. -/
def queueMutants : List (Mutant QState QLabel) :=
  [ { id := "Q-W1", attacks := "queue_conservation"
    , represents := "the tests notice a take that drains one element instead of the whole buffer"
    , machine := queueW1 }
  , { id := "Q-W2", attacks := "queue_graded"
    , represents := "the tests notice a fail that discards a non-empty buffer instead of keeping it"
    , machine := queueW2 }
  , { id := "Q-W3", attacks := "queue_noLoss_at_quiescence"
    , represents := "the tests notice a shutdown that keeps the buffer instead of discarding it"
    , machine := queueW3 } ]

/-! ## The receipts

The two aggregates are the gate; the six per-pair receipts are what a reader
needs, because the aggregate says only that *some* test moved. Each `decide` is
at most seven runs of at most four steps. -/

/-- Every mutant is killed by the suite: 21 runs, one `decide`. -/
theorem queue_mutants_killed :
    queueMutants.all (Mutant.killed queueReading queueTests) = true := by decide

/-- No kill is vacuous: every mutant passes some test. 21 runs, one `decide`. -/
theorem queue_mutants_not_vacuous :
    queueMutants.all (Mutant.survivesSome queueReading queueTests) = true := by decide

/-- `drain` kills W1: after two offers `takeAll [1, 2]` is refused. One run. -/
theorem w1_fails_drain : Test.run queueW1 queueReading queueTests[0]! = false := by decide

/-- `shutdown-discards` touches no `takeAll`, so W1 passes it. One run. -/
theorem w1_passes_shutdown : Test.run queueW1 queueReading queueTests[4]! = true := by decide

/-- `closing-keeps-buffer` kills W2: the buffer is gone and `takeAll [1]` is
disabled on `done 7`. One run. -/
theorem w2_fails_closing : Test.run queueW2 queueReading queueTests[3]! = false := by decide

/-- `drain` contains no `fail`, so W2 passes it. One run. -/
theorem w2_passes_drain : Test.run queueW2 queueReading queueTests[0]! = true := by decide

/-- `shutdown-discards` kills W3 through the residue: the word is accepted and
the residue is `[1]`, not `[]`. One run. -/
theorem w3_fails_shutdown : Test.run queueW3 queueReading queueTests[4]! = false := by decide

/-- `drain` contains no `shutdown`, so W3 passes it. One run. -/
theorem w3_passes_drain : Test.run queueW3 queueReading queueTests[0]! = true := by decide

/-! ## The kept refutation of the design report's `takeExit` arm -/

namespace Refute

/-- The design report's step (`semantic-api-type-design.md:1637`): `takeExit`
does not clear the taker. Every other arm is the model's. -/
def queueDoc (cap : Nat) : Machine QState QLabel where
  init := (queue cap).init
  step := fun s l =>
    match l, s.status with
    | .takeExit e, .done e' => if e = e' then some { s with status := .shutdown } else none
    | _, _ => (queue cap).step s l

/-- The word `takePark; fail 7; takeExit 7` reaches a state with a parked taker
on a shut-down queue, which `QInv.takerLive` forbids. Three steps, `decide`. -/
theorem doc_step_breaks_takerLive :
    (queueDoc 4).run (queueDoc 4).init [.takePark, .fail 7, .takeExit 7]
      = some { buffer := [], status := .shutdown, taker := true } := by
  decide

/-- The corrected arm clears the taker on the same word. Three steps, `decide`. -/
theorem fix_step_keeps_takerLive :
    (queue 4).run (queue 4).init [.takePark, .fail 7, .takeExit 7]
      = some { buffer := [], status := .shutdown, taker := false } := by
  decide

end Refute

end Effect4.Char.Queue
