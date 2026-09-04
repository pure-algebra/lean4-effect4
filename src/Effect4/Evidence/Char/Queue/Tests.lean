import Effect4.Evidence.Char.Queue.Reading

/-!
# Char.Queue.Tests: the suite and its receipt

Hand-authored part 4 of the five. Seven tests at `cap = 2`, two of them
negative, from `workshop/Char/01-model/04-mutants.md` section 3. The suite is
capacity-free data; the capacity is a parameter of the machine the receipts name
(`07-open-questions.md` Q6). `over-capacity-refused` needs a *third* offer at
`cap = 2`, which is the one row that differs from the design report's suite.

Each test's word is at most four labels over a three-field state whose only
unbounded field is a `List Nat` of length at most three, so kernel reduction of
`Suite.run` is linear in the word and the receipt is well under a second.
-/

set_option autoImplicit false

namespace Effect4.Char.Queue

open Effect4.Char

/-- The queue's suite. Every word is a fixture; the replay driver is built from
this list. -/
def queueTests : Suite QLabel Unit :=
  [ { name := "drain", labels := [.offer 1, .offer 2, .takeAll [1, 2]],
      residue := [((), [])] }
  , { name := "fifo", labels := [.offer 1, .offer 2, .takeAll [1, 2], .offer 3],
      residue := [((), [3])] }
  , { name := "park-then-wake", labels := [.takePark, .offer 1, .wake [1]],
      residue := [((), [])] }
  , { name := "closing-keeps-buffer", labels := [.offer 1, .fail 7, .takeAll [1]],
      residue := [((), [])] }
  , { name := "shutdown-discards", labels := [.offer 1, .shutdown],
      residue := [((), [])] }
  , { name := "over-capacity-refused", labels := [.offer 1, .offer 2, .offer 3],
      accept := false }
  , { name := "one-at-a-time-refused", labels := [.offer 1, .offer 2, .takeAll [1]],
      accept := false } ]

/-- The model passes its own suite. Seven runs of at most four steps, one
`decide`. -/
theorem queue_tests_pass : Suite.run (queue 2) queueReading queueTests = true := by decide

/-! ## Receipts pinning `Grade.holds` on literal runs

`07-open-questions.md` Q7: a change to `Grade.holds` should fail a test rather
than re-interpret a theorem. Two runs at `Grade.top` under `F-none`, each one
`decide` over a three-label word. -/

/-- The drain word holds at the top grade. -/
theorem queue_holds_top_drain :
    Grade.holds queueReading queueKinds queueCrash Grade.top ()
      [.offer 1, .offer 2, .takeAll [1, 2]]
      { buffer := [], status := .opened, taker := false } = true := by decide

/-- A word that offers one item twice does **not** hold at the top grade: the
`noDup` axis of `Grade.holds` carries no freshness hypothesis, so a queue that
faithfully delivers a duplicate it was handed fails it. This is the receipt
behind `Refute.queue_graded_top_refuted` in `Grade.lean`. -/
theorem queue_holds_top_dup :
    Grade.holds queueReading queueKinds queueCrash Grade.top ()
      [.offer 1, .offer 1, .takeAll [1, 1]]
      { buffer := [], status := .opened, taker := false } = false := by decide

end Effect4.Char.Queue
