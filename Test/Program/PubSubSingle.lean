import Effect4.Laws.Library.PubSub.Steps
import Effect4.Program.Native

/-! Readers of pubsub-single-steps-agree and finite controls of its capacity-one profile.
These controls retain multi-reader ownership, late registration, and stale-item eviction.
They establish no host delivery, cancellation, scope, or allocation claim. -/

set_option autoImplicit false
namespace Test.Program.PubSubSingle
open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Schema Effect4.Schema.Model Effect4.Modules
open Effect4.PubSub
open Effect4.PubSub.Model

def one : State := (subscribe initial 10).2
def two : State := (subscribe one 20).2
def published : State := (tryPublish two 7).2
def firstRead : State := (poll published 10).2
def late : State := (subscribe published 30).2
def lastLeft : State := (unsubscribe firstRead 20).2
def slid : State := (slide published).2
def replaced : State := (tryPublish slid 9).2

-- Finite latest-source interpretation controls; these are not preservation theorems.
example : Live initial := by unfold Live; decide
example : Live two := by unfold Live; decide
example : Live published := by unfold Live; decide
example : Live firstRead := by unfold Live; decide
example : Live late := by unfold Live; decide
example : Live lastLeft := by unfold Live; decide
example : Live slid := by unfold Live; decide
example : Live replaced := by unfold Live; decide

-- Current subscribers each own one read of the same message.
#guard (poll published 10).1 = some 7
#guard firstRead.remaining = 1
#guard firstRead.value = some 7
#guard (poll firstRead 10) = (none, firstRead)
#guard (poll firstRead 20).1 = some 7
#guard (poll firstRead 20).2.remaining = 0
#guard (poll firstRead 20).2.value = none
-- Wrong queue-like ownership: the first poll frees the shared slot.
#guard firstRead.remaining ≠ 0
#guard (poll firstRead 20).1 ≠ none

-- A subscriber added after publication owns no read of that retained item.
#guard late.remaining = 2
#guard (poll late 30) = (none, late)
#guard (unsubscribe late 30).2.remaining = 2
-- Wrong replay and removal predictions.
#guard (poll late 30).1 ≠ some 7
#guard (unsubscribe late 30).2.remaining ≠ 1

-- Full publication cannot replace the retained item.
#guard tryPublish published 9 = (false, published)
#guard (tryPublish published 9).2.value ≠ some 9
-- Already-read removal does not decrement another subscriber's retained ownership.
#guard (unsubscribe firstRead 10).2.remaining = 1
#guard (unsubscribe firstRead 10).2.value = some 7
#guard (unsubscribe firstRead 10).2.remaining ≠ 0
-- The last unread removal releases retention. Repeated removal is inert.
#guard lastLeft.remaining = 0
#guard lastLeft.value = none
#guard unsubscribe lastLeft 20 = ((), lastLeft)
#guard lastLeft.value ≠ some 7

-- No subscriber means successful discard with no index change.
#guard tryPublish initial 7 = (true, initial)
#guard (tryPublish initial 7).2.value ≠ some 7
#guard (tryPublish initial 7).2.publisherIndex ≠ 1

-- Sliding removes the stale item and leaves source cursors and index unchanged.
#guard slid.publisherIndex = published.publisherIndex
#guard slid.subscribers = published.subscribers
#guard (poll slid 10).1 = none
#guard replaced.publisherIndex = 2
#guard (poll replaced 10).1 = some 9
#guard (poll (poll replaced 10).2 20).1 = some 9
#guard (poll replaced 10).1 ≠ some 7
#guard slid.publisherIndex ≠ published.publisherIndex + 1

-- Freshness is necessary for the source interpretation's distinct live names.
example : ¬ Fresh published 10 := by unfold Fresh; decide
example : ¬ Live (subscribe published 10).2 := by unfold Live; decide
-- An impossible source state still has a total pure-data equation.
def impossible : State := { remaining := 1 }
example : ¬ Live impossible := by unfold Live; decide
example : Data.tryPublish.eval Leaves.refused (publishing impossible 9) =
    (false, encoded impossible) := tryPublish_eval impossible 9

-- Readers apply the independent connector at actual populated carriers.
example : Data.subscribe.eval Leaves.refused (named published 30) =
    ((), encoded late) := subscribe_eval published 30 (by unfold Fresh; decide)
example : Data.tryPublish.eval Leaves.refused (publishing two 7) =
    (true, encoded published) := tryPublish_eval two 7
example : Data.poll.eval Leaves.refused (named published 10) =
    (some (7 : Nat), encoded firstRead) := poll_eval published 10
example : Data.unsubscribe.eval Leaves.refused (named firstRead 20) =
    ((), encoded lastLeft) := unsubscribe_eval firstRead 20
example : Data.slide.eval (Γ := Data.CellInputs.types) Leaves.refused
    (input_values% (Data.CellInputs) (Leaves.refused) {cell := encoded published}) =
    ((), encoded slid) := slide_eval published

-- Real source terms compose all six reading connectors through projections.
def oneSrc : TermSrc := app "snd" [subscribeStep (nat 10) initialStep]
def twoSrc : TermSrc := app "snd" [subscribeStep (nat 20) oneSrc]
def publishedSrc : TermSrc := app "snd" [tryPublishStep (nat 7) twoSrc]

theorem oneReading : Reads oneSrc {} [] [] ((Modeled.image State).toVal one) :=
  reads_app (.cons (subscribe_reads initial 10 (reads_nat 10 {} [] []) initial_reads (by unfold Fresh; decide)) .nil) rfl
theorem twoReading : Reads twoSrc {} [] [] ((Modeled.image State).toVal two) :=
  reads_app (.cons (subscribe_reads one 20 (reads_nat 20 {} [] []) oneReading (by unfold Fresh; decide)) .nil) rfl
theorem publishedReading : Reads publishedSrc {} [] [] ((Modeled.image State).toVal published) :=
  reads_app (.cons (tryPublish_reads two 7 (reads_nat 7 {} [] []) twoReading) .nil) rfl

example : Reads (pollStep (nat 10) publishedSrc) {} [] []
    ((Store.Image.tuple2 (Store.Image.option Store.Image.nat) (Modeled.image State)).toVal
      (some 7, firstRead)) :=
  poll_reads published 10 rfl (reads_nat 10 {} [] []) publishedReading
example : Reads (unsubscribeStep (nat 20) publishedSrc) {} [] []
    ((Store.Image.tuple2 Store.Image.unit (Modeled.image State)).toVal (unsubscribe published 20)) :=
  unsubscribe_reads published 20 rfl (reads_nat 20 {} [] []) publishedReading
example : Reads (slideStep publishedSrc) {} [] []
    ((Store.Image.tuple2 Store.Image.unit (Modeled.image State)).toVal ((), slid)) :=
  slide_reads published publishedReading

-- Real typing consumers, including both subscriber-list folds.
theorem oneTyping : TypesEach nativeSignature oneSrc {} [] [] cellTy :=
  fun _ => types_app (.cons ((subscribe_types nativeSignature rfl (types_nat 10) (initial_types nativeSignature rfl)) false) .nil) rfl
theorem twoTyping : TypesEach nativeSignature twoSrc {} [] [] cellTy :=
  fun _ => types_app (.cons ((subscribe_types nativeSignature rfl (types_nat 20) oneTyping) false) .nil) rfl
theorem publishedTyping : TypesEach nativeSignature publishedSrc {} [] [] cellTy :=
  fun _ => types_app (.cons ((tryPublish_types nativeSignature rfl (types_nat 7) twoTyping) false) .nil) rfl
example : TypesEach nativeSignature (pollStep (nat 10) publishedSrc) {} [] [] (.prod (.option .nat) cellTy) :=
  poll_types nativeSignature rfl rfl (types_nat 10) publishedTyping
example : TypesEach nativeSignature (unsubscribeStep (nat 20) publishedSrc) {} [] [] (.prod .unit cellTy) :=
  unsubscribe_types nativeSignature rfl rfl (types_nat 20) publishedTyping
example : TypesEach nativeSignature (slideStep publishedSrc) {} [] [] (.prod .unit cellTy) :=
  slide_types nativeSignature rfl publishedTyping

-- Finite source evaluation reads the stored term, with no theorem restatement.
#guard match pollStep (nat 10) publishedSrc {} [] with
  | .ok term => evalTerm [] term == some
      ((Store.Image.tuple2 (Store.Image.option Store.Image.nat) (Modeled.image State)).toVal (some 7, firstRead))
  | .error _ => false
#guard match pollStep (nat 10) publishedSrc {} [] with
  | .ok term => termTy nativeSignature [] term == some (.prod (.option .nat) cellTy)
  | .error _ => false

end Test.Program.PubSubSingle
