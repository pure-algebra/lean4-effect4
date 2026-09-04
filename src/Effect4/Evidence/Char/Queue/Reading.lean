import Effect4.Evidence.Char.Queue.Machine

/-!
# Char.Queue.Reading: the delivery reading, the failure model, the clean machine

`workshop/Char/01-model/05-reading-client-index.md`. The queue has the unit
client: an rc.112 `Queue` is a single dequeue (`takeAll` is
`takeBetween(self, 1, +∞)` on the one `Dequeue`, `Queue.ts:1297`), and
`releaseTakers` walks the takers handing each the same message list until the
buffer empties (`Queue.ts:1955-1967`), so two takers split one stream. `offer`
is the only accepting label; `takeAll` and `wake` are the only emitting ones and
emit the same chunk; `residue` is the buffer, which is the port of
`size_eq_length` (`EffectQueueLaws.lean:51-54`), true by `rfl` since `size` is
an observation and not a verb.

The failure model `queueCrash` is `F-none` under ruling R1: a graded run may
contain neither `fail` nor `shutdown`. `queueClean cap` is the queue restricted
to the admitted labels, and `QOpened` is its one-clause invariant, which is not
an invariant of `queue cap` because `fail` breaks it.

`Queue.ts` citations are at rc.112, `vendor/effect-4.0.0-rc.112/src/Queue.ts`,
SHA-256 `dc355d1a…`.
-/

set_option autoImplicit false

namespace Effect4.Char.Queue

open Effect4.Char

/-- The queue's reading at the unit client. -/
def queueReading : Reading QState QLabel Unit where
  accepts := fun l => match l with | .offer m => some ((), m) | _ => none
  emits := fun l => match l with
    | .takeAll c => c.map (fun m => ((), m))
    | .wake c => c.map (fun m => ((), m))
    | _ => []
  residue := fun s _ => s.buffer

/-- The port of `size_eq_length`: the residue is the buffer. The `Done → 0` arm
of `sizeUnsafe` (`Queue.ts:1789`) is not modelled; on every reachable state the
two agree by `QInv.doneEmpty` and `QInv.shutdownClear`, which is the owed row
`queue_size_agrees_on_reachable` in `Grade.lean`. -/
theorem queue_residue_eq_buffer (s : QState) : queueReading.residue s () = s.buffer := rfl

/-- `F-none`: nothing bad happens in a graded run. -/
def queueCrash : Failure QKind where
  name := "F-none"
  excluded := [.fail, .shutdown]
  escapes := ["a failed queue keeps a non-empty buffer and delivers it on the next take",
              "a shutdown discards the buffer"]

/-- The queue on words that stay inside `F-none`. -/
def queueClean (cap : Nat) : Machine QState QLabel :=
  (queue cap).restrict (queueCrash.admits queueKinds)

/-- On a run that contains no excluded label the queue never leaves `opened`.
Not an invariant of `queue cap`: `fail` breaks it. It is an invariant of
`queueClean cap`. -/
def QOpened (s : QState) : Prop := s.status = QStatus.opened

/-- The one induction of the clean machine. -/
theorem qOpened_inductive (cap : Nat) : Inductive (queueClean cap) QOpened where
  init := rfl
  step := by
    intro s s' l hi hstep0
    simp only [QOpened] at hi
    obtain ⟨hadm, hstep⟩ := Machine.step_restrict_some hstep0
    cases l <;>
      (try (simp [queueCrash, queueKinds, Failure.admits, qKind] at hadm)) <;>
      simp only [queue, hi] at hstep <;>
      (try split at hstep) <;>
      first
        | (injection hstep with heq
           subst heq
           rfl)
        | injection hstep

end Effect4.Char.Queue
