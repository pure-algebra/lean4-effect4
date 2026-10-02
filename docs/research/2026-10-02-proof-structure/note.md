# The scheduler's obligations by structure: frames, token senders, and the host reply

2026-10-02, claude/proofs at `179ee784`. A design note before the remaining M6 steps (`wake`,
`loop`, `deliver`, `launch`, `registrationDone`), written because the thirteen proved steps and
thirteen edits already cost about 7,100 lines of threading (`Typed/Commands/*.lean`,
`Typed/Edits.lean`), most of it rebuilding clauses a step never touched. No proof is claimed here;
the pilot (§7) is the first test of the claims.

## 1. The finding

Every preservation proof so far is three kinds of work, and only the third depends on the command:

1. **Frames.** A clause of `J` or `I` reads a few parts of the machine (its *views*); a step writes
   a few. A clause whose views the step does not write holds after it by rewriting. Today each
   proof rebuilds whole records (`MachineWide`, `FiberTyped`, `QueueOk`, `HeadOk`) field by field,
   so adding one clause touched about twenty sites (`a7294954`).
2. **Token senders.** A parked fiber waits on a token. Exactly one party will answer it: a timer, a
   Deferred waiter (pending or in a batch), an owed `due` entry, a queued `resume`, a race, a
   stored or queued observer, a dispatcher task, or the host. Each kind has its own clause saying
   its answer fits the token's declared type (`w.Θ`). A step moves the answering role from one
   kind to another, and each move needs one implication between the two kinds' demands.
3. **The edited fiber's code.** The typing rules for the code a step installs (`resume_step`,
   `evaluate_entry`, `storeStep_typed`, the fiber rows of `M3bAdequacy`).

Items 1 and 2 are tables. Written once, they turn each remaining step into: name the views it
writes, name the transfers it makes, prove item 3.

## 2. Tokens are one-shot typed channels

A token `(fiber, n)` is a channel used once, between one sender and one receiver.

- **The type.** `w.Θ fiber n`, declared when the token is allocated and never changed afterwards
  (`World.le` extends `Θ`, it never rewrites it).
- **The receiver.** The fiber parked on the token: its saved stack accepts the declared type
  (`ActiveDelivery`).
- **The sender.** Exactly one, of the kinds below. Its clause is always the same shape: *the key is
  declared, and what this sender will deliver fits the declaration.*
- **Exclusivity.** At most one sender per key, below the token supply: `InternalKeysBelow`,
  `requestsOwned`, `ReservedKeysR`, `raceObservers`. A token is consumed at most once: the
  `resume` arm lands only on a park at that exact token (`Machine/Fibers.lean:1865-1878`), and the
  landing clears the park.

| Sender kind | Where its keys live | Its clause today | What it delivers |
| --- | --- | --- | --- |
| timer | `state.timers.wake` | `WorldValid.timers` (row 134 (a)) | `void` |
| Deferred waiter | each cell's `wake`, pending and batch | `WorldValid.waiters` (row 134 (b)) | the cell's completion |
| owed resume | `state.deferreds.due` | `PromiseTableOk.due` | its completion |
| queued resume | `Cmd.resume` in the queue | `QueueOk.payload` (`ResumeOk`) | its code |
| race | `(race.host, race.token)` | `RegistrationState`, `RacePayload` | the race's result |
| stored observer | `fiber.observers` | `ObserverState.observers` (`StoredObserverOk`) | the source's exit, by mode |
| queued observer | `Cmd.observe` in the queue | `QueueOk.observer` (`ObserverCommandOk`) | the exit it carries |
| dispatcher task | `fiber.dispatcher.buckets` | `DispatcherOk` (`TaskOk`) | its code |
| the host | an external request at a park | `AnswerOk` (M6); `PreparedFits` (host lane) | the prepared reply |

The clauses are the same proposition at different places. One definition says it once:

```lean
/-- Every key is declared, at a type the sender's delivery fits. -/
def KeysTyped (w : World) (demand : EffTy → Prop) (keys : List GuardKey) : Prop :=
  ∀ k ∈ keys, ∃ ty, w.Θ k.1 k.2 = some ty ∧ demand ty
```

`WakeTyped w d l` is `KeysTyped w d (Guard.wakeKeys l)` (`Typed/Validity.lean`); the due list, the
queued resumes and the observers fit the same shape with their own demand. `KeysTyped` is
monotone in the world (`Θ` only grows) and antitone in the key list (fewer keys, fewer
obligations): the two facts every frame needs, proved once.

## 3. The transfer table

A step moves a sender role. The move is sound when the old sender's demand implies the new one's,
given what the step itself knows. This is protocol subsumption (de Vilhena and Pottier 2021, §3.3,
PDF p9): a protocol may be replaced by one it implies.

| From | To | The implication | Used by | Status |
| --- | --- | --- | --- | --- |
| timer | queued resume | `SleepDemand ty → ResumeOk (succeed void)` | clock fire | proved (`completionStrong_sleep`, `ed50d19c`) |
| waiter, pending | waiter, batch | identity | `wakeAll` (schedule) | open (loop) |
| waiter, batch | waiter, pending | identity | `wake`, cell not completed | open (pilot) |
| waiter | owed resume | `AwaitDemand a e ty ∧ CompletionStrong ⟨a,e⟩ c → CompletionStrong ty c` | `wake` (completed cell), `complete` | open (pilot) |
| owed resume | queued resume | `CompletionStrong ty c → ResumeOk (denoteCompletion c)` | `drainDue` | proved (`denoteCompletion_typed`) |
| queued resume | the park lands | `ResumeOk` and `ActiveDelivery` give the new code | `resume` | proved (`resume_step`) |
| park registration | timer | `asyncPre`'s sleep clause gives `SleepDemand` | `loop`, `registerSleep` | open |
| park registration | waiter | `asyncPre`'s await clause gives `AwaitDemand` | `loop`, `registerAwait` | open |
| park registration | the host | `bitEntry`, the row's columns | `loop`, external | open (reference parks forever) |
| race | the host's park | `RegistrationState`'s result type | `registrationDone` | open |
| stored observer | queued observer | the exit in hand fits the source's type | `finish` | proved (`configTyped_observes`) |
| dispatcher task | queued resume | `TaskOk` | `fire` | proved (`snapshotTyped_drain`) |
| the host | queued resume | `AnswerOk` | `answerAsync` | proved (`edit_answer`) |

Exclusivity moves with the role: the key leaves one sender's list and joins another's, so the
union of all senders' keys is unchanged or smaller, or gains exactly the fresh token at
`nextToken`. One lemma covers every row of the table on that side: a new key list that is a
sublist of the old one, plus the fresh token, keeps `InternalKeysBelow`, `requestsOwned` and the
queue's reserved keys. Today this is the `keys : internalKeys new ⊆ internalKeys old` premise of
the restate lemmas and `Guard.syncOpStep_storeKeys`.

## 4. Frames as views

`J`'s store clauses read exactly these views of `m.state`: the refs (heap typing, `Ρ` coverage),
each cell's completion and the cell count (`Π` coverage, the promise column), each cell's wake keys
(waiters), the timers' wake keys (timers), the due list (the promise table's due row), the memo
world's layer cells (the memo row), the scopes (scope typing, presence), the externals, and
well-formedness. A store edit is admitted by stating how it moves each view:

```lean
/-- How a store edit moves the views `J` reads. -/
structure StoreFrame (w : World) (s s' : Stores) : Prop where
  le          : s.le s'
  refs        : s'.refs = s.refs
  completions : ∀ k c', s'.deferreds.cellAt k = some c' →
                  ∃ c, s.deferreds.cellAt k = some c ∧ c'.completion = c.completion
  cellCount   : s'.deferreds.cells.length = s.deferreds.cells.length
  cellWakes   : ∀ k c', s'.deferreds.cellAt k = some c' →
                  ∃ c, s.deferreds.cellAt k = some c ∧ wakeKeys c'.wake ⊆ wakeKeys c.wake
  timers      : wakeKeys s'.timers.wake ⊆ wakeKeys s.timers.wake
  due         : the due row at `s'` (each new entry is a transfer, §3)
  memo        : ∀ p ∈ s'.memo.layerCells, p ∈ s.memo.layerCells
  scopes, externals, wf, keys : ...
```

with `StoreFrame.refl`, `StoreFrame.trans`, one builder per primitive store edit (`wakeBatch`,
`complete`, `cancel`, `clockStep`, `drain`), and one theorem:

```lean
theorem configTyped_storeFrame (typed : ConfigTyped root rootTy w m q) (frame : StoreFrame w m.state s) :
    w.leHost { w with state := s } ∧ ConfigTyped root rootTy { w with state := s } { m with state := s } q
```

`configTyped_restate` is its instance with every view unchanged; its callers (`clockNone`,
`clockSome`, `drainDue`, `scopeAdd`, the observe walk) move over, then the old lemma goes
(AGENTS.md: build beside, move the callers, delete). The proved promise-table column already reads
only the two fields it types (`PromiseTableOk`, `179ee784`), the pattern every column should follow:
a clause that names whole records breaks the moment a step edits an unrelated field.

The fiber side has the same structure and an existing instance. Other fibers' clauses must
survive a step that edits one fiber: that is stability under interference (rely-guarantee). The
rely is `ObsView m m'` (lookups keep ids and only weaken pending, races agree, scopes stay
present); `fiberTyped_transport` is the stability lemma, proved once. What is missing is the
guarantee side as builders: one lemma per primitive fiber edit (`update`, `modify`, `updateRace`,
`emit`, spawn at `nextId`) that it yields `ObsView` for the fibers it does not edit.

## 5. The host session is the external sender

`docs/core/host-boundary.md` §4.1's interfaces are §2's structure for the one sender outside the
machine:

| Host contract (§4.1–4.2) | In §2's terms |
| --- | --- |
| `RequestFits` | the sender is issued at a declared token, for the exact row and request |
| `ReplyFits`, `PreparedFits` | the sender's demand: the prepared completion fits the token's declared type in the new world |
| `ApplyReply`, "consume its guard at most once" | the transfer host → queued resume; exclusivity |
| the lifecycle (`issued` … `released`) | the external sender's states |
| "interruption before application retires the association" | the sender is removed with the park; keys only shrink |
| `RegistryAgrees` | the declarations (`Γ`, `Ρ`, `Π`, `Θ`) come from creation evidence, like every internal sender's |
| §4.6, "timers, yields, deferred deliveries ... through their own delivery paths" | the internal rows of §3's table |

Two consequences. The M6 edit `answer` (`AnswerOk`, `edit_answer`) is the empty-table instance of
the host lane's application theorem (§4.5): when the lane lands, its application theorem is one
more row of §3, discharged by the same lemma from `PreparedFits`. And the reply lane's at-most-once
and accounting obligations are the exclusivity facts of §3, not a separate bookkeeping. In
rely-guarantee terms the host is the environment: the machine relies on replies meeting
`PreparedFits` and guarantees each request is issued at a declared, exclusive token. The live
session (`Api/HostSession.lean`) checks the rely at `applyReply`, so the guarantee side is what the
proofs owe.

## 6. The remaining obligations, placed

| Goal | Views written | Transfers | Command-specific (item 3) |
| --- | --- | --- | --- |
| `step_wake` | one cell's wake, the due list | waiter batch → due, or → pending | none |
| `step_loop`, store ops | per op, `Guard.syncOpStep_storeKeys` | waiter → due (`complete`) | `storeStep_typed` with `StoreImplements` (31 of 31, `179ee784`) |
| `step_loop`, fiber ops | per row of `M3bAdequacy`'s fiber instances | registration → timer, waiter, host; race | the row's frame (`answerFrame_typed`, `seqFrame_typed`) |
| `step_deliver` | the delivering fiber's frame | none | `StackAccepts` at the answered type |
| `step_launch` | a fresh fiber at `nextId`, the race's programs | none (fresh, row 134 (e)) | the entrant's code at the race's type (`RacePayload`) |
| `step_registrationDone` | the host fiber's frame and park, the race | race → the host's park | the settle code or the cancel frame |
| M6b, M6c | none | none | `decisionKeeps_of_steps`, `typedState_reachable_of_steps` once the steps are in |
| M7 | none | none | reads `J` (`m7_of_ledger`; row 180 (a) for `exitHandles_valid`) |

The store arm of `loop` becomes one theorem: a typed store operation steps (`storeStep_typed`),
its edit is a `StoreFrame` (one builder per row, most `refl` in every view but one), and the key
union only shrinks (`syncOpStep_storeKeys`).

## 7. The pilot and the order

1. **`step_wake`** with `StoreFrame` and the waiter → due implication; the measure is its length
   against a restate-style proof, and `E4-TYPED-CE-026` repaired.
2. Move the restate callers onto `configTyped_storeFrame`; delete `configTyped_restate`.
3. `KeysTyped` as the one sender clause; `WakeTyped` and the due row restated through it.
4. The `loop` store arm as one theorem; then the fiber arms, one transfer row at a time.
5. `launch` and `registrationDone` with the fiber-edit guarantee builders.
6. The host lane (X1–X4 of `host-boundary.md` §6), when it is unparked, as rows of §3.

## 8. Sources

- Lynch and Vaandrager 1995, *Forward and Backward Simulations*: an invariant is any property of
  all reachable states, proved by induction on executions (PDF p15). `J` is one, and each
  command's preservation is one inductive case.
- Ahmed, Dreyer and Rossberg 2009, §3.2 *Local Reasoning via Possible Worlds and Islands* (PDF
  pp3–4): worlds are a separating conjunction of islands, and extending a world with a new island is
  sound because a freshly allocated island is separate from the rest. Our `World.le` and the fresh
  token at `nextToken` are this.
- Jung et al. 2015, *Iris*: frame-preserving updates of owned ghost state (PDF p4) and the
  authoritative monoid, one party owning the whole state and others fragments of it (§3.6, PDF p5).
  `Θ` is the authoritative map; each sender owns its key exclusively; a transfer is a
  frame-preserving update.
- de Vilhena and Pottier 2021, *A Separation Logic for Effect Handlers*: protocols describe what a
  program may request and the replies it may expect (PDF p3); the frame rule gives local reasoning
  (PDF pp1–3); protocols are ordered by subsumption (§3.3, PDF p9). §3's implications are
  subsumptions; `StoreImplements` (Adequacy) is already the handler rule.
- Pickering, Gibbons and Wu 2017, *Profunctor Optics*: a lens is well behaved when updating the
  view and reading it back agree, and the source factors into the view and its complement (PDF
  p23). A clause reading a view untouched by a step's update is the complement case; §4's views are
  lenses on `RState` and `Stores`.

These are design adaptations, not imported theorems: nothing above is proved by citing them.
