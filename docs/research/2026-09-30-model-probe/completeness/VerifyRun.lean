import Effect4.Api
import Effect4.Api.HostProtocol

/-!
# Verifier of the completeness seat: four checks on the seat's probes and proposals

Finite checks only (`#guard`): evidence word **tested**. Read against HEAD `7cae243a`. The
kernel-decided half of check 2 is `VerifyKernel.lean`.

1. **"Runs once" needs a counting release** (against C-05's evidence). The seat's
   `Outcomes.lean` part 2 releases by writing `1` into the cell, which reads the same after one
   run or two. A release that increments separates them: one interruption leaves the counter
   at 1, a second interruption does not move it, and two registered releases leave 2 where two
   setter releases leave 1. Also against C-05's A4: a release registered in a manual scope the
   program never closes does not run, although the run finishes, so `finished_released` as the
   seat states it is false.
2. **No reason does not mean deadlock** (against C-06's recommendation `noReason_deadlocked`).
   A root parked on its own `yieldNow` with the tape `[evaluate]` is a frontier with no reason
   and host state `parked`, while its dispatcher is armed; one `flush` finishes it. A real
   deadlock (after the flush) also has no reason, and its armed list is empty.
3. **Insertion can re-point a call silently** (sharpens C-03). Inserting a row of the same
   type in front keeps the program's type and the table's lawfulness, and the same program
   now prints a call to a different host row. Appending an unregistrable row keeps the type
   and revokes admission.
4. **The dogfood §2 disagreement still holds at HEAD** on the Lean side (for C-07's
   pedigree).

The red control is `VerifyRunRed.lean`: the six discriminating guards flipped (marked
`-- [red]` below). It must fail with exactly six guard errors.
-/

set_option autoImplicit false

namespace Probe.CompletenessVerify.Run

open Effect4 Effect4.Machine Effect4.Program

/-- `interruptUnsafe` from outside, at the root (the seat's `interruptRoot`). -/
def interruptRoot : Api.Decision :=
  RunDecision.interruptFrom none ReasonAnnotations.empty Api.root

/-- `pair(a, b)` as a term. -/
def pairT (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))

/-! ## 1. A counting release -/

/-- A cell at 0; a scope whose release increments the cell (`Ref.update(c, incr)`); the body
parks forever on a deferred; after the scope, read the cell. The seat's `leaky` with the
setter replaced by an increment. -/
def counting : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))
          (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 2)))))
      (.perform .refGet (.var 0)))

/-- The counting release, the body finishing at once. -/
def countingDone : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0))))
      (.perform .refGet (.var 0)))

/-- Two setter releases (the seat's release, registered twice) in one scope. -/
def setterTwice : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit))
            (.perform .refSet (pairT (.var 0) (.lit (.nat 1)))))
          (.acquireRelease (.succeed (.lit .unit))
            (.perform .refSet (pairT (.var 0) (.lit (.nat 1)))))))
      (.perform .refGet (.var 0)))

/-- Two counting releases in one scope. -/
def counterTwice : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind
      (.scoped
        (.bind
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0)))))
      (.perform .refGet (.var 0)))

#guard (Api.typeOf counting).isSome
#guard (Api.typeOf countingDone).isSome
#guard (Api.typeOf setterTwice).isSome
#guard (Api.typeOf counterTwice).isSome

-- Owed at the frontier, as the seat showed.
#guard (Api.run counting 200).outcome = Api.Outcome.frontier
#guard (Api.run counting 200).machine.state.refs = [Val.nat 0]
-- One interruption: the release ran exactly once.
#guard (Api.replay counting 200 [Api.evaluate, Api.flush, interruptRoot]).outcome =
  Api.Outcome.finished
#guard (Api.replay counting 200 [Api.evaluate, Api.flush, interruptRoot]).machine.state.refs =
  [Val.nat 1]
-- A second interruption of the finished run does not run it again.
#guard (Api.replay counting 200
  [Api.evaluate, Api.flush, interruptRoot, interruptRoot]).machine.state.refs = [Val.nat 1]
-- A body that finishes: once.
#guard (Api.run countingDone 200).outcome = Api.Outcome.finished
#guard (Api.run countingDone 200).machine.state.refs = [Val.nat 1]
-- Discrimination: two setter releases read as one; two counting releases read as two.
#guard (Api.run setterTwice 200).machine.state.refs = [Val.nat 1]
#guard (Api.run counterTwice 200).machine.state.refs = [Val.nat 2]   -- [red]

/-- A counting release registered in a manual scope (`Scope.make`, provided as the ambient
`Scope`) that the program never closes. rc.112 runs a scope's finalizers only when the scope
is closed (`vendor/effect-4.0.0-rc.112/src/Scope.ts:240`, the `scopeMake` row's cite). -/
def unclosed : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 0)))
    (.bind (.perform (.scopeMake .sequential) (.lit .unit))
      (.bind
        (.provideService nativeScopeKey (.var 1)
          (.acquireRelease (.succeed (.lit .unit)) (.perform (.refUpdate .incr) (.var 0))))
        (.perform .refGet (.var 0))))

-- A typed program with nothing required ...
#guard Api.typeOf unclosed = some ⟨.nat, .never, .empty⟩
-- ... whose run finishes (every fiber exited) with its registered release never run.
#guard (Api.run unclosed 200).outcome = Api.Outcome.finished
#guard (Api.run unclosed 200).machine.fibers.all (fun f => f.exit.isSome)
#guard (Api.run unclosed 200).exit = some (.success (.nat 0))
#guard (Api.run unclosed 200).machine.state.refs = [Val.nat 0]   -- [red]
#guard (Api.run unclosed 200).machine.state.scopes.entries.length = 1

/-! ## 2. An empty reason list that is not a deadlock -/

/-- The root yields, then answers 3. -/
def yielding : NativeEff := .bind (.yieldNow 0) (.succeed (.lit (.nat 3)))

/-- The seat's deadlock shape behind a fork: the child answers, the root waits forever. -/
def forkThenWait : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1)))
      { startImmediately := false, daemon := false, maskMode := .inherit }))
    (.bind (.perform .deferredMake (.lit .unit)) (.perform .deferredAwait (.var 1)))

#guard (Api.typeOf yielding).isSome
#guard (Api.typeOf forkThenWait).isSome

-- The yielded root: a frontier with no reason, observed as `parked`, its dispatcher armed.
#guard (Api.replay yielding 200 [Api.evaluate]).outcome = Api.Outcome.frontier
#guard (Api.replay yielding 200 [Api.evaluate]).reasons = []
#guard Api.HostProtocol.observe (Api.replay yielding 200 [Api.evaluate]).machine =
  Api.HostProtocol.State.parked
#guard (Api.replay yielding 200 [Api.evaluate]).machine.armed = [Api.root]
-- One flush finishes it, so "no reason" was not a deadlock.
#guard (Api.replay yielding 200 [Api.evaluate, Api.flush]).outcome =
  Api.Outcome.finished   -- [red]
-- A real deadlock also has no reason; what separates the two is the armed list.
#guard (Api.replay forkThenWait 200 [Api.evaluate, Api.flush]).outcome = Api.Outcome.frontier
#guard (Api.replay forkThenWait 200 [Api.evaluate, Api.flush]).reasons = []
#guard (Api.replay forkThenWait 200 [Api.evaluate, Api.flush]).machine.armed = []

/-! ## 3. Silent re-pointing by an inserted row -/

/-- An asynchronous host row answered by the host. -/
def row (name spelling : String) (request answer : Ty) : Row :=
  { name, spelling, kind := .async, registration := .external, request, answer,
    error := .never, cite := "docs/research/2026-09-30-model-probe/completeness/VerifyRun.lean" }

def table : RowTable :=
  [ row "ping" "Host.ping" .unit .string, row "pong" "Host.pong" .unit .string ]

/-- A fresh row of the same type as the others, inserted in front. -/
def zap : Row := row "zap" "Host.zap" .unit .string

/-- Call the second row. -/
def callPong : NativeEff := .perform (.external 1) (.lit .unit)

#guard (Api.typeOf callPong table).isSome
#guard LawfulTable table
-- Inserted in front: the type is unchanged and the larger table is lawful ...
#guard Api.typeOf callPong (zap :: table) = Api.typeOf callPong table
#guard LawfulTable (zap :: table)
-- ... and the same program now calls a different row.
#guard (Api.print callPong table).map (TypeScript.Render.expr TypeScript.house0 0) =
  .ok "Host.pong()"
#guard (Api.print callPong (zap :: table)).map (TypeScript.Render.expr TypeScript.house0 0) =
  .ok "Host.ping()"   -- [red]

/-- A fresh, lawfully named row this runner cannot register (`registration := .deferred`). -/
def unregistrable : Row := { row "later" "Host.later" .unit .string with registration := .deferred }

-- Appending it keeps the type and the names' lawfulness, and revokes admission (DI-47's
-- separate "execution permission" comparison): `checkTable` reads the whole table.
#guard Api.typeOf callPong (table ++ [unregistrable]) = Api.typeOf callPong table
#guard LawfulTable (table ++ [unregistrable])
#guard (admitProgram callPong table).toOption.isSome
#guard (admitProgram callPong (table ++ [unregistrable])).toOption.isNone   -- [red]

/-! ## 4. The dogfood §2 identity program at HEAD (Lean side)

`docs/research/2026-09-16-dogfood-conclusions-review.md` §2: one service built through a
singleton `mergeAll` reads its building fiber's id; the body compares it with its own. The
pinned rc.112 host answered `true` (that note's evidence folder); the Lean machine answered
`false`. Still `false` at HEAD, and no register row names the difference. -/

def dogKey : ServiceKey := ⟨⟨7⟩, ⟨4⟩⟩

def identityProgram : NativeEff :=
  .provideLayer (.mergeAll (.cons (.effect dogKey (.withFiber .getId)) .nil)) false
    (.bind (.service dogKey)
      (.bind (.withFiber .getId)
        (.succeed (.app "eq" (.cons (.var 0) (.cons (.var 1) .nil))))))

#guard Api.typeOf identityProgram = some ⟨.bool, .never, .empty⟩
#guard (Api.run identityProgram 1000).outcome = Api.Outcome.finished
#guard (Api.run identityProgram 1000).exit = some (.success (.bool false))   -- [red]

end Probe.CompletenessVerify.Run
