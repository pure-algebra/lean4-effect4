import Test.Dogfood.Stage
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB

/-!
# p4: dogfood 1's rate limiter

The rc.112 source is `Test/Dogfood/rc112/p4-rate-limiter.ts`. It lets at most three requests
through per 1000 ms window, refills the window from a detached daemon, runs five requests at once
and interrupts the daemon at shutdown. Its state is one record in one `Ref`, and `Ref.modify`
decides a request in one atomic step. `run-p4.ts` ran it on effect 4.0.0-rc.112 under bun 1.4.2,
and it answered `[3, 2, 3]` (`Test/Dogfood/rc112/hostruns.log`).

This battery started as a port of the model probe's program 4
(`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ProbePrograms345.lean`, section
"Program 4"), with the verifier's checks of
`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/verify/VerifyPrograms.lean`. The
probe's encoding was dogfood 1's design: three number cells, and a request that reads, then
updates. It is section 3's race control now.

**Changes since 2026-09-30.**
* The request answers whether it went through, and the program answers rc.112's triple as a tuple
  (row 159). The probe answered the pair `(admitted, rejected)` only, which is the triple's first
  two items. The probe could have written the triple with nested pairs, so this change is the
  encoding's, not the language's.
* No construct the probe used changed its spelling.

**Changes in the state plan's T3a.** `Ref` is a template over its type: the `Window` record in one
cell builds, and it is read and written.

**Changes in the state plan's T3b.** A read-modify-write row carries a binder term, so the measured
program is rc.112's: one `Window` cell, and each request one `Ref.modify` whose term decides and
rewrites the record in one store step. It answers `[3, 2, 3]`, with or without a yield before the
step. The three-cell program stays as the race control (section 3). The stage loses `printed` and
`readBack`: the term of a request is no name's image, so the printer refuses the row by name until
the state plan's T5 prints a term as a lambda (section 4).

**Waits on:** R4, the faces' part (a binder term printed and read as a lambda, the state plan's T5),
and R10 (DI-89's `all`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P4RateLimiter

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The program -/

/-- `interface Window { used, admitted, rejected }`, every field a number. -/
def windowFields : List (String × Bool × Ty) :=
  [("used", false, .nat), ("admitted", false, .nat), ("rejected", false, .nat)]

/-- The type of the window, its fields in canonical order. -/
def windowTy : Ty :=
  .record [("admitted", false, .nat), ("rejected", false, .nat), ("used", false, .nat)]

/-- `{ used, admitted, rejected }` as a value, its fields in canonical order. -/
def windowVal (used admitted rejected : Nat) : Val :=
  recordOf ["admitted", "rejected", "used"] [.nat admitted, .nat rejected, .nat used]

/-- `{ used: 0, admitted: 0, rejected: 0 }`. -/
def window0 : TermSrc :=
  record windowFields [("used", nat 0), ("admitted", nat 0), ("rejected", nat 0)]

/-- The decision of one request over the window `w` (`p4-rate-limiter.ts`, `request`):
`w.used < 3 ? [true, { ...w, used: w.used + 1, admitted: w.admitted + 1 }] :
[false, { ...w, rejected: w.rejected + 1 }]`. `ite` evaluates both arms, and both are pure. -/
def decision (w : TermSrc) : TermSrc :=
  app "ite" [app "lt" [field w "used", nat 3],
    app "pair" [bool true,
      recordSet (recordSet w "used" (app "succ" [field w "used"]))
        "admitted" (app "succ" [field w "admitted"])],
    app "pair" [bool false, recordSet w "rejected" (app "succ" [field w "rejected"])]]

/-- One request: one `Ref.modify` that decides and rewrites the window in one store step, and
answers the decision. The optional yield comes before the step, never inside it. -/
def request (yielding : Bool) (state : TermSrc) : Src NativeOp :=
  andThen (if yielding then yieldNow 0 else succeed unit)
    (Ref.modify "w" (decision (var "w")) state)

/-- The refill daemon (`p4-rate-limiter.ts`, `refill`): forever, sleep a window, then reset the
count with `Ref.update(state, w => ({ ...w, used: 0 }))`. `Effect.forever` is an `iterate` whose
test is the constant `true`. -/
def refill (state : TermSrc) : Src NativeOp :=
  iterateWith (bool true)
    { while_ := fun _ => bool true
      body := fun _ => andThen (Effect.sleep (nat 1000))
        (Ref.update "w" (recordSet (var "w") "used" (nat 0)) state)
      step := fun c _ => c }

/-- One accepted request as a count. -/
def countOne (decision : TermSrc) : TermSrc := app "ite" [decision, nat 1, nat 0]

/-- The program (`p4-rate-limiter.ts`, `program`): one `Window` cell, the daemon, five forked
requests joined in order, the daemon interrupted, then
`[w.admitted, w.rejected, decisions.filter(d => d).length]`. Five forks and five joins spell
`Effect.all` with unbounded concurrency. -/
def limiter (yielding : Bool) : Src NativeOp := eff do
  let state ← Ref.make window0
  let daemonFiber ← daemon (refill state)
  let f1 ← fork (request yielding state)
  let f2 ← fork (request yielding state)
  let f3 ← fork (request yielding state)
  let f4 ← fork (request yielding state)
  let f5 ← fork (request yielding state)
  let d1 ← join f1
  let d2 ← join f2
  let d3 ← join f3
  let d4 ← join f4
  let d5 ← join f5
  let _ ← withFiber (Action.interrupt daemonFiber)
  let w ← Ref.get state
  return tuple [field w "admitted", field w "rejected", app "add" [countOne d1,
    app "add" [countOne d2, app "add" [countOne d3, app "add" [countOne d4, countOne d5]]]]]

def limiterProgram (yielding : Bool) : Option Effect4.Api.Program :=
  (elaborate (limiter yielding)).toOption

def limiterModule (yielding : Bool) : Module NativeOp := program (limiter yielding)

-- Both variants type at the triple, fail with nothing and need nothing.
#guard (limiterProgram false).bind (Effect4.Api.typeOf ·) =
  some ⟨.tuple [.nat, .nat, .nat], .never, .empty⟩
#guard (limiterProgram true).bind (Effect4.Api.typeOf ·) =
  some ⟨.tuple [.nat, .nat, .nat], .never, .empty⟩
-- The module builds: elaborated, typed and admitted at the empty row table.
#guard verdict (limiterModule false) = "built"
#guard verdict (limiterModule true) = "built"

/-! ## 2. The run

The ordinary decisions: evaluate the root, then flush. No decision advances the clock, so the
refill never fires; the shutdown interrupts it. -/

def answer (yielding : Bool) : Option ExitV :=
  (limiterProgram yielding).bind fun p => (Effect4.Api.run p 4000).exit

/-- rc.112's answer, `[3, 2, 3]` (`Test/Dogfood/rc112/hostruns.log`), as the tuple's value. -/
def rc112 : ExitV := .success (.list [.nat 3, .nat 2, .nat 3])

-- The answer is rc.112's.
#guard answer false = some rc112
-- With a yield before each request's step the answer is still rc.112's: the decision and the
-- write are one store step, so no request reads a count another has yet to write.
#guard answer true = some rc112

/-! ## 3. The race control: three cells, a read and then a write

Dogfood 1's encoding, the measured program of this battery before the state plan's T3b: three
number cells, and a request that reads the count and then updates it in a second store step. It
is kept as the control of section 2: the same yield, placed between its read and its write, lets
all five requests through. -/

/-- One request over three cells: read, optionally yield, then accept or reject. The read and the
write are two store steps, so the request is not atomic. -/
def raceRequest (yielding : Bool) (used admitted rejected : TermSrc) : Src NativeOp :=
  bindName "current" (Ref.get used) fun current =>
    andThen (if yielding then yieldNow 0 else succeed unit)
      (ifElse (app "lt" [current, nat 3])
        (andThen (Ref.update "n" (app "succ" [var "n"]) used)
          (andThen (Ref.update "n" (app "succ" [var "n"]) admitted) (succeed (bool true))))
        (andThen (Ref.update "n" (app "succ" [var "n"]) rejected) (succeed (bool false))))

/-- The refill daemon over the count's own cell. -/
def raceRefill (used : TermSrc) : Src NativeOp :=
  iterateWith (bool true)
    { while_ := fun _ => bool true
      body := fun _ => andThen (Effect.sleep (nat 1000)) (Ref.set used (nat 0))
      step := fun c _ => c }

/-- The three-cell program. -/
def raceLimiter (yielding : Bool) : Src NativeOp := eff do
  let used ← Ref.make (nat 0)
  let admitted ← Ref.make (nat 0)
  let rejected ← Ref.make (nat 0)
  let daemonFiber ← daemon (raceRefill used)
  let f1 ← fork (raceRequest yielding used admitted rejected)
  let f2 ← fork (raceRequest yielding used admitted rejected)
  let f3 ← fork (raceRequest yielding used admitted rejected)
  let f4 ← fork (raceRequest yielding used admitted rejected)
  let f5 ← fork (raceRequest yielding used admitted rejected)
  let d1 ← join f1
  let d2 ← join f2
  let d3 ← join f3
  let d4 ← join f4
  let d5 ← join f5
  let _ ← withFiber (Action.interrupt daemonFiber)
  let a ← Ref.get admitted
  let r ← Ref.get rejected
  return tuple [a, r, app "add" [countOne d1, app "add" [countOne d2,
    app "add" [countOne d3, app "add" [countOne d4, countOne d5]]]]]

def raceProgram (yielding : Bool) : Option Effect4.Api.Program :=
  (elaborate (raceLimiter yielding)).toOption

def raceAnswer (yielding : Bool) : Option ExitV :=
  (raceProgram yielding).bind fun p => (Effect4.Api.run p 4000).exit

#guard verdict (program (raceLimiter false)) = "built"
-- Without the yield the three-cell program answers rc.112's triple. Its first two items are
-- dogfood 1's `[3, 2]`, as the verifier recorded them from dogfood 1's untracked receipt
-- (`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/verify.md`, PROG-12).
#guard raceAnswer false = some rc112
-- Red control: with a yield between the read and the write, all five requests read 0 before any
-- write, so all five go through. This is dogfood 1's `[5, 0]` race.
#guard raceAnswer true = some (.success (.list [.nat 5, .nat 0, .nat 5]))
-- Its three updates are `incr`'s image at their nodes' levels, so it prints as TypeScript and
-- reads back as itself (the verifier's green control).
#guard (raceProgram false).map (fun p => ((Effect4.Api.print p).isOk, Effect4.Api.readable p)) =
  some (true, true)

/-! ## 4. The request's row, its printing, and which theorem reaches the program -/

/-- The request's term at a node of level 1, over the cell at `var 0` and the window at `var 1`. -/
def decisionTerm : Option Term := ((decision (var "w")) { names := ["s", "w"] } []).toOption

/-- The request alone, over a bound cell `s`. -/
def requestEff : Option Effect4.Api.Program :=
  ((request false (var "s")) { names := ["s"] } []).toOption

/-- The printer's refusal of a program, by the row it names; `none` when the program prints. -/
def printRefusal (p : Effect4.Api.Program) : Option String :=
  match Effect4.Api.print p with
  | .error (.binderTerm spelling) => some ("binderTerm " ++ spelling)
  | .error _ => some "another refusal"
  | .ok _ => none

-- `B` is not `A`: over a `Ref<Window>` the request answers a boolean and stores a window.
#guard (elaborate (bindName "s" (Ref.make window0) fun s => request false s)).toOption.bind
    (Effect4.Api.typeOf ·) = some ⟨.bool, .never, .empty⟩
-- One store step decides and writes: at two used it admits and counts, at three it rejects and
-- counts. The term runs at the node's environment and the window (decisions row 43).
#guard decisionTerm.bind (fun f =>
    refStep (SyncOp.refModify ⟨0⟩ f [Val.cell ⟨0⟩]) [windowVal 2 2 0]) =
  some (Val.bool true, [windowVal 3 3 0])
#guard decisionTerm.bind (fun f =>
    refStep (SyncOp.refModify ⟨0⟩ f [Val.cell ⟨0⟩]) [windowVal 3 3 0]) =
  some (Val.bool false, [windowVal 3 3 1])
-- Red control: the pair in the other order is refused at the term's result, by name.
#guard (typingReason? (program (bindName "s" (Ref.make window0) fun s =>
    Ref.modify "w" (app "pair" [var "w", bool true]) s))).map (·.head) = some "resultNotSubtype"
-- Red control: a term over a name that is not in scope is refused before typing.
#guard verdict (program (bindName "s" (Ref.make window0) fun s =>
    Ref.modify "w" (decision (var "v")) s)) = "scope"

-- Since the state plan's T5 a row's term prints as a function of the current value: the
-- daemon's `Ref.update` and the request's `Ref.modify` print, and the limiter reads back.
#guard (limiterProgram false).map printRefusal = some none
#guard requestEff.map printRefusal = some none
#guard (limiterProgram false).map (fun p => Effect4.Api.readable p) = some true

-- `Straight` and `Looped` are the fragments of `run_eq_meaning` and `loopAgreement`. The whole
-- limiter is in neither.
open Effect4.Program.Denote in
#guard (limiterProgram false).map (fun p => (Straight p, Looped p)) = some (false, false)
-- The request alone is in both: one store step.
open Effect4.Program.Denote in
#guard requestEff.map (fun e => (Straight e, Looped e)) = some (true, true)
-- The refill daemon parks on the clock: in neither fragment.
open Effect4.Program.Denote in
#guard ((refill (var "s")) { names := ["s"] } []).toOption.map (fun e => (Straight e, Looped e))
  = some (false, false)
-- No host row: the run at the empty row table finishes, so `run_eq_ref` reaches it.
#guard (limiterProgram false).map (fun p => (Effect4.Api.run p 4000).outcome) =
  some Effect4.Api.Outcome.finished

/-! ## 5. The record cell, and the forms the language lacks -/

def built? (m : Module NativeOp) : Option Effect4.Api.Built := (Effect4.Api.Author.build m).toOption

/-- The `Window` record in one cell, written and read: `Ref.set(w, { used: 1, … })`, `Ref.get(w)`. -/
def windowReadWrite : Module NativeOp :=
  program (bindName "w" (Ref.make window0) fun w =>
    andThen (Ref.set w (record windowFields [("used", nat 1), ("admitted", nat 1), ("rejected", nat 0)]))
      (Ref.get w))

-- A cell holds any type since the state plan's T3a: the window builds at `Ref<Window>`.
#guard (built? (program (Ref.make window0))).map (fun b => b.ty.answer) = some (.refOf windowTy)
-- Written and read, it answers the window it holds.
#guard (built? windowReadWrite).map (fun b => (b.ty.answer, b.runSync)) = some
  (windowTy, .success (windowVal 1 1 0))
-- The same state as a pair builds the same way (the model probe's `ProbeRefusals.lean` refused it).
#guard (built? (program (Ref.make (app "pair" [nat 1, nat 2])))).map (fun b => b.ty.answer) =
  some (.refOf (.prod .nat .nat))
-- An update of the window by a binder term builds and runs: the refill's own step.
#guard (built? (program (bindName "s" (Ref.make
      (record windowFields [("used", nat 3), ("admitted", nat 3), ("rejected", nat 2)])) fun s =>
    andThen (Ref.update "w" (recordSet (var "w") "used" (nat 0)) s) (Ref.get s)))).map
    (fun b => b.runSync) = some (.success (windowVal 0 3 2))

-- The form table admits `Effect.forkDetach`, the daemon's rc.112 spelling, and not `Effect.all`
-- (DI-89) or `Effect.forever`.
#guard formAdmits "Effect.forkDetach"
#guard ["Effect.all", "Effect.forever"].filter formAdmits = []

/-! ## 6. The stage -/

def measured : Reach :=
  { refused := []
    admitted := verdict (limiterModule false) == "built"
    answer := answerOf (answer false) rc112
    printed := ((limiterProgram false).map fun p => (Effect4.Api.print p).isOk) == some true
    readBack := ((limiterProgram false).map fun p => Effect4.Api.readable p) == some true }

/-- The stage p4 reaches today, as `Test/Dogfood/README.md` quotes it. Since the state plan's T3b
the measured program is rc.112's, one `Window` cell and one atomic `Ref.modify` a request. Since
the state plan's T5 its terms print as functions of the window, so it is printed and read back
(section 4). -/
def stage : Reach :=
  { refused := []
    admitted := true, answer := .rc112, printed := true, readBack := true }

#guard measured = stage

/-- The requirements of the system map's §8 that this program waits on, as its row in
`Test/Dogfood/README.md` explains them. The semantics report lists the program under each and
prints `stage` beside it (decisions row 206). -/
def waitsOn : List String := ["R4", "R10"]

end Test.Dogfood.P4RateLimiter
