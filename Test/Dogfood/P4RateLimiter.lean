import Test.Dogfood.Stage
import Effect4.Program.Authoring.Loops
import Effect4.Laws.Program.DenoteB

/-!
# p4: dogfood 1's rate limiter

The rc.112 source is `Test/Dogfood/rc112/p4-rate-limiter.ts`. It admits at most three requests per
1000 ms window, refills the window from a detached daemon, runs five requests at once and
interrupts the daemon at shutdown. Its state is one record in one `Ref`, and `Ref.modify` admits a
request in one atomic step. `run-p4.ts` ran it on effect 4.0.0-rc.112 under bun 1.4.2, and it
answered `[3, 2, 3]` (`Test/Dogfood/rc112/hostruns.log`).

This battery ports the model probe's program 4
(`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/ProbePrograms345.lean`, section
"Program 4"), with the verifier's checks of
`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/verify/VerifyPrograms.lean`. The
encoding is dogfood 1's design: three number cells, and a request that reads, then updates.

**Changes since 2026-09-30.**
* The request answers whether it admitted, and the program answers rc.112's triple as a tuple
  (row 159). The probe answered the pair `(admitted, rejected)` only, which is the triple's first
  two items. The probe could have written the triple with nested pairs, so this change is the
  encoding's, not the language's.
* No construct the probe used changed its spelling.

**What the language refuses** (section 4): the `Window` record in one cell (`requestNotSubtype`,
the cell row expects `nat`), and the atomic admit, which needs `Ref.modify` with a binder term.
`Ref.update` takes one of the five names of `fnNames` (`src/Effect4/Program/Native.lean`).

**Waits on:** R4, rows 42–43 steps 3–5 (a record cell and a function row with a binder term), and
R10 (DI-89's `all`). The slice of row 204 that moves it: state at any type.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Dogfood.P4RateLimiter

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-! ## 1. The program -/

/-- The refill daemon (`p4-rate-limiter.ts`, `refill`): forever, sleep a window, then reset the
count. `Effect.forever` is an `iterate` whose test is the constant `true`. -/
def refill (used : TermSrc) : Src NativeOp :=
  iterateWith (bool true)
    { while_ := fun _ => bool true
      body := fun _ => andThen (Effect.sleep (nat 1000)) (Ref.set used (nat 0))
      step := fun c _ => c }

/-- One request: read, optionally yield, then admit or reject, and answer the decision. The read
and the write are two store steps, so the request is not atomic. -/
def request (yielding : Bool) (used admitted rejected : TermSrc) : Src NativeOp :=
  bindName "current" (Ref.get used) fun current =>
    andThen (if yielding then yieldNow 0 else succeed unit)
      (ifElse (app "lt" [current, nat 3])
        (andThen (Ref.update .incr used)
          (andThen (Ref.update .incr admitted) (succeed (bool true))))
        (andThen (Ref.update .incr rejected) (succeed (bool false))))

/-- One admitted decision as a count. -/
def countOne (decision : TermSrc) : TermSrc := app "ite" [decision, nat 1, nat 0]

/-- The program (`p4-rate-limiter.ts`, `program`): three cells, the daemon, five forked requests
joined in order, the daemon interrupted, then `[admitted, rejected, decisions.filter(d => d).length]`.
Five forks and five joins spell `Effect.all` with unbounded concurrency. -/
def limiter (yielding : Bool) : Src NativeOp := eff do
  let used ← Ref.make (nat 0)
  let admitted ← Ref.make (nat 0)
  let rejected ← Ref.make (nat 0)
  let daemonFiber ← daemon (refill used)
  let f1 ← fork (request yielding used admitted rejected)
  let f2 ← fork (request yielding used admitted rejected)
  let f3 ← fork (request yielding used admitted rejected)
  let f4 ← fork (request yielding used admitted rejected)
  let f5 ← fork (request yielding used admitted rejected)
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

/-! ## 2. The run

The ordinary decisions: evaluate the root, then flush. No decision advances the clock, so the
refill never fires; the shutdown interrupts it. -/

def answer (yielding : Bool) : Option ExitV :=
  (limiterProgram yielding).bind fun p => (Effect4.Api.run p 4000).exit

/-- rc.112's answer, `[3, 2, 3]` (`Test/Dogfood/rc112/hostruns.log`), as the tuple's value. -/
def rc112 : ExitV := .success (.list [.nat 3, .nat 2, .nat 3])

-- Without the yield the answer is rc.112's. Its first two items are dogfood 1's `[3, 2]`, as the
-- verifier recorded them from dogfood 1's untracked receipt
-- (`git:ce2ece4f:docs/research/2026-09-30-model-probe/programs/verify.md`, PROG-12).
#guard answer false = some rc112
-- Red control: with a yield between the read and the write, all five requests read 0 before any
-- write, so all five admit. This is dogfood 1's `[5, 0]` race; the atomic `Ref.modify` of the
-- rc.112 program has no such interleaving, and the encoding cannot spell it (section 4).
#guard answer true = some (.success (.list [.nat 5, .nat 0, .nat 5]))

/-! ## 3. Printing, and which theorem reaches the program -/

-- The program prints as TypeScript and reads back as itself (the verifier's green control).
#guard (limiterProgram false).map (fun p => ((Effect4.Api.print p).isOk, Effect4.Api.readable p)) =
  some (true, true)

-- `Straight` and `Looped` are the fragments of `run_eq_meaning` and `loopAgreement`. The whole
-- limiter is in neither.
open Effect4.Program.Denote in
#guard (limiterProgram false).map (fun p => (Straight p, Looped p)) = some (false, false)
-- The request body alone (dogfood 1's L2 lane) is in both.
open Effect4.Program.Denote in
#guard ((request false (var "u") (var "a") (var "r")) { names := ["u", "a", "r"] } []).toOption.map
    (fun e => (Straight e, Looped e)) = some (true, true)
-- The refill daemon parks on the clock: in neither fragment.
open Effect4.Program.Denote in
#guard ((refill (var "u")) { names := ["u"] } []).toOption.map (fun e => (Straight e, Looped e))
  = some (false, false)
-- No host row: the run at the empty row table finishes, so `run_eq_ref` reaches it.
#guard (limiterProgram false).map (fun p => (Effect4.Api.run p 4000).outcome) =
  some Effect4.Api.Outcome.finished

/-! ## 4. What the language refuses -/

/-- `interface Window { used, admitted, rejected }`, every field a number. -/
def windowFields : List (String × Bool × Ty) :=
  [("used", false, .nat), ("admitted", false, .nat), ("rejected", false, .nat)]

/-- `Ref.make<Window>({ used: 0, admitted: 0, rejected: 0 })`, the rc.112 program's one cell. -/
def windowCell : Module NativeOp :=
  program (Ref.make (record windowFields [("used", nat 0), ("admitted", nat 0), ("rejected", nat 0)]))

-- Refused at the cell's request: the row `refMake` expects a number. Generic cells (rows 42–43,
-- steps 3–5) lift it, and this pin turns red.
#guard typingReason? windowCell = some (.requestNotSubtype "refMake"
  (.record [("admitted", false, .nat), ("rejected", false, .nat), ("used", false, .nat)]) .nat)
-- The checker refuses the same state as a pair the same way (the model probe's `ProbeRefusals.lean`).
#guard typingReason? (program (Ref.make (app "pair" [nat 1, nat 2]))) =
  some (.requestNotSubtype "refMake" (.prod .nat .nat) .nat)
-- Green control: a number cell builds, and so does the nearest update, `incr`.
#guard verdict (program (bindName "r" (Ref.make (nat 0)) fun r => Ref.update .incr r)) = "built"
-- The admit step `w.used < limit ? … : …` is a function the update rows cannot take: they take
-- one of five names (row 43 step 3 retires the alphabet for a binder term).
#guard Effect4.Program.fnNames.length = 5

-- The form table admits `Effect.forkDetach`, the daemon's rc.112 spelling, and not `Effect.all`
-- (DI-89) or `Effect.forever`.
#guard formAdmits "Effect.forkDetach"
#guard ["Effect.all", "Effect.forever"].filter formAdmits = []

/-! ## 5. The stage -/

def measured : Reach :=
  { refused := [("the Window record in one Ref", verdict windowCell)]
    admitted := verdict (limiterModule false) == "built"
    answer := answerOf (answer false) rc112
    printed := ((limiterProgram false).map fun p => (Effect4.Api.print p).isOk) == some true
    readBack := ((limiterProgram false).map fun p => Effect4.Api.readable p) == some true }

/-- The stage p4 reaches today, as `Test/Dogfood/README.md` quotes it. -/
def stage : Reach :=
  { refused := [("the Window record in one Ref", "typing: requestNotSubtype")]
    admitted := true, answer := .rc112, printed := true, readBack := true }

#guard measured = stage

end Test.Dogfood.P4RateLimiter
