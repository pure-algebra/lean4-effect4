import Effect4.Api.Author
import Effect4.Run
import Effect4.Program.Authoring.Loops
import Effect4.Program.Authoring.Mask
import Effect4.Modules.Waiting
import Effect4.Modules.Pool.Steps
import Effect4.Store.Carrier.Fold
import Effect4.Store.Domain.ProgramWire

/-!
# Pool on the machine: the first check of the cases (decisions rows 267 to 269)

The card's answers are the two builds' answers and readings of the machine's rules
(`docs/research/2026-10-05-claude-lead/module-cards/pool.md`, section 9). This battery runs Pool
programs on the Lean machine and compares each answer with the profile's, case by case. The
pin's answers are the probe's
(`docs/research/2026-10-05-claude-lead/module-cards/pool-probes/pool-lifecycle.v401.out`).

| Case | The schedule | The profile's answer |
| --- | --- | --- |
| PP1 | Size 1. A borrows and returns, then B. The pool's scope closes | B gets the same resource, and no finalizer runs between |
| PP2 | Size 2. A and B hold 1 and 2. A returns, then B. C borrows, then D | C gets resource 2, then D gets resource 1: a returned item joins the front (row 269) |
| PP3 | Size 1. H holds. A waits, then B. H returns. Then A returns | A gets the item, and B still waits. After A's return B gets it |
| PP4 | PP3, and A is interrupted after H's return and before the posted helper runs | The helper serves B: the selection is made when the helper runs |
| PP8 | Size 1. H holds. A waits and is interrupted. H returns, and B borrows | No waiter is left after the interruption. B gets the item, and nobody is notified |
| PP5, the public retry case | Size 1. H holds, A enrols, H returns | The helper selects A at the count 1. After the selection the item is idle, no waiter is enrolled and A holds nothing. A's own step then takes the item |
| PP5, the low-level control | A stated state: the pool is open, the item is idle, and A and then B wait. One helper at the count 2 | One selection removes A and B. A takes the item and returns it, and B then takes it |

**PP5 is no public schedule of the profile.** Its borrowers ask while the acquisition waits,
and row 267's `make` acquires every item before it answers. So it runs in two forms, each
labelled below.

- **The low-level control** builds its state by hand: a raw lease of the root, the enrolments
  of A and of B, and a raw return that posts nothing. PP3 reaches the same state, after H's
  return and before its helper. The state and the count 2 are premises of the control. No
  public operation posts that count at an open pool: a return posts 1, and the close posts
  every waiter only after it refuses new leases.
- **The public retry case** is a schedule of the profile.

**The operations here are test fixtures.** `use` is one mask around the lease and the body's
hook: the lease loop with a wait and a withdrawal, then the body under `onExit` at the mask's
restore site. A return posts one helper with the count 1 where a wake is owed (decisions row
238). The helper runs one selection step, and it then resolves each selected hint in order.
The fixtures use `posted`, `onInterrupt` and `waitAt` of `src/Effect4/Modules/Waiting.lean`,
and the mask's builder. They do not use `waitRetry`: its own mask ends before the body's hook
is installed. The public `make` and `use` come with a later slice.

**The steps are the library's** (`src/Effect4/Modules/Pool/Steps.lean`): the lease step, the
return step, the selection, the withdrawal and the close's first step. The cell is the
library's too (`src/Effect4/Modules/Pool/Cell.lean`), at a resource type of numbers. Each red
control changes one step or one fixture.

**The settings of every run.**

- The tape is `[evaluate root, flush]`: two decisions.
- The fuel is 20000, and the compile fuel is 20000.
- The budget of operations before a yield is the default, 2048 for each fiber. No run holds
  an injected yield.
- A child is forked with the default options: it starts at once. A helper is posted: a
  detached fork with a deferred start, uninterruptible.
- The root yields four times where a case lets the posted helpers run.

**What a scenario observes.** A snapshot of the cell is `[the idle stamps, the borrowed items'
stamps, their leases' stamps, the number of waiters, closing, next]`. The log holds rows of
numbers. A borrower's mark is a number: H is 9, A is 1, B is 2, C is 3 and D is 4.

| Row | Who writes it | What it says |
| --- | --- | --- |
| `[1, mark, resource, lease]` | the borrower, after its own lease step | the lease commits |
| `[2, mark, resource, lease]` | the borrower's hook, after its return step | the lease returned |
| `[3, mark, …]` | a probed helper, after its selection step | the selected identities, in order |
| `[4, mark]` | the borrower, when its wait ends | it was notified |
| `[5, idle, borrowed, waiters]` | a probed helper, after its selection step | the cell before any notification |
| `[6, mark]` | the borrower | its lease was refused |
| `[9, resource]` | the resource's finalizer | it ran |

Placement. Each scenario is a finite control of the proposed claim `pool-expansion-agrees`
(concept `translation-simulation`, requirement R10), on the side of the steps' use in a
program. The cases PP3, PP4 and the two forms of PP5 are the finite controls of the card's
reading of the machine's wake (concept `reactive-scheduling`, requirement R12): a resumed
borrower runs inside the helper's task. Every guard is one run on one schedule. None proves
delivery, a cancellation law, a law of the wake across helpers or liveness, and none is a host
run.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

namespace Test.Program.PoolScenarios

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Modules
open Effect4.Pool

/-! ## The operations, as fixtures

Every binder of an operation is minted: each row is `Ref.modifyWith`, and each sequence is
`bindWith`, `andThen`, `selectOptionWith`, `iterateWith` or `onExitWith`. A scenario writes its
own names with `eff do`. -/

/-- The steps that a policy runs. The library's are the defaults, and each red control changes
one. -/
structure Steps where
  lease : TermSrc → TermSrc → TermSrc → TermSrc := leaseStep
  giveBack : TermSrc → TermSrc → TermSrc → TermSrc := returnStep
  select : TermSrc → TermSrc → TermSrc := selectStep
  withdraw : TermSrc → TermSrc → TermSrc := withdrawStep

/-- What a scenario hands every operation: the pool's handle, the log, the registry of the
borrowers' marks, and the slot of the one red control that hands an item. -/
structure Ctx where
  pool : TermSrc
  log : TermSrc
  names : TermSrc
  slot : TermSrc

/-- The empty list of numbers, and the empty list of rows. -/
def noNumbers : TermSrc := app "take" [single (nat 0), nat 0]
def noRows : TermSrc := app "take" [single (single (nat 0)), nat 0]

/-- Write one row of the log. -/
def say (log : TermSrc) (row : List TermSrc) : Src NativeOp :=
  Ref.updateWith log fun l => snoc l (listOf row)

/-- A pool at the given resources, with its registry and its slot. -/
def withCtx (resources : List TermSrc) (log : TermSrc) (k : Ctx → Src NativeOp) : Src NativeOp :=
  bindWith (Ref.make (initial .nat resources)) fun pool =>
    bindWith (Deferred.make .unit .never) fun first =>
      bindWith (Ref.make (app "take" [single (app "pair" [nat 0, first]), nat 0])) fun names =>
        bindWith (Ref.get pool) fun s =>
          bindWith (Ref.make (noItem s)) fun slot => k ⟨pool, log, names, slot⟩

/-- Resolve each selected waiter's hint, in order. A resumed borrower runs inside this
fiber's task. -/
def resolveAll (selected : TermSrc) : Src NativeOp :=
  iterateWith (nat 0)
    { while_ := fun i => app "lt" [i, len selected]
      body := fun i => selectOptionWith (app "get" [selected, i]) (succeed unit) fun w =>
        andThen (Deferred.succeed (field w "hint") unit) (succeed unit)
      step := fun i _ => app "succ" [i]
      result := fun _ => unit }

/-- The wake's helper, over a selection step: one selection at the count, then each selected
hint in order. `seen` is a probe of a control: it runs after the selection and before any
notification. -/
def wakeWith (select : TermSrc → TermSrc → TermSrc) (seen : Ctx → TermSrc → Src NativeOp)
    (c : Ctx) (count : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith c.pool (select count)) fun selected =>
    andThen (seen c selected) (resolveAll selected)

/-- Post one helper (decisions row 238). -/
def post (helper : Src NativeOp) : Src NativeOp :=
  andThen (withFiber (Action.fork helper posted)) (succeed unit)

def withdraw (steps : Steps) (c : Ctx) (id : TermSrc) : Src NativeOp :=
  andThen (Ref.modifyWith c.pool (steps.withdraw id)) (succeed unit)

/-- The lease, with a wait and a withdrawal. Each round allocates a fresh hint and runs the
lease step. A refused lease answers nothing. A request that enrolled waits at the mask's
restore site, and the next round follows: a resumed borrower runs its own step again. A lease
that commits writes its row. Answer: an option of the leased item. -/
def leaseLoop (steps : Steps) (c : Ctx) (mark : Nat) (restore : Src NativeOp → Src NativeOp)
    (id : TermSrc) : Src NativeOp :=
  bindWith
    (iterateWith noneT
      { cursorTy := some (.option (.option (itemTy .nat)))
        while_ := fun cursor => notT (app "isSome" [cursor])
        body := fun _ =>
          bindWith (Deferred.make .unit .never) fun hint =>
            bindWith (Ref.modifyWith c.pool (steps.lease id hint)) fun reply =>
              ifElse (tupleAt reply 0)
                (succeed (app "some" [tupleAt reply 1]))
                (selectOptionWith (tupleAt reply 1)
                  (andThen (waitAt restore hint (withdraw steps c id))
                    (andThen (say c.log [nat 4, nat mark]) (succeed noneT)))
                  fun item =>
                    andThen
                      (say c.log [nat 1, nat mark, field item "resource", field item "lease"])
                      (succeed (app "some" [app "some" [item]])))
        step := fun _ answer => answer })
    fun last =>
      selectOptionWith last (failCause (Authoring.Cause.die (str "pool: the loop ended")))
        fun answer => succeed answer

/-- The return of a leased item: the return step, its row, and what a policy does where a wake
is owed. -/
def giveBackWith (steps : Steps) (owed : Ctx → Src NativeOp) (c : Ctx) (mark : Nat)
    (item : TermSrc) : Src NativeOp :=
  bindWith (Ref.modifyWith c.pool (steps.giveBack (field item "stamp") (field item "lease")))
    fun reply =>
      andThen (say c.log [nat 2, nat mark, field item "resource", field item "lease"])
        (ifElse (tupleAt reply 1) (owed c) (succeed unit))

/-- `use`: borrow one item, run the body with it, and return it at every exit. The lease and
the hook's installation are one masked region, and the body runs at the mask's restore site.
The borrower's identity goes into the registry under its mark. -/
def useWith (lease : Ctx → Nat → (Src NativeOp → Src NativeOp) → TermSrc → Src NativeOp)
    (giveBack : Ctx → Nat → TermSrc → Src NativeOp) (c : Ctx) (mark : Nat)
    (body : TermSrc → Src NativeOp) : Src NativeOp :=
  uninterruptibleMaskWith fun restore =>
    bindWith (Deferred.make .unit .never) fun id =>
      andThen (Ref.updateWith c.names fun reg => snoc reg (app "pair" [nat mark, id]))
        (bindWith (lease c mark restore id) fun got =>
          selectOptionWith got (say c.log [nat 6, nat mark]) fun item =>
            onExitWith (restore (body item)) fun _ => giveBack c mark item)

/-- A policy: the protected lease, and the helper that a control posts itself. -/
structure Ops where
  use : Ctx → Nat → (TermSrc → Src NativeOp) → Src NativeOp
  wake : Ctx → TermSrc → Src NativeOp

/-- The helper with no probe. -/
def plainWake (steps : Steps) (c : Ctx) (count : TermSrc) : Src NativeOp :=
  wakeWith steps.select (fun _ _ => succeed unit) c count

/-- The policy of a set of steps and a helper: a return posts one helper at the count 1. -/
def opsOf (steps : Steps) (wake : Ctx → TermSrc → Src NativeOp) : Ops :=
  { use := useWith (leaseLoop steps) (giveBackWith steps fun c => post (wake c (nat 1)))
    wake := wake }

/-- The profile's policy. -/
def library : Ops := opsOf {} (plainWake {})

/-! ### What a scenario observes -/

/-- A waiter's mark, through the registry. -/
def markOf (reg wid : TermSrc) : TermSrc :=
  foldWith reg (nat 0) fun found e => ifT (same (app "snd" [e]) wid) (app "fst" [e]) found

/-- The row of the selected identities. -/
def marksOf (reg selected : TermSrc) : TermSrc :=
  foldWith selected (single (nat 3)) fun acc w => snoc acc (markOf reg (field w "id"))

def heldOf (s : TermSrc) : TermSrc :=
  foldWith (field s "items") noNumbers fun acc it =>
    ifT (field it "borrowed") (snoc acc (field it "stamp")) acc

def leasesOf (s : TermSrc) : TermSrc :=
  foldWith (field s "items") noNumbers fun acc it =>
    ifT (field it "borrowed") (snoc acc (field it "lease")) acc

/-- A snapshot of the cell. -/
def snapshot (c : Ctx) : Src NativeOp :=
  bindWith (Ref.get c.pool) fun s =>
    succeed (tuple [field s "available", heldOf s, leasesOf s, len (field s "waiters"),
      field s "closing", field s "next"])

/-- A control's probe: the selected identities, then the cell, before any notification. -/
def seenProbe (c : Ctx) (selected : TermSrc) : Src NativeOp :=
  bindWith (Ref.get c.names) fun reg =>
    andThen (Ref.updateWith c.log fun l => snoc l (marksOf reg selected))
      (bindWith (Ref.get c.pool) fun s =>
        say c.log [nat 5, len (field s "available"), len (heldOf s), len (field s "waiters")])

/-- The profile's policy, with the probe in its helper. -/
def probed : Ops := opsOf {} (wakeWith selectStep seenProbe)

/-- The root yields four times: the posted helpers and the resumed fibers run. -/
def settle : Src NativeOp := forRange (nat 0) (nat 4) fun _ => yieldNow 0

/-! ## The changed policies of the red controls -/

/-- A return that puts its item at the end of the idle items: rc.112's order. -/
def returnBackStep (i l s : TermSrc) : TermSrc :=
  ifT (heldBy i l s)
    (app "pair" [tuple [bool true, notT (isEmpty (field s "waiters"))],
      recordSet (recordSet s "items" (freed i l s)) "available" (snoc (field s "available") i)])
    (app "pair" [tuple [bool false, bool false], s])

def backOrder : Ops :=
  opsOf { giveBack := returnBackStep } (plainWake { giveBack := returnBackStep })

/-- A selection made when the wake is posted: the returning fiber selects, and the posted
helper resolves the hints that it was given. -/
def early : Ops :=
  { use := useWith (leaseLoop {}) (giveBackWith {} fun c =>
      bindWith (Ref.modifyWith c.pool (selectStep (nat 1))) fun selected =>
        post (resolveAll selected))
    wake := plainWake {} }

/-- A return that runs the item's finalizer. -/
def finalizing (finalize : Ctx → TermSrc → Src NativeOp) : Ops :=
  { use := useWith (leaseLoop {}) fun c mark item =>
      andThen (giveBackWith {} (fun c => post (plainWake {} c (nat 1))) c mark item)
        (finalize c item)
    wake := plainWake {} }

/-- The changed selection of a wake that hands an item. The front idle item is leased for the
waiters that the step selects, before any of them runs. -/
def selectHandStep (count s : TermSrc) : TermSrc :=
  let selected := app "take" [field s "waiters", count]
  let rest := recordSet s "waiters" (app "drop" [field s "waiters", count])
  ifT (andT (notT (isEmpty selected)) (notT (isEmpty (field s "available"))))
    (app "pair" [tuple [selected, app "get" [leasedOf s, nat 0]],
      recordSet
        (recordSet (recordSet rest "items" (marked s)) "available"
          (app "drop" [field s "available", nat 1]))
        "next" (app "add" [field s "next", len selected])])
    (app "pair" [tuple [selected, noItem s], rest])

/-- The commits of a handing wake: one row for each selected waiter. -/
def commitAll (c : Ctx) (selected handed : TermSrc) : Src NativeOp :=
  selectOptionWith handed (succeed unit) fun item =>
    bindWith (Ref.get c.names) fun reg =>
      iterateWith (nat 0)
        { while_ := fun i => app "lt" [i, len selected]
          body := fun i => selectOptionWith (app "get" [selected, i]) (succeed unit) fun w =>
            say c.log [nat 1, markOf reg (field w "id"), field item "resource",
              field item "lease"]
          step := fun i _ => app "succ" [i]
          result := fun _ => unit }

/-- The helper of a handing wake: the changed selection, the probe, the handed item into the
slot, the commits, and then each selected hint. -/
def handWake (seen : Ctx → TermSrc → Src NativeOp) (c : Ctx) (count : TermSrc) :
    Src NativeOp :=
  bindWith (Ref.modifyWith c.pool (selectHandStep count)) fun reply =>
    andThen (seen c (tupleAt reply 0))
      (andThen (Ref.set c.slot (tupleAt reply 1))
        (andThen (commitAll c (tupleAt reply 0) (tupleAt reply 1))
          (resolveAll (tupleAt reply 0))))

/-- A handed borrower: when its wait ends it holds the item that the wake handed it, and it
runs no step of its own. -/
def leaseHanded (c : Ctx) (mark : Nat) (restore : Src NativeOp → Src NativeOp)
    (id : TermSrc) : Src NativeOp :=
  bindWith
    (iterateWith noneT
      { cursorTy := some (.option (.option (itemTy .nat)))
        while_ := fun cursor => notT (app "isSome" [cursor])
        body := fun _ =>
          bindWith (Deferred.make .unit .never) fun hint =>
            bindWith (Ref.modifyWith c.pool (leaseStep id hint)) fun reply =>
              ifElse (tupleAt reply 0)
                (succeed (app "some" [tupleAt reply 1]))
                (selectOptionWith (tupleAt reply 1)
                  (andThen (waitAt restore hint (withdraw {} c id))
                    (andThen (say c.log [nat 4, nat mark])
                      (bindWith (Ref.get c.slot) fun handed =>
                        selectOptionWith handed (succeed noneT) fun item =>
                          succeed (app "some" [app "some" [item]]))))
                  fun item =>
                    andThen
                      (say c.log [nat 1, nat mark, field item "resource", field item "lease"])
                      (succeed (app "some" [app "some" [item]])))
        step := fun _ answer => answer })
    fun last =>
      selectOptionWith last (failCause (Authoring.Cause.die (str "pool: the loop ended")))
        fun answer => succeed answer

/-- A wake that hands an item to each selected waiter (the card's section 9). -/
def handing : Ops :=
  { use := useWith leaseHanded (giveBackWith {} fun c => post (handWake seenProbe c (nat 1)))
    wake := handWake seenProbe }

/-! ## Runs -/

def mk (src : Src NativeOp) : Module NativeOp := { main := src }

def verdict (src : Src NativeOp) : String :=
  match Effect4.Api.Author.build (mk src) with
  | .ok _ => "built"
  | .error (.scope _) => "scope"
  | .error (.typing r) => "typing: " ++ r.reason.head
  | .error (.admission _) => "admission"
  | .error (.serviceCarrier _ _ _) => "serviceCarrier"

def budget : Api.Budget := { fuel := 20000, compileFuel := 20000 }

/-- A source's run on a tape of decisions, through the checked session. -/
def runOn (tape : List Api.Decision) (src : Src NativeOp) : Option Run :=
  match Effect4.Api.Author.build (mk src) with
  | .error _ => none
  | .ok b => some ((Run.open b "pool" budget).play (Rows.tape tape))

/-- The tape of every run: the root evaluated, then one flush of every armed dispatcher. -/
def plain : List Api.Decision := [Api.evaluate, Api.flush]

/-- The root's exit on a tape. -/
def exitOn (tape : List Api.Decision) (src : Src NativeOp) : Option ExitV :=
  (runOn tape src).bind (·.exit)

def exitOf (src : Src NativeOp) : Option ExitV := exitOn plain src

/-- The fibers that exited, in the order of their exits. -/
def exitsOf (src : Src NativeOp) : Option (List Nat) :=
  (runOn plain src).map fun r => r.machine.trace.filterMap fun
    | .exited fiber _ => some fiber.value
    | _ => none

/-- The injected yields of a run: the fiber, and its count of operations at the yield. -/
def yieldsOf (src : Src NativeOp) : Option (List (Nat × Nat)) :=
  (runOn plain src).map fun r => r.machine.trace.filterMap fun
    | .yieldInjected fiber atOp => some (fiber.value, atOp)
    | _ => none

/-! ## The cases -/

/-- PP1. Size 1. A borrows and returns, then B. The pool's scope closes. The resource is
acquired inside the scope, and its finalizer writes its row. `opsOf` takes the log, for the
one red control whose return runs the finalizer. -/
def pp1 (opsOfLog : TermSrc → Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let snap ← scope (eff do
    let r ← acquireRelease "res" "x" (succeed (nat 1)) (say log [nat 9, var "res"])
    withCtx [r] log fun c => eff do
      let _ ← fork ((opsOfLog log).use c 1 fun _ => succeed unit)
      let _ ← fork ((opsOfLog log).use c 2 fun _ => succeed unit)
      snapshot c)
  let l ← Ref.get log
  return tuple [snap, l]

/-- PP2. Size 2. A and B hold the resources 1 and 2. A returns, then B. C borrows, then D. -/
def pp2 (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gA ← Deferred.make .unit .never
  let gB ← Deferred.make .unit .never
  let gC ← Deferred.make .unit .never
  let gD ← Deferred.make .unit .never
  withCtx [nat 1, nat 2] log fun c => eff do
    let _ ← fork (ops.use c 1 fun _ => Deferred.await gA)
    let _ ← fork (ops.use c 2 fun _ => Deferred.await gB)
    let _ ← Deferred.succeed gA unit
    let _ ← Deferred.succeed gB unit
    let between ← snapshot c
    let _ ← fork (ops.use c 3 fun _ => Deferred.await gC)
    let _ ← fork (ops.use c 4 fun _ => Deferred.await gD)
    let after ← snapshot c
    let l ← Ref.get log
    return tuple [between, after, l]

/-- PP3. Size 1. H holds. A waits, then B. H returns. Then A returns. -/
def pp3 (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gH ← Deferred.make .unit .never
  let gA ← Deferred.make .unit .never
  let gB ← Deferred.make .unit .never
  withCtx [nat 1] log fun c => eff do
    let _ ← fork (ops.use c 9 fun _ => Deferred.await gH)
    let _ ← fork (ops.use c 1 fun _ => Deferred.await gA)
    let _ ← fork (ops.use c 2 fun _ => Deferred.await gB)
    let before ← snapshot c
    let _ ← Deferred.succeed gH unit
    let posted ← snapshot c
    let _ ← settle
    let afterOne ← snapshot c
    let _ ← Deferred.succeed gA unit
    let _ ← settle
    let afterTwo ← snapshot c
    let l ← Ref.get log
    return tuple [before, posted, afterOne, afterTwo, l]

/-- PP4. PP3, and A is interrupted after H's return and before the posted helper runs. The
root does not yield between H's return and A's interruption. -/
def pp4 (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gH ← Deferred.make .unit .never
  let gB ← Deferred.make .unit .never
  withCtx [nat 1] log fun c => eff do
    let _ ← fork (ops.use c 9 fun _ => Deferred.await gH)
    let a ← fork (ops.use c 1 fun _ => succeed unit)
    let _ ← fork (ops.use c 2 fun _ => Deferred.await gB)
    let before ← snapshot c
    let _ ← Deferred.succeed gH unit
    let posted ← snapshot c
    let _ ← withFiber (Action.interrupt a)
    let left ← snapshot c
    let _ ← settle
    let after ← snapshot c
    let l ← Ref.get log
    return tuple [before, posted, left, after, l]

/-- PP8. Size 1. H holds. A waits and is interrupted. H returns, and B borrows. -/
def pp8 (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gH ← Deferred.make .unit .never
  let gB ← Deferred.make .unit .never
  withCtx [nat 1] log fun c => eff do
    let _ ← fork (ops.use c 9 fun _ => Deferred.await gH)
    let a ← fork (ops.use c 1 fun _ => succeed unit)
    let waiting ← snapshot c
    let _ ← withFiber (Action.interrupt a)
    let left ← snapshot c
    let _ ← Deferred.succeed gH unit
    let _ ← settle
    let returned ← snapshot c
    let _ ← fork (ops.use c 2 fun _ => Deferred.await gB)
    let after ← snapshot c
    let l ← Ref.get log
    return tuple [waiting, left, returned, after, l]

/-- **PP5, the public retry case.** A schedule of the profile: H leases, A enrols, H returns,
the helper selects A at the count 1, and A's own step takes the item. -/
def pp5public (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gH ← Deferred.make .unit .never
  let gA ← Deferred.make .unit .never
  withCtx [nat 1] log fun c => eff do
    let _ ← fork (ops.use c 9 fun _ => Deferred.await gH)
    let _ ← fork (ops.use c 1 fun _ => Deferred.await gA)
    let before ← snapshot c
    let _ ← Deferred.succeed gH unit
    let _ ← settle
    let after ← snapshot c
    let l ← Ref.get log
    return tuple [before, after, l]

/-- **PP5, the low-level control.** It is no public schedule: no public operation posts the
count 2 at an open pool. The state and the count are its premises. The root leases the item by
a raw step. A and then B enrol. A raw return makes the item idle and posts nothing: PP3's
state after H's return. Then the root posts one helper at the count 2. `bodyA` is A's body:
it returns at once in PP5, and it waits in the control where A holds. -/
def pp5control (ops : Ops) (bodyA : TermSrc → TermSrc → Src NativeOp) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gA ← Deferred.make .unit .never
  let gB ← Deferred.make .unit .never
  withCtx [nat 1] log fun c => eff do
    let mine ← Deferred.make .unit .never
    let hint ← Deferred.make .unit .never
    let held ← Ref.modifyWith c.pool (leaseStep mine hint)
    let _ ← fork (ops.use c 1 (bodyA gA))
    let _ ← fork (ops.use c 2 fun _ => Deferred.await gB)
    let _ ← Ref.modifyWith c.pool (returnStep (nat 0) (nat 0))
    let premise ← snapshot c
    let _ ← post (ops.wake c (nat 2))
    let _ ← settle
    let after ← snapshot c
    let l ← Ref.get log
    return tuple [tupleAt held 0, premise, after, l]

/-- A's body in PP5: it returns at once. -/
def atOnce : TermSrc → TermSrc → Src NativeOp := fun _ _ => succeed unit

/-- A's body in the control where A holds: it waits for its gate. -/
def holding : TermSrc → TermSrc → Src NativeOp := fun gate _ => Deferred.await gate

/-- C1, the close's first step alone. H holds and W waits. The step refuses new leases, and a
helper at its count wakes W, whose lease is refused. A second close begins nothing. H then
returns. The close that waits for H is another slice. -/
def c1 (ops : Ops) : Src NativeOp := eff do
  let log ← Ref.make noRows
  let gH ← Deferred.make .unit .never
  withCtx [nat 1] log fun c => eff do
    let _ ← fork (ops.use c 9 fun _ => Deferred.await gH)
    let _ ← fork (ops.use c 1 fun _ => succeed unit)
    let first ← Ref.modifyWith c.pool closeStep
    let _ ← ifElse (tupleAt first 0) (post (ops.wake c (tupleAt first 1))) (succeed unit)
    let closedNow ← snapshot c
    let _ ← settle
    let woken ← snapshot c
    let _ ← fork (ops.use c 2 fun _ => succeed unit)
    let second ← Ref.modifyWith c.pool closeStep
    let _ ← Deferred.succeed gH unit
    let _ ← settle
    let after ← snapshot c
    let l ← Ref.get log
    return tuple [first, closedNow, woken, second, after, l]

/-- S1, a stale lease's return. The lease 0 returns. The item is leased again, at the stamp 1.
A second return of the lease 0 is refused, and the lease 1 then returns. -/
def stale : Src NativeOp := eff do
  let log ← Ref.make noRows
  withCtx [nat 1] log fun c => eff do
    let a ← Deferred.make .unit .never
    let b ← Deferred.make .unit .never
    let hint ← Deferred.make .unit .never
    let _ ← Ref.modifyWith c.pool (leaseStep a hint)
    let first ← Ref.modifyWith c.pool (returnStep (nat 0) (nat 0))
    let _ ← Ref.modifyWith c.pool (leaseStep b hint)
    let held ← snapshot c
    let second ← Ref.modifyWith c.pool (returnStep (nat 0) (nat 0))
    let still ← snapshot c
    let third ← Ref.modifyWith c.pool (returnStep (nat 0) (nat 1))
    let after ← snapshot c
    return tuple [first, held, second, still, third, after]

/-! ## What a case answers, as values -/

/-- A snapshot as a value. -/
def snap (idle held leases : List Nat) (waiters : Nat) (closing : Bool) (next : Nat) : Val :=
  .list [.list (idle.map .nat), .list (held.map .nat), .list (leases.map .nat), .nat waiters,
    .bool closing, .nat next]

/-- A log as a value. -/
def rows (rs : List (List Nat)) : Val := .list (rs.map fun r => .list (r.map .nat))

/-- The commits and the returns of one resource, in order: the kind, the mark and the lease. -/
def eventsOf (resource : Nat) (rs : List (List Nat)) : List (Nat × Nat × Nat) :=
  rs.filterMap fun
    | [kind, mark, r, lease] =>
      if (kind = 1 ∨ kind = 2) ∧ r = resource then some (kind, mark, lease) else none
    | _ => none

/-- A commit, then its own lease's return, then the next commit. -/
def alternates : Option (Nat × Nat) → List (Nat × Nat × Nat) → Bool
  | _, [] => true
  | none, (1, mark, lease) :: rest => alternates (some (mark, lease)) rest
  | some (m, l), (2, mark, lease) :: rest => m == mark && l == lease && alternates none rest
  | _, _ => false

/-- **One borrower for an item**, on a log: each commit of a resource is returned by its own
lease before the next commit of that resource. -/
def oneBorrower (resource : Nat) (rs : List (List Nat)) : Bool :=
  alternates none (eventsOf resource rs)

/-- The profile's policy as PP1 takes it: it does not read the log. -/
def plainly : TermSrc → Ops := fun _ => library

-- Each scenario builds: the checker types every step inside its `Ref.modify`.
#guard [pp1 plainly, pp2 library, pp3 library, pp4 library, pp8 library, pp5public probed,
    pp5control probed atOnce, pp5control probed holding, c1 library, stale].map verdict =
  List.replicate 10 "built"

/-! ### The profile's answers, on the machine -/

-- PP1. B gets the same resource: both commits name the resource 1. No finalizer runs between:
-- the one row of the finalizer is the last, at the scope's close.
def pp1Rows : List (List Nat) := [[1, 1, 1, 0], [2, 1, 1, 0], [1, 2, 1, 1], [2, 2, 1, 1], [9, 1]]
#guard exitOf (pp1 plainly) = some (.success (.list [snap [0] [] [] 0 false 2, rows pp1Rows]))

-- PP2. After the two returns the idle items are `[1, 0]`: B's item, which came back last, is
-- at the front. C gets the resource 2, then D gets the resource 1 (row 269).
def pp2Rows : List (List Nat) :=
  [[1, 1, 1, 0], [1, 2, 2, 1], [2, 1, 1, 0], [2, 2, 2, 1], [1, 3, 2, 2], [1, 4, 1, 3]]
#guard exitOf (pp2 library) = some (.success (.list
  [snap [1, 0] [] [] 0 false 2, snap [] [0, 1] [3, 2] 0 false 4, rows pp2Rows]))

-- PP3. After H's return and before the helper, the item is idle beside two waiters: a state
-- of the profile. The helper then notifies A alone, and A's own step takes the item: B still
-- waits. After A's return the next helper notifies B.
def pp3Rows : List (List Nat) :=
  [[1, 9, 1, 0], [2, 9, 1, 0], [4, 1], [1, 1, 1, 1], [2, 1, 1, 1], [4, 2], [1, 2, 1, 2]]
#guard exitOf (pp3 library) = some (.success (.list
  [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [] [0] [1] 1 false 2,
    snap [] [0] [2] 0 false 3, rows pp3Rows]))

-- PP4. After H's return two requests wait. A's interruption leaves one. The helper then
-- selects the first waiter of the state that it finds, which is B: it serves no waiter that
-- left.
def pp4Rows : List (List Nat) := [[1, 9, 1, 0], [2, 9, 1, 0], [4, 2], [1, 2, 1, 1]]
#guard exitOf (pp4 library) = some (.success (.list
  [snap [] [0] [0] 2 false 1, snap [0] [] [] 2 false 1, snap [0] [] [] 1 false 1,
    snap [] [0] [1] 0 false 2, rows pp4Rows]))

-- PP8. The interrupted waiter's entry leaves. H's return then owes no wake, and B leases at
-- once: no row of a notification.
def pp8Rows : List (List Nat) := [[1, 9, 1, 0], [2, 9, 1, 0], [1, 2, 1, 1]]
#guard exitOf (pp8 library) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [0] 0 false 1, snap [0] [] [] 0 false 1,
    snap [] [0] [1] 0 false 2, rows pp8Rows]))

-- PP5, the public retry case. The selection selects A. After it and before A's step, one
-- item is idle, none is borrowed and no waiter is enrolled: A holds nothing. A is then
-- notified, and A's own step takes the item.
def pp5publicRows : List (List Nat) :=
  [[1, 9, 1, 0], [2, 9, 1, 0], [3, 1], [5, 1, 0, 0], [4, 1], [1, 1, 1, 1]]
#guard exitOf (pp5public probed) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [1] 0 false 2, rows pp5publicRows]))

-- PP5, the low-level control. The premise holds: the pool is open, the item is idle, and two
-- requests wait. One selection removes A and B, in that order. After it the item is idle and
-- nobody holds it. A is notified, A's own step takes the item, and A returns it. B is then
-- notified, and B's own step takes it.
def pp5controlRows : List (List Nat) :=
  [[3, 1, 2], [5, 1, 0, 0], [4, 1], [1, 1, 1, 1], [2, 1, 1, 1], [4, 2], [1, 2, 1, 2]]
#guard exitOf (pp5control probed atOnce) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [2] 0 false 3, rows pp5controlRows]))

-- The control where A holds. B is notified too, and it finds no idle item: a wake reserves
-- nothing. B's own step enrols B again.
def pp5holdingRows : List (List Nat) := [[3, 1, 2], [5, 1, 0, 0], [4, 1], [1, 1, 1, 1], [4, 2]]
#guard exitOf (pp5control probed holding) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [1] 1 false 2, rows pp5holdingRows]))

-- The probe changes no answer: the helper with no probe gives the same cells and the same
-- order of leases, on both forms.
#guard exitOf (pp5public library) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [1] 0 false 2,
    rows [[1, 9, 1, 0], [2, 9, 1, 0], [4, 1], [1, 1, 1, 1]]]))
#guard exitOf (pp5control library atOnce) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [] [0] [2] 0 false 3,
    rows [[4, 1], [1, 1, 1, 1], [2, 1, 1, 1], [4, 2], [1, 2, 1, 2]]]))

-- C1. The first step begins the close and counts one waiter. W is notified and refused. A new
-- borrower is refused at once. A second close begins nothing. H's lease is still held while
-- the pool is closing, and H's return makes the item idle.
#guard exitOf (c1 library) = some (.success (.list
  [.list [.bool true, .nat 1], snap [] [0] [0] 1 true 1, snap [] [0] [0] 0 true 1,
    .list [.bool false, .nat 0], snap [0] [] [] 0 true 1,
    rows [[1, 9, 1, 0], [4, 1], [6, 1], [6, 2], [2, 9, 1, 0]]]))

-- S1. The lease 0 returns. The second return of the lease 0 is refused, and nothing changes:
-- the lease 1 still holds the item. The lease 1 then returns.
#guard exitOf stale = some (.success (.list
  [.list [.bool true, .bool false], snap [] [0] [1] 0 false 2, .list [.bool false, .bool false],
    snap [] [0] [1] 0 false 2, .list [.bool true, .bool false], snap [0] [] [] 0 false 2]))

-- One borrower for an item, on each log of the profile's policy.
#guard [pp1Rows, pp3Rows, pp4Rows, pp8Rows, pp5publicRows, pp5controlRows, pp5holdingRows].all
  (oneBorrower 1)
#guard oneBorrower 1 pp2Rows && oneBorrower 2 pp2Rows

/-! ### The reading of the machine, on the trace

A borrower that a helper resumes runs inside the helper's task. -/

-- PP5, the control. A is fiber 1, B fiber 2 and the helper fiber 3. A exits before the helper
-- does: A's lease, its body and its return ran inside the helper's task.
#guard exitsOf (pp5control probed atOnce) = some [1, 3, 2, 0]
-- C1. W is fiber 2 and the helper fiber 3. The refused W exits inside the helper's task.
#guard exitsOf (c1 library) = some [2, 3, 4, 1, 0]
-- PP3. H is fiber 1, A fiber 2, B fiber 3, and the helpers are fibers 4 and 5. A holds, so
-- the first helper exits before A does.
#guard exitsOf (pp3 library) = some [1, 4, 2, 5, 3, 0]
-- PP4. The interrupted A (fiber 2) exits before the helper (fiber 4) runs.
#guard exitsOf (pp4 library) = some [1, 2, 4, 3, 0]

/-! ### The settings -/

-- No run holds an injected yield: the budget of 2048 operations is not reached.
#guard [pp1 plainly, pp2 library, pp3 library, pp4 library, pp8 library, pp5public probed,
    pp5control probed atOnce, c1 library, stale].map yieldsOf = List.replicate 9 (some [])
-- Each fiber's budget of operations before a yield, at the end of PP3.
#guard ((runOn plain (pp3 library)).map fun r => r.machine.fibers.map (·.maxOpsBeforeYield)) =
  some (List.replicate 6 2048)
-- Each run finishes, and each of the tape's two decisions is played: none is refused.
#guard ([pp1 plainly, pp2 library, pp3 library, pp4 library, pp8 library, pp5public probed,
    pp5control probed atOnce, c1 library, stale].map fun src =>
      (runOn plain src).map fun r => (decide (r.inspect.outcome = .finished), r.phases)) =
  List.replicate 9 (some (true, [.progressed, .progressed]))
-- One flush is every flush: two more change nothing.
#guard exitOn [Api.evaluate, Api.flush, Api.flush, Api.flush] (pp3 library) =
  exitOf (pp3 library)

/-! ### The red controls: each changed policy fails its own case

Each changed policy builds, so typing does not catch it. -/

/-- The return that runs the finalizer, as PP1 takes it. -/
def finalizingAt : TermSrc → Ops := fun log =>
  finalizing fun _ item => say log [nat 9, field item "resource"]

#guard [pp2 backOrder, pp4 early, pp5public handing, pp5control handing atOnce,
    pp1 finalizingAt].map verdict = List.replicate 5 "built"

-- A return that puts the item at the end fails PP2: the idle items are `[0, 1]`, and C gets
-- the resource 1.
#guard exitOf (pp2 backOrder) = some (.success (.list
  [snap [0, 1] [] [] 0 false 2, snap [] [0, 1] [2, 3] 0 false 4,
    rows [[1, 1, 1, 0], [1, 2, 2, 1], [2, 1, 1, 0], [2, 2, 2, 1], [1, 3, 1, 2], [1, 4, 2, 3]]]))
#guard exitOf (pp2 backOrder) != exitOf (pp2 library)
-- At the size 1 the two orders are one: PP2 is the case that tells them apart.
#guard exitOf (pp3 backOrder) = exitOf (pp3 library)

-- A selection made when the wake is posted fails PP4. H's return selects A at once. A then
-- leaves, and the helper resolves the hint of a waiter that left. B is never served: the
-- item stays idle while B waits.
#guard exitOf (pp4 early) = some (.success (.list
  [snap [] [0] [0] 2 false 1, snap [0] [] [] 1 false 1, snap [0] [] [] 1 false 1,
    snap [0] [] [] 1 false 1, rows [[1, 9, 1, 0], [2, 9, 1, 0]]]))
#guard exitOf (pp4 early) != exitOf (pp4 library)

-- A wake that hands an item fails the public retry case: after the selection the item is not
-- idle, and a lease is committed before A runs any step.
def pp5publicHandedRows : List (List Nat) :=
  [[1, 9, 1, 0], [2, 9, 1, 0], [3, 1], [5, 0, 1, 0], [1, 1, 1, 1], [4, 1]]
#guard exitOf (pp5public handing) = some (.success (.list
  [snap [] [0] [0] 1 false 1, snap [] [0] [1] 0 false 2, rows pp5publicHandedRows]))
#guard exitOf (pp5public handing) != exitOf (pp5public probed)

-- A wake that hands an item fails the low-level control at its own property: B's commit of
-- the resource 1 comes before A's return of it. So B holds an item that A did not return. At
-- the end the cell reads the item as idle while B holds it.
def pp5controlHandedRows : List (List Nat) :=
  [[3, 1, 2], [5, 0, 1, 0], [1, 1, 1, 1], [1, 2, 1, 1], [4, 1], [2, 1, 1, 1], [4, 2]]
#guard exitOf (pp5control handing atOnce) = some (.success (.list
  [.bool false, snap [0] [] [] 2 false 1, snap [0] [] [] 0 false 3, rows pp5controlHandedRows]))
#guard !oneBorrower 1 pp5controlHandedRows
#guard oneBorrower 1 pp5controlRows

-- A return that runs the item's finalizer fails PP1: the finalizer's row stands between A's
-- return and B's commit, so B gets a finalized resource.
#guard exitOf (pp1 finalizingAt) = some (.success (.list
  [snap [0] [] [] 0 false 2,
    rows [[1, 1, 1, 0], [2, 1, 1, 0], [9, 1], [1, 2, 1, 1], [2, 2, 1, 1], [9, 1], [9, 1]]]))
#guard exitOf (pp1 finalizingAt) != exitOf (pp1 plainly)

end Test.Program.PoolScenarios
