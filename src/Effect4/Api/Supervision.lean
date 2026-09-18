import Effect4.Api

/-!
# Effect4.Api.Supervision — who holds a fiber, before the run and during it

Effect TypeScript gives `fork`, `forkDaemon`, `forkIn` and `forkScoped` and then stops: a
daemon is untracked, and nothing tells you it is there until it bites. Here the same thing is
data, twice over.

**Before the run.** Every fork a program can make is written in the program, so the
supervision tree of a program is a fold over the program. `ForkSite` is one fork — its path,
what it makes (a tracked child, an unpinned daemon, a daemon at a scope, a race entrant) and
the options written at it — and `supervision` is the list of them in program order, computed
by one walk that has no case per constructor: it reads each node through the generated layer
view (`Program/LayerView.lean`, `view`) and matches the four constructor names that fork.
Paths are the existing addressing (`Program/Refs.lean`, `Node.at_`), so a site names a node
of the tree and `ForkSite.body` names the program it forks.

**During the run.** `FiberStatus` says what the machine is holding each fiber by: its parent's
`children` list (`Machine/Fibers.lean:244`), the keyed scope finalizer a `forkIn` registered
(`:961-990`, the `Observer.dropScopeFinalizer` the link leaves on the fiber), nothing at all,
or an exit. `fiberStatuses` reads that off the machine — no trace needed, the three
observations are all machine state — and `unpinnedDaemonsAlive` is the list nobody holds. So
"no unpinned daemon is alive" (`daemonsQuiet`) is a decidable fact about a run, and DI-75's
invisible daemon is a value you can print.

What the four statuses do **not** separate: a fiber pinned by `fiberRunIn` (the `runIn`
action) rather than by a fork. `runIn` links an existing fiber to a scope through the same
`linkScope` (`Machine/Fibers.lean:1229-1232`), so it leaves the same observer and reads as
`.pinned`. It is the one action that pins without forking, which is why it is not a fork site.

The laws are `src/Effect4/Laws/Api/Supervision.lean`; the battery is
`Test/Api/SupervisionContract.lean`.
-/

set_option autoImplicit false

namespace Effect4.Api

universe u v

open Effect4 Effect4.Machine Effect4.Program

/-! ## The fork sites of a program: supervision before the run -/

/-- What a fork site makes.

`fork` is the only site that can make a tracked child; rc.112's `forkIn` and `forkScoped`
force the daemon flag at the pin (`internal/effect.ts:5366`, `:5406`, transcribed at
`Machine/Fibers.lean:1205`, `:1213`), and a `raceAll` entrant is an immediate daemon the race
owns (`:1521`, `Machine/Fibers.lean` `launchEntrant`). -/
inductive ForkKind
  /-- `fork` with `daemon := false` (`Effect.forkChild`): tracked by the forking fiber, so the
  parent's exit interrupts it (`Machine/Fibers.lean:1724`). -/
  | child
  /-- `fork` with `daemon := true` (`Effect.forkDetach`): no parent tracks it and no scope
  holds it. This is the fiber that survives its parent unobserved. -/
  | daemon
  /-- A daemon at a pin: `forkIn` at the scope the term names, or `forkScoped` at the ambient
  scope (`none`). The scope's close interrupts it. -/
  | pinned (scope : Option Effect4.Program.Term)
  /-- One entrant of a `raceAll`: an immediate daemon, interruptible, cancelled by the race. -/
  | raceEntrant
deriving DecidableEq

/-- Whether the fiber this kind of site makes is a daemon. Only `.child` is not. -/
def ForkKind.isDaemon : ForkKind → Bool
  | .child => false
  | _ => true

/-- One fork written in a program: where it is, what it makes, and the options written at it.

`options` is what the *program* says. For `.pinned` and `.raceEntrant` the machine overrides
its `daemon` field — that override is the rc.112 fact, and keeping the written options beside
the kind is what makes the override visible rather than lost. -/
structure ForkSite where
  /-- The path of the node that forks: the `action` node for `fork`, `forkIn` and
  `forkScoped`, the `effs` cons cell for a race entrant. `Node.at_` at this path is that
  node. -/
  path : List Nat
  kind : ForkKind
  options : Effect4.Supervision.ForkOptions
deriving DecidableEq

/-- Whether this site forks a daemon: a property of the kind alone. -/
def ForkSite.isDaemon (s : ForkSite) : Bool := s.kind.isDaemon

/-- The path of the program this site forks. Every forking node holds it as child `0`:
`fork`, `forkIn` and `forkScoped` take the program first, and a race entrant is the head of
its cons cell (`Program/LayerView.lean`, `argSorts`). -/
def ForkSite.body (s : ForkSite) : List Nat := s.path ++ [0]

/-- The options every `raceAll` entrant is forked with: immediate, daemon, interruptible
(`internal/effect.ts:1521`, `Machine/Fibers.lean` `launchEntrant`). -/
def raceEntrantOptions : Effect4.Supervision.ForkOptions :=
  ⟨true, true, Effect4.Supervision.MaskMode.interruptible⟩

/-- The fork sites of one node, read off its constructor name and its arguments.

This is the whole classification, in four rows. Nothing here matches a constructor: the node
arrives through the generated layer view as a name and a list of `ArgF`, so a constructor
added to the alphabet reaches this table as a name it does not carry and yields nothing. -/
def forkSitesOf {Op : Type} :
    EffFam → String → List (ArgF Op (EffSelfCarrier Op)) → List Nat → List ForkSite
  | .action, "fork", [_, .forkOptions o], p =>
    [⟨p, if o.daemon then ForkKind.daemon else ForkKind.child, o⟩]
  | .action, "forkIn", [_, .forkOptions o, .term scope], p => [⟨p, .pinned (some scope), o⟩]
  | .action, "forkScoped", [_, .forkOptions o], p => [⟨p, .pinned none, o⟩]
  | .effs, "cons", _, p => [⟨p, .raceEntrant, raceEntrantOptions⟩]
  | _, _, _, _ => []

/-- The fork sites of one node of any family, through the generated layer view. -/
def siteAt {Op : Type} (fam : EffFam) : EffSelfCarrier Op fam → List Nat → List ForkSite :=
  fun node p => forkSitesOf fam (view fam node).1 (view fam node).2 p

/-- Every fork site of a program, in program order: one walk over the path fold
(`foldMapAt_eff`, `Program/Fold.lean`), yielding at the two sorts that fork. `effs` occurs
only under `raceAll` (`Program/LayerView.lean`, `argSorts`), so its cells are exactly the race
entrants. -/
def supervision {Op : Type} (e : Effect4.Program.Eff Op) : List ForkSite :=
  foldMapAt_eff [] (· ++ ·) [] e (f_effs := siteAt .effs) (f_action := siteAt .action)

/-- `a` encloses `b`: it is `b` or a proper prefix of it. -/
def enclosingPath (a b : List Nat) : Bool := decide (a = b) || Path.properPrefix a b

/-- The site that forked the fiber this site runs on: the innermost site whose body encloses
it. `none` is the root fiber. This is the supervision *tree* as a projection of the list — no
second representation. -/
def ForkSite.parent (sites : List ForkSite) (s : ForkSite) : Option ForkSite :=
  (sites.filter fun t => enclosingPath t.body s.path).foldl
    (fun best t => match best with
      | some b => if b.body.length < t.body.length then some t else some b
      | none => some t) none

/-! ## The fibers of a run: supervision during it -/

/-- One fiber of the machine at the application's alphabet. -/
abbrev Fiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx

/-- What the machine is holding a fiber by.

The four are read in this order, which is the order of what governs the fiber: an exit ends
the question; a tracked fiber answers to its parent's exit; an untracked one that carries a
scope link answers to that scope's close; anything else answers to nobody. -/
inductive FiberStatus
  /-- `parent` tracks it (`RunFiber.children`, `Machine/Fibers.lean:244`), so the parent's
  exit interrupts it (`:1724`, `RunEvent.childrenInterrupted`). -/
  | child (parent : FiberId)
  /-- A daemon linked to `scope` under the registration identity `key`, which the scope's
  close interrupts and whose drop observer the machine left on the fiber (`:988-990`). -/
  | pinned (scope : Nat) (key : Nat)
  /-- Alive, untracked and unpinned: DI-75's fiber, whose rows appear on neither face. -/
  | daemon
  /-- It has exited. -/
  | exited (exit : ExitV)
deriving DecidableEq

/-- Whether the fiber is still running or parked. -/
def FiberStatus.live : FiberStatus → Bool
  | .exited _ => false
  | _ => true

/-- The fiber that tracks `id`, if any. Tracking is `Cmd.trackChild`, run after a non-daemon
child's start (`Machine/Fibers.lean:1903-1910`), and it is dropped by the child's
`Observer.untrackChild` when the child exits (`:1616-1617`). -/
def parentOf (m : Machine) (id : FiberId) : Option FiberId :=
  (m.fibers.find? fun g => g.children.contains id).map RunFiber.id

/-- The scope a fiber is pinned to and the registration identity the store allocated for it.
`linkScope` leaves exactly this observer on the linked fiber (`Machine/Fibers.lean:988-989`),
so the link is recoverable from machine state alone — the trace is not needed. -/
def pinOf (f : Fiber) : Option (Nat × Nat) :=
  f.observers.findSome? fun
    | .dropScopeFinalizer scope key => some (scope, key)
    | _ => none

/-- What the machine holds this fiber by. -/
def statusOf (m : Machine) (f : Fiber) : FiberStatus :=
  match f.exit with
  | some exit => .exited exit
  | none =>
    match parentOf m f.id with
    | some parent => .child parent
    | none =>
      match pinOf f with
      | some (scope, key) => .pinned scope key
      | none => .daemon

/-- Every fiber of the run with what holds it, in creation order (`spawn` appends and nothing
removes a fiber, `Machine/Fibers.lean:922`). -/
def fiberStatuses (m : Machine) : List (FiberId × FiberStatus) :=
  m.fibers.map fun f => (f.id, statusOf m f)

/-- The live fibers nobody holds: alive, untracked, unpinned. -/
def unpinnedDaemonsAlive (m : Machine) : List FiberId :=
  (fiberStatuses m).filterMap fun entry =>
    if entry.2 = FiberStatus.daemon then some entry.1 else none

/-- The decidable check: no unpinned daemon is alive. -/
def daemonsQuiet (m : Machine) : Bool := (unpinnedDaemonsAlive m).isEmpty

/-- The property `daemonsQuiet` decides: every live fiber is a tracked child or a daemon at a
pin. At a terminated observation nothing is live, so it holds for a different reason; the
content of the check is at every other observation. -/
def Supervised (m : Machine) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → statusOf m f ≠ FiberStatus.daemon

/-- No exited fiber is parked. `RunFiber.publish` writes the exit and clears the guard in one
step (`Machine/Fibers.lean:1696-1704`), so every machine a run reaches satisfies it; a machine
written by hand need not, which is why the laws that need it take it as a hypothesis. -/
def exitedUnparked (m : Machine) : Bool :=
  m.fibers.all fun f => !f.exit.isSome || f.parked == Parked.notParked

/-! ## The `forked` events of a trace

What the machine stamps when it forks. Kept beside the static table so the law that they
agree has both halves in one place. -/

/-- Every `RunEvent.forked` of a trace, as parent, child and the daemon flag the machine
stamped. -/
def forkedOf {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {κ η : Type (max u v)}
    (trace : List (RunEvent ν σ β ε δ ι α χ κ η)) : List (FiberId × FiberId × Bool) :=
  trace.filterMap fun
    | .forked parent child daemon => some (parent, child, daemon)
    | _ => none

/-- The `forked` events of a run. -/
def forkedEvents (m : Machine) : List (FiberId × FiberId × Bool) := forkedOf m.trace

/-! ## A run, read for supervision -/

/-- Every fiber of a finished or parked run with what holds it. -/
def Run.fibers (r : Run) : List (FiberId × FiberStatus) := fiberStatuses r.machine

/-- The live fibers of a run that nobody holds. -/
def Run.unpinnedDaemonsAlive (r : Run) : List FiberId := Api.unpinnedDaemonsAlive r.machine

/-- Whether the run left no unpinned daemon alive. -/
def Run.daemonsQuiet (r : Run) : Bool := Api.daemonsQuiet r.machine

/-- Every fork the run made, with the flag the machine stamped. -/
def Run.forked (r : Run) : List (FiberId × FiberId × Bool) := forkedEvents r.machine

/-! ## Receipts -/

section Receipts

/-- A fork inside a forked program: the inner site's parent is the outer one. -/
private def nestedForks : Effect4.Program.Eff Nat :=
  .withFiber (.fork
    (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, true, .interruptible⟩))
    ⟨true, false, .interruptible⟩)

/-- Two forks side by side: both are forks of the root fiber, not of each other. -/
private def siblingForks : Effect4.Program.Eff Nat :=
  .bind (.withFiber (.fork (.succeed (.var 0)) ⟨true, false, .interruptible⟩))
    (.withFiber (.fork (.succeed (.var 0)) ⟨true, true, .interruptible⟩))

-- A plain child fork: one site, at the action node under `withFiber`.
#guard supervision (Op := Nat)
    (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩)) =
  [⟨[0], .child, ⟨true, false, .interruptible⟩⟩]

-- The same fork with the daemon flag set: the kind changes, the options are kept.
#guard supervision (Op := Nat)
    (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, true, .interruptible⟩)) =
  [⟨[0], .daemon, ⟨true, true, .interruptible⟩⟩]

-- `forkIn` is a daemon at the scope the term names, whatever the written flag says.
#guard supervision (Op := Nat)
    (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩ (.var 0))) =
  [⟨[0], .pinned (some (.var 0)), ⟨true, false, .inherit⟩⟩]
#guard (supervision (Op := Nat)
    (.withFiber (.forkIn (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩ (.var 0)))).all
  ForkSite.isDaemon

-- `forkScoped` is a daemon at the ambient scope.
#guard supervision (Op := Nat)
    (.withFiber (.forkScoped (.succeed (.lit (.nat 1))) ⟨true, false, .inherit⟩)) =
  [⟨[0], .pinned none, ⟨true, false, .inherit⟩⟩]

-- A `raceAll` is one site per entrant, at the cons cell that holds it.
#guard supervision (Op := Nat)
    (.withFiber (.raceAll (.cons (.succeed (.var 0)) (.cons (.succeed (.var 1)) .nil)))) =
  [⟨[0, 0], .raceEntrant, raceEntrantOptions⟩, ⟨[0, 0, 1], .raceEntrant, raceEntrantOptions⟩]

-- A program with no fork has no site.
#guard supervision (Op := Nat) (.bind (.succeed (.var 0)) (.perform 3 (.var 0))) = []

-- The site's body is the program it forks, and `Node.at_` finds it there.
#guard (Node.eff (Op := Nat)
    (.withFiber (.fork (.succeed (.lit (.nat 1))) ⟨true, false, .interruptible⟩))).at_
  (ForkSite.body ⟨[0], .child, ⟨true, false, .interruptible⟩⟩) =
  some (Node.eff (.succeed (.lit (.nat 1))))

-- The nesting of the sites is the supervision tree.
#guard (supervision nestedForks).map ForkSite.path = [[0], [0, 0, 0]]
#guard (supervision nestedForks).map
    (fun s => (ForkSite.parent (supervision nestedForks) s).map ForkSite.path) =
  [none, some [0]]

#guard (supervision siblingForks).map ForkSite.path = [[0, 0], [1, 0]]
#guard (supervision siblingForks).map
    (fun s => (ForkSite.parent (supervision siblingForks) s).map ForkSite.path) = [none, none]

-- Only a `.child` site is not a daemon.
#guard (supervision siblingForks).map ForkSite.isDaemon = [false, true]

end Receipts

end Effect4.Api
