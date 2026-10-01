import Effect4.Api.Supervision

/-! Registry seat, task 1: what every fiber-creating construct records.

Research evidence outside the Test root. Base `be15b062`. Finite checks, not proofs.

Each program below exercises one construct that creates a fiber on the native machine. The
guards pin, for every fiber of the run, the recorded origin and the sort of the node at the
recorded site. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Research.Pass.Registry.Sites
open Effect4 Effect4.Machine Effect4.Program

/-- What the node at a recorded site is. First-order; no strings. -/
inductive SiteKind
  | root
  /-- `withFiber (fork …)`: the site is the action node. -/
  | fork
  /-- `withFiber (forkIn …)`. -/
  | forkIn
  /-- `withFiber (forkScoped …)`, whose fork runs through the machine's `forkIn` arm. -/
  | forkScoped
  /-- A `raceAll` entrant: the site is the `effs` cons cell whose head is the entrant. -/
  | raceEntrant
  /-- A `merge` or `mergeAll` sibling build (`EffThunk.forkLayer`): the site is a layer node. -/
  | layerBuild
  /-- The empty site: a fork with no source point. -/
  | empty
  /-- A non-empty site whose node is none of the above. -/
  | other
deriving DecidableEq, Repr

def siteKind (root : Api.Program) : Origin → SiteKind
  | .root => .root
  | .forked _ _ [] => .empty
  | .forked _ _ site =>
    match Node.at_ (.eff root) site with
    | some (.action (.fork _ _)) => .fork
    | some (.action (.forkIn _ _ _)) => .forkIn
    | some (.action (.forkScoped _ _)) => .forkScoped
    | some (.effs (.cons _ _)) => .raceEntrant
    | some (.layer _) => .layerBuild
    | _ => .other

abbrev E := Eff NativeOp
def n (i : Nat) : Term := .lit (.nat i)
def u : Term := .lit .unit
def v (i : Nat) : Term := .var i
def es : List E → Effs NativeOp | [] => .nil | e :: r => .cons e (es r)
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def key2 : ServiceKey := ⟨⟨5⟩, ⟨4⟩⟩

def forkProg : E := .bind (.withFiber (.fork (.succeed (n 1)) opts)) (.awaitFiber (v 0) .joinEffect)
def forkInProg : E :=
  .bind (.perform (.scopeMake .sequential) u) (.withFiber (.forkIn (.succeed (n 1)) opts (v 0)))
def forkScopedProg : E := .scoped (.withFiber (.forkScoped (.succeed (n 1)) opts))
/-- The first entrant fails, so the race launches the second too. -/
def raceProg : E := .withFiber (.raceAll (es [.fail (n 1), .succeed (n 2)]))
def mergeProg : E :=
  .provideLayer (.merge (.succeed key (.nat 1)) (.succeed key2 (.nat 2))) false (.service key2)
def mergeAllProg : E :=
  .provideLayer (.mergeAll (.cons (.succeed key (.nat 1)) (.cons (.succeed key2 (.nat 2)) .nil)))
    false (.service key)
/-- A parallel scope holding two `forkIn` children, closed: its close forks one daemon per
finalizer (`closePar`, `Machine/Fibers.lean:965-971`). The children sleep so they are still
live, and so linked, when the scope closes. -/
def closeParProg : E :=
  .bind (.perform (.scopeMake .parallel) u)
    (.bind (.withFiber (.forkIn (.perform .sleep (n 10)) opts (v 0)))
      (.bind (.withFiber (.forkIn (.perform .sleep (n 10)) opts (v 0)))
        (.bind (.exit (.succeed u))
          (.withFiber (.closeScope (v 0) (v 3))))))

def programs : List E :=
  [forkProg, forkInProg, forkScopedProg, raceProg, mergeProg, mergeAllProg, closeParProg]

#guard programs.all fun p => Api.wellTyped p

def runOf (p : E) : Api.Inspection := Api.run p 2000

/-- Every fiber of the run: its id, origin and site kind. -/
def census (p : E) : List (FiberId × Origin × SiteKind) :=
  (runOf p).machine.fibers.map fun f => (f.id, f.origin, siteKind p f.origin)

#guard census forkProg = [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ false [0, 0], .fork)]
#guard census forkInProg = [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ true [1, 0], .forkIn)]
#guard census forkScopedProg =
  [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ true [0, 0], .forkScoped)]
#guard census raceProg =
  [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ true [0, 0], .raceEntrant),
   (⟨2⟩, .forked ⟨0⟩ true [0, 0, 1], .raceEntrant)]
-- A `merge` forks one build per sibling at the sibling's layer path; when the provided scope
-- closes, the merge's parallel parent scope closes through `closePar`, one empty-site daemon per
-- finalizer.
#guard census mergeProg =
  [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ true [0, 0], .layerBuild),
   (⟨2⟩, .forked ⟨0⟩ true [0, 1], .layerBuild),
   (⟨3⟩, .forked ⟨0⟩ true [], .empty), (⟨4⟩, .forked ⟨0⟩ true [], .empty),
   (⟨5⟩, .forked ⟨0⟩ true [], .empty)]
#guard census mergeAllProg =
  [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ true [0, 0, 0], .layerBuild),
   (⟨2⟩, .forked ⟨0⟩ true [0, 0, 1, 0], .layerBuild),
   (⟨3⟩, .forked ⟨0⟩ true [], .empty), (⟨4⟩, .forked ⟨0⟩ true [], .empty),
   (⟨5⟩, .forked ⟨0⟩ true [], .empty)]
#guard census closeParProg =
  [(⟨0⟩, .root, .root), (⟨1⟩, .forked ⟨0⟩ true [1, 0, 0], .forkIn),
   (⟨2⟩, .forked ⟨0⟩ true [1, 1, 0, 0], .forkIn),
   (⟨3⟩, .forked ⟨0⟩ true [], .empty), (⟨4⟩, .forked ⟨0⟩ true [], .empty)]

/-! The static fork table `Api.supervision` lists action and race-cell sites only. A layer
build's recorded site is a layer node, which the table does not list. -/

#guard (Api.supervision mergeProg).map (·.path) = []
#guard (Api.supervision mergeAllProg).map (·.path) = []
#guard (Api.supervision raceProg).map (·.path) = [[0, 0], [0, 0, 1]]
#guard (Api.supervision closeParProg).map (·.path) = [[1, 0, 0], [1, 1, 0, 0]]

/-! While a layer sibling build is running, the supervision view reads it as an unpinned daemon:
it is forked as a daemon (`Compile.lean:1453-1455`), no parent tracks it and no scope link pins
it. -/

def slowMerge : E :=
  .scoped (.provideLayer
    (.merge (.effect key (.bind (.perform .sleep (n 5)) (.succeed (n 1)))) (.succeed key2 (.nat 2)))
    false (.service key))

#guard Api.wellTyped slowMerge
#guard ((Api.replay slowMerge 2000 [Api.evaluate, Api.flush]).machine.fibers.map
    fun f => (f.id, siteKind slowMerge f.origin)) =
  [(⟨0⟩, .root), (⟨1⟩, .layerBuild), (⟨2⟩, .layerBuild)]
#guard Api.unpinnedDaemonsAlive (Api.replay slowMerge 2000 [Api.evaluate, Api.flush]).machine = [⟨1⟩]

#eval IO.println "Registry sites probe: all guards passed."

end Research.Pass.Registry.Sites
