import Test.Program.ExitTypeLane
import Effect4.Laws.Machine.ForkLedger

/-!
Temporary comparison for fork-ledger migration, origin-ledger plan §3. It compares the old
fiber field and the new machine reader for every member fiber at initialization and after
each raw tape decision. The corpus/tape check is finite evidence at decision boundaries,
not a theorem about all reachable machines or every internal command. Retire with the old field.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
namespace Test.Api.ForkLedgerRunner
open Effect4 Effect4.Machine Effect4.Program
open Test.Program.TypedCorpus (Entry es key key2)

/-- Comparison includes the child identity through the lookup, and the parent, flag and site. -/
def same (m : Api.Machine) : Bool :=
  m.fibers.all fun f => m.originOf f.id = some f.origin

structure Counts where
  boundaries : Nat
  fibers : Nat
  agrees : Bool

/-- Exactly the boundary machines of `steppedBy`, including the initial machine. -/
def executePrefix (entry : Entry) (m : Api.Machine) : List Api.Decision → Counts
  | [] => ⟨1, m.fibers.length, same m⟩
  | decision :: rest =>
    let after := steppedBy entry.program 4000 entry.table m decision
    let tail := executePrefix entry after rest
    ⟨tail.boundaries + 1, tail.fibers + m.fibers.length, same m && tail.agrees⟩

def u : Term := .lit .unit
def unitProgram : NativeEff := .succeed u
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def daemon : Supervision.ForkOptions := ⟨true, true, .inherit⟩
def ordinary : NativeEff :=
  .bind (.withFiber (.fork unitProgram opts)) (.awaitFiber (.var 0) .joinEffect)
def explicitScope : NativeEff :=
  .bind (.perform (.scopeMake .sequential) u)
    (.withFiber (.forkIn unitProgram opts (.var 0)))
/-- The parallel-close fixture from RuntimeRContract.parTwo: two original children and
both finalizer forks must actually exist before its site check counts as coverage. -/
def finalizers : NativeEff :=
  .bind (.perform (.scopeMake .parallel) u)
    (.bind (.perform .deferredMake u)
      (.bind (.withFiber (.forkIn (.perform .deferredAwait (.var 1)) daemon (.var 0)))
        (.bind (.withFiber (.forkIn (.perform .deferredAwait (.var 1)) daemon (.var 0)))
          (.bind (.exit unitProgram) (.withFiber (.closeScope (.var 0) (.var 4)))))))
def race : NativeEff :=
  .withFiber (.raceAll (es [.perform .sleep (.lit (.nat 1)), unitProgram]))
def multiple : NativeEff :=
  .bind (.withFiber (.fork unitProgram opts))
    (.bind (.withFiber (.fork unitProgram daemon)) unitProgram)
def merge : NativeEff :=
  .provideLayer (.merge (.succeed key (.nat 1)) (.succeed key2 (.nat 2))) false (.service key)
def mergeAll : NativeEff :=
  .provideLayer (.mergeAll (.cons (.succeed key (.nat 1))
    (.cons (.succeed key2 (.nat 2)) .nil))) false (.service key)

def fixtures : List Entry :=
  [⟨"ledger/root", unitProgram, []⟩,
   ⟨"ledger/ordinary", ordinary, []⟩,
   ⟨"ledger/scoped", .scoped (.withFiber (.forkScoped unitProgram opts)), []⟩,
   ⟨"ledger/scoped-without-scope", .withFiber (.forkScoped unitProgram opts), []⟩,
   ⟨"ledger/forkIn", explicitScope, []⟩,
   ⟨"ledger/race", race, []⟩,
   ⟨"ledger/finalizers", finalizers, []⟩,
   ⟨"ledger/multiple", multiple, []⟩,
   ⟨"ledger/merge", merge, []⟩,
   ⟨"ledger/mergeAll", mergeAll, []⟩]

def inputs : List Entry := Test.Program.ExitTypeLane.lanePrograms ++ fixtures

def result (entry : Entry) (tape : List Api.Decision) : Counts :=
  executePrefix entry (Api.load entry.program 4000 Test.Program.ExitTypeLane.hostReplies) tape

def finished (p : NativeEff) : Api.Machine :=
  (Api.replay p 4000 [Api.evaluate, Api.flush]).machine

-- Coverage controls pin actual fork creation, not just the presence of fixture names.
#guard (finished unitProgram).forks = []
#guard (finished ordinary).forks = [⟨⟨1⟩, ⟨0⟩, false, [0, 0]⟩]
#guard (finished (.scoped (.withFiber (.forkScoped unitProgram opts)))).forks =
  [⟨⟨1⟩, Api.root, true, [0, 0]⟩]
#guard (finished (.withFiber (.forkScoped unitProgram opts))).forks = []
#guard ((finished (.withFiber (.forkScoped unitProgram opts))).fiber? Api.root).bind (·.exit) =
  some (.failure (Cause.die Defect.missingService))
#guard (finished explicitScope).forks.length = 1
#guard (finished race).forks.length = 2
#guard (finished finalizers).forks.length = 4
#guard ((finished finalizers).forks.filter fun r => r.site.isEmpty).length = 2
#guard (finished multiple).forks.length = 2
-- Layer builds also close their memo scopes through three source-free finalizer forks.
#guard (finished merge).forks.map (·.site) = [[0, 0], [0, 1], [], [], []]
#guard (finished mergeAll).forks.map (·.site) = [[0, 0, 0], [0, 0, 1, 0], [], [], []]

-- Missing fibers and roots remain distinct even when a malformed machine has a stray record.
#guard (Api.load unitProgram 40).originOf Api.root = some .root
#guard (Api.load unitProgram 40).originOf ⟨7⟩ = none
#guard ({ Api.load unitProgram 40 with forks := [⟨⟨7⟩, Api.root, true, [8]⟩] } : Api.Machine).originOf ⟨7⟩ = none

/-- Three independent mutations, each applied to a real fork with a nonempty source site. -/
def mutate (change : ForkRecord → ForkRecord) : Api.Machine :=
  let m := finished ordinary
  { m with forks := m.forks.map change }
#guard same (finished ordinary)
#guard !same (mutate fun r => { r with site := [] })
#guard !same (mutate fun r => { r with daemon := !r.daemon })
#guard !same (mutate fun r => { r with parent := ⟨r.parent.value + 1⟩ })

#eval show IO Unit from do
  let mut runs := 0
  let mut boundaries := 0
  let mut fibers := 0
  let mut failures : List String := []
  for entry in inputs do
    for (name, tape) in Test.Program.ExitTypeLane.tapes do
      let r := result entry tape
      runs := runs + 1
      boundaries := boundaries + r.boundaries
      fibers := fibers + r.fibers
      unless r.agrees do failures := (entry.name ++ "@" ++ name) :: failures
  unless failures.isEmpty do
    throw (IO.userError s!"fork ledger: mismatches {failures.take 20}")
  IO.println s!"fork ledger: {inputs.length} programs, {runs} runs, {boundaries} decision boundaries, {fibers} member-fiber comparisons, 0 mismatches; all 3 mutants rejected"

end Test.Api.ForkLedgerRunner
