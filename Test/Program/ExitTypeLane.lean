import Test.Program.TypedCorpus

/-!
# Test.Program.ExitTypeLane — every typed run's exit against its checked type

The dynamic soundness lane of the typed-state admission audit (decision row 89). Each well-typed
program of the typed corpus and of the random corpus runs on the shipped machine (`Api.replay`;
the reference machine is equal by `run_eq_ref`) under a small family of decision tapes: quiet,
with the clock advanced, with the root interrupted at once, and interrupted after the first
timer. A run that exits must fit the program's checked type (`CompletionOk`'s check on the
answer and error columns), and its cause must carry no bad-shape or not-implemented defect,
nor a missing service when the program requires none.

This is an empirical check over a finite program and tape family, for the fragment where type
soundness has no proof yet. It observes the root fiber's exit only; forked fibers' exits are
not checked. Host rows answer from a fixed well-typed reply.
-/

set_option autoImplicit false
namespace Test.Program.ExitTypeLane
open Effect4 Effect4.Program Effect4.Machine Test.Program.TypedCorpus

def interruptRoot : Api.Decision := .interruptFrom none ReasonAnnotations.empty Api.root
def advanceAll : Api.Decision := .advance (ClockMillis.ofNat 100000)

def tapes : List (String × List Api.Decision) := [
  ("quiet", [Api.evaluate, Api.flush]),
  ("timers", [Api.evaluate, Api.flush, advanceAll, Api.flush]),
  ("interrupt", [Api.evaluate, interruptRoot, Api.flush, advanceAll, Api.flush]),
  ("late-interrupt", [Api.evaluate, Api.flush, .advance (ClockMillis.ofNat 1), interruptRoot,
    Api.flush, advanceAll, Api.flush])]

/-- A defect no well-typed program may produce. -/
def badDefect (ty : EffTy) : Reason Err Defect FiberId Ann → Bool
  | .die d _ => d == .badName || d == .notImplemented ||
      (d == .missingService && ty.requires == Env.Requirement.empty)
  | _ => false

/-- The exit fits the checked type at the run's allocated external spellings. -/
def fits (ty : EffTy) (allocated : List String) : ExitV → Bool
  | .success v => Val.hasTy v ty.answer allocated
  | .failure c => causeAdmits (fun v t => Val.hasTy v t allocated) ty.error c &&
      !(c.reasons.any (badDefect ty))

/-- The fixed replies host rows read, one per call. -/
def hostReplies : List (Completion Val Err Defect FiberId Ann) :=
  List.replicate 8 (.ofExit (.success (Val.nat 5)))

/-- One run: `none` when the root has not exited (a parked timer or a frontier). -/
def verdict (e : Entry) (ty : EffTy) (tape : List Api.Decision) : Option Bool :=
  let r := Api.replay e.program 4000 tape hostReplies e.table
  r.exit.map (fits ty r.machine.state.externals.allocated)

/-- The lane's programs: the typed corpus, its interleaving pairs, and the random corpus's typed
programs. -/
def lanePrograms : List Entry :=
  programs ++ pairPrograms ++ ((Test.Program.Gen.sample.zipIdx.filter fun (p, _) => Api.wellTyped p).map
    fun (p, i) => { name := s!"gen/g{i}", program := p })

/-- One program's verdicts, one per tape. -/
structure Result where
  name : String
  verdicts : List (String × Option Bool)

def results : List Result :=
  lanePrograms.filterMap fun e => (Api.typeOf e.program e.table).map fun ty =>
    ⟨e.name, tapes.map fun (tn, t) => (tn, verdict e ty t)⟩

def violationsOf (rs : List Result) : List String :=
  rs.flatMap fun r => (r.verdicts.filter (·.2 == some false)).map fun (tn, _) => r.name ++ "@" ++ tn

/-- Programs that exit under no tape of the family: the lane would check nothing of them. -/
def neverExitsOf (rs : List Result) : List String :=
  (rs.filter fun r => r.verdicts.all (·.2.isNone)).map (·.name)

/-! ## Pins

The runs are computed once. The build fails on a violation, on a program that exits under no
tape, and on an ill-typed lane program; the counts are printed, not pinned. -/

#eval show IO Unit from do
  unless lanePrograms.all fun e => Api.wellTyped e.program e.table do
    throw (IO.userError "exit-type lane: an ill-typed program")
  let rs := results
  let violations := violationsOf rs
  let never := neverExitsOf rs
  unless violations.isEmpty do throw (IO.userError s!"exit-type lane: violations {violations.take 20}")
  unless never.isEmpty do throw (IO.userError s!"exit-type lane: never exit {never.take 20}")
  let exited := (rs.map fun r => (r.verdicts.filter (·.2.isSome)).length).sum
  IO.println s!"exit-type lane: {rs.length} programs, {rs.length * tapes.length} runs, {exited} exited, 0 violations, every program exits under some tape"

/-! ## Controls: the check is not vacuous -/

-- The rc.112 escape's exit (`E4-SCHED-CE-008`, before the divergence): a typed `Fail 42` at an
-- error column `never`.
#guard !fits (EffTy.pure .nat) [] (.failure (Cause.fail (Err.tag 42)))
-- The contagion's defect (`E4-SCHED-CE-008`): a bad-shape death is a violation at every type.
#guard !fits ⟨.nat, .unknown, Env.Requirement.empty⟩ [] (.failure (Cause.die Defect.badName))
-- A typed entry's own exit checked against a wrong type is a violation.
#guard (entries.find? (·.name == "succeed")).all fun e =>
  verdict e (EffTy.pure .unit) [Api.evaluate, Api.flush] == some false
-- An interrupted or user-defect exit fits every type.
#guard fits (EffTy.pure .nat) [] (.failure (Cause.interrupt none))
#guard fits (EffTy.pure .nat) [] (.failure (Cause.die (Defect.user 3)))

end Test.Program.ExitTypeLane
