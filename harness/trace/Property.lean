import Effect4.Meta.Derive
import Effect4.Target.TypeScript.Trace
import Effect4.Target.TypeScript.Lower
import Effect4.Target.TypeScript.ScriptFlow
import Effect4.Target.TypeScript.FlowLower

/-!
# The property loop (plan packet P-T6)

Flows are generated *by construction* over the Cell family's type graph, so
every generated flow is admitted (`Effects.admit` is the free oracle: a
refusal is a generator bug). Tapes are built by policy through the runner
itself (all-left, all-right, alternating, seeded random), so every tape names
the sites the run actually reaches; a tape longer than the cap ends the run
at the unanswered frontier, which the host must report as `frontier` too.

Modes:
- `corpus <seed> <count> <dir>`: writes `dir/property-fixture.ts` (every flow,
  dispatch form), `dir/goldens/<program>.<tape>.tsv`, and prints the summary
  row the ledger records.
- `shrink <seed> <count> <program> <tape> <path> <dir>`: the candidates of one
  case after the shrink steps in `path` (comma-separated candidate indices),
  as a corpus of their own.
- `case <seed> <count> <program> <path>`: the raw flow of a case, as data.
-/

open Effects Effect4 Effect4.Meta Effect4.Target.EffectV4 Effect4.Flow
open Effects.Trace (Val)

effect_signature Cell where
  | get : Nat ⟪ "read the cell" ⟫
  | put (n : Nat) : Unit ⟪ "write the cell" ⟫

/-! ## A seeded generator -/

structure Rng where
  seed : Nat

def Rng.next (r : Rng) : Nat × Rng :=
  let s := (r.seed * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
  (s / 2 ^ 33, ⟨s⟩)

abbrev Gen := StateM Rng

def below (n : Nat) : Gen Nat :=
  modifyGet fun r => let (x, r) := r.next; (x % (max n 1), r)

def coin : Gen Bool := do pure ((← below 2) = 1)

/-! ## The type graph -/

/-- The operations a generated flow may perform; positions are `OperationId`s. -/
def propertyTable : List OpSpec :=
  [ { name := "get", kind := .family, requestTy := "void", answerTy := "number" }
  , { name := "put", kind := .family, requestTy := "number", answerTy := "void" }
  , { name := "succ", kind := .atom, requestTy := "number", answerTy := "number" }
  , { name := "lit", kind := .lit .unit, requestTy := "number", answerTy := "void" }
  , { name := "lit", kind := .lit (.nat 3), requestTy := "number", answerTy := "number" } ]

def propertyAlphabet := tableAlphabet ⟨0⟩ propertyTable

def cellFamily : String → Val → StateT Nat Id Val
  | "get", _ => do let n ← get; pure (.nat n)
  | "put", .nat n => do set n; pure .unit
  | _, _ => pure .unit

def cellAtom : String → Val → Val
  | "succ", .nat n => .nat (n + 1)
  | _, _ => .unit


/-- Variables of a type in a scope, by position. -/
def varsOfType (scope : List String) (ty : String) : List Var :=
  ((List.range scope.length).zip scope).filterMap fun (index, t) =>
    if t == ty then some ⟨index⟩ else none

def allVars (scope : List String) : List Var :=
  (List.range scope.length).map Var.mk

/-- Swap two same-typed positions of the argument list, when the scope has
two of a type; the parameter lists stay equal, the values move. -/
def swapSameType (scope : List String) (pick : Nat) : List Var :=
  let vars := allVars scope
  let pairs := (List.range scope.length).flatMap fun a =>
    (List.range scope.length).filterMap fun b =>
      if a < b && scope[a]? == scope[b]? then some (a, b) else none
  match pairs[pick % (max pairs.length 1)]? with
  | some (a, b) => vars.map fun v => if v.index = a then ⟨b⟩ else if v.index = b then ⟨a⟩ else v
  | none => vars

/-- One generated flow: a chain of `count` blocks whose scope grows by one
parameter per `perform`. A decision comes as a pair: block `i` splits forward
(left into block `i + 1`, right past it), and block `i + 1` loops (left back to
`i`, or to itself with two same-typed parameters swapped) or continues. Both
arms of every site are therefore distinguishable on the trace: the left path
of a split takes one more decision, and a loop re-decides or swaps values. -/
def genFlow (count : Nat) : Gen (RawFlow String) := do
  let mut blocks : List (RawBlock String) := []
  let mut scope : List String := ["number"]
  let mut site := 0
  let mut skip := false
  for i in List.range count do
    if skip then
      skip := false
    else if i + 1 = count then
      let candidates := varsOfType scope "number"
      let value := candidates[(← below candidates.length)]?.getD ⟨0⟩
      blocks := blocks ++ [{ id := ⟨i⟩, params := scope, term := .ret value }]
    else
      let kind ← below 3
      if kind < 2 || i + 3 > count then
        let available := ((List.range propertyTable.length).zip propertyTable).filter fun (_, spec) =>
          !(varsOfType scope spec.requestTy).isEmpty
        let (op, spec) := available[(← below available.length)]?.getD (0, default)
        let requests := varsOfType scope spec.requestTy
        let request := requests[(← below requests.length)]?.getD ⟨0⟩
        blocks := blocks ++
          [{ id := ⟨i⟩, params := scope, term := .perform ⟨op⟩ request ⟨i + 1⟩ (allVars scope) }]
        scope := scope ++ [spec.answerTy]
      else
        let selfLoop ← coin
        let pick ← below 8
        let args := if selfLoop then swapSameType scope pick else allVars scope
        blocks := blocks ++
          [ { id := ⟨i⟩, params := scope,
              term := .choose ⟨site⟩ ⟨i + 1⟩ ⟨i + 2⟩ (allVars scope) }
          , { id := ⟨i + 1⟩, params := scope,
              term := .choose ⟨site + 1⟩ (if selfLoop then ⟨i + 1⟩ else ⟨i⟩) ⟨i + 2⟩ args } ]
        site := site + 2
        skip := true
  pure { alphabet := ⟨0⟩, roots := [⟨0⟩], entry := ⟨0⟩, inputTy := "number", resultTy := "number",
         blocks := blocks }

/-! ## Running and tapes -/

def input : Val := .nat 5
def initial : Nat := 41
def tapeCap : Nat := 12

structure Outcome where
  result : RunResult
  log : Effect4.Trace.Log
  rest : Tape

def runCase {table : List OpSpec} (flow : CheckedFlow (tableAlphabet ⟨0⟩ table)) (tape : Tape) :
    Outcome :=
  let raw := flow.erase
  let r : ((RunResult × Tape) × Effect4.Trace.Log) × Nat :=
    ((Flow.runTape (Flow.fuelFor raw tape) flow (tableService ⟨0⟩ table cellFamily cellAtom)
      (tableNameOf ⟨0⟩ table) tape input).run []).run initial
  { result := r.1.1.1, log := r.1.2, rest := r.1.1.2 }

/-- Build a tape by policy: answer the unanswered `site` at step `k` with
`policy site k` until the run finishes or the cap is reached. -/
def buildTape {table : List OpSpec} (flow : CheckedFlow (tableAlphabet ⟨0⟩ table))
    (policy : Nat → Nat → Bool) : Tape := Id.run do
  let mut tape : Tape := []
  for k in List.range (tapeCap + 1) do
    match (runCase flow tape).result with
    | .frontier (.unansweredDecision site) =>
        if tape.length < tapeCap then tape := tape ++ [⟨site, policy site.value k⟩]
    | _ => pure ()
  pure tape

def randomPolicy (seed : Nat) (_site k : Nat) : Bool :=
  ((seed + k) * 2654435761 % 2 ^ 32) / 2 ^ 31 = 1

/-- The four policies plus, per site, the tapes that make it take both
branches. Sites come in pairs: an even site splits forward (its left arm
enters the loop block), the odd site after it loops. `only s` goes left at
`s` (and at the split guarding a loop site); `visit s` enters a loop site
through its split and goes right there. With `right` every split takes its
right arm, so every site takes both branches across the corpus. -/
def tapes {table : List OpSpec} (seed : Nat) (flow : CheckedFlow (tableAlphabet ⟨0⟩ table)) :
    List (String × Tape) :=
  let sites := (flow.erase.blocks.filterMap fun block => block.term.decision?).map (·.value)
  let guard (s : Nat) : Nat → Bool := fun site => s % 2 = 1 && site + 1 = s
  [ ("left", buildTape flow fun _ _ => true)
  , ("right", buildTape flow fun _ _ => false)
  , ("alternate", buildTape flow fun _ k => k % 2 = 0)
  , ("random", buildTape flow (randomPolicy seed)) ] ++
  sites.map (fun s => ("only" ++ toString s, buildTape flow fun site _ => site = s || guard s site)) ++
  (sites.filter (· % 2 = 1)).map (fun s => ("visit" ++ toString s, buildTape flow fun site _ => guard s site))

/-! ## The corpus -/

structure Case where
  name : String
  program : FlowProgram
  tapeName : String
  tape : Tape
  outcome : Outcome

def admitProgram (name : String) (raw : RawFlow String) : Option FlowProgram :=
  match admit propertyAlphabet raw with
  | .ok flow => some { name := name, param := ("n", "number"), result := "number",
                       table := propertyTable, flow := flow }
  | .error _ => none

/-- Every generated flow with its four tapes; `refused` counts generator bugs. -/
def corpus (seed count : Nat) : List Case × Nat := Id.run do
  let mut cases : List Case := []
  let mut refused := 0
  let mut rng : Rng := ⟨seed⟩
  for k in List.range count do
    let (blockCount, rng') := (below 7).run rng
    let (raw, rng'') := (genFlow (blockCount + 2)).run rng'
    rng := rng''
    match admitProgram ("f" ++ toString k) raw with
    | none => refused := refused + 1
    | some program =>
        for (tapeName, tape) in tapes (seed + k) program.flow do
          cases := cases ++ [{ name := program.name, program := program, tapeName := tapeName,
                               tape := tape, outcome := runCase program.flow tape }]
  pure (cases, refused)

/-- Per-site branch coverage over a corpus: every site must take both branches. -/
def uncoveredSites (cases : List Case) : List (String × Nat) := Id.run do
  let mut seen : List (String × Nat × Bool) := []
  for c in cases do
    for event in c.outcome.log do
      match event with
      | .decide site branch =>
          if !seen.contains (c.name, site, branch) then seen := seen ++ [(c.name, site, branch)]
      | _ => pure ()
  let mut sites : List (String × Nat) := []
  for c in cases do
    for block in c.program.flow.erase.blocks do
      match block.term.decision? with
      | some site =>
          if !sites.contains (c.name, site.value) then sites := sites ++ [(c.name, site.value)]
      | none => pure ()
  pure (sites.filter fun (name, site) =>
    !(seen.contains (name, site, true) && seen.contains (name, site, false)))

def goldenOf (c : Case) : String :=
  Effect4.Target.TypeScript.Trace.golden (c.name ++ "." ++ c.tapeName) c.tape.wire
    ((Flow.ruleSet Cell.rows c.program).map Rule.id) c.outcome.log (face := "lean-flow")

def isFrontier (c : Case) : Bool :=
  match c.outcome.result with
  | .frontier _ => true
  | _ => false

def writeCorpus (dir : String) (cases : List Case) : IO Unit := do
  IO.FS.createDirAll dir
  let programs := cases.foldl (init := ([] : List FlowProgram)) fun acc c =>
    if acc.any (·.name == c.name) then acc else acc ++ [c.program]
  match flowModules? [(Cell.rows, programs)] [.named ["succ"] "./atoms.ts"] with
  | some source => IO.FS.writeFile (dir ++ "/property-fixture.ts") source
  | none => throw (IO.userError "dispatch lowering refused a generated flow")
  IO.FS.createDirAll (dir ++ "/goldens")
  for c in cases do
    IO.FS.writeFile (dir ++ "/goldens/" ++ c.name ++ "." ++ c.tapeName ++ ".tsv") (goldenOf c)

/-! ## Shrinking -/

/-- The first branch a run took at each site. -/
def takenBranches (log : Effect4.Trace.Log) : List (Nat × Bool) :=
  log.foldl (init := []) fun acc event =>
    match event with
    | .decide site branch => if acc.any (·.1 = site) then acc else acc ++ [(site, branch)]
    | _ => acc

/-- Delete a `perform` block whose answer no later block reads: drop its
parameter from every later block and redirect its predecessors past it. -/
def deletePerform (raw : RawFlow String) (index : Nat) : Option (RawFlow String) := do
  let block ← raw.blocks[index]?
  let .perform _ _ next _ := block.term | none
  let answer := block.params.length
  let later := raw.blocks.filter fun b => b.id.value > block.id.value
  -- the answer is read if any later operand names it
  guard (!later.any fun b => b.term.operands.any (·.index = answer))
  let dropParam (params : List String) : List String :=
    (params.take answer) ++ (params.drop (answer + 1))
  let dropVar (vars : List Var) : List Var := vars.filter (·.index != answer)
  let retarget (target : BlockId) : BlockId := if target = block.id then next else target
  let rewrite (b : RawBlock String) : RawBlock String :=
    let params := if b.id.value > block.id.value then dropParam b.params else b.params
    let term := match b.term with
      | .ret v => .ret v
      | .jump t args => .jump (retarget t) (dropVar args)
      | .perform op r t args => .perform op r (retarget t) (dropVar args)
      | .choose d l r args => .choose d (retarget l) (retarget r) (dropVar args)
    { b with params := params, term := term }
  let blocks := (raw.blocks.filter (·.id != block.id)).map rewrite
  some { raw with blocks := blocks }

/-- At most a few dozen candidates: shorter tapes, a `choose` replaced by the
branch the run took (with its site removed from the tape), and a
type-neutral `perform` deleted. -/
def shrinkCandidates (raw : RawFlow String) (tape : Tape) (log : Effect4.Trace.Log) :
    List (RawFlow String × Tape) :=
  let shorter : List (RawFlow String × Tape) :=
    (if tape.length > 0 then [(raw, tape.take (tape.length - 1))] else []) ++
    (if tape.length > 1 then [(raw, tape.take (tape.length / 2))] else [])
  let taken := takenBranches log
  let chosen : List (RawFlow String × Tape) := raw.blocks.filterMap fun block =>
    match block.term with
    | .choose site left right args =>
        (taken.find? (·.1 = site.value)).map fun (_, branch) =>
          let blocks := raw.blocks.map fun b =>
            if b.id = block.id then { b with term := .jump (if branch then left else right) args } else b
          ({ raw with blocks := blocks }, tape.filter (·.site != site))
    | _ => none
  let deleted : List (RawFlow String × Tape) :=
    (List.range raw.blocks.length).filterMap fun index =>
      (deletePerform raw index).map fun raw' => (raw', tape)
  (shorter ++ chosen ++ deleted).take 64

/-- Follow a path of candidate indices from the root case. -/
def followPath (raw : RawFlow String) (tape : Tape) : List Nat → Option (RawFlow String × Tape)
  | [] => some (raw, tape)
  | index :: rest => do
      let program ← admitProgram "case" raw
      let candidates := shrinkCandidates raw tape (runCase program.flow tape).log
      let (raw', tape') ← candidates[index]?
      followPath raw' tape' rest

def parsePath (path : String) : List Nat :=
  (path.splitOn ",").filterMap fun s => if s.isEmpty then none else s.toNat?

/-- The root case of a corpus entry: regenerate the flow of `program`. -/
def rootCase (seed count : Nat) (program tapeName : String) : Option (RawFlow String × Tape) := do
  let (cases, _) := corpus seed count
  let c ← cases.find? fun c => c.name == program && c.tapeName == tapeName
  some (c.program.flow.erase, c.tape)

def main (args : List String) : IO Unit := do
  match args with
  | ["corpus", seedText, countText, dir] =>
      let seed := seedText.toNat!; let count := countText.toNat!
      let (cases, refused) := corpus seed count
      if refused > 0 then throw (IO.userError s!"FAIL generator bug: admission refused {refused} generated flows")
      let uncovered := uncoveredSites cases
      if !uncovered.isEmpty then
        throw (IO.userError s!"FAIL branch coverage: {uncovered.length} sites never took both branches ({repr (uncovered.take 3)})")
      writeCorpus dir cases
      let programs := (cases.map (·.name)).eraseDups.length
          let sites := cases.foldl (init := ([] : List (String × Nat))) fun acc c =>
        c.program.flow.erase.blocks.foldl (init := acc) fun acc block =>
          match block.term.decision? with
          | some site => if acc.contains (c.name, site.value) then acc else acc ++ [(c.name, site.value)]
          | none => acc
      IO.println s!"seed\t{seed}\tgenerated\t{count}\tadmitted\t{programs}\truns\t{cases.length}\tfrontiers\t{(cases.filter isFrontier).length}\tsites\t{sites.length}"
  | ["shrink", seedText, countText, program, tapeName, path, dir] =>
      let seed := seedText.toNat!; let count := countText.toNat!
      let some (raw, tape) := rootCase seed count program tapeName
        | throw (IO.userError s!"no case {program}.{tapeName}")
      let some (raw, tape) := followPath raw tape (parsePath path)
        | throw (IO.userError s!"no case at path {path}")
      let some root := admitProgram program raw | throw (IO.userError "shrink root not admitted")
      let candidates := shrinkCandidates raw tape (runCase root.flow tape).log
      let mut cases : List Case := []
      let mut index := 0
      for (raw', tape') in candidates do
        match admitProgram ("s" ++ toString index) raw' with
        | some program' =>
            cases := cases ++ [{ name := program'.name, program := program', tapeName := "t",
                                 tape := tape', outcome := runCase program'.flow tape' }]
        | none => pure ()
        index := index + 1
      writeCorpus dir cases
      IO.println s!"candidates\t{candidates.length}\tadmitted\t{cases.length}"
  | ["case", seedText, countText, program, tapeName, path] =>
      let seed := seedText.toNat!; let count := countText.toNat!
      let some (raw, tape) := rootCase seed count program tapeName
        | throw (IO.userError s!"no case {program}.{tapeName}")
      let some (raw, tape) := followPath raw tape (parsePath path)
        | throw (IO.userError s!"no case at path {path}")
      IO.println s!"flow\t{repr raw}"
      IO.println s!"tape\t{repr tape.wire}"
  | _ => throw (IO.userError "usage: Property.lean corpus <seed> <count> <dir> | shrink <seed> <count> <program> <tape> <path> <dir> | case <seed> <count> <program> <tape> <path>")
