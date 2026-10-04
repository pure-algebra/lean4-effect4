import Tools.Semantics

/-!
Finite acceptance and refusal controls for the semantics report. The fixture is imported at
runtime, so the green checks exercise persistent attribute entries loaded from another module.
Only the fixture root is loaded; this driver does not require the whole Laws graph.
-/
namespace Tools.Semantics.Controls
open Lean Meta

private def fixtureModule : Name := `Test.Audit.SemanticsCensus
private def fixtureName (suffix : Name) : Name := fixtureModule ++ suffix

private def one : Concept :=
  { id := "fixture-one", title := "First fixture concept", defaultModules := [fixtureModule] }

private def two : Concept :=
  { id := "fixture-two", title := "Second fixture concept" }

private def claim (id : String) (pointer : Pointer) : Claim :=
  { id, concept := "fixture-one", role := .compatibility, title := "Fixture claim", pointer }

private def base : Registry :=
  { roots := [fixtureModule], concepts := [one, two]
    claims := [claim "fixture-claim" (.witness (fixtureName `firstWitness))], cuts := [] }

private def ceRecord (id status : String) : String :=
  s!"| `{id}` | {status} | fixture attack and repair history |"

private def registers : Registers :=
  { counterexamples := #[
      { id := "E4-TEST-CE-001", status := "PINNED", row := ceRecord "E4-TEST-CE-001" "PINNED" },
      { id := "E4-TEST-CE-002", status := "RETIRED", row := ceRecord "E4-TEST-CE-002" "RETIRED" },
      { id := "E4-TEST-CE-003", status := "SEEDED", row := ceRecord "E4-TEST-CE-003" "SEEDED" }]
    decisions := #[(1, "fixture owner")] }

private def toolchain := "leanprover/lean4:v4.33.1"

private def withPointer (pointer : Pointer) : Registry :=
  { base with claims := [claim "fixture-claim" pointer] }

private def cut (concept : String := "fixture-one") (row : Nat := 1) : Cut :=
  { concept, decisionRow := row, excluded := "Fixture exclusion", reason := "Fixture reason" }

private def checked {α : Type} (location : String) (result : Except String α) : MetaM α := do
  match result with
  | .ok value => return value
  | .error reason => throwError "semantics controls: {location}: {reason}"

private def field (value : Json) (key : String) : MetaM Json :=
  checked key (value.getObjVal? key)

private def stringField (value : Json) (key : String) : MetaM String :=
  checked key (value.getObjValAs? String key)

private def arrayField (value : Json) (key : String) : MetaM (Array Json) :=
  checked key (value.getObjValAs? (Array Json) key)

private def named (values : Array Json) (key name : String) : MetaM Json := do
  let some value := values.find? fun value => (value.getObjValAs? String key).toOption == some name
    | throwError "semantics controls: missing {key}={name}"
  return value

private def expectString (value : Json) (key expected : String) : MetaM Unit := do
  let actual ← stringField value key
  unless actual == expected do
    throwError "semantics controls: {key}: expected {expected}, received {actual}"

private def accepted (label : String) (registry : Registry) : MetaM Json := do
  match ← buildReport registry registers toolchain with
  | .ok report => return report
  | .error refusals => throwError "semantics controls: positive {label} refused: {refusals}"

/-- Every expected location/reason pair must occur together in one returned refusal. -/
private def refused {α : Type} (label : String) (result : Except (Array String) α)
    (expected : Array (Array String)) : MetaM Unit := do
  match result with
  | .ok _ => throwError "semantics controls: negative {label} accepted"
  | .error refusals =>
    if refusals.isEmpty then throwError "semantics controls: {label}: empty refusal list"
    for fragments in expected do
      unless refusals.any (fun reason => fragments.all (fun fragment => reason.contains fragment)) do
        throwError "semantics controls: {label}: missing located refusal {fragments}; received {refusals}"

private structure ReportCase where
  label : String
  registry : Registry
  expected : Array (Array String)

private def negativeCases : Array ReportCase := #[
  { label := "duplicate concept id", registry := { base with concepts := [one, one, two] }
    expected := #[#["fixture-one", "duplicate"]] },
  { label := "duplicate claim id", registry := { base with claims := base.claims ++ base.claims }
    expected := #[#["fixture-claim", "duplicate"]] },
  { label := "duplicate default in one concept"
    registry := { base with concepts := [{ one with defaultModules := [fixtureModule, fixtureModule] }, two] }
    expected := #[#["Test.Audit.SemanticsCensus", "duplicate"]] },
  { label := "default shared by two concepts"
    registry := { base with concepts := [one, { two with defaultModules := [fixtureModule] }] }
    expected := #[#["Test.Audit.SemanticsCensus", "duplicate"]] },
  { label := "duplicate planned goal"
    registry := { base with claims := [claim "first-goal" (.witness (fixtureName `wantedGoal)),
                                      claim "second-goal" (.witness (fixtureName `wantedGoal))] }
    expected := #[#["wantedGoal", "duplicate"]] },
  { label := "stale theorem"
    registry := withPointer (.witness (fixtureName `missingWitness))
    expected := #[#["fixture-claim", "missingWitness", "Unknown constant"]] },
  { label := "missing default module"
    registry := { base with concepts := [{ one with defaultModules := [`Missing.Semantics.Module] }, two] }
    expected := #[#["Missing.Semantics.Module", "not loaded"]] },
  { label := "missing root", registry := { base with roots := [fixtureModule, `Missing.Semantics.Root] }
    expected := #[#["Missing.Semantics.Root", "not loaded"]] },
  { label := "unknown claim concept"
    registry := { base with claims := [{ (claim "fixture-claim" (.witness (fixtureName `firstWitness))) with
                                        concept := "unknown-concept" }] }
    expected := #[#["fixture-claim", "unknown-concept", "unknown"]] },
  { label := "unknown cut concept", registry := { base with cuts := [cut "unknown-concept"] }
    expected := #[#["unknown-concept", "unknown"]] },
  { label := "unknown imported tag", registry := { base with concepts := [one] }
    expected := #[#["secondWitness", "fixture-two", "unknown"]] },
  { label := "unregistered counterexample"
    registry := withPointer (.refutedBy "E4-TEST-CE-999" (fixtureName `firstWitness))
    expected := #[#["fixture-claim", "E4-TEST-CE-999", "unknown"]] },
  { label := "retired counterexample"
    registry := withPointer (.refutedBy "E4-TEST-CE-002" (fixtureName `firstWitness))
    expected := #[#["fixture-claim", "E4-TEST-CE-002", "retired"]] },
  { label := "unknown contested row"
    registry := { base with claims := [{ (claim "fixture-claim" (.witness (fixtureName `firstWitness))) with
                                        contestedBy := ["E4-TEST-CE-999"] }] }
    expected := #[#["fixture-claim", "E4-TEST-CE-999", "unknown"]] },
  { label := "duplicate contested row"
    registry := { base with claims := [{ (claim "fixture-claim" (.witness (fixtureName `firstWitness))) with
                                        contestedBy := ["E4-TEST-CE-003", "E4-TEST-CE-003"] }] }
    expected := #[#["fixture-claim", "E4-TEST-CE-003", "duplicate"]] },
  { label := "missing decision", registry := { base with cuts := [cut "fixture-one" 999] }
    expected := #[#["999", "unknown decision row"]] },
  { label := "requirement without evidence or open part"
    registry := { base with requirements := [{ id := "R0", title := "Fixture requirement", top := [] }] }
    expected := #[#["requirement R0", "no top node, no placed node and no open part"]] },
  { label := "plan scope matching no module", registry := { base with planScope := [`Missing.Scope] }
    expected := #[#["Missing.Scope", "matches no loaded module"]] },
  { label := "duplicate requirement id"
    registry := { base with requirements := [{ id := "R0", title := "A", top := [], openParts := ["x"] },
                                             { id := "R0", title := "B", top := [], openParts := ["y"] }] }
    expected := #[#["requirement R0", "duplicate"]] },
  { label := "plain definition is not a witness", registry := withPointer (.witness (fixtureName `semantics))
    expected := #[#["fixture-claim", "semantics", "not a theorem"]] },
  { label := "plain witness outside axiom ceiling", registry := withPointer (.witness `Classical.em)
    expected := #[#["fixture-claim", "Classical.em", "disallowed axioms"]] },
  { label := "refutation resting on a goal"
    registry := withPointer (.refutedBy "E4-TEST-CE-001" (fixtureName `restingWitness))
    expected := #[#["fixture-claim", "restingWitness", "rests on planned goals"]] },
  { label := "refutation that is a goal"
    registry := withPointer (.refutedBy "E4-TEST-CE-001" (fixtureName `wantedGoal))
    expected := #[#["fixture-claim", "wantedGoal", "is a planned goal"]] },
  { label := "acceptance program without a stage", registry := { base with acceptance := [fixtureModule] }
    expected := #[#["acceptance", "SemanticsCensus", "no `stage` definition"]] },
  { label := "acceptance stage that is not a Reach literal"
    registry := { base with acceptance := [fixtureName `notReach],
                            requirements := [{ id := "R1", title := "A", top := [fixtureName `firstWitness] }] }
    expected := #[#["acceptance", "notReach", "not a `Reach` literal"]] },
  { label := "acceptance waiting on an unknown requirement"
    registry := { base with acceptance := [fixtureName `unknownWait] }
    expected := #[#["acceptance", "unknownWait", "unknown requirement R99"]] },
  { label := "placement at an unknown requirement", registry := base
    expected := #[#["placedGoal", "unknown requirement R2"], #["placedWitness", "unknown requirement R2"]] },
  { label := "requirement top that is not a theorem"
    registry := { base with requirements := [{ id := "R0", title := "A", top := [fixtureName `semantics] }] }
    expected := #[#["plan", "semantics", "not a theorem"]] },
  { label := "requirement top outside the axiom ceiling"
    registry := { base with requirements := [{ id := "R0", title := "A", top := [`Classical.em] }] }
    expected := #[#["plan", "Classical.em", "disallowed axioms"]] },
  { label := "blank absence reason", registry := withPointer (.absent "  ")
    expected := #[#["fixture-claim", "reason"]] },
  { label := "blank assumption source", registry := withPointer (.assumed " " "Fixture reason")
    expected := #[#["fixture-claim", "source"]] },
  { label := "blank assumption reason", registry := withPointer (.assumed "Fixture source" " ")
    expected := #[#["fixture-claim", "reason"]] },
  { label := "accumulate independent failures"
    registry := { base with
      concepts := [{ one with defaultModules := [`Missing.Semantics.Module] }, two]
      claims := [claim "missing-first" (.witness (fixtureName `missingFirst)),
                 claim "missing-second" (.witness (fixtureName `missingSecond))]
      cuts := [cut "fixture-one" 999] }
    expected := #[#["Missing.Semantics.Module", "not loaded"],
                  #["missing-first", "missingFirst", "Unknown constant"],
                  #["missing-second", "missingSecond", "Unknown constant"], #["999", "unknown decision row"]] }
]

private def checkPositive : MetaM Unit := do
  let env ← getEnv
  let placement (suffix : Name) := Effect4.Laws.Auto.semanticsAttribute.getParam? env (fixtureName suffix)
  unless placement `firstWitness == some { concept := "fixture-one" } do
    throwError "semantics controls: first imported attribute was not loaded"
  unless placement `secondWitness == some { concept := "fixture-two" } do
    throwError "semantics controls: second imported attribute was not loaded"
  -- a sketch's parts carry the sketch's placement (decisions row 207)
  for suffix in [`placedGoal, `placedSketch, `placedSketch.part1] do
    unless placement suffix == some { concept := "fixture-two", requirement := some "R2" } do
      throwError "semantics controls: {suffix} is not placed at R2"
  let report ← accepted "all statuses" { base with
    claims := [claim "plain" (.witness (fixtureName `firstWitness)),
               claim "resting" (.witness (fixtureName `restingWitness)),
               { (claim "wanted" (.witness (fixtureName `wantedGoal))) with contestedBy := ["E4-TEST-CE-003"] },
               claim "sketched" (.witness (fixtureName `sketchedGoal)),
               claim "part" (.witness (fixtureName `sketchedGoal.part1)),
               claim "refuted" (.refutedBy "E4-TEST-CE-001" (fixtureName `firstWitness)),
               claim "absent" (.absent "No fixture witness is claimed"),
               claim "assumed" (.assumed "External fixture" "Not locally proved")]
    cuts := [cut "fixture-one" 1]
    requirements := [{ id := "R0", title := "Fixture requirement", top := [fixtureName `restingWitness] },
                     { id := "R1", title := "Proved fixture requirement", top := [fixtureName `firstWitness] },
                     { id := "R2", title := "Placed fixture requirement", top := [] }]
    planScope := [fixtureModule] }
  let claims ← arrayField report "claims"
  for (id, status) in #[("plain", "proved"), ("resting", "modulo"), ("wanted", "wanted"),
                       ("sketched", "modulo"), ("part", "wanted"),
                       ("refuted", "refuted"), ("absent", "absent"), ("assumed", "assumed")] do
    expectString (← field (← named claims "id" id) "status") "_tag" status
  expectString (← field (← named claims "id" "plain") "status") "by" "theorem"
  expectString (← field (← named claims "id" "wanted") "status") "by" "goal"
  -- a theorem that uses a goal is proved modulo exactly the goals its proof reaches
  let restsOn (id : String) : MetaM (Array Json) := do
    arrayField (← field (← named claims "id" id) "status") "restsOn"
  unless (← restsOn "resting") == #[toJson s!"{fixtureModule}.wantedGoal"] do
    throwError "semantics controls: the resting witness does not rest on exactly wantedGoal"
  unless (← restsOn "sketched") == #[toJson s!"{fixtureModule}.sketchedGoal.part1",
      toJson s!"{fixtureModule}.sketchedGoal.part2"] do
    throwError "semantics controls: the sketch does not rest on exactly its two parts"
  -- the plan: R0 rests on the goal, R1 is proved; the parts no requirement reaches are listed
  let plan ← field report "plan"
  let reqs ← arrayField plan "requirements"
  expectString (← named reqs "id" "R0") "status" "open"
  expectString (← named reqs "id" "R1") "status" "proved"
  unless (← arrayField (← named reqs "id" "R0") "next") == #[toJson s!"{fixtureModule}.wantedGoal"] do
    throwError "semantics controls: R0's next goal is not wantedGoal"
  unless (← arrayField plan "unplacedGoals") == #[toJson s!"{fixtureModule}.sketchedGoal.part1",
      toJson s!"{fixtureModule}.sketchedGoal.part2"] do
    throwError "semantics controls: the unplaced goals are not the sketch's parts"
  -- R2 has no top node: its nodes are the declarations placed at it, and its next goals are the
  -- placed goal and the placed sketch's part
  let r2 ← named reqs "id" "R2"
  expectString r2 "status" "open"
  let placedNames ← (← arrayField r2 "placed").mapM (stringField · "name")
  unless placedNames == #["placedGoal", "placedSketch", "placedSketch.part1", "placedWitness"].map
      (s!"{fixtureModule}." ++ ·) do
    throwError "semantics controls: R2's placed nodes are {placedNames}"
  unless (← arrayField r2 "next") == #[toJson s!"{fixtureModule}.placedGoal",
      toJson s!"{fixtureModule}.placedSketch.part1"] do
    throwError "semantics controls: R2's next goals are not the placed goal and the placed part"
  expectString (← named (← arrayField r2 "placed") "name" s!"{fixtureModule}.placedWitness") "status" "proved"
  let wanted ← named claims "id" "wanted"
  let contested ← arrayField wanted "contestedBy"
  expectString (← named contested "id" "E4-TEST-CE-003") "registerStatus" "SEEDED"
  expectString (← named contested "id" "E4-TEST-CE-003") "record"
    (ceRecord "E4-TEST-CE-003" "SEEDED")
  let refuted ← field (← field (← named claims "id" "refuted") "status") "counterexample"
  expectString refuted "record" (ceRecord "E4-TEST-CE-001" "PINNED")
  let placements ← arrayField (← field report "placement") "declarations"
  for (suffix, concept, kind) in #[("firstWitness", "fixture-one", "tagged"),
                                  ("secondWitness", "fixture-two", "tagged"),
                                  ("untaggedWitness", "fixture-one", "inherited"),
                                  ("eq_cata", "fixture-one", "inherited")] do
    let placed ← named placements "name" s!"{fixtureModule}.{suffix}"
    expectString placed "concept" concept
    expectString placed "placement" kind
  let concepts ← arrayField report "concepts"
  let counts ← field (← named concepts "id" "fixture-one") "counts"
  for (key, expected) in #[("claims", 8), ("proved", 1), ("modulo", 2), ("wanted", 2), ("refuted", 1),
                          ("absent", 1), ("assumed", 1)] do
    let actual ← checked key (counts.getObjValAs? Nat key)
    unless actual == expected do throwError "semantics controls: count {key}: {actual} != {expected}"
  let cuts ← arrayField report "cuts"
  unless cuts.size == 1 do throwError "semantics controls: expected one cut"
  expectString cuts[0]! "who" "fixture owner"

private def ceRow (id status : String) : String := ceRecord id status ++ "\n"
private def decisionRow : String := "| 1 | fixture decision | recommendation | source | fixture owner | ruled |\n"

private def checkParsing : MetaM Nat := do
  let statuses := #["SEEDED", "PINNED", "RESERVED", "MOVED", "REPAIRED", "RETIRED"]
  for status in statuses do
    match parseRegisters (ceRow "E4-TEST-CE-001" (status ++ " (fixture detail)")) decisionRow with
    | .error errors => throwError "semantics controls: valid register status {status} refused: {errors}"
    | .ok parsed =>
      unless parsed.counterexamples == #[{ id := "E4-TEST-CE-001", status := status, row := ceRecord "E4-TEST-CE-001" (status ++ " (fixture detail)") }] do
        throwError "semantics controls: register status or original row changed: {status}"
      unless parsed.decisions == #[(1, "fixture owner")] do
        throwError "semantics controls: decision owner was not read verbatim"
  let pipeCases : Array (String × String × String × String) := #[
    ("unquoted absolute value", "| `E4-TEST-CE-001` | PINNED | bound |n| |\n",
      "| 1 | bound |n| | recommendation | source | fixture owner | ruled |\n", "fixture owner"),
    ("semicolon status history", "| `E4-TEST-CE-001` | PINNED; later history | claim |\n",
      decisionRow, "fixture owner"),
    ("quoted pipe", "| `E4-TEST-CE-001` | PINNED | `a|b` |\n",
      "| 1 | `a|b` | recommendation | source | fixture `a|b` owner | ruled |\n",
      "fixture `a|b` owner"),
    ("escaped pipe", "| `E4-TEST-CE-001` | PINNED | a \\| b |\n",
      "| 1 | a \\| b | recommendation | source | fixture \\| owner | ruled |\n",
      "fixture \\| owner"),
    ("backtick runs", "| `E4-TEST-CE-001` | PINNED | ``a`|b`` |\n",
      "| 1 | ``a`|b`` | recommendation | source | fixture ``a`|b`` owner | ruled |\n",
      "fixture ``a`|b`` owner")]
  for (label, counterexamples, decisions, owner) in pipeCases do
    match parseRegisters counterexamples decisions with
    | .error errors => throwError "semantics controls: valid {label} refused: {errors}"
    | .ok parsed =>
      unless parsed.counterexamples == #[{ id := "E4-TEST-CE-001", status := "PINNED", row := (counterexamples.splitOn "\n").head! }] do
        throwError "semantics controls: {label}: counterexample columns shifted or original row changed"
      unless parsed.decisions == #[(1, owner)] do
        throwError "semantics controls: {label}: owner bytes changed or columns shifted"
  let cases : Array (String × String × String × Array (Array String)) := #[
    ("malformed register id", ceRow "E4-TEST-CE-1" "PINNED", decisionRow,
      #[#["counterexamples:1", "E4-TEST-CE-1", "malformed register row"]]),
    ("unknown register status", ceRow "E4-TEST-CE-001" "UNKNOWN", decisionRow,
      #[#["counterexamples:1", "E4-TEST-CE-001", "malformed register row"]]),
    ("duplicate counterexample row", ceRow "E4-TEST-CE-001" "PINNED" ++ ceRow "E4-TEST-CE-001" "REPAIRED", decisionRow,
      #[#["E4-TEST-CE-001", "duplicate"]]),
    ("malformed counterexample row", "| `E4-TEST-CE-001` |\n", decisionRow,
      #[#["counterexamples:1", "E4-TEST-CE-001", "malformed register row"]]),
    ("duplicate decision row", ceRow "E4-TEST-CE-001" "PINNED", decisionRow ++ decisionRow,
      #[#["decisions:2", "duplicate row 1"]]),
    ("malformed decision row", ceRow "E4-TEST-CE-001" "PINNED", "| 1 | truncated |\n",
      #[#["decisions:1", "malformed decision row 1"]]),
    ("accumulate parse failures", ceRow "E4-TEST-CE-001" "UNKNOWN" ++ ceRow "E4-TEST-CE-002" "UNKNOWN",
      "| 1 | truncated |\n", #[#["counterexamples:1", "E4-TEST-CE-001", "malformed register row"],
        #["counterexamples:2", "E4-TEST-CE-002", "malformed register row"], #["decisions:1", "malformed decision row 1"]])]
  for (label, counterexamples, decisions, expected) in cases do
    refused label (parseRegisters counterexamples decisions) expected
  return statuses.size + pipeCases.size + cases.size

private def checkUnloadedWitness : MetaM Unit := do
  -- A kernel-checked theorem in the current environment is not an imported source module.
  -- This separates missing-module refusal from the stale-name control.
  let name := `Tools.Semantics.Controls.currentWitness
  addDecl <| .thmDecl { name, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro }
  refused "witness without a loaded source module"
    (← buildReport (withPointer (.witness name)) registers toolchain)
    #[#["fixture-claim", "currentWitness", "witness module is not loaded"]]

def run : MetaM Unit := do
  checkPositive
  for test in negativeCases do
    refused test.label (← buildReport test.registry registers toolchain) test.expected
  checkUnloadedWitness
  let parsing ← checkParsing
  IO.println s!"PASS semantics controls: imported tags and all statuses; {negativeCases.size + 1} report refusals; {parsing} register controls"

end Tools.Semantics.Controls

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Test.Audit.SemanticsCensus }] {} 0
  let context : Lean.Core.Context := { fileName := "<semantics-controls>", fileMap := default }
  discard <| (Tools.Semantics.Controls.run.run' {}).toIO context { env }
