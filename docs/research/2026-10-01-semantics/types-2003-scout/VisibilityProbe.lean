import Tools.Semantics

open Lean Meta Elab Command ProofGraph Tools.Semantics

namespace VisibilityProbe

theorem firstGoal : Obligation True := ⟨⟩
theorem secondGoal : Obligation True := ⟨⟩
theorem trueWitness : True := True.intro

private def expectRefusal (label fragment : String) (action : MetaM α) : MetaM Unit := do
  let result ← try
    discard <| action
    pure (none : Option String)
  catch error => pure (some (← error.toMessageData.toString))
  match result with
  | none => throwError "{label}: unexpectedly accepted"
  | some message =>
    unless message.contains fragment do throwError "{label}: wrong refusal: {message}"
    logInfo m!"PASS {label}: {message}"

private def reportWith (work locator relation : String) : Registry :=
  { roots := [`Tools.Semantics]
    concepts := [{ id := "probe", title := "Probe concept" }]
    claims := [{
      id := "unproved-probe"
      concept := "probe"
      role := .compatibility
      title := "Unproved probe, never a theorem claim"
      pointer := .absent "Probe only"
      literature := [{ work, locator, relation }] }]
    cuts := [] }

run_elab do
  let some a ← readGoal ``firstGoal | throwError "first goal missing"
  let some b ← readGoal ``secondGoal | throwError "second goal missing"
  let evidence := #[Entry.mk a.id (.proved ``trueWitness), Entry.mk b.id (.proved ``trueWitness)]
  let noEdges ← ProofGraph.check #[a, b] evidence 0
  unless a.dependencies.isEmpty && b.dependencies.isEmpty && noEdges.edges.isEmpty do
    throwError "readGoal unexpectedly inferred dependencies"
  logInfo "PASS extracted goals: 2 proved, 0 registered dependency edges"
  let edge ← ProofGraph.check #[a, { b with dependencies := #[a.id] }] evidence 0
  unless edge.edges == #[(b.id, a.id)] do throwError "explicit edge missing"
  logInfo "PASS explicit dependency: 1 edge retained"
  expectRefusal "cycle" "dependency cycle" <|
    ProofGraph.check #[{ a with dependencies := #[b.id] }, { b with dependencies := #[a.id] }] evidence 0
  expectRefusal "unknown dependency" "unknown dependency" <|
    ProofGraph.check #[a, { b with dependencies := #[`VisibilityProbe.missing] }] evidence 0
  expectRefusal "wrong proposition" "proposition changed" <|
    ProofGraph.check #[{ a with proposition := mkConst ``False }]
      #[Entry.mk a.id (.proved ``trueWitness)] 0
  let fakeWork := "NO-SUCH-SOURCE-VISIBILITY-PROBE"
  let result ← buildReport (reportWith fakeWork "NO-SUCH-LOCATOR" "analogy") {} "leanprover/lean4:v4.33.1"
  let .ok report := result | throwError "nonblank unknown citation unexpectedly refused"
  unless report.compress.contains fakeWork do throwError "JSON lost citation"
  if (renderMarkdown report).contains fakeWork then throwError "Markdown now displays citations"
  logInfo "OBSERVED unknown source/locator accepted; JSON retains citation; Markdown omits it"
  for (label, registry) in [
      ("blank source", reportWith "" "locator" "analogy"),
      ("unknown relation", reportWith "work" "locator" "not-a-relation")] do
    let .error errors ← buildReport registry {} "leanprover/lean4:v4.33.1"
      | throwError "{label}: unexpectedly accepted"
    unless errors.any (·.contains "invalid literature reference") do
      throwError "{label}: wrong refusal {errors}"
    logInfo m!"PASS {label}: {errors}"

#print axioms trueWitness
end VisibilityProbe
