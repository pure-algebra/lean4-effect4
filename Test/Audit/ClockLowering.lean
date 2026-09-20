import Test.Audit.ClockLiteralFixtures
import OCaml5.Lcnf.Translate
import OCaml5.Ml.Render

/-! Clock literals retain exact decimal values through the actual mono-LCNF route.
These are finite translation controls; the ordinary Nat target profile is unchanged. -/
open Lean Elab Command OCaml5

run_cmd liftTermElabM do
  for (root, expected) in [
      (`Test.ClockLiteralFixtures.direct, "4611686018427387904"),
      (`Test.ClockLiteralFixtures.numeral, "4611686018427387905"),
      (`Test.ClockLiteralFixtures.positive, "4611686018427387905")] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.todos.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
      throwError "clock literal control {root} refused: {translated.todos}; {translated.missing}; {translated.frontier}"
    let rendered := String.intercalate "\n" (translated.decls.toList.map fun d =>
      Ml.renderExpr 0 d.bind.body)
    unless (rendered.splitOn s!"E4_clock.literal \"{expected}\"").length > 1 do
      throwError "clock literal control {root} lost its exact value: {rendered}"

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.narrowed]
  unless translated.todos.any (fun text =>
      (text.splitOn "consumes a narrowed Nat without exact literal provenance").length > 1) do
    throwError "clock ingress accepted a narrowed arithmetic result"

run_cmd liftTermElabM do
  for root in [`Test.ClockLiteralFixtures.throughWrapper,
      `Test.ClockLiteralFixtures.throughNestedWrapper,
      `Test.ClockLiteralFixtures.throughFactory,
      `Test.ClockLiteralFixtures.throughNestedFactory,
      `Test.ClockLiteralFixtures.throughClockCallback,
      `Test.ClockLiteralFixtures.throughGenericClockCallback,
      `Test.ClockLiteralFixtures.throughValue,
      `Test.ClockLiteralFixtures.throughKnownNatCallback] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.todos.any (fun text =>
        (text.splitOn "reaches clock ingress after Nat saturation").length > 1) do
      throwError "clock helper control {root} accepted a saturated argument"

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.throughUnknown]
  unless translated.todos.any (fun text =>
      (text.splitOn "from unknown higher-order Nat production").length > 1) do
    throwError "clock ingress accepted unknown higher-order Nat production"

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.unrelatedNat]
  unless translated.todos.isEmpty do
    throwError "clock analysis changed unrelated Nat lowering: {translated.todos}"

run_cmd liftTermElabM do
  for root in [`Test.ClockLiteralFixtures.closedCallback,
      `Test.ClockLiteralFixtures.closedRecordCallback] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.todos.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
      throwError "closed clock callback control {root} refused: {translated.todos}"

run_cmd liftTermElabM do
  for root in [`Test.ClockLiteralFixtures.unknownRecordCallback,
      `Test.ClockLiteralFixtures.unknownContainer] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.todos.any (fun text =>
        (text.splitOn "from unknown higher-order Nat production").length > 1) do
      throwError "clock ingress accepted unknown function-bearing carrier {root}"

-- Carrier inference returns only its settled, clock-checked closure.
run_cmd liftTermElabM do
  for (root, reason) in [
      (`Test.ClockLiteralFixtures.throughKnownNatCallback, "after Nat saturation"),
      (`Test.ClockLiteralFixtures.throughUnknown, "from unknown higher-order Nat production")] do
    let (translated, _, _) ← Lcnf.translateClosureInferring #[root]
    unless translated.todos.any (fun text => (text.splitOn reason).length > 1) do
      throwError "settled carrier inference accepted an unchecked clock boundary {root}"

-- An independent callback export does not supply arguments to a concrete clock entry.
run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure
    #[`Test.ClockLiteralFixtures.closedCallback, `Test.ClockLiteralFixtures.applyNat]
  unless translated.todos.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
    throwError "independent callback export contaminated a closed clock root: {translated.todos}"

-- A callback export that reaches a clock remains part of the checked root context.
run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.closedCallback,
    `Test.ClockLiteralFixtures.applyNat, `Test.ClockLiteralFixtures.throughUnknown]
  unless translated.todos.any (fun text =>
      (text.splitOn "from unknown higher-order Nat production").length > 1) do
    throwError "multi-root clock analysis dropped an unknown clock-reaching export"
