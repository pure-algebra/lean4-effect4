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
    unless translated.problems.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
      throwError "clock literal control {root} refused: {translated.problems}; {translated.missing}; {translated.frontier}"
    let rendered := String.intercalate "\n" (translated.decls.toList.map fun d =>
      Ml.renderExpr 0 d.bind.body)
    unless (rendered.splitOn s!"E4_clock.literal \"{expected}\"").length > 1 do
      throwError "clock literal control {root} lost its exact value: {rendered}"

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.narrowed]
  unless translated.problems.any (fun text =>
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
    unless translated.problems.any (fun text =>
        (text.splitOn "reaches clock ingress after Nat saturation").length > 1) do
      throwError "clock helper control {root} accepted a saturated argument"

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.throughUnknown]
  unless translated.problems.any (fun text =>
      (text.splitOn "from unknown higher-order Nat production").length > 1) do
    throwError "clock ingress accepted unknown higher-order Nat production"

run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.unrelatedNat]
  unless translated.problems.isEmpty do
    throwError "clock analysis changed unrelated Nat lowering: {translated.problems}"

run_cmd liftTermElabM do
  for root in [`Test.ClockLiteralFixtures.closedCallback,
      `Test.ClockLiteralFixtures.closedRecordCallback] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.problems.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
      throwError "closed clock callback control {root} refused: {translated.problems}"

run_cmd liftTermElabM do
  for root in [`Test.ClockLiteralFixtures.unknownRecordCallback,
      `Test.ClockLiteralFixtures.unknownContainer] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.problems.any (fun text =>
        (text.splitOn "from unknown higher-order Nat production").length > 1) do
      throwError "clock ingress accepted unknown function-bearing carrier {root}"

-- Carrier inference returns only its settled, clock-checked closure.
run_cmd liftTermElabM do
  for (root, reason) in [
      (`Test.ClockLiteralFixtures.throughKnownNatCallback, "after Nat saturation"),
      (`Test.ClockLiteralFixtures.throughUnknown, "from unknown higher-order Nat production")] do
    let (translated, _, _) ← Lcnf.translateClosureInferring #[root]
    unless translated.problems.any (fun text => (text.splitOn reason).length > 1) do
      throwError "settled carrier inference accepted an unchecked clock boundary {root}"

-- An independent callback export does not supply arguments to a concrete clock entry.
run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure
    #[`Test.ClockLiteralFixtures.closedCallback, `Test.ClockLiteralFixtures.applyNat]
  unless translated.problems.isEmpty && translated.missing.isEmpty && translated.frontier.isEmpty do
    throwError "independent callback export contaminated a closed clock root: {translated.problems}"

-- A callback export that reaches a clock remains part of the checked root context.
run_cmd liftTermElabM do
  let translated ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.closedCallback,
    `Test.ClockLiteralFixtures.applyNat, `Test.ClockLiteralFixtures.throughUnknown]
  unless translated.problems.any (fun text =>
      (text.splitOn "from unknown higher-order Nat production").length > 1) do
    throwError "multi-root clock analysis dropped an unknown clock-reaching export"

-- A builtin passed as a callback is a known callable: a global's arity is its mono arity, and
-- `List.appendTR._redArg` has no kernel constant. Over a narrowed argument its result still
-- carries the narrowing.
run_cmd liftTermElabM do
  let known ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.throughBuiltinCallback]
  unless known.problems.isEmpty && known.missing.isEmpty && known.frontier.isEmpty do
    throwError "a builtin callback is read as unknown production: {known.problems}"
  let narrowed ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.throughBuiltinCallbackNarrowed]
  unless narrowed.problems.any (fun text =>
      (text.splitOn "reaches clock ingress after Nat saturation").length > 1) do
    throwError "a builtin callback dropped the narrowing of its argument: {narrowed.problems}"

-- A host's reactor at a root is host ingress (decisions row 394 (1)). A callback of another
-- type, a reactor inside other data and a function whose two states differ stay unknown.
run_cmd liftTermElabM do
  let reactor ← Lcnf.translateClosure #[`Test.ClockLiteralFixtures.reactorClock]
  unless reactor.problems.isEmpty && reactor.missing.isEmpty && reactor.frontier.isEmpty do
    throwError "a host's reactor at a root is refused: {reactor.problems}"
  for root in [`Test.ClockLiteralFixtures.otherCallbackClock,
      `Test.ClockLiteralFixtures.boxedReactorClock,
      `Test.ClockLiteralFixtures.mixedStateClock] do
    let translated ← Lcnf.translateClosure #[root]
    unless translated.problems.any (fun text =>
        (text.splitOn "from unknown higher-order Nat production").length > 1) do
      throwError "clock ingress accepted {root} as a host's reactor: {translated.problems}"
