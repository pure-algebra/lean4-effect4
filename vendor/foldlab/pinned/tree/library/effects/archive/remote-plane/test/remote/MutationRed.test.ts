import { expect, it, layer } from "@effect/vitest"
import { Effect } from "effect"
import {
  assertFamilyRed,
  remoteStepLayer,
  RemoteStepSUT,
} from "../conformance/harness.ts"
import {
  remoteBinding,
  remoteR3Binding,
  runRemoteRow,
  runRemoteR3Row,
} from "./MachineFixtures.ts"
import { controlBinding } from "./ControlFixtures.ts"
import { mutantStep as cacheBeforeAdmission } from "./mutants/RMT001_CacheBeforeAdmission.ts"
import { mutantStep as oversizeAccepted } from "./mutants/RMT002_OversizeAccepted.ts"
import { mutantStep as retryUnchangedBytes } from "./mutants/RMT003_RetryUnchangedBytes.ts"
import { mutantStep as duplicateUploadTransfers } from "./mutants/RMT004_DuplicateUploadTransfers.ts"
import { mutantStep as substitutedDelivery } from "./mutants/RMT015_SubstitutedDelivery.ts"
import { mutantStep as presenceAdmits } from "./mutants/RMT005_PresenceAdmits.ts"
import { mutantStep as partialBatch } from "./mutants/RMT006_PartialBatch.ts"
import { mutantStep as publishUnconfirmed } from "./mutants/RMT007_PublishUnconfirmed.ts"
import { mutantStep as interruptAdmits } from "./mutants/RMT008_InterruptAdmits.ts"
import { mutantDecodeCapabilityResult as acceptTruncated } from "./mutants/RMT014_AcceptTruncated.ts"

layer(remoteStepLayer(cacheBeforeAdmission))("direction 2 RMT001 cache-before-admission mutant", (it) => {
  it.effect("RMT-001 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteBinding("RMT-001"), (row) => runRemoteRow(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("load-wrong-bytes-rejected-001"))),
    )))
})

layer(remoteStepLayer(oversizeAccepted))("direction 2 RMT002 oversize-accepted mutant", (it) => {
  it.effect("RMT-002 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteBinding("RMT-002"), (row) => runRemoteRow(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("upload-over-budget-000"))),
    )))
})

layer(remoteStepLayer(retryUnchangedBytes))("direction 2 RMT003 unchanged-retry mutant", (it) => {
  it.effect("RMT-003 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteBinding("RMT-003"), (row) => runRemoteRow(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("upload-rejected-then-repeat-000"))),
    )))
})

layer(remoteStepLayer(duplicateUploadTransfers))("direction 2 RMT004 duplicate-transfer mutant", (it) => {
  it.effect("RMT-004 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteBinding("RMT-004"), (row) => runRemoteRow(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("upload-after-load-needs-no-transfer-000"))),
    )))
})

layer(remoteStepLayer(substitutedDelivery))("direction 2 RMT015 substituted-delivery mutant", (it) => {
  it.effect("RMT-015 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteBinding("RMT-015"), (row) => runRemoteRow(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("load-substituted-bytes-refused-001"))),
  )))
})

layer(remoteStepLayer(presenceAdmits))("direction 2 RMT005 presence-admits mutant", (it) => {
  it.effect("RMT-005 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteR3Binding("RMT-005"), (row) => runRemoteR3Row(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("batch-found-bytes-dropped-001"))),
    )))
})

layer(remoteStepLayer(partialBatch))("direction 2 RMT006 partial-batch mutant", (it) => {
  it.effect("RMT-006 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteR3Binding("RMT-006"), (row) => runRemoteR3Row(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("batch-reordered-rejected-002"))),
    )))
})

layer(remoteStepLayer(publishUnconfirmed))("direction 2 RMT007 publish-unconfirmed mutant", (it) => {
  it.effect("RMT-007 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteR3Binding("RMT-007"), (row) => runRemoteR3Row(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("publish-unconfirmed-root-refused-000"))),
    )))
})

layer(remoteStepLayer(interruptAdmits))("direction 2 RMT008 interrupt-admits mutant", (it) => {
  it.effect("RMT-008 is red with named kill witnesses", () => RemoteStepSUT.use((sut) =>
    assertFamilyRed(remoteR3Binding("RMT-008"), (row) => runRemoteR3Row(sut, row)).pipe(
      Effect.tap((witnesses) => Effect.sync(() =>
        expect(witnesses).toContain("interrupt-upload-in-flight-001"))),
    )))
})

it.effect("RMT-014 is red with named kill witnesses", () => assertFamilyRed(
  controlBinding,
  (row) => Effect.succeed(acceptTruncated(row.input.bytes)),
).pipe(
  Effect.tap((witnesses) => Effect.sync(() =>
    expect(witnesses).toContain("truncated-rejected-001"))),
))
