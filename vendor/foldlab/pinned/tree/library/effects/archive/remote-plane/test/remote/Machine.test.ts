import { it, layer } from "@effect/vitest"
import { Effect } from "effect"
import { step } from "../../src/internal/remoteMachine.ts"
import {
  assertFamilyRows,
  remoteStepLayer,
  RemoteStepSUT,
} from "../conformance/harness.ts"
import {
  assertRemoteGuards,
  remoteBinding,
  remoteR3Binding,
  runRemoteRow,
  runRemoteR3Row,
} from "./MachineFixtures.ts"
import { controlBinding, runControlRow } from "./ControlFixtures.ts"

it.effect("RMT-014 consumes every ratified capability-codec row structurally", () =>
  assertFamilyRows(controlBinding, runControlRow))

layer(remoteStepLayer(step))("direction 1 remote machine mirror", (it) => {
  it.effect("RMT-001 consumes every ratified remote-admission row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteBinding("RMT-001"),
      (row) => runRemoteRow(sut, row),
    )))

  it.effect("RMT-002 consumes every ratified remote-budget row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteBinding("RMT-002"),
      (row) => runRemoteRow(sut, row),
    )))

  it.effect("RMT-003 consumes every ratified terminal-integrity row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteBinding("RMT-003"),
      (row) => runRemoteRow(sut, row),
    )))

  it.effect("RMT-004 consumes every ratified deduplicated-upload row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteBinding("RMT-004"),
      (row) => runRemoteRow(sut, row),
    )))

  it.effect("RMT-015 consumes every ratified remote-load agreement row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteBinding("RMT-015"),
      (row) => runRemoteRow(sut, row),
    )))

  it.effect("RMT-005 consumes every ratified presence-planning row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteR3Binding("RMT-005"),
      (row) => runRemoteR3Row(sut, row),
    )))

  it.effect("RMT-006 consumes every ratified batch-accounting row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteR3Binding("RMT-006"),
      (row) => runRemoteR3Row(sut, row),
    )))

  it.effect("RMT-007 consumes every ratified closure-gated publish row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteR3Binding("RMT-007"),
      (row) => runRemoteR3Row(sut, row),
    )))

  it.effect("RMT-008 consumes every ratified interruption row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteR3Binding("RMT-008"),
      (row) => runRemoteR3Row(sut, row),
    )))

  it.effect("RMT-017 consumes every ratified attested-presence row structurally", () =>
    RemoteStepSUT.use((sut) => assertFamilyRows(
      remoteR3Binding("RMT-017"),
      (row) => runRemoteR3Row(sut, row),
    )))

  it.effect("remote admission and budget guards agree with their manifest consumers", () =>
    Effect.forEach(
      [
        "RMT-001",
        "RMT-002",
        "RMT-003",
        "RMT-004",
        "RMT-015",
        "RMT-005",
        "RMT-006",
        "RMT-007",
        "RMT-008",
        "RMT-017",
      ] as const,
      assertRemoteGuards,
      { discard: true },
    ))
})
