import { it } from "@effect/vitest"
import { assertFamily } from "./ReplayFixtures.ts"

it.effect("RPL-002 consumes every ratified replay-hermeticity row structurally", () =>
  assertFamily("RPL-002"))

it.effect("RPL-003 consumes every ratified exact-consumption row structurally", () =>
  assertFamily("RPL-003"))

it.effect("RPL-004 consumes every ratified fail-closed row structurally", () =>
  assertFamily("RPL-004"))

it.effect("RPL-005 consumes every ratified completion row structurally", () =>
  assertFamily("RPL-005"))

it.effect("SES-001 consumes every ratified structural-abort row structurally", () =>
  assertFamily("SES-001"))

it.effect("SES-002 consumes every ratified well-formedness row structurally", () =>
  assertFamily("SES-002"))

it.effect("SES-003 consumes every ratified delegation-protocol row structurally", () =>
  assertFamily("SES-003"))

it.effect("CMP-002 consumes every ratified occurrence-distinctness row structurally", () =>
  assertFamily("CMP-002"))
