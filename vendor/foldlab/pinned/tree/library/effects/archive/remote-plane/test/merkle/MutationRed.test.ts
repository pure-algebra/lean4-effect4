import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { assertFamilyRed } from "../conformance/harness.ts"
import {
  mrk001Binding,
  mrk002Binding,
  mrk003Binding,
  mrk005Binding,
  mrk006Binding,
  mrk007Binding,
  mrk011Binding,
  mrk012Binding,
  runChunkRow,
  runConsistencyRow,
  runDecoderRow,
  runInclusionRow,
  runOpeningMutantRow,
  runStreamMutantRow,
} from "./MerkleFixtures.ts"
import { mutantChunk as lossyChunk } from "./mutants/MRK001_LossyChunk.ts"
import { mutantStep as emitUnverified } from "./mutants/MRK002_EmitUnverified.ts"
import { mutantStep as validateEarly } from "./mutants/MRK003_ValidateEarly.ts"
import { mutantStep as skipEmitsGhost } from "./mutants/MRK005_SkipEmitsGhost.ts"
import { mutantVerify as acceptAnyRoot } from "./mutants/MRK006_AcceptAnyRoot.ts"
import { mutantVerify as acceptEqualRoots } from "./mutants/MRK007_AcceptEqualRoots.ts"
import { mutantDecode as padShortOpening } from "./mutants/MRK011_PadShortOpening.ts"
import { mutantDecode as lenientTags } from "./mutants/MRK012_LenientTags.ts"

it.effect("MRK-001 is red with named kill witnesses", () =>
  assertFamilyRed(mrk001Binding, (row) => runChunkRow(lossyChunk, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("ragged-tail-002"))),
  ))

it.effect("MRK-002 is red with named kill witnesses", () =>
  assertFamilyRed(mrk002Binding, (row) => runDecoderRow(emitUnverified, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("tampered-chunk-rejected-001"))),
  ))

it.effect("MRK-003 is red with named kill witnesses", () =>
  assertFamilyRed(mrk003Binding, (row) => runDecoderRow(validateEarly, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("truncated-run-exposes-no-length-000"))),
  ))

it.effect("MRK-005 is red with named kill witnesses", () =>
  assertFamilyRed(mrk005Binding, (row) => runDecoderRow(skipEmitsGhost, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("slice-middle-chunk-000"))),
  ))

it.effect("MRK-006 is red with named kill witnesses", () =>
  assertFamilyRed(mrk006Binding, (row) => runInclusionRow(acceptAnyRoot, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("short-path-rejected-002"))),
  ))

it.effect("MRK-007 is red with named kill witnesses", () =>
  assertFamilyRed(mrk007Binding, (row) => runConsistencyRow(acceptEqualRoots, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("same-roots-not-shortcut-005"))),
  ))

it.effect("MRK-011 is red with named kill witnesses", () =>
  assertFamilyRed(mrk011Binding, (row) => runOpeningMutantRow(padShortOpening, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("empty-rejected-003"))),
  ))

it.effect("MRK-012 is red with named kill witnesses", () =>
  assertFamilyRed(mrk012Binding, (row) => runStreamMutantRow(lenientTags, row)).pipe(
    Effect.tap((witnesses) => Effect.sync(() =>
      expect(witnesses).toContain("unknown-tag-rejected-002"))),
  ))
