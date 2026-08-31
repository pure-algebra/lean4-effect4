import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import { assertFamilyRed } from "../conformance/harness.ts"
import {
  mrk018Binding,
  runManifestMutantRow,
} from "./BlobFixtures.ts"
import { mutantDecode } from "./mutants/MRK018_GuessUnknownRecipe.ts"

it.effect("MRK-018 is red with the named unknown-recipe kill witness", () =>
  assertFamilyRed(
    mrk018Binding,
    (row) => runManifestMutantRow(mutantDecode, row),
  ).pipe(Effect.tap((witnesses) => Effect.sync(() =>
    expect(witnesses).toContain("unknown-recipe-rejected-002")))))
