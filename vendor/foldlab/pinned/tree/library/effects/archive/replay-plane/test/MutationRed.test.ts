import { expect, it } from "@effect/vitest"
import { Effect } from "effect"
import {
  replayFamilyBinding,
  replayRowEvaluator,
  type ReplayFamily,
  type ReplayReducer,
} from "./ReplayFixtures.ts"
import { assertFamilyRed } from "./conformance/harness.ts"
import {
  meaning as cmp002Meaning,
  mutant as cmp002,
} from "./mutants/CMP002_CollapseIdentical.ts"
import {
  meaning as rpl002Meaning,
  mutant as rpl002,
} from "./mutants/RPL002_LiveFallback.ts"
import {
  meaning as rpl003Meaning,
  mutant as rpl003,
} from "./mutants/RPL003_SkipAdvance.ts"
import {
  meaning as rpl004Meaning,
  mutant as rpl004,
} from "./mutants/RPL004_ConsumeOnMismatch.ts"
import {
  meaning as rpl005Meaning,
  mutant as rpl005,
} from "./mutants/RPL005_AcceptSuffix.ts"
import {
  meaning as ses001Meaning,
  mutant as ses001,
} from "./mutants/SES001_AppendPastAbort.ts"
import {
  meaning as ses002Meaning,
  mutant as ses002,
} from "./mutants/SES002_CursorUnpinned.ts"
import {
  meaning as ses003InterleavedMeaning,
  mutant as ses003Interleaved,
} from "./mutants/SES003_AcceptInterleavedInvoke.ts"
import {
  meaning as ses003UnsolicitedMeaning,
  mutant as ses003Unsolicited,
} from "./mutants/SES003_AcceptUnsolicited.ts"

const assertRed = (
  family: ReplayFamily,
  meaning: string,
  mutant: ReplayReducer,
  namedWitness: string,
) =>
  Effect.gen(function* () {
    expect(meaning.length).toBeGreaterThan(0)
    const witnesses = yield* assertFamilyRed(
      replayFamilyBinding(family),
      replayRowEvaluator(mutant),
    )
    expect(witnesses).toContain(namedWitness)
  })

it.effect("RPL-002 mutant suite is RED under live fallback", () =>
  assertRed("RPL-002", rpl002Meaning, rpl002, "replay-mismatch-stays-hermetic-001"))

it.effect("RPL-003 mutant suite is RED under zero consumption", () =>
  assertRed("RPL-003", rpl003Meaning, rpl003, "exact-match-consumes-one-000"))

it.effect("RPL-004 mutant suite is RED under mismatch consumption", () =>
  assertRed("RPL-004", rpl004Meaning, rpl004, "reject-operation-mismatch-000"))

it.effect("RPL-005 mutant suite is RED under suffix acceptance", () =>
  assertRed("RPL-005", rpl005Meaning, rpl005, "suffix-rejected-with-terminal-000"))

it.effect("SES-001 mutant suite is RED under append past abort", () =>
  assertRed("SES-001", ses001Meaning, ses001, "append-failure-truncates-000"))

it.effect("SES-002 mutant suite is RED under cursor unpinning", () =>
  assertRed("SES-002", ses002Meaning, ses002, "wf-preserved-record-000"))

it.effect("SES-003 mutant suite is RED under interleaved-invoke acceptance", () =>
  assertRed("SES-003", ses003InterleavedMeaning, ses003Interleaved,
    "interleaved-invoke-rejected-001"))

it.effect("SES-003 mutant suite is RED under unsolicited-outcome acceptance", () =>
  assertRed("SES-003", ses003UnsolicitedMeaning, ses003Unsolicited,
    "unsolicited-outcome-rejected-002"))

it.effect("CMP-002 mutant suite is RED under identical occurrence collapse", () =>
  assertRed("CMP-002", cmp002Meaning, cmp002, "repeated-occurrence-distinct-000"))
