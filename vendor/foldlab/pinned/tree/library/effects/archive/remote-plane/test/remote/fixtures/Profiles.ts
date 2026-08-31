/**
 * Deterministic seeded workload fixtures: the named profiles.
 *
 * Each profile is a documented params record — never duplicated code —
 * naming one production sync situation. `buildScenario` in `Sync.ts` turns
 * a profile into its full derived scenario; the same profile always yields
 * the same workload byte for byte.
 *
 * | profile         | shape                     | nodes | remoteHas | width | notes                                  |
 * |-----------------|---------------------------|-------|-----------|-------|----------------------------------------|
 * | freshPush       | tree b=3 d=2              | 13    | 0         | 4     | first publish to an empty remote       |
 * | incrementalPush | tree b=3 d=3              | 40    | ~0.8      | 4     | push only the missing closure          |
 * | coldPull        | diamond 6 leaves, 3 forks | 10    | 1         | 2     | empty replica fills children first     |
 * | warmPull        | diamond 6 leaves, 3 forks | 10    | 1         | 2     | second traversal hits the local mirror |
 * | dedupHeavy      | duplicateHeavy 24 slots   | 25    | 0         | 4     | 75% duplicate slots, dedup pressure    |
 * | interruptedSync | tree b=4 d=2              | 21    | 0         | 1     | cancelled halfway through the schedule |
 * | mixedReadWrite  | tree b=2 d=3              | 15    | ~0.5      | 2     | probes (reads) interleave with uploads |
 *
 * Evidence class: G4 sampled evidence only. These fixtures model production
 * sync loads for exploratory and regression tests; they are NEVER a
 * substitute for the ratified conformance vectors under
 * `conformance/manifest`.
 */
import type { SyncWorkloadProfile } from "./Sync.ts"

/** First publish: the remote holds nothing; every node uploads, children
 * before parents, root last. */
export const freshPush: SyncWorkloadProfile = {
  name: "freshPush",
  meaning: "first publish of a directory tree to an empty remote",
  seed: 0x0f01d001,
  shape: { _tag: "tree", depth: 2, branching: 3 },
  payload: { _tag: "smallMeta" },
  remoteHasRatio: 0,
  concurrency: 4,
}

/** Routine sync: the remote already holds about four fifths; a correct
 * sync uploads only the missing closure and short-circuits the rest. */
export const incrementalPush: SyncWorkloadProfile = {
  name: "incrementalPush",
  meaning: "routine push where the remote already holds most of the graph",
  seed: 0x0f01d002,
  shape: { _tag: "tree", depth: 3, branching: 3 },
  payload: { _tag: "smallMeta" },
  remoteHasRatio: 0.8,
  concurrency: 4,
}

/** Empty replica: everything fetches once, children first, shared
 * subtrees once. */
export const coldPull: SyncWorkloadProfile = {
  name: "coldPull",
  meaning: "empty replica pulls a shared-subtree graph the remote holds in full",
  seed: 0x0f01d003,
  shape: { _tag: "diamond", sharedLeaves: 6, forks: 3 },
  payload: { _tag: "mixed", blobRatio: 0.25, maxPayloadBytes: 256 },
  remoteHasRatio: 1,
  concurrency: 2,
}

/** Warm replica: the local mirror already holds everything; a second
 * traversal issues no wire fetch. */
export const warmPull: SyncWorkloadProfile = {
  name: "warmPull",
  meaning: "repeat pull served entirely from the warm local mirror",
  seed: 0x0f01d004,
  shape: { _tag: "diamond", sharedLeaves: 6, forks: 3 },
  payload: { _tag: "smallMeta" },
  remoteHasRatio: 1,
  concurrency: 2,
}

/** Bulk import where three quarters of the slots are byte-identical: the
 * store admits every slot but keeps one node per distinct byte sequence. */
export const dedupHeavy: SyncWorkloadProfile = {
  name: "dedupHeavy",
  meaning: "bulk import dominated by byte-identical duplicates",
  seed: 0x0f01d005,
  shape: { _tag: "duplicateHeavy", leafSlots: 24, dedupRatio: 0.75 },
  payload: { _tag: "smallMeta" },
  remoteHasRatio: 0,
  concurrency: 4,
}

/** Cancellation halfway through a fresh push, driven serially so the cut
 * point is exact; the transferred prefix must stay closed — no parent
 * without its children. */
export const interruptedSync: SyncWorkloadProfile = {
  name: "interruptedSync",
  meaning: "push cancelled mid-schedule; the remote must hold no partial parent",
  seed: 0x0f01d006,
  shape: { _tag: "tree", depth: 2, branching: 4 },
  payload: { _tag: "smallMeta" },
  remoteHasRatio: 0,
  concurrency: 1,
  interruptAfterRatio: 0.5,
}

/** Half-resident graph with mixed payload sizes: frontier probes (reads)
 * interleave with uploads (writes) in one schedule. */
export const mixedReadWrite: SyncWorkloadProfile = {
  name: "mixedReadWrite",
  meaning: "sync whose schedule mixes residency probes with uploads",
  seed: 0x0f01d007,
  shape: { _tag: "tree", depth: 3, branching: 2 },
  payload: { _tag: "mixed", blobRatio: 0.3, maxPayloadBytes: 512 },
  remoteHasRatio: 0.5,
  concurrency: 2,
}

export const workloadProfiles: ReadonlyArray<SyncWorkloadProfile> = [
  freshPush,
  incrementalPush,
  coldPull,
  warmPull,
  dedupHeavy,
  interruptedSync,
  mixedReadWrite,
]
