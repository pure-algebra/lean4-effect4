/**
 * Deterministic seeded workload fixtures: sync scenarios.
 *
 * Given a generated graph and a remote-residency ratio, these builders
 * derive what a correct sync issues: the upload schedule (children before
 * parents, root last, per the ratified upload-ordering obligation) with the
 * expected dedup short-circuits for nodes the remote already holds, the
 * pull schedules (root-first discovery and children-first cold admission),
 * a cancellation injection point into the schedule, and named fault hooks
 * the hostile peer can realize. All derivations are pure functions of
 * (graph, seed, params).
 *
 * Residency note: the delivered remote adapter admits against its local
 * mirror on BOTH put and load, so a present frontier node can be made
 * resident only together with its present closure. The upload plan
 * therefore probes the closure of the frontier, children first, before any
 * upload — and the plan's expected wire counts price those probes in.
 *
 * Evidence class: G4 sampled evidence only. These fixtures model production
 * sync loads for exploratory and regression tests; they are NEVER a
 * substitute for the ratified conformance vectors under
 * `conformance/manifest`.
 */
import { Effect, Ref } from "effect"
import type { CasError, CasNodeInput, ContentId } from "../../../src/cas/Node.ts"
import type { CasStoreShape } from "../../../src/cas/Store.ts"
import type { HostileFault } from "../harness/HostilePeer.ts"
import {
  generateGraph,
  resolveNode,
  type GraphShape,
  type PayloadProfile,
  type WorkloadGraph,
} from "./Graph.ts"
import { deriveSeed, makeRng } from "./Rng.ts"

/** One issued sync operation: `probe` loads a node the remote already
 * holds (one GET, establishing local residency); `upload` transfers a
 * missing node (one PUT). Present nodes outside the frontier closure are
 * never issued — they are the dedup short-circuits, listed as `skipped`. */
export interface UploadStep {
  readonly _tag: "probe" | "upload"
  readonly index: number
}

export interface UploadPlan {
  /** Executable order: every probe before the uploads, both ascending, so
   * children always precede parents and the root is the last upload. */
  readonly schedule: ReadonlyArray<UploadStep>
  /** Remote-resident nodes needing no wire operation at all. Structural
   * consequence worth knowing: while anything is missing, the missing root
   * puts every present node inside some frontier closure, so this list is
   * empty and the dedup short-circuit shows up as probe-instead-of-upload;
   * when nothing is missing (pull profiles) it is the whole present set. */
  readonly skipped: ReadonlyArray<number>
  /** Wire fetches a conforming sync issues: one per probed node. */
  readonly expectedGets: number
  /** Wire transfers a conforming sync issues: one per missing node. */
  readonly expectedPuts: number
}

export interface PullPlan {
  /** Root-first traversal order (depth-first, children in declared order,
   * shared subtrees visited once). Correct once residency is established —
   * an in-memory store, or a warm remote mirror. */
  readonly discovery: ReadonlyArray<number>
  /** Children-first order a cold admission-coupled replica accepts. */
  readonly admission: ReadonlyArray<number>
}

/** A fully derived sync scenario over one generated graph. */
export interface SyncScenario {
  readonly graph: WorkloadGraph
  /** Downward-closed remote-resident subset, ascending indices. */
  readonly remoteHas: ReadonlyArray<number>
  readonly upload: UploadPlan
  readonly pull: PullPlan
  /** How many operations a driver keeps in flight. */
  readonly concurrency: number
  /** Cancellation injection: the schedule position before which the sync
   * fiber is interrupted; exactly that many steps complete. Undefined
   * means the sync runs to completion. */
  readonly interruptAfter: number | undefined
  /** Named fault hooks: schedule position to the hostile-peer fault that
   * realizes it. The current hostile peer realizes one fault per served
   * lifetime, so multi-fault plans take one peer per faulted operation. */
  readonly faultPlan: ReadonlyMap<number, HostileFault>
}

/** Named workload profile: a params record, never code. */
export interface SyncWorkloadProfile {
  readonly name: string
  readonly meaning: string
  readonly seed: number
  readonly shape: GraphShape
  readonly payload: PayloadProfile
  /** Fraction of the graph the remote already holds, approximately;
   * realized as a seeded downward-closed subset. Below 1 the root is
   * always missing — a sync is issued because the root moved. */
  readonly remoteHasRatio: number
  readonly concurrency: number
  /** Fraction of the upload schedule to complete before cancellation. */
  readonly interruptAfterRatio?: number
  readonly faults?: ReadonlyArray<readonly [number, HostileFault]>
}

/** Select the remote-resident subset: a seeded downward-closed subset
 * hitting the ratio approximately (a node can be present only when every
 * child is). Ratio 1 selects everything; below 1 the root stays missing. */
export const selectRemoteResidency = (
  graph: WorkloadGraph,
  seed: number,
  ratio: number,
): ReadonlyArray<number> => {
  if (ratio < 0 || ratio > 1) throw new Error("remoteHasRatio must sit in [0, 1]")
  const rng = makeRng(deriveSeed(seed, "remote-residency"))
  const present: Array<boolean> = []
  graph.nodes.forEach((node, index) => {
    const closed = node.children.every((child) => present[child] === true)
    const flip = rng.fraction() < ratio
    present[index] = closed && flip
  })
  if (ratio < 1) present[graph.root] = false
  return present.flatMap((held, index) => (held ? [index] : []))
}

/** Derive the upload plan a correct sync issues against the remote. */
export const planUpload = (
  graph: WorkloadGraph,
  remoteHas: ReadonlyArray<number>,
): UploadPlan => {
  const present = new Set(remoteHas)
  const missing: Array<number> = []
  for (let index = 0; index < graph.nodes.length; index += 1) {
    if (!present.has(index)) missing.push(index)
  }

  const probes = new Set<number>()
  const addClosure = (index: number): void => {
    if (probes.has(index)) return
    const node = graph.nodes[index]
    if (node === undefined) throw new Error(`no node at index ${index}`)
    for (const child of node.children) addClosure(child)
    probes.add(index)
  }
  for (const index of missing) {
    const node = graph.nodes[index]
    if (node === undefined) throw new Error(`no node at index ${index}`)
    for (const child of node.children) {
      if (present.has(child)) addClosure(child)
    }
  }

  const probeList = [...probes].sort((left, right) => left - right)
  const schedule: Array<UploadStep> = [
    ...probeList.map((index) => ({ _tag: "probe" as const, index })),
    ...missing.map((index) => ({ _tag: "upload" as const, index })),
  ]
  const skipped = remoteHas.filter((index) => !probes.has(index))
  return {
    schedule,
    skipped,
    expectedGets: probeList.length,
    expectedPuts: missing.length,
  }
}

/** Derive both pull orders for the graph. */
export const planPull = (graph: WorkloadGraph): PullPlan => {
  const discovery: Array<number> = []
  const visited = new Set<number>()
  const visit = (index: number): void => {
    if (visited.has(index)) return
    visited.add(index)
    discovery.push(index)
    const node = graph.nodes[index]
    if (node === undefined) throw new Error(`no node at index ${index}`)
    for (const child of node.children) visit(child)
  }
  visit(graph.root)
  const admission = [...visited].sort((left, right) => left - right)
  return { discovery, admission }
}

/** Build the full scenario for a named profile. Pure: same profile, same
 * scenario, byte for byte. */
export const buildScenario = (profile: SyncWorkloadProfile): SyncScenario => {
  const graph = generateGraph({
    seed: profile.seed,
    shape: profile.shape,
    payload: profile.payload,
  })
  const remoteHas = selectRemoteResidency(graph, profile.seed, profile.remoteHasRatio)
  const upload = planUpload(graph, remoteHas)
  const pull = planPull(graph)
  const interruptAfter = profile.interruptAfterRatio === undefined
    ? undefined
    : Math.max(1, Math.floor(upload.schedule.length * profile.interruptAfterRatio))
  return {
    graph,
    remoteHas,
    upload,
    pull,
    concurrency: profile.concurrency,
    interruptAfter,
    faultPlan: new Map(profile.faults ?? []),
  }
}

/** What one schedule run observed, in completion order. Addresses come
 * from the consuming store under test, never from the fixture. */
export interface UploadRunReport {
  readonly completed: ReadonlyArray<UploadStep>
  readonly admitted: ReadonlyMap<number, ContentId>
}

/**
 * Drive an upload plan against a store. At concurrency 1 the steps run in
 * exact schedule order, so `beforeStep` positions are deterministic — the
 * cancellation fixture parks there. Above 1, steps run in dependency waves
 * (a parent's wave strictly follows its scheduled children's), each wave
 * width-limited; wire counts stay deterministic, intra-wave order does not.
 */
export const driveUploadSchedule = (options: {
  readonly store: CasStoreShape
  readonly graph: WorkloadGraph
  /** Index-to-address map from the local source of truth. */
  readonly ids: ReadonlyArray<ContentId>
  readonly plan: UploadPlan
  readonly concurrency: number
  /** Runs before the step at that schedule position starts. */
  readonly beforeStep?: (
    step: UploadStep,
    position: number,
  ) => Effect.Effect<void>
}): Effect.Effect<UploadRunReport, CasError> =>
  Effect.gen(function* () {
    const completedRef = yield* Ref.make<ReadonlyArray<UploadStep>>([])
    const admittedRef = yield* Ref.make<ReadonlyMap<number, ContentId>>(new Map())

    const runStep = (step: UploadStep, position: number): Effect.Effect<void, CasError> =>
      Effect.gen(function* () {
        yield* (options.beforeStep === undefined
          ? Effect.void
          : options.beforeStep(step, position))
        const expected = options.ids[step.index]
        if (expected === undefined) {
          return yield* Effect.die(new Error(`no source address for index ${step.index}`))
        }
        const admitted = step._tag === "probe"
          ? yield* options.store.load(expected).pipe(Effect.as(expected))
          : yield* options.store.put(resolveNode(options.graph, step.index, options.ids))
        yield* Ref.update(completedRef, (steps) => [...steps, step])
        yield* Ref.update(admittedRef, (entries) => {
          const next = new Map(entries)
          next.set(step.index, admitted)
          return next
        })
      })

    if (options.concurrency <= 1) {
      for (let position = 0; position < options.plan.schedule.length; position += 1) {
        const step = options.plan.schedule[position]
        if (step === undefined) continue
        yield* runStep(step, position)
      }
    } else {
      const scheduled = new Map<number, number>()
      options.plan.schedule.forEach((step, position) => scheduled.set(step.index, position))
      const waveOf = new Map<number, number>()
      for (const step of options.plan.schedule) {
        const node = options.graph.nodes[step.index]
        if (node === undefined) throw new Error(`no node at index ${step.index}`)
        let wave = 0
        for (const child of node.children) {
          const childWave = waveOf.get(child)
          if (childWave !== undefined) wave = Math.max(wave, childWave + 1)
        }
        waveOf.set(step.index, wave)
      }
      const waves = new Map<number, Array<UploadStep>>()
      for (const step of options.plan.schedule) {
        const wave = waveOf.get(step.index) ?? 0
        const members = waves.get(wave)
        if (members === undefined) waves.set(wave, [step])
        else members.push(step)
      }
      for (const wave of [...waves.keys()].sort((left, right) => left - right)) {
        yield* Effect.forEach(
          waves.get(wave) ?? [],
          (step) => runStep(step, scheduled.get(step.index) ?? -1),
          { concurrency: options.concurrency, discard: true },
        )
      }
    }

    return {
      completed: yield* Ref.get(completedRef),
      admitted: yield* Ref.get(admittedRef),
    }
  })

/** Load every listed node in order and return what the store delivered. */
export const drivePull = (options: {
  readonly store: CasStoreShape
  readonly order: ReadonlyArray<number>
  readonly ids: ReadonlyArray<ContentId>
}): Effect.Effect<ReadonlyArray<CasNodeInput>, CasError> =>
  Effect.gen(function* () {
    const loaded: Array<CasNodeInput> = []
    for (const index of options.order) {
      const id = options.ids[index]
      if (id === undefined) {
        return yield* Effect.die(new Error(`no source address for index ${index}`))
      }
      loaded.push(yield* options.store.load(id))
    }
    return loaded
  })

/** What a fresh replica of the remote observed, probing children first. */
export interface ClosureAudit {
  /** Nodes the remote serves and the replica admitted cleanly. */
  readonly held: ReadonlyArray<number>
  /** Partial parents: nodes the remote serves whose children it lacks.
   * A conforming sync never produces one, interrupted or not. */
  readonly dangling: ReadonlyArray<number>
}

/** Audit the remote through a FRESH admission-coupled replica: probe every
 * address children-first; a served parent with an unserved child surfaces
 * as a dangling reference and lands in `dangling`. */
export const auditRemoteClosure = (options: {
  readonly store: CasStoreShape
  readonly graph: WorkloadGraph
  readonly ids: ReadonlyArray<ContentId>
}): Effect.Effect<ClosureAudit, CasError> =>
  Effect.gen(function* () {
    const held: Array<number> = []
    const dangling: Array<number> = []
    for (let index = 0; index < options.graph.nodes.length; index += 1) {
      const id = options.ids[index]
      if (id === undefined) {
        return yield* Effect.die(new Error(`no source address for index ${index}`))
      }
      const outcome = yield* options.store.load(id).pipe(Effect.match({
        onFailure: (error) => ({ _tag: "failure" as const, error }),
        onSuccess: () => ({ _tag: "success" as const }),
      }))
      if (outcome._tag === "success") {
        held.push(index)
        continue
      }
      switch (outcome.error._tag) {
        case "CasError/ContentNotFound":
          break
        case "CasError/DanglingReference":
          dangling.push(index)
          break
        default:
          return yield* Effect.fail(outcome.error)
      }
    }
    return { held, dangling }
  })
