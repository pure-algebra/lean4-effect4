/**
 * prelude.ts — the pure atoms and Ref function names of the native route, on rc.112.
 *
 * What it is: one export per name the printed programs can mention outside the `effect`
 * package: the pure atoms of `src/Effect4/Program/Native.lean` (`nativeAtom`) and the
 * `FnName`s of `src/Effect4/Machine/Stores.lean` (`FnName.total`, `FnName.partialUpdate`).
 * Part of the truth claim (`Test/contracts/faces.contract.md` §4): the doc comment on each
 * export below is the table mapping it to its Lean definition — there is no separate notes
 * file. Hand-written transcription (no generator exists for it yet); when either Lean table
 * changes, this file changes with it, and the self-test refuses an atom it does not export.
 *
 * Depends on `effect` (`Option`) only.
 *
 * Behaviours held:
 *  - one error, one representation: every package row whose Lean row type has the DB-15 pair
 *    as its error column projects its failure to that pair **at the adapter**, before the
 *    program sees it (`toPair`, DI-59), so a printed `Effect.catch`/`Effect.catchCause`
 *    handler, the recorded tape row and the Lean machine all observe one value (tested:
 *    `docs/research/2026-09-09-seat-host-face-probes.ts`);
 *  - each atom agrees with `nativeAtom` on the values `typeOf` admits — naturals, booleans,
 *    pairs (tested: `run-truth.ts` `selfTest` evaluates the table below against fixed cases
 *    before any program runs);
 *  - `pred` is Lean's truncated subtraction, `pred(0) = 0` (by construction);
 *  - one identifier, one shape: `incr`, `double`, `takeAndBump` are the `FnName.total`
 *    shape `(a) => a` that `Ref.update`/`getAndUpdate`/`updateAndGet` take;
 *    `zeroWhenPositive`, `noChange` are the `FnName.partialUpdate` shape `(a) => Option<a>`
 *    that `Ref.updateSome`/`getAndUpdateSome`/`updateSomeAndGet` take. The `modify` and
 *    `modifySome` shapes (`FnName.modify`, `FnName.modifySome`: `(a) => [b, a']`) are NOT
 *    these identifiers — a printed `Ref.modify(ref, takeAndBump)` would call the total shape
 *    and misbehave on rc.112. Recorded as finding F3 in `REPORT.md`; not patched here.
 */
import { Effect, Exit, Option, Scope } from "effect"
import { KeyValueStore } from "effect/unstable/persistence"
import * as Reactivity from "effect/unstable/reactivity/Reactivity"
import { SqliteClient } from "@effect/sql-sqlite-bun"

// ---- nativeAtom (Native.lean:59-70) -------------------------------------------------

/** `"succ", [nat n] => nat (n + 1)` */
export const succ = (n: number): number => n + 1
/** `"pred", [nat n] => nat (n - 1)` — Lean `Nat` subtraction truncates at zero. */
export const pred = (n: number): number => (n === 0 ? 0 : n - 1)
/** `"isZero", [nat n] => bool (n = 0)` */
export const isZero = (n: number): boolean => n === 0
/** `"not", [bool b] => bool (!b)` */
export const not = (b: boolean): boolean => !b
/** `"add", [nat a, nat b] => nat (a + b)` */
export const add = (a: number, b: number): number => a + b
/** `"lt", [nat a, nat b] => bool (a < b)` */
export const lt = (a: number, b: number): boolean => a < b
/** `"eq", [nat a, nat b] => bool (a = b)` */
export const eq = (a: number, b: number): boolean => a === b
/** `"pair", [a, b] => Val.tuple [a, b]` — a two-element tuple, the wire's JSON array. */
export const pair = <A, B>(a: A, b: B): readonly [A, B] => [a, b]
/** `"fst", [exitCons a _] => a` */
export const fst = <A, B>(p: readonly [A, B]): A => p[0]
/** `"snd", [exitCons _ (exitCons b _)] => b` */
export const snd = <A, B>(p: readonly [A, B]): B => p[1]

// ---- FnName, total shape (Stores.lean:458-462 `FnName.total`) ------------------------

/** `FnName.incr`: `a ↦ a + 1`. */
export const incr = (a: number): number => a + 1
/** `FnName.double`: `a ↦ 2 * a`. */
export const double = (a: number): number => a * 2
/** `FnName.takeAndBump` under `FnName.total`: `a ↦ a + 1` (its `modify` shape is
 * `a ↦ [a, a + 1]`, not this identifier — see the header). */
export const takeAndBump = (a: number): number => a + 1

// ---- FnName, partial shape (Stores.lean:465-469 `FnName.partialUpdate`) --------------

/** `FnName.zeroWhenPositive`: `Some 0` on a positive cell, `None` otherwise. */
export const zeroWhenPositive = (a: number): Option.Option<number> =>
  a > 0 ? Option.some(0) : Option.none()
/** `FnName.noChange`: `None` always. */
export const noChange = (_a: number): Option.Option<number> => Option.none()

/** The table the runner's self-test walks. `atom` is the name in `nativeAtom` or `FnName`
 * that the case exercises: `run-truth.ts` checks the atom names against the profile's own
 * atom set (`ts/eff/profile.gen.ts`, cut from `nativeAtom` — DI-40), so an atom appended in
 * Lean cannot stay untested here. `strings` was untested until that check existed. */
export const selfTestCases: ReadonlyArray<{
  readonly atom: string; readonly name: string; readonly apply: () => unknown; readonly expected: unknown
}> = [
  { atom: "succ", name: "succ 41", apply: () => succ(41), expected: 42 },
  { atom: "pred", name: "pred 0", apply: () => pred(0), expected: 0 },
  { atom: "pred", name: "pred 5", apply: () => pred(5), expected: 4 },
  { atom: "isZero", name: "isZero 0", apply: () => isZero(0), expected: true },
  { atom: "isZero", name: "isZero 3", apply: () => isZero(3), expected: false },
  { atom: "not", name: "not true", apply: () => not(true), expected: false },
  { atom: "add", name: "add 2 3", apply: () => add(2, 3), expected: 5 },
  { atom: "lt", name: "lt 2 3", apply: () => lt(2, 3), expected: true },
  { atom: "lt", name: "lt 3 3", apply: () => lt(3, 3), expected: false },
  { atom: "eq", name: "eq 3 3", apply: () => eq(3, 3), expected: true },
  { atom: "pair", name: "pair 1 2 is a two-element array", apply: () => JSON.stringify(pair(1, 2)), expected: "[1,2]" },
  { atom: "fst", name: "fst (pair 1 2)", apply: () => fst(pair(1, 2)), expected: 1 },
  { atom: "snd", name: "snd (pair 1 2)", apply: () => snd(pair(1, 2)), expected: 2 },
  { atom: "strings", name: "strings () is empty", apply: () => JSON.stringify(strings()), expected: "[]" },
  { atom: "strings", name: "strings (\"7\", \"\\\"x\\\"\") keeps its JSON texts",
    apply: () => JSON.stringify(strings("7", "\"x\"")), expected: "[\"7\",\"\\\"x\\\"\"]" },
  { atom: "incr", name: "incr 1", apply: () => incr(1), expected: 2 },
  { atom: "double", name: "double 4", apply: () => double(4), expected: 8 },
  { atom: "takeAndBump", name: "takeAndBump 4", apply: () => takeAndBump(4), expected: 5 },
  { atom: "zeroWhenPositive", name: "zeroWhenPositive 3", apply: () => Option.getOrUndefined(zeroWhenPositive(3)), expected: 0 },
  { atom: "zeroWhenPositive", name: "zeroWhenPositive 0 is none", apply: () => Option.isNone(zeroWhenPositive(0)), expected: true },
  { atom: "noChange", name: "noChange 7 is none", apply: () => Option.isNone(noChange(7)), expected: true }
]

/** A unit-declared resource used only by pAcquireHandle. Effect supplies the execution
 * and scoped-finalizer behavior; this is not a canonical package implementation. */
class Resource {
  readonly ["~effect4/ExternalHandle"] = "Host.Resource"
  closed = false
}
/** The explicit target type binding for the canonical name `Host.Resource`. */
export type HostResource = Resource
export const Host = {
  acquire: () => Effect.sync(() => new Resource()),
  close: (resource: Resource) => Effect.sync(() => {
    if (resource.closed) throw new Error("resource released twice")
    resource.closed = true
  }),
  read: (resource: Resource) => Effect.sync(() => resource.closed ? 1 : 0)
}
/** Type-only namespace for printed annotations; the runtime Host object is unchanged. */
export namespace Host { export type Resource = HostResource }

// ---- the canonical package tables (host rows step 6, 2026-09-09) -----------------------
//
// `Program/Packages/SqliteBun.lean` and `KeyValueStoreMemory.lean` say what below is the
// package's and what is the harness's plumbing. The packages execute; this file only opens
// the scope the sqlite client's own finalizer runs on, decodes DB-15's JSON-text parameters
// before the package binds them, crosses the answers as the rows' types spell them, and
// posts every call to the tape.

/** `"strings", vs => list vs` — the parameter list of a host row, JSON texts (DB-15). */
export const strings = (...texts: string[]): ReadonlyArray<string> => texts

// ---- the error projection (DI-59, ruling G1) -------------------------------------------
//
// DB-15: an error crosses a host row as `prod string string`. The pair is made **here**, at
// the adapter, so a `catch` or `catchCause` handler inside a printed program observes exactly
// the value the tape records and the Lean machine replays; before this it was made only at
// the recorder, and a program's own handler saw the package's error object.
//
// Where it is applied: exactly the rows whose Lean row type has the pair in its error column
// — `sqlUnsafe` (`Program/Packages/SqliteBun.lean`) and `kvGet`/`kvSet`/`kvRemove`/`kvHas`
// (`KeyValueStoreMemory.lean`). The three rows typed `error := .never` there —
// `sqliteOpen`, `sqliteClose`, `kvMake` — are **not** projected: their error channel is
// `never` on both faces, and widening it to the pair would make `Sql.close` inadmissible in
// `Effect.acquireRelease`'s release slot, which rc.112 types `Effect<unknown, never, R2>`
// (`vendor/effect-4.0.0-rc.112/src/Effect.ts:12930`). An unopenable file stays the defect
// rc.112 throws.
//
// Where it is applied *relative to the tape*: outside `recorded`, so the tape row keeps the
// raw diagnostics (the outer `_tag`) it has always kept and its bytes do not move. The tape
// and the program cannot disagree, because `run-truth.ts`'s `taggedPair` is this same
// `pairOf`.

/** DB-15's `prod string string` on the host: the two-element tuple `pair` builds. */
export type Pair = readonly [string, string]

/** A host failure the projection does not admit. Raised as a **defect**, never as a typed
 * failure: no tag is invented for a shape DB-15 does not describe. */
export class UnsupportedHostFailure extends Error {
  override readonly name = "UnsupportedHostFailure"
  constructor(readonly raw: unknown) {
    super(`no DB-15 pair for host failure ${describeRaw(raw)}`)
  }
}

const describeRaw = (value: unknown): string => {
  if (value instanceof Error) return `${value.name}: ${value.message}`
  try { return JSON.stringify(value) ?? String(value) } catch { return String(value) }
}

/** The projection policy, as a table of the shapes DB-15 admits — **not** a total function
 * (settlement review R1a). `null` means "no pair", and each caller says what it does with
 * that: the adapter (`toPair`) makes it a defect; the recorder describes it.
 *
 *  1. a value that already is the pair — a two-element array of strings (a printed
 *     `Effect.fail(pair(…))`, or a row already projected) — is itself;
 *  2. a two-level tagged error, whose field `reason` is itself tagged (rc.112's `SqlError`,
 *     `vendor/effect-4.0.0-rc.112/src/unstable/sql/SqlError.ts:409-411`, the shape
 *     `Effect.catchReason` dispatches on) — the reason's tag and the driver's message under
 *     it (`reason.cause.message`, else `reason.message`); the outer `_tag` is implied by the
 *     row and is not in the pair (ruling G1). What is lost: the outer tag, `operation`,
 *     `isRetryable`, and the driver error's `code`;
 *  3. a flat tagged error with a string `message` (`Data.TaggedError`: `KeyValueStoreError`,
 *     `vendor/effect-4.0.0-rc.112/src/unstable/persistence/KeyValueStore.ts:183-195`) — its
 *     own tag and message. What is lost: `method`, `key`, `cause`;
 *  4. anything else — a plain `Error` with no `_tag`, a non-`Error` value, a tagged value
 *     whose message is not a string — has **no pair**. A plain `Error` in particular has no
 *     tag and one must never be invented.
 *
 * A defect (`Die`) and an interruption never reach here: the projection is applied with
 * `Effect.mapError`, which rewrites only the first `Fail` reason of a cause and leaves
 * `Die`/`Interrupt` reasons exactly as rc.112 raised them (tested). */
export const pairOf = (e: unknown): Pair | null => {
  if (Array.isArray(e) && e.length === 2 && typeof e[0] === "string" && typeof e[1] === "string") return [e[0], e[1]]
  if (e === null || typeof e !== "object") return null
  const record = e as Record<string, unknown>
  if (typeof record["_tag"] !== "string") return null
  const reason = record["reason"]
  if (reason !== null && typeof reason === "object" && typeof (reason as Record<string, unknown>)["_tag"] === "string") {
    const inner = reason as Record<string, unknown>
    const cause = inner["cause"]
    const driver = cause !== null && typeof cause === "object" && typeof (cause as Record<string, unknown>)["message"] === "string"
      ? (cause as Record<string, unknown>)["message"] as string
      : inner["message"]
    return typeof driver === "string" ? [inner["_tag"] as string, driver] : null
  }
  const message = record["message"]
  return typeof message === "string" ? [record["_tag"] as string, message] : null
}

/** The projection at the adapter: `pairOf` where it answers, a defect where it does not.
 * `Effect.mapError` turns a throw in this function into a `Die` carrying it (tested), so an
 * inadmissible host failure becomes a defect of the row's call and never a fabricated typed
 * failure. */
export const toPair = (e: unknown): Pair => {
  const p = pairOf(e)
  if (p === null) throw new UnsupportedHostFailure(e)
  return p
}

/** The recording seam. `run-truth.ts` installs a sink for the duration of one run; each
 * package call posts its operation, request and exit raw, and the runner wires them. */
export interface TapeCall { readonly op: string; readonly request: ReadonlyArray<unknown>; readonly exit: Exit.Exit<unknown, unknown> }
// One seam per process, not per module instance: the runner imports this file directly while
// the generated modules import the copy beside them, and both must see the same sink.
export const tape: { sink: ((call: TapeCall) => void) | null } =
  ((globalThis as Record<string, unknown>)["~effect4/tape"] ??= { sink: null }) as { sink: ((call: TapeCall) => void) | null }
const recorded = <A, E, R>(op: string, request: ReadonlyArray<unknown>, effect: Effect.Effect<A, E, R>): Effect.Effect<A, E, R> =>
  Effect.onExit(effect, (exit) => Effect.sync(() => { tape.sink?.({ op, request, exit }) }))

/** A row set crossing as `list (list (prod string string))`: one `(column, cell)` pair per
 * column in the driver's order, every cell JSON text (DB-15). */
const rowsToWire = (rows: ReadonlyArray<unknown>): ReadonlyArray<ReadonlyArray<readonly [string, string]>> =>
  rows.map((row) => Object.entries(row as Record<string, unknown>).map(([column, cell]) => [column, JSON.stringify(cell === undefined ? null : cell)] as const))

/** The SQL client handle: the package's client and the scope the prelude minted for it. The
 * one method the table spells, `unsafe`, is the package's own (`sql.unsafe(text, params)`,
 * a `Statement`, the effect that runs it) with each JSON-text parameter decoded before it
 * binds (DB-15: `"7"` binds a number, `"\"x\""` a string) and the rows crossed as pairs. */
export class SqlHandle {
  readonly ["~effect4/ExternalHandle"] = "SqlClient.SqlClient"
  constructor(readonly scope: Scope.Closeable, readonly client: SqliteClient.SqliteClient) {}
  unsafe(text: string, params: ReadonlyArray<string>) {
    return Effect.mapError(recorded("unsafe", [this, text, params],
      Effect.map(this.client.unsafe(text, params.map((p) => JSON.parse(p) as unknown)), rowsToWire)), toPair)
  }
}
export const Sql = {
  /** `SqliteClient.make({ filename, disableWAL: true })` under a scope the prelude mints, so the
   * package's own release (a finalizer it registers on that scope) runs at `Sql.close`.
   * Not projected: the row is typed `error := .never` because `make` is typed `never`, and a
   * file that cannot be opened is a defect `new Database` throws, which no tape replays. */
  open: (filename: string) => recorded("Sql.open", [filename], Effect.gen(function* () {
    const scope = yield* Scope.make()
    const client = yield* SqliteClient.make({ filename, disableWAL: true }).pipe(
      Effect.provideService(Scope.Scope, scope),
      Effect.provide(Reactivity.layer),
    )
    return new SqlHandle(scope, client)
  })),
  close: (handle: SqlHandle) => recorded("Sql.close", [handle], Scope.close(handle.scope, Exit.void)),
}

/** The key-value store handle over the store `KeyValueStore.layerMemory` builds: the four
 * method rows are the store's own; `get`'s `string | undefined` crosses as the row's
 * `.option string`, and `set`/`remove` answer `void` where the store answers its `Map`'s
 * results (`{}`, `true`). Each of the four carries the pair as its error column, so each
 * projects (`toPair`); the memory store itself never fails, and the projection is exercised
 * on a stubbed `KeyValueStoreError` in the seat's probes. */
export class KvHandle {
  readonly ["~effect4/ExternalHandle"] = "KeyValueStore.KeyValueStore"
  constructor(readonly store: KeyValueStore.KeyValueStore) {}
  get(key: string) { return Effect.mapError(recorded("get", [this, key], Effect.map(this.store.get(key), Option.fromNullishOr)), toPair) }
  set(key: string, value: string) { return Effect.mapError(recorded("set", [this, key, value], Effect.asVoid(this.store.set(key, value))), toPair) }
  remove(key: string) { return Effect.mapError(recorded("remove", [this, key], Effect.asVoid(this.store.remove(key))), toPair) }
  has(key: string) { return Effect.mapError(recorded("has", [this, key], this.store.has(key)), toPair) }
}
export const Kv = {
  make: () => recorded("Kv.make", [],
    Effect.map(Effect.provide(Effect.service(KeyValueStore.KeyValueStore), KeyValueStore.layerMemory), (store) => new KvHandle(store))),
}
