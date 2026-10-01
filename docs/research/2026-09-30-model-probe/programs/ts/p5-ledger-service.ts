/**
 * Program 5 (seat PROGRAMS, 2026-09-30): a small stateful service. Its state is a typed record
 * (with a list of tagged variants) in a Ref; it fails with a structured error; it takes
 * callbacks (listeners that run on every change, registered for a scope and removed by
 * identity); and it wraps a host callback API with a cancellation. Idiomatic Effect rc.112.
 *
 * rc.112 lines relied on (vendor/effect-4.0.0-rc.112/src/):
 *   Context.Service             Context.ts:160-201
 *   Layer.effect                Layer.ts:1347, :1427-1440
 *   Ref.make / get / modify / update   Ref.ts:173, :200, :797, :1200
 *   Data.TaggedError            Data.ts:1111
 *   Effect.acquireRelease       Effect.ts:12928-12932
 *   Effect.forEach              Effect.ts:1088 (sequential at the default concurrency 1,
 *                               internal/effect.ts:4675-4677, :4697-4718)
 *   Effect.callback             Effect.ts:1667-1673; internal/effect.ts:1163-1170 and
 *                               callbackOptions :1102-1141 (the register's returned effect is
 *                               the cancellation, run by asyncFinalizer on interruption :1143-1159)
 *   Effect.scoped / provide     Effect.ts:12815, :11383
 */
import { Context, Data, Effect, Layer, Ref } from "effect"

/** A tagged variant. */
type Entry =
  | { readonly _tag: "Deposit"; readonly amount: number }
  | { readonly _tag: "Withdraw"; readonly amount: number }

/** The state: a record holding a string, a number and a list of variants. */
interface Account {
  readonly id: string
  readonly balance: number
  readonly history: ReadonlyArray<Entry>
}

/** A structured typed error: two numbers. */
export class InsufficientFunds extends Data.TaggedError("InsufficientFunds")<{
  readonly needed: number
  readonly available: number
}> {}

/** A callback the service keeps and runs later, on another caller's fiber. */
type Listener = (account: Account) => Effect.Effect<void>

export class Ledger extends Context.Service<Ledger, {
  readonly deposit: (amount: number) => Effect.Effect<number>
  readonly withdraw: (amount: number) => Effect.Effect<number, InsufficientFunds>
  /** Register a listener for the lifetime of the caller's scope. */
  readonly onChange: (listener: Listener) => Effect.Effect<void, never, import("effect").Scope.Scope>
  /** Wait for the host's settlement callback; interruption cancels the host timer. */
  readonly settle: Effect.Effect<string>
}>()("app/Ledger") {}

export const LedgerLive = Layer.effect(Ledger, Effect.gen(function*() {
  const state = yield* Ref.make<Account>({ id: "acc-1", balance: 0, history: [] })
  const listeners = yield* Ref.make<ReadonlyArray<Listener>>([])

  const notify = (account: Account) =>
    Effect.flatMap(Ref.get(listeners), (ls) => Effect.forEach(ls, (l) => l(account), { discard: true }))

  /** One atomic transition of the record; then every listener sees the new state. */
  const transition = <E>(step: (a: Account) => readonly [Effect.Effect<number, E>, Account]) =>
    Ref.modify(state, (a): [readonly [Effect.Effect<number, E>, Account], Account] => {
      const [answer, next] = step(a)
      return [[answer, next], next]
    }).pipe(Effect.flatMap(([answer, next]) => Effect.andThen(notify(next), answer)))

  return {
    deposit: (amount) =>
      transition((a) => {
        const next: Account = { ...a, balance: a.balance + amount, history: [...a.history, { _tag: "Deposit", amount }] }
        return [Effect.succeed(next.balance), next]
      }),
    withdraw: (amount) =>
      transition((a) =>
        a.balance < amount
          ? [Effect.fail(new InsufficientFunds({ needed: amount, available: a.balance })), a]
          : [Effect.succeed(a.balance - amount), {
            ...a,
            balance: a.balance - amount,
            history: [...a.history, { _tag: "Withdraw", amount }]
          }]
      ),
    onChange: (listener) =>
      Effect.acquireRelease(
        Ref.update(listeners, (ls) => [...ls, listener]),
        () => Ref.update(listeners, (ls) => ls.filter((l) => l !== listener)) // removal by identity
      ),
    settle: Effect.callback<string>((resume) => {
      const timer = setTimeout(() => resume(Effect.succeed("settled")), 5)
      return Effect.sync(() => clearTimeout(timer))
    })
  }
}))

export const program = Effect.gen(function*() {
  const ledger = yield* Ledger
  const seen = yield* Ref.make<ReadonlyArray<number>>([])
  const result = yield* Effect.scoped(
    Effect.gen(function*() {
      yield* ledger.onChange((a) => Ref.update(seen, (s) => [...s, a.balance]))
      yield* ledger.deposit(10)
      const after = yield* ledger.withdraw(25).pipe(
        Effect.catchTag("InsufficientFunds", (e) => Effect.succeed(e.available - e.needed))
      )
      return after
    })
  )
  yield* ledger.deposit(1) // the listener is gone: not seen
  const settled = yield* ledger.settle
  return [result, yield* Ref.get(seen), settled] as const
}).pipe(Effect.provide(LedgerLive))

/** The checked type, pinned. */
export const pinProgram: Effect.Effect<readonly [number, ReadonlyArray<number>, string]> = program
