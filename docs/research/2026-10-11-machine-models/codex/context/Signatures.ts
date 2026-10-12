import { Context, Effect } from "effect"

const Db = Context.Service<"Db", number>("Db")
const Log = Context.Service<"Log", string>("Log")
const db = Context.make(Db, 2)
const both = Context.add(db, Log, "ready")

const reader: Effect.Effect<Context.Context<"Db">, never, "Db"> = Effect.context<"Db">()
const provided: Effect.Effect<number, never, never> = Effect.provideContext(Effect.service(Db), db)
const unsupplied: Effect.Effect<number, never, "Db"> = Effect.provideContext(Effect.service(Db), Context.empty())
const narrowed: Context.Context<"Db"> = both

// Reading an empty context cannot supply Db.
// @ts-expect-error the effect still requires Db
const invalidClosed: Effect.Effect<number, never, never> = Effect.provideContext(Effect.service(Db), Context.empty())
// @ts-expect-error an empty context does not meet the typed Db context promise
const invalidContext: Context.Context<"Db"> = Context.empty()

// Merging the captured empty context inside provision retains the local Db binding.
const captured: Effect.Effect<number, never, never> = Effect.flatMap(
  Effect.context<never>(),
  (outer) => Effect.provideService(Effect.provideContext(Effect.service(Db), outer), Db, 1)
)

// A parameter run under a providing body loses that supplied key from its call row.
const callbackRegion = <A, E, R>(callback: Effect.Effect<A, E, R>): Effect.Effect<A, E, Exclude<R, "Db">> =>
  Effect.provideContext(callback, db)

void [reader, provided, unsupplied, narrowed, invalidClosed, invalidContext, captured, callbackRegion]
