// The three probe programs in the printed Effect TypeScript fragment, as an agent writes them.
// Each `export const` is read by `check.ts` (readTypeScript) under the row table named beside it.
// Binder names must be a0, a1, … by depth (ts/eff/read.ts `varRead`, `sameParams`).

// (a) rows "todo": add a to-do through the host row, answer the list's length.
export const a = Effect.flatMap(Todos.add("milk"), (a0) => Effect.succeed(length(a0)))

// (b) rows "db": acquire a connection in a scope; the release takes the resource and the exit.
export const b = Effect.scoped(Effect.flatMap(Effect.acquireRelease(Db.open("db"), (a0, a1) => Db.close(a0)), (a0) => Db.query(a0)))

// (c) no rows: fork two children, join both, add.
export const c = Effect.flatMap(Effect.forkChild(Effect.succeed(1), { startImmediately: false, uninterruptible: "inherit" }), (a0) => Effect.flatMap(Effect.forkChild(Effect.succeed(2), { startImmediately: false, uninterruptible: "inherit" }), (a1) => Effect.flatMap(Fiber.join(a0), (a2) => Effect.flatMap(Fiber.join(a1), (a3) => Effect.succeed(add(a2, a3))))))

// (a-hole) rows "todo" plus one hole row named "count" (answer number): a hole is a named call.
export const aHole = Effect.flatMap(Todos.add("milk"), (a0) => count())
