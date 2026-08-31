#!/usr/bin/env bun
/**
 * cas — the content-addressed store, spoken from a shell.
 *
 * The entry point wires the command tree to the platform once:
 * `BunServices.layer` supplies the filesystem, path, stdio, and
 * terminal realizations the runner and every verb speak through, and
 * nothing below this file touches the platform directly. Bun is the
 * host everywhere — the shim runs this file under it, so the platform
 * layer is the Bun one and no Node realization is loaded.
 *
 * The tree is `bin/cli/tree.ts`'s and the runner is
 * `bin/cli/entry.ts`'s, so this file is only the wiring: what the
 * arguments are, and what the platform is. `--wizard` on any command
 * walks through its inputs — one of the runner's own built-in global
 * flags (`GlobalFlag.wizard`), not a declaration of this package's.
 */
import { BunRuntime, BunServices } from "@effect/platform-bun"
import { Effect, Stdio } from "effect"
import { runCas } from "./cli/entry.ts"
import { cas } from "./cli/tree.ts"

// The argument vector comes from `Stdio`, exactly as `Command.run`
// takes it — this entry point differs from `Command.run` only in what
// it does with a refusal, never in where the arguments come from.
BunRuntime.runMain(
  Stdio.Stdio.use(({ args }) => args).pipe(
    Effect.flatMap(runCas(cas, { version: "0.1.0" })),
    Effect.provide(BunServices.layer),
  ),
)
