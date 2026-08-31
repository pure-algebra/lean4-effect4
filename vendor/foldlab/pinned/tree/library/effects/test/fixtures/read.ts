/**
 * Fixture reads through the `FileSystem` service — the ONE door
 * (operator ruling 2026-08-28: NO `node:fs`, ever; filesystem is an
 * effect and enters only through the service seam). Paths are
 * package-root-relative: vitest runs with cwd = `library/effects`.
 */
import { Effect, FileSystem, PlatformError } from "effect"

export const readFixtureString = (
  path: string,
): Effect.Effect<string, PlatformError.PlatformError, FileSystem.FileSystem> =>
  FileSystem.FileSystem.pipe(Effect.flatMap((fs) => fs.readFileString(path)))

export const readFixtureBytes = (
  path: string,
): Effect.Effect<Uint8Array, PlatformError.PlatformError, FileSystem.FileSystem> =>
  FileSystem.FileSystem.pipe(Effect.flatMap((fs) => fs.readFile(path)))
