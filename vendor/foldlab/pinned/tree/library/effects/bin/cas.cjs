#!/usr/bin/env node
/**
 * The runtime-portable entry for the `cas` bin.
 *
 * The CLI itself (./cas.ts) is Bun-native by ruling — BunRuntime and
 * BunServices are the platform layer, and the honest v0 distribution
 * bar is repo + bun + mise (FRONTEND ask 11; see PACKAGING.md). This
 * shim implements that bar cleanly rather than pretending otherwise:
 *
 *   - under Bun, it hands straight to the CLI in-process;
 *   - under Node, it supervises a `bun` child faithfully: argv passed
 *     through, stdio inherited, SIGINT/SIGTERM/SIGHUP forwarded to the
 *     child (a killed supervisor must not orphan a store-holding
 *     server), the child's exit code propagated, and a signal-death
 *     reported as 128+signal the way a shell would (Ctrl-C is 130,
 *     not 1);
 *   - where bun is absent, it says exactly what is missing and how to
 *     get it, instead of `env: bun: No such file or directory`.
 *
 * CommonJS on purpose: this file must parse and run under plain Node
 * with zero dependencies installed, before any runtime choice is made.
 * It is a platform boundary, not Effect code — errors here are process
 * exits with guidance, by design.
 *
 * Windows note: Bun normally installs a real bun.exe, which Node's
 * spawn resolves from PATH without a shell. Where the PATH entry is a
 * `.cmd`/`.bat` shim instead, post-CVE-2024-27980 Node refuses the
 * spawn with EINVAL (not ENOENT) — so on win32 an EINVAL is retried
 * once through the shell, with the arguments quoted.
 */
"use strict"
const { spawn } = require("node:child_process")
const { constants } = require("node:os")
const { join } = require("node:path")

const missingBun = () => {
  console.error(
    [
      "cas: the Bun runtime is required and was not found on PATH.",
      "",
      "This CLI is Bun-native (engines.bun >= 1.4.0). Install one of:",
      "  - mise, then `mise install` in the repository (the pinned route), or",
      "  - bun directly: https://bun.sh",
    ].join("\n"),
  )
  process.exit(127)
}

/** Quote one argument for cmd.exe — only used on the win32
 * shell-retry path, where Node passes the command line verbatim. */
const quoted = (argument) =>
  /[\s"^&|<>()%!]/u.test(argument)
    ? `"${argument.replaceAll(`"`, `""`)}"`
    : argument

if (process.versions.bun === undefined) {
  const cli = join(__dirname, "cas.ts")
  const args = [cli, ...process.argv.slice(2)]

  const supervise = (child, onSpawnError) => {
    // Forward the terminating signals: the supervisor must never exit
    // leaving a store-holding child reparented to init. SIGINT from a
    // terminal reaches the whole foreground group already; forwarding
    // is what covers a `kill` aimed at this pid alone.
    for (const signal of ["SIGINT", "SIGTERM", "SIGHUP"]) {
      process.on(signal, () => {
        child.kill(signal)
      })
    }
    child.on("error", onSpawnError)
    child.on("exit", (code, signal) => {
      if (signal !== null) {
        const number = constants.signals[signal]
        process.exit(number === undefined ? 1 : 128 + number)
      }
      process.exit(code === null ? 1 : code)
    })
  }

  const shellRetry = () => {
    const command = ["bun", ...args.map((argument) => quoted(argument))].join(" ")
    const child = spawn(command, { shell: true, stdio: "inherit" })
    supervise(child, (error) => {
      console.error(`cas: failed to start bun: ${String(error)}`)
      process.exit(127)
    })
  }

  const child = spawn("bun", args, { stdio: "inherit" })
  supervise(child, (error) => {
    if (error.code === "ENOENT") return missingBun()
    if (error.code === "EINVAL" && process.platform === "win32") {
      return shellRetry()
    }
    console.error(`cas: failed to start bun: ${String(error)}`)
    process.exit(127)
  })
} else {
  require("./cas.ts")
}
