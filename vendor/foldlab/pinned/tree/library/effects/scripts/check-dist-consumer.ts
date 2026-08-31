/** The built package must be consumable, not merely compiled: the dist
 * entry resolves as ESM at runtime, both public namespaces are present
 * with their layer constructors, and no emitted file kept a source-only
 * `.ts` specifier past the declaration rewrite — and a FOREIGN consumer
 * resolving the bare specifier through the exports map (a linked
 * `node_modules/@foldlab/cas`, never a relative path into dist) gets
 * the same surface, under both pinned runtimes (bun, and node — the
 * claim-target engine). Run after `bun run build`. */
import { spawn, spawnSync } from "node:child_process"
import {
  existsSync,
  mkdirSync,
  mkdtempSync,
  readdirSync,
  readFileSync,
  rmSync,
  statSync,
  symlinkSync,
  writeFileSync,
} from "node:fs"
import { tmpdir } from "node:os"
import { join, relative } from "node:path"
import { fileURLToPath } from "node:url"

const failures: Array<string> = []
const distDir = fileURLToPath(new URL("../dist", import.meta.url))
const srcDir = fileURLToPath(new URL("../src", import.meta.url))

const mod = await import(new URL("../dist/index.js", import.meta.url).href) as {
  readonly Cas?: Record<string, unknown>
  readonly Server?: Record<string, unknown>
}
const rootExports = Object.keys(mod).sort()
if (rootExports.length !== 2
  || rootExports[0] !== "Cas"
  || rootExports[1] !== "Server") {
  failures.push(`dist entry exports ${rootExports.join(", ")}; expected Cas, Server`)
}
if (typeof mod.Cas !== "object" || mod.Cas === null) {
  failures.push("dist entry is missing the Cas namespace")
} else {
  if (mod.Cas.layerMemory === undefined) failures.push("Cas.layerMemory is missing")
  if (mod.Cas.layerFile === undefined) failures.push("Cas.layerFile is missing")
}
if (typeof mod.Server !== "object" || mod.Server === null) {
  failures.push("dist entry is missing the Server namespace")
} else {
  if (mod.Server.httpApp === undefined) failures.push("Server.httpApp is missing")
  if (mod.Server.Core === undefined) failures.push("Server.Core is missing")
}

const walk = (dir: string): Array<string> =>
  readdirSync(dir).flatMap((entry) => {
    const path = join(dir, entry)
    return statSync(path).isDirectory() ? walk(path) : [path]
  })

const normalizedRelative = (root: string, file: string): string =>
  relative(root, file).replaceAll("\\", "/")

const expectedInventory = walk(srcDir)
  .filter((file) => file.endsWith(".ts"))
  .flatMap((file) => {
    const stem = normalizedRelative(srcDir, file).slice(0, -3)
    return [`${stem}.d.ts`, `${stem}.d.ts.map`, `${stem}.js`, `${stem}.js.map`]
  })
  .sort()
const actualInventory = walk(distDir)
  .map((file) => normalizedRelative(distDir, file))
  .sort()

const missing = expectedInventory.filter((file) => !actualInventory.includes(file))
const unexpected = actualInventory.filter((file) => !expectedInventory.includes(file))
for (const file of missing) failures.push(`dist output is missing ${file}`)
for (const file of unexpected) failures.push(`dist output is unexpected ${file}`)

for (const file of walk(distDir)) {
  if (!file.endsWith(".d.ts") && !file.endsWith(".js")) continue
  if (/from\s+"[^"]*\.ts"/.test(readFileSync(file, "utf8"))) {
    failures.push(`unrewritten .ts specifier in ${file}`)
  }
}

// ─── The packaging surface itself ───────────────────────────────────
// Every path package.json points a consumer at must exist: the files
// whitelist, the bin target, and each exports-map leaf. A publish that
// names a missing file fails HERE, not at a consumer's install.
const packageRoot = fileURLToPath(new URL("..", import.meta.url))
const manifest = JSON.parse(
  readFileSync(join(packageRoot, "package.json"), "utf8"),
) as {
  readonly name: string
  readonly version: string
  readonly files: ReadonlyArray<string>
  readonly bin: Record<string, string>
  readonly exports: Record<string, Record<string, string> | string>
}
for (const entry of manifest.files) {
  if (!existsSync(join(packageRoot, entry))) {
    failures.push(`files whitelist names a missing entry: ${entry}`)
  }
}
for (const [name, target] of Object.entries(manifest.bin)) {
  if (!existsSync(join(packageRoot, target))) {
    failures.push(`bin "${name}" points at a missing file: ${target}`)
  }
}
for (const [subpath, targets] of Object.entries(manifest.exports)) {
  const leaves = typeof targets === "string" ? [targets] : Object.values(targets)
  for (const leaf of leaves) {
    if (!existsSync(join(packageRoot, leaf))) {
      failures.push(`exports["${subpath}"] points at a missing file: ${leaf}`)
    }
  }
}

// ─── The foreign consumer ───────────────────────────────────────────
// A scratch package with node_modules/@foldlab/cas linked to this
// package root, importing the BARE specifier so resolution goes
// through the exports map — exactly what an installed consumer does.
// Run under the current runtime (bun in the chain) and under node,
// the pinned claim-target engine, which must serve dist unaided.
const consumerDir = mkdtempSync(join(tmpdir(), "cas-consumer-"))
try {
  const scopeDir = join(consumerDir, "node_modules", "@foldlab")
  mkdirSync(scopeDir, { recursive: true })
  // A junction on Windows needs no privilege; a symlink elsewhere.
  symlinkSync(
    packageRoot,
    join(scopeDir, "cas"),
    process.platform === "win32" ? "junction" : "dir",
  )
  const probe = [
    `import { Cas, Server } from "${manifest.name}"`,
    `import { createRequire } from "node:module"`,
    `const require = createRequire(import.meta.url)`,
    `const pkg = require("${manifest.name}/package.json")`,
    `const defects = []`,
    `if (Cas?.layerMemory === undefined) defects.push("Cas.layerMemory unresolved")`,
    `if (Cas?.layerFile === undefined) defects.push("Cas.layerFile unresolved")`,
    `if (Server?.httpApp === undefined) defects.push("Server.httpApp unresolved")`,
    `if (pkg.name !== "${manifest.name}") defects.push("./package.json export unresolved")`,
    `if (defects.length > 0) { console.error(defects.join("; ")); process.exit(1) }`,
    `console.log("resolved " + pkg.name + "@" + pkg.version)`,
  ].join("\n")
  const probePath = join(consumerDir, "main.mjs")
  writeFileSync(probePath, probe)
  const runtimes: ReadonlyArray<readonly [string, string]> = [
    ["current runtime", process.execPath],
    ["node (claim-target engine)", "node"],
  ]
  for (const [label, executable] of runtimes) {
    const run = spawnSync(executable, [probePath], {
      cwd: consumerDir,
      encoding: "utf8",
    })
    if (run.error !== undefined || run.status !== 0) {
      const detail = run.error !== undefined
        ? String(run.error)
        : `${run.stdout ?? ""}${run.stderr ?? ""}`.trim()
      failures.push(`foreign consumer failed under ${label}: ${detail}`)
    }
  }
} finally {
  rmSync(consumerDir, { force: true, recursive: true })
}

// ─── The tarball consumer ───────────────────────────────────────────
// The linked-node_modules leg above structurally cannot catch a
// missing runtime dependency or a file outside the whitelist (it links
// the whole dev tree). This leg can: pack a real tarball, install it
// into a scratch package so ONLY declared `dependencies` exist, then
// EXECUTE the bin — `--version`, and one full MCP handshake against a
// fresh store, which forces the shipped manifest through `cas serve`'s
// boot gate. Finally, typecheck a consumer against the installed d.ts
// under both `node16` and `bundler` resolution.
const run = (
  label: string,
  executable: string,
  args: ReadonlyArray<string>,
  options: {
    readonly cwd: string
    readonly input?: string
    readonly okStatuses?: ReadonlyArray<number>
  },
): { readonly ok: boolean; readonly stdout: string } => {
  const result = spawnSync(executable, [...args], {
    cwd: options.cwd,
    encoding: "utf8",
    input: options.input,
    timeout: 120_000,
  })
  const accepted = options.okStatuses ?? [0]
  const ok = result.error === undefined
    && result.status !== null
    && accepted.includes(result.status)
  if (!ok) {
    const detail = result.error !== undefined
      ? String(result.error)
      : `exit ${result.status}\n${result.stdout ?? ""}${result.stderr ?? ""}`.trim()
    failures.push(`${label}: ${detail}`)
  }
  return { ok, stdout: result.stdout ?? "" }
}

const tarballDir = mkdtempSync(join(tmpdir(), "cas-tarball-"))
try {
  run("bun pm pack", "bun", ["pm", "pack", "--destination", tarballDir], {
    cwd: packageRoot,
  })
  const tarball = readdirSync(tarballDir).find((file) => file.endsWith(".tgz"))
  if (tarball === undefined) {
    failures.push("bun pm pack produced no tarball")
  } else {
    const consumer = join(tarballDir, "consumer")
    mkdirSync(consumer, { recursive: true })
    writeFileSync(
      join(consumer, "package.json"),
      JSON.stringify({
        name: "cas-tarball-consumer",
        private: true,
        type: "module",
        dependencies: {
          "@foldlab/cas": `file:${join(tarballDir, tarball).replaceAll("\\", "/")}`,
        },
      }),
    )
    const installed = run("tarball install", "bun", ["install"], { cwd: consumer })
    const shippedBin = join(consumer, "node_modules", "@foldlab", "cas", "bin", "cas.cjs")

    if (installed.ok) {
      // The bin, node-supervised, from the installed tree only.
      const version = run("installed bin --version", "node", [shippedBin, "--version"], {
        cwd: consumer,
      })
      if (version.ok && !version.stdout.includes("cas")) {
        failures.push(`installed bin --version answered oddly: ${version.stdout.trim()}`)
      }

      // One real MCP handshake: init a store, then `serve` must pass
      // its manifest boot gate (the shipped mcp/cas-tools.json) and
      // answer `initialize`. stdin closing after the handshake is the
      // session ending, so the process exits on its own.
      const storeDir = join(consumer, "store")
      mkdirSync(storeDir, { recursive: true })
      run("installed bin init", "node", [shippedBin, "init"], { cwd: storeDir })
      const handshake = [
        JSON.stringify({
          jsonrpc: "2.0",
          id: 1,
          method: "initialize",
          params: {
            protocolVersion: "2025-06-18",
            capabilities: {},
            clientInfo: { name: "dist-smoke", version: "0" },
          },
        }),
        JSON.stringify({ jsonrpc: "2.0", method: "notifications/initialized" }),
        "",
      ].join("\n")
      // The session must stay open until the host answers (an
      // immediate stdin EOF interrupts the serving fiber before the
      // reply flushes), so this leg is a live child: write the
      // handshake, hold stdin, wait for the id:1 frame, then end the
      // session. The answered frame proves the boot gate accepted the
      // SHIPPED manifest and the protocol spoke from the installed
      // tree.
      const serveFailure = await new Promise<string | undefined>((resolve) => {
        const child = spawn("node", [shippedBin, "serve"], { cwd: storeDir })
        let out = ""
        let err = ""
        let settled = false
        const done = (failure: string | undefined): void => {
          if (settled) return
          settled = true
          clearTimeout(timer)
          child.stdin.end()
          child.kill("SIGTERM")
          resolve(failure)
        }
        const timer = setTimeout(
          () => done(`serve answered no initialize frame in 30s; stderr: ${err.trim()}`),
          30_000,
        )
        child.stdout.on("data", (chunk: Buffer) => {
          out += chunk.toString()
          if (out.includes(`"id":1`)) done(undefined)
        })
        child.stderr.on("data", (chunk: Buffer) => {
          err += chunk.toString()
        })
        child.on("error", (error) => done(`serve failed to start: ${String(error)}`))
        child.on("exit", (code) =>
          done(out.includes(`"id":1`)
            ? undefined
            : `serve exited ${code} before answering; stderr: ${err.trim()}`))
        child.stdin.write(handshake)
      })
      if (serveFailure !== undefined) {
        failures.push(`installed bin serve handshake: ${serveFailure}`)
      }

      // The d.ts surface, resolved as consumers resolve it.
      writeFileSync(
        join(consumer, "consumer.ts"),
        [
          `import { Cas, Server } from "@foldlab/cas"`,
          `export const memory: typeof Cas.layerMemory = Cas.layerMemory`,
          `export const app: typeof Server.httpApp = Server.httpApp`,
        ].join("\n"),
      )
      for (const resolution of ["node16", "bundler"] as const) {
        const config = join(consumer, `tsconfig.${resolution}.json`)
        writeFileSync(
          config,
          JSON.stringify({
            compilerOptions: {
              module: resolution === "node16" ? "node16" : "esnext",
              moduleResolution: resolution,
              strict: true,
              noEmit: true,
              // Mirrors tsconfig.test.json: upstream rc declaration
              // defects are not this gate's subject; the consumer's
              // own resolution of our d.ts is.
              skipLibCheck: true,
              types: [],
            },
            files: [join(consumer, "consumer.ts")],
          }),
        )
        // `bun x` resolves the package's own patched tsc from
        // packageRoot; the tsconfig's directory governs resolution,
        // so the consumer tree is what gets typechecked.
        run(`type-level consumer (${resolution})`, "bun", ["x", "tsc", "-p", config], {
          cwd: packageRoot,
        })
      }
    }
  }
} finally {
  rmSync(tarballDir, { force: true, recursive: true })
}

if (failures.length > 0) {
  console.error(failures.join("\n"))
  process.exit(1)
}
console.log(
  "dist consumer smoke: exact exports and inventory, namespaces present, specifiers rewritten, "
    + "packaging paths present, bare-specifier resolution green under bun and node, "
    + "tarball install executes the bin (--version, init, one MCP handshake through the manifest "
    + "boot gate), d.ts consumable under node16 and bundler resolution",
)
