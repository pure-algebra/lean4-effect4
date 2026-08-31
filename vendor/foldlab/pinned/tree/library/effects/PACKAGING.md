# PACKAGING — the distribution posture of `@foldlab/cas`

Status: packaging record, 2026-08-29 (the production-package lane,
docs/SPECS.md decision 26 seat 2). This file states what the package
IS as a distributable, what is deliberately withheld, and exactly what
flips at publish time — so that publishing is a decision, never an
archaeology.

## The posture: publish-capable, not published

The estate's ratified product shape is dual output — the product and
OSS libraries from one substrate
([VISION](../../.staging/product-sphere/VISION.md), decision 1). This
package is the first OSS half. It stays `"private": true` because
publication is an operator decision (an unpublished 0.x with honest
gates beats a published one with unstated ones), but everything a
publish needs is staged and gated now:

- **`exports` map** — one root entry (`.`), resolving `types` →
  `dist/index.d.ts` and `import`/`default` → `dist/index.js`, plus
  `./package.json`. **dist is the consumed surface**; nothing in the
  map points at `src`.
- **`files` whitelist** — `dist` (the surface), `src` (shipped for
  sourcemap/declarationMap fidelity and because the Bun-native bin
  runs the TypeScript directly), `bin`, `mcp` (below), and the law
  documents (README, BACKEND, PROFILE-CAS-HTTP-0, SERVING,
  VOCABULARY, PACKAGING, RELEASING, LICENSE). Every entry's existence is asserted
  by `scripts/check-dist-consumer.ts`, which also resolves the bare
  specifier through a linked `node_modules` — the exports map
  exercised exactly as a foreign consumer would, under both bun and
  node (the pinned claim-target engine) — and then goes the rest of
  the way: it packs a real tarball, installs it into a scratch
  package so only declared `dependencies` exist, EXECUTES the bin
  (`--version`, `init`, and one full MCP `initialize` handshake
  against `cas serve`), and typechecks a consumer against the
  installed declarations under both `node16` and `bundler`
  resolution.
- **`mcp/cas-tools.json`, the shipped manifest** — `cas serve`'s boot
  gate reads the Lean-emitted tool manifest at one fixed relative
  path which resolves to `library/cas/mcp/cas-tools.json` in the
  repository and to `<packageRoot>/mcp/cas-tools.json` in an
  installed package (the package directory is named `cas`, so the
  loader's `../../../cas/` segment lands back inside it). The build
  (`scripts/copy-mcp-manifest.ts`) materializes that package-local
  copy byte-for-byte from the byte-gated authority; it is gitignored
  here, derived never committed, and the tarball smoke's handshake
  leg proves the installed server boots on it.
- **`publishConfig`** — `access: public`, `provenance: true` (npm
  provenance attestation from CI), inert while `private` stands.
- **`engines.bun >= 1.4.0`** — the CLI's honest requirement, see
  below.
- **`prepack`** runs the build, so a tarball can never carry a stale
  `dist`.

### What flips at publish time, exhaustively

1. `"private": true` is removed (one line; `publishConfig` is already
   staged).
2. The version moves per [RELEASING.md](RELEASING.md)'s gate sequence
   — `mise run check:ci` green on a fresh clone is the floor, and the
   `foldlab.effectProvenance` correspondence (below) is re-verified.
3. The `effect` peer reality is stated: this package pins
   `effect@4.0.0-rc.112` exactly (estate-wide Wave-1 ruling,
   docs/SPECS.md decision 23). A published 0.x keeps the exact pin —
   an rc dependency range would be a lie about compatibility.
4. A publish WORKFLOW exists before the first publish, and it is
   owed, not written: `publishConfig.provenance` requires npm
   provenance attestation, which only works from a CI run with OIDC
   (`permissions: id-token: write`) — it cannot be satisfied from a
   laptop. The `repository` field (with `directory`) is already
   staged because provenance verification requires it.
5. Nothing else. If a publish needs a step this list does not name,
   the step lands here first.

## Version story: 0.x, honestly

`0.1.0` means what 0.x means: the surface moves with the rulings, and
minor bumps may break. The version is not decoration — it moves only
through RELEASING.md's sequence, and it will not reach 1.0 before the
Lean-model correspondence claims it rides on are stamped at their
gates (CLAIM-GATES G-ladder; no soundness word without its judgment).

## The `foldlab.effectProvenance` field

`package.json` carries a `foldlab.effectProvenance` object — the
package's half of the AGENTS.md dependency law ("the `effect` npm
version and the provenance source pin must name each other"):

- `commit` — the upstream `Effect-TS/effect` commit the resolved npm
  version corresponds to (verified by reading
  `packages/effect/package.json` at that commit).
- `lockRow` — the id of the row in the provenance lock that records
  the correspondence (`effect-runtime`).
- `lock` — the repo-relative path to that lock
  (`.reference/provenance/sources.lock.json`).

When the `effect` dependency moves, this field and the lock row move
in the same change, or the change is wrong. The Stage-1 extraction pin
(lock row `effect`) is deliberately a different row and does NOT move
with the dependency.

## The bin: Bun-native, with a portable front door

The ruled distribution bar is **repo + bun + mise**
([FRONTEND](../../.staging/operational-structure/FRONTEND.md) ask 11:
recommended and honest). The CLI is Bun-native (`BunRuntime`,
`BunServices`), and this package implements the bar cleanly instead of
half-porting:

- `bin.cas` → `bin/cas.cjs`, a dependency-free CommonJS launcher that
  runs under plain Node: under Bun it hands to the CLI in-process;
  under Node it SUPERVISES a `bun` child faithfully — stdio
  inherited, SIGINT/SIGTERM/SIGHUP forwarded (a killed supervisor
  must not orphan a store-holding server; probed), the child's exit
  code propagated, signal-death reported as 128+signal; with no bun
  present it prints exactly what is missing and the two install
  routes (mise or bun.sh) and exits 127.
- `engines` states both requirements machine-readably: `bun >= 1.4.0`
  (the CLI's runtime) and `node >= 22` (the supervising shim and the
  ESM dist surface).
- A Node-hosted CLI is not promised, so none is pretended.

## Windows honesty

The PC (PowerShell) is a first-class host in this estate. The T7
portability tier was retired 2026-08-29 (commit `a5fb51a9`) and is
deliberately not rebuilt; in its place, this section states what is
and is not verified on Windows, so the claim surface matches the gate
surface.

**Verified or safe by construction:**

- Every script under `scripts/` is TypeScript run by bun — paths via
  `node:path`, separators normalized where compared
  (`replaceAll("\\", "/")`); no shell strings.
- `bin/cas.cjs` spawns `bun` without a shell, which resolves Bun's
  usual real `bun.exe` from PATH. Where the PATH entry is a
  `.cmd`/`.bat` shim instead, post-CVE-2024-27980 Node refuses that
  spawn with EINVAL — the launcher retries once through the shell
  with quoted arguments on win32 EINVAL, so both install shapes work;
  the shell-retry path itself is untested on a real PC and is part of
  the windows-latest CI verification below.
- `scripts/litestream-check.ts` documents its PowerShell invocation
  verbatim, including the litestream 0.5.12 `file://` drive-letter
  gotcha and its workaround.
- Package scripts chain with `&&` only (portable under bun's runner).
- CI runs the full `mise run check:ci` on `windows-latest` for every
  push to main (.github/workflows/check.yml), which is the standing
  cross-OS assertion.

**NOT verified on Windows, stated plainly:**

- The BS1 gate batching (`lake env sh -c 'set -e; …'` in root
  `mise.toml`'s `check:cas` family) requires an `sh` on PATH. GitHub's
  Windows runners carry one (Git for Windows); a bare PowerShell host
  does not necessarily. This landed 2026-08-29 and has not been run on
  the PC as of this writing — the first `windows-latest` `check:ci`
  run is the verification, and if it reds there, the fix belongs in
  `mise.toml` (per-gate `run` lines or a windows-safe batching), not
  in a weaker gate.
- `check:extract-twin` uses `bash` outright — already declared
  host-local and outside the chain
  (library/cas/meta/out/environment.META.json `residence` column), so
  it makes no
  Windows claim.
- The foreign-consumer smoke's junction-link leg
  (`check-dist-consumer.ts`) is written for Windows
  (`symlinkSync(..., "junction")`) but was authored on macOS; the
  `windows-latest` CI leg is its verification too.

## What CI runs (the one-line summary)

`.github/workflows/check.yml` → an install prelude for the three
package trees the gen chain reads, then `mise run check:ci`: every
emitter forced (`gen:ci`), `git diff --exit-code`, every gate forced.
The skip-list authority is `library/cas/meta/out/environment.META.json` —
precisely: CI attempts no host-local task, forces every task inside
the chain, and the portable tasks it does not run are exactly the
portable members of that ledger's `excludedGates` (the three frozen
archive tasks and `check:lift-roundtrip`), each excluded with its own
stated reason. The workflow's own comments carry the job structure,
the caching rationale, and their stated tradeoffs.
