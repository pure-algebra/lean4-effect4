/**
 * Ship the Lean-emitted MCP tool manifest inside the package.
 *
 * `bin/mcp/manifest.ts` resolves the manifest at ONE fixed relative
 * URL: `../../../cas/mcp/cas-tools.json` from its own location. In the
 * repository that lands on `library/cas/mcp/cas-tools.json` (the
 * byte-gated emitter output). In an INSTALLED package the same URL
 * lands on `<packageRoot>/mcp/cas-tools.json` — because the package
 * directory is named `cas` under `@foldlab/`, the `../../../cas/`
 * segment resolves back into the package itself. This build step
 * materializes that path, byte-identically, so `cas serve`'s boot gate
 * finds its contract in both worlds without the loader knowing which
 * world it is in.
 *
 * The copy is DERIVED, never committed (`mcp/` is gitignored here):
 * the authority stays `library/cas/mcp/cas-tools.json`, whose own
 * byte gate (`mcpspec --check`) guards its content. A drifted copy
 * cannot survive a build, because this step always overwrites from
 * the authority and refuses when the authority is absent.
 */
import { copyFileSync, existsSync, mkdirSync } from "node:fs"
import { dirname, join } from "node:path"
import { fileURLToPath } from "node:url"

const packageRoot = fileURLToPath(new URL("..", import.meta.url))
const authority = join(packageRoot, "..", "cas", "mcp", "cas-tools.json")
const shipped = join(packageRoot, "mcp", "cas-tools.json")

if (!existsSync(authority)) {
  console.error(
    `mcp manifest copy: authority missing at ${authority}\n`
      + "  it is generated: run `lake exe mcpspec` in library/cas",
  )
  process.exit(1)
}
mkdirSync(dirname(shipped), { recursive: true })
copyFileSync(authority, shipped)
console.log("mcp manifest copy: mcp/cas-tools.json materialized from library/cas")
