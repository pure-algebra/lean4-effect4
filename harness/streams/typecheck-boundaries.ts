/** Check the boundary test body against the selected rc.112 distribution's declarations.
 * Runtime tests import vendored source. Type imports select the same pinned distribution,
 * avoiding a rebuild of upstream source with this harness's stricter indexing options. */
import ts from "../../ts/eff/node_modules/typescript/lib/typescript.js"
import { readFileSync } from "node:fs"
import { resolve } from "node:path"

const root = resolve(import.meta.dir, "../..")
const effect = resolve(root, "ts/eff/node_modules/effect")
if (JSON.parse(readFileSync(resolve(effect, "package.json"), "utf8")).version !== "4.0.0-rc.112")
  throw Error("boundary type checking requires effect@4.0.0-rc.112")
const config = ts.readConfigFile(resolve(import.meta.dir, "tsconfig.json"), ts.sys.readFile)
if (config.error) throw Error(ts.flattenDiagnosticMessageText(config.error.messageText, "\n"))
const parsed = ts.parseJsonConfigFileContent(config.config, ts.sys, import.meta.dir)
if (parsed.errors.length) throw Error("invalid boundary compiler configuration")
const host = ts.createCompilerHost(parsed.options)
host.resolveModuleNames = (names, containing) => names.map(name => {
  const vendor = /^\.\.\/\.\.\/vendor\/effect-4\.0\.0-rc\.112\/src\/(\w+)\.ts$/.exec(name)
  const target = vendor ? resolve(effect, "dist", vendor[1] + ".js") : name
  return ts.resolveModuleName(target, containing, parsed.options, host).resolvedModule
})
const program = ts.createProgram([resolve(import.meta.dir, "boundary.test.ts")], parsed.options, host)
const diagnostics = ts.getPreEmitDiagnostics(program)
if (diagnostics.length) {
  console.error(ts.formatDiagnostics(diagnostics, {
    getCanonicalFileName: name => name, getCurrentDirectory: () => root, getNewLine: () => "\n"
  }))
  process.exitCode = 1
} else console.log("PASS boundary types: exact test body against effect@4.0.0-rc.112 declarations")
