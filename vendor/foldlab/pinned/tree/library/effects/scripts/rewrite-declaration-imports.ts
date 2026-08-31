import { readdir, readFile, writeFile } from "node:fs/promises"
import { relative } from "node:path"
import { fileURLToPath } from "node:url"

const outputRoot = new URL("../dist/", import.meta.url)
const outputRootPath = fileURLToPath(outputRoot)
const relativeTypeScriptSpecifier = /(["'])(\.\.?\/[^"'\r\n]+)\.ts\1/g

const declarationFiles = async (directory: URL): Promise<ReadonlyArray<URL>> => {
  const entries = await readdir(directory, { withFileTypes: true })
  const nested = await Promise.all(entries.map((entry) => {
    const location = new URL(`${entry.name}${entry.isDirectory() ? "/" : ""}`, directory)
    if (entry.isDirectory()) return declarationFiles(location)
    return entry.name.endsWith(".d.ts") ? [location] : []
  }))
  return nested.flat()
}

const files = await declarationFiles(outputRoot)
if (files.length === 0) throw new Error("declaration emit produced no .d.ts files")

for (const file of files) {
  const source = await readFile(file, "utf8")
  const rewritten = source.replace(
    relativeTypeScriptSpecifier,
    (_match, quote: string, specifier: string) => `${quote}${specifier}.js${quote}`,
  )
  if (rewritten !== source) await writeFile(file, rewritten)
  if (relativeTypeScriptSpecifier.test(rewritten)) {
    const emitted = relative(outputRootPath, fileURLToPath(file)).replaceAll("\\", "/")
    throw new Error(`unrewritten TypeScript declaration specifier in dist/${emitted}`)
  }
  relativeTypeScriptSpecifier.lastIndex = 0
}
