import { fileURLToPath } from "node:url"
import { defineConfig } from "vitest/config"

export default defineConfig({
  resolve: {
    alias: {
      // The Effect-native register's materialized snapshots are
      // committed VERBATIM, and Effect's `toCodeDocument` spells this
      // package's own declaration import by package name. The alias is
      // the truth of that specifier inside this package — the same
      // mapping `tsconfig.test.json` gives the compiler — so the
      // snapshot evaluates without a build step and without the
      // generator rewriting what it emitted.
      "@foldlab/cas": fileURLToPath(new URL("./src/index.ts", import.meta.url)),
    },
  },
  test: {
    include: ["test/**/*.test.ts"],
  },
})
