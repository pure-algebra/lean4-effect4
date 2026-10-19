import { toJson } from "../../../../../ts/eff/json.gen.ts"
const prog = JSON.parse(await Bun.file(process.argv[2]).text())
const out = toJson(prog)
console.log("V", out.length)
console.log(out)
