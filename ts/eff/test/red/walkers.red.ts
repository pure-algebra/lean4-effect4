// The red twin of the exhaustive walkers. A hand walker over the program's sorts ends every
// switch in a default that takes `never` (`childrenOf` of `read.ts` is one), so the package's
// own type check refuses a constructor with no case. Each line below is a walker that has a
// case for every constructor of a sort but one. tsgo 7 must refuse it at its default, with the
// code and the constructor that `test/read.test.ts` pins. The constructor lists are the
// generated types' (`eff.gen.ts`), so an appended constructor needs no edit here. Excluded from
// the package's own check (`tsconfig.json`); checked by `test/red/tsconfig.json`.
import type { ActionTerm, Eff, LayerTerm, Stmt } from "../../eff.gen.ts"

const noCase = (node: never): never => { throw new Error(JSON.stringify(node)) }

export const effWithoutRestore = (e: Eff): number => e._tag !== "restore" ? 0 : noCase(e)
export const stmtWithoutRet = (s: Stmt): number => s._tag !== "ret" ? 0 : noCase(s)
export const actionWithoutGetInterruptible = (a: ActionTerm): number => a._tag !== "getInterruptible" ? 0 : noCase(a)
export const layerWithoutRef = (l: LayerTerm): number => l._tag !== "ref" ? 0 : noCase(l)
