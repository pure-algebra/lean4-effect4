import { pair, tuple, ite, add, cons, nil } from "./prelude-atoms.gen.ts"
import { fold } from "./prelude.ts"
import { tupleAt } from "./tuples.ts"
declare const flag: boolean
export const choice: readonly [boolean, number] = ite(flag,pair(true,0),pair(false,0))
export const counted: readonly [number,boolean] = fold(cons(1,nil()),tuple(0,false),(acc,x)=>tuple(add(tupleAt<"0">("0")(acc),x),true))
