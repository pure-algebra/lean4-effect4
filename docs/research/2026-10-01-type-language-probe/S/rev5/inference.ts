import {NAT, INT, NESTED, MODIFIER, TUPLE, ARRAY, UNION} from './generated'
type Equal<A,B> = (<T>()=>T extends A ? 1 : 2) extends (<T>()=>T extends B ? 1 : 2) ? true : false
type Assert<T extends true> = T
type IsMutableOptional = Assert<Equal<typeof MODIFIER.Type, {'a-b'?: string}>>
type IsNested = Assert<Equal<typeof NESTED.Type, {readonly user:{readonly age:number;readonly name:string}}>>
type IsNatNumber = Assert<Equal<typeof NAT.Type, number>>
type IsIntNumber = Assert<Equal<typeof INT.Type, number>>
type IsTuple = Assert<Equal<typeof TUPLE.Type, readonly [string]>>
type IsArray = Assert<Equal<typeof ARRAY.Type, readonly string[]>>
type IsUnion = Assert<Equal<typeof UNION.Type, string | number>>
const good: typeof NESTED.Type={user:{age:1,name:'Sam'}}
// Runtime checks, not TypeScript number types, enforce integer restrictions.
const runtimeMustRefuse: typeof NAT.Type=-1.5
const mutable: typeof MODIFIER.Type={}
mutable['a-b']='ok'
// @ts-expect-error Missing name.
const missing: typeof NESTED.Type={user:{age:1}}
// @ts-expect-error Wrong primitive type.
const wrong: typeof NESTED.Type={user:{age:'1',name:'Sam'}}
// @ts-expect-error Required readonly property.
good.user.age=2
// @ts-expect-error Exact optional property excludes explicit undefined.
const optionalWrong: typeof MODIFIER.Type={'a-b':undefined}
// @ts-expect-error Tuple requires an element.
const emptyTuple: typeof TUPLE.Type=[]
export {good,runtimeMustRefuse,mutable,missing,wrong,optionalWrong,emptyTuple}
export type {IsMutableOptional,IsNested,IsNatNumber,IsIntNumber,IsTuple,IsArray,IsUnion}
