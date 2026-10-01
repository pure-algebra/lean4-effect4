import assert from 'node:assert/strict'
import {readFileSync, writeFileSync} from 'node:fs'
import * as S from 'effect/Schema'
import * as R from 'effect/SchemaRepresentation'

const log=readFileSync(new URL('./schema.log',import.meta.url),'utf8')
const expressions=Object.fromEntries(log.split('\n').filter(s=>s.startsWith('EXPR_')).map(s=>{
  const i=s.indexOf(':');return [s.slice(5,i),s.slice(i+1)]
}))
const actual=Object.fromEntries(Object.entries(expressions).filter(([,e])=>e!=='REFUSED').map(([n,e])=>[n,Function('Schema',`return (${e})`)(S)]))
const accepts=(schema,v)=>{try {S.decodeUnknownSync(schema,{onExcessProperty:'error'})(v);return true} catch{return false}}
const numericInputs=[0,42,-1,1.5,'42',Number.MAX_SAFE_INTEGER,Number.MAX_SAFE_INTEGER+1,NaN,Infinity,-Infinity,-0]
const natExpected=[true,true,false,false,false,true,false,false,false,false,true]
const intExpected=[true,true,true,false,false,true,false,false,false,false,true]
numericInputs.forEach((v,i)=>{
  assert.equal(accepts(actual.NAT,v),natExpected[i]);
  assert.equal(accepts(actual.INT,v),intExpected[i]);
  assert.equal(accepts(actual.NAT,v),accepts(S.Natural,v));
})
for(const [v,ok] of [[{user:{age:42,name:'Sam'}},true],[{user:{age:-1,name:'Sam'}},false],
    [{user:{age:1.5,name:'Sam'}},false],[{user:{age:1}},false],[{user:{age:1,name:'Sam',extra:1}},false]])
  assert.equal(accepts(actual.NESTED,v),ok)
assert.equal(accepts(actual.MODIFIER,{}),true)
assert.equal(accepts(actual.MODIFIER,{'a-b':'ok'}),true)
assert.equal(accepts(actual.MODIFIER,{'a-b':undefined}),false)
assert.equal(accepts(actual.MODIFIER,{'a-b':42}),false)
assert.equal(accepts(actual.ESCAPE,{'x"\n\\y':'ok'}),true)
assert.equal(accepts(actual.ESCAPE,{}),false)
assert.equal(accepts(actual.TUPLE,[]),false)
assert.equal(accepts(actual.TUPLE,['s']),true)
assert.equal(accepts(actual.TUPLE,['s','extra']),false)
assert.equal(accepts(actual.ARRAY,[]),true)
assert.equal(accepts(actual.ARRAY,['s','t']),true)
assert.equal(accepts(actual.ARRAY,[1]),false)
assert.equal(accepts(actual.UNION,'s'),true)
assert.equal(accepts(actual.UNION,1),true)
assert.equal(accepts(actual.UNION,true),false)

// The former emitted-output failures are now located refusals in Lean.
assert.equal(expressions.DUP,'REFUSED')
assert.equal(expressions.CHECK_CHILD,'REFUSED')
assert.equal(accepts(actual.UNIQUE,{a:42,b:'ok'}),true)
assert.equal(accepts(actual.UNIQUE,{a:'wrong',b:'ok'}),false)

// Independent upstream path follows check schemas before it invokes the isInt reviver.
const nestedDoc={representation:{_tag:'Number',checks:[{_tag:'Filter',aborted:false,
  representation:{id:'effect/schema/isInt',payload:null,schemas:[{
    _tag:'Declaration',representation:{id:'custom/missing',payload:null},typeParameters:[],checks:[]
  }]}}]},references:{}}
let nestedError=''
try {R.fromRepresentation(nestedDoc,{revivers:[S.isIntReviver]})} catch(e){nestedError=e.message}
assert.match(nestedError,/Missing reviver for custom\/missing/)
assert.equal(actual.CHECK_CHILD,undefined)
const canonicalIntDoc={representation:{_tag:'Number',checks:[{_tag:'Filter',aborted:false,
  representation:{id:'effect/schema/isInt',payload:null}}]},references:{}}
assert.equal(accepts(R.fromRepresentation(canonicalIntDoc,{revivers:[S.isIntReviver]}),1),true)

// Previously behavior-changing annotations must now be rejected before any code is emitted.
for(const name of ['ANNOT_ERROR','ANNOT_PRESERVE','ANNOT_DISABLE']) {
  assert.equal(expressions[name],'REFUSED')
  assert.equal(actual[name],undefined)
}
const revive=doc=>R.fromRepresentation(R.fromJson(R.toJson(doc)),{revivers:[S.isIntReviver]})
const observe=(schema,value,options={})=>{try{return {accepted:true,value:S.decodeUnknownSync(schema,options)(value)}}catch{return {accepted:false}}}
const doc=representation=>({representation,references:{}})
const docKeys={identifier:'Example',title:'Example',description:'Fixture',documentation:'Fixture docs',
  examples:['example'],default:'default',message:'bad value',expected:'a string'}
let annotationComparisons=0
function compare(source,target,values) {
  for(const options of [{},{onExcessProperty:'error'}]) for(const value of values) {
    assert.deepEqual(observe(source,value,options),observe(target,value,options))
    annotationComparisons++
  }
}
for(const [key,value] of Object.entries(docKeys)) {
  compare(revive(doc({_tag:'String',checks:[],annotations:{[key]:value}})),actual.DOC_STRING,
    ['ok','',1,null,undefined,{},[]])
}
compare(revive(doc({_tag:'String',checks:[],annotations:docKeys})),actual.DOC_STRING,
  ['ok',42,undefined])
const display={title:'Example',description:'Fixture'}
compare(revive(doc({_tag:'Objects',checks:[],propertySignatures:[{name:'child',
  type:{_tag:'String',checks:[]},isOptional:false,isMutable:false,annotations:display}],indexSignatures:[]})),
  actual.DOC_PROPERTY,[{child:'ok'},{child:3},{},{child:'ok',extra:2}])
compare(revive(doc({_tag:'Arrays',checks:[],elements:[{isOptional:false,type:{_tag:'String',checks:[]},annotations:display}],rest:[]})),
  actual.DOC_ELEMENT,[['ok'],[],[3],['ok','extra']])
compare(revive(doc({_tag:'Number',checks:[{_tag:'Filter',aborted:false,
  representation:{id:'effect/schema/isInt',payload:null},annotations:display}]})),
  actual.DOC_FILTER,[1,0.5,'wrong',Number.MAX_SAFE_INTEGER,Number.MAX_SAFE_INTEGER+1])
const annotationControls={semanticObjectError:expressions.ANNOT_ERROR,
  semanticObjectPreserve:expressions.ANNOT_PRESERVE,checkDisabling:expressions.ANNOT_DISABLE,
  documentationKeys:Object.keys(docKeys),annotationComparisons}

const exports=Object.entries(expressions).filter(([,e])=>e!=='REFUSED').map(([n,e])=>`export const ${n} = ${e};`).join('\n')
writeFileSync(new URL('./generated.ts',import.meta.url),'import * as Schema from "effect/Schema";\n'+exports+'\n')
writeFileSync(new URL('./duplicate-red.ts',import.meta.url),'// Historical malformed output retained only as a rejecting compiler control.\nimport * as Schema from "effect/Schema";\nexport const DUP = Schema.Struct({a: Schema.Number, a: Schema.String});\n')
writeFileSync(new URL('./expressions.json',import.meta.url),JSON.stringify(expressions,null,2)+'\n')
console.log(JSON.stringify({numericControls:numericInputs.map((v,i)=>({input:String(v),nat:natExpected[i],int:intExpected[i]})),
  naturalAliasAgreesOnControls:true,duplicateExpression:expressions.DUP,duplicateFields:'No code emitted; refused',
  checkChildExpression:expressions.CHECK_CHILD,upstreamChildError:nestedError,annotationControls,
  result:'Current semantic-annotation inputs are refused before code emission. Supported generated expressions and documentation-erasure comparisons pass. Historical malformed duplicate output remains a rejecting compiler control.'},null,2))
