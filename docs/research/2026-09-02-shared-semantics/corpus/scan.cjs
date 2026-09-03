const fs=require('fs'),path=require('path'),crypto=require('crypto');
const ts=require('/Users/pooks/Dev/foldlab/experiments/lift-harness/node_modules/typescript/lib/typescript.js');
const inv=JSON.parse(fs.readFileSync(process.env.Q9_INVENTORY||'/tmp/effect-q9-research/inventory.json','utf8'));
const root=inv.root, repos=inv.repos.filter(r=>r.listed), hash=crypto.createHash('sha256');
const calls=[], refs=[], gens=[], files=[], errors=[], imports=[], aliasHits=[];
const config={target:ts.ScriptTarget.Latest,noLib:true,noResolve:true,skipLibCheck:true,allowJs:false};
const modules=new Set(['Effect','Layer','Scope']);
function imported(spec,name){
  if(spec==='effect') return modules.has(name)?name:null;
  const m=spec.match(/^(?:effect|@effect\/io)\/(Effect|Layer|Scope)$/);
  if(m) return name==='*'?m[1]:m[1]+'.'+name;
  if(spec==='@effect/io') return modules.has(name)?name:null;
  return null;
}
function group(key){
  if(key.split('.').length!==2)return null;
  if(key.startsWith('Layer.')) return 'Layer';
  if(key.startsWith('Scope.')) return 'Scope-module';
  if(!key.startsWith('Effect.')) return null;
  let k=key.slice(7);
  if(/^fork/.test(k)) return 'fork';
  if(/^race/.test(k)) return 'race';
  if(/^catch/.test(k)) return 'catch';
  if(['scoped','acquireRelease','acquireUseRelease','acquireReleaseInterruptible','addFinalizer','ensuring','onExit','onInterrupt'].includes(k)) return 'resource';
  if(k==='gen') return 'gen';
  return null;
}
function loc(sf,n){let l=sf.getLineAndCharacterOfPosition(n.getStart(sf));return [l.line+1,l.character+1]}
function loop(n){return ts.isForStatement(n)||ts.isForOfStatement(n)||ts.isForInStatement(n)||ts.isWhileStatement(n)||ts.isDoStatement(n)}
function fn(n){return ts.isFunctionLike(n)}
function strip(n){while(n&&(ts.isParenthesizedExpression(n)||ts.isAsExpression(n)||ts.isTypeAssertionExpression(n)||ts.isNonNullExpression(n)||ts.isSatisfiesExpression(n)))n=n.expression;return n}
for(const repo of repos){
  let done=0;
  for(const rel of repo.analysis_files){
    const full=path.join(root,repo.repo,rel), data=fs.readFileSync(full),text=data.toString('utf8');
    hash.update(repo.repo+'/'+rel+'\0'+crypto.createHash('sha256').update(data).digest('hex')+'\n');
    const sf=ts.createSourceFile(full,text,ts.ScriptTarget.Latest,true,rel.endsWith('.tsx')?ts.ScriptKind.TSX:ts.ScriptKind.TS);
    const row={repo:repo.repo,file:rel,bytes:data.length,parseErrors:sf.parseDiagnostics.length,lexical:{}};
    for(const m of text.matchAll(/\b(Effect|Layer|Scope)\s*\.\s*([A-Za-z_$][\w$]*)/g)){const k=m[1]+'.'+m[2];row.lexical[k]=(row.lexical[k]||0)+1}
    files.push(row);
    if(sf.parseDiagnostics.length){errors.push({repo:repo.repo,file:rel,diagnostics:sf.parseDiagnostics.map(d=>({start:d.start,message:ts.flattenDiagnosticMessageText(d.messageText,' ')}))});continue}
    const imps=sf.statements.filter(ts.isImportDeclaration).filter(s=>ts.isStringLiteral(s.moduleSpecifier)&&(/^(effect(?:\/|$)|@effect\/io(?:\/|$))/.test(s.moduleSpecifier.text)));
    if(!imps.length)continue;
    const host={getSourceFile:f=>f===full?sf:undefined,writeFile(){},getCurrentDirectory:()=>root,getDirectories:()=>[],getCanonicalFileName:f=>f,useCaseSensitiveFileNames:()=>true,getNewLine:()=> '\n',fileExists:f=>f===full,readFile:f=>f===full?text:undefined,getDefaultLibFileName:()=>''};
    const program=ts.createProgram([full],config,host),checker=program.getTypeChecker(), bindings=new Map();
    for(const im of imps){
      const spec=im.moduleSpecifier.text, c=im.importClause;
      if(!c||c.isTypeOnly)continue;
      const b=c.namedBindings;
      if(!b) continue;
      if(ts.isNamespaceImport(b)){
        const v=spec==='effect'||spec==='@effect/io'?'@package':imported(spec,'*');
        if(v){bindings.set(checker.getSymbolAtLocation(b.name),v);imports.push({repo:repo.repo,file:rel,source:spec,local:b.name.text,imported:'*',canonical:v})}
      } else for(const e of b.elements){
        if(e.isTypeOnly)continue;
        const v=imported(spec,(e.propertyName||e.name).text);
        if(v){bindings.set(checker.getSymbolAtLocation(e.name),v);imports.push({repo:repo.repo,file:rel,source:spec,local:e.name.text,imported:(e.propertyName||e.name).text,canonical:v})}
      }
    }
    if(!bindings.size)continue;
    const memo=new Map();
    function resolve(expr,depth=0){
      expr=strip(expr);if(!expr||depth>10)return null;
      if(ts.isIdentifier(expr)){
        const s=checker.getSymbolAtLocation(expr);if(!s)return null;
        if(bindings.has(s))return bindings.get(s);
        if(memo.has(s))return memo.get(s);
        memo.set(s,null);
        const d=s.valueDeclaration;
        let v=null;
        if(d&&ts.isVariableDeclaration(d)&&d.initializer&&(d.parent.flags&ts.NodeFlags.Const)) v=resolve(d.initializer,depth+1);
        else if(d&&ts.isBindingElement(d)&&!d.dotDotDotToken&&!d.initializer&&ts.isObjectBindingPattern(d.parent)&&ts.isVariableDeclaration(d.parent.parent)&&d.parent.parent.initializer&&(d.parent.parent.parent.flags&ts.NodeFlags.Const)){
          const base=resolve(d.parent.parent.initializer,depth+1), k=(d.propertyName||d.name).text;
          if(base&&k)v=base==='@package'?(modules.has(k)?k:null):base+'.'+k;
        }
        memo.set(s,v);return v;
      }
      if(ts.isPropertyAccessExpression(expr)||ts.isElementAccessExpression(expr)){
        const b=resolve(expr.expression,depth+1);if(!b)return null;
        const k=ts.isPropertyAccessExpression(expr)?expr.name.text:ts.isStringLiteralLike(expr.argumentExpression)?expr.argumentExpression.text:null;
        if(!k)return null;
        return b==='@package'?(modules.has(k)?k:null):b+'.'+k;
      }
      return null;
    }
    function valuePosition(n){
      for(let p=n.parent;p;p=p.parent){if(ts.isExpression(p)||ts.isStatement(p)&&!ts.isImportDeclaration(p))break;if(ts.isTypeNode(p)||ts.isImportDeclaration(p))return false}
      if(ts.isIdentifier(n)){
        const p=n.parent;
        if((ts.isPropertyAccessExpression(p)&&p.name===n)||(ts.isElementAccessExpression(p)&&p.argumentExpression===n)||
           ((ts.isVariableDeclaration(p)||ts.isParameter(p)||ts.isBindingElement(p)||ts.isFunctionDeclaration(p)||ts.isPropertyAssignment(p)||ts.isPropertyDeclaration(p)||ts.isMethodDeclaration(p))&&p.name===n))return false;
      }
      return true;
    }
    const fileGen=[];
    function visit(n){
      if(ts.isCallExpression(n)){
        const k=resolve(n.expression), g=k&&group(k);
        if(g){const [line,column]=loc(sf,n);const c={repo:repo.repo,file:rel,line,column,op:k,group:g};calls.push(c);
          if(k==='Effect.gen'){
            const generator=n.arguments.map(strip).find(a=>ts.isFunctionExpression(a)&&a.asteriskToken&&a.body);
            const e={...c,start:n.pos,end:n.end,inline:!!generator,lexicalNested:0,nestingDepth:0};
            fileGen.push({entry:e,node:n,generator});gens.push(e);
          }
        }
      }
      if((ts.isIdentifier(n)||ts.isPropertyAccessExpression(n)||ts.isElementAccessExpression(n))&&valuePosition(n)){
        const k=resolve(n),g=k&&group(k);
        if(g){const [line,column]=loc(sf,n);refs.push({repo:repo.repo,file:rel,line,column,op:k,group:g});
          if(!n.getText(sf).startsWith(k))aliasHits.push({repo:repo.repo,file:rel,line,spelling:n.getText(sf),op:k});
        }
      }
      ts.forEachChild(n,visit);
    }
    visit(sf);
    for(const {entry,node,generator}of fileGen){
      entry.nestingDepth=fileGen.filter(q=>q.generator&&q.generator.body.pos<node.pos&&q.generator.body.end>node.end).length;
      if(!generator)continue;
      entry.lexicalNested=fileGen.filter(q=>q.node.pos>generator.body.pos&&q.node.end<generator.body.end).length;
      entry.direct={loops:0,loopKinds:{},ifs:0,switches:0,tries:0,finally:0,breaks:0,continues:0,labeledBreaks:0,labeledContinues:0,yields:0,throws:0,returns:0,functions:0,loopYield:0};
      entry.lexical={loops:0,ifs:0,functions:0};
      function lex(n){if(loop(n))entry.lexical.loops++;if(ts.isIfStatement(n))entry.lexical.ifs++;if(fn(n))entry.lexical.functions++;ts.forEachChild(n,lex)}
      lex(generator.body);
      function direct(n,ld=0){
        const d=entry.direct;
        if(fn(n)){d.functions++;return}
        if(loop(n)){d.loops++;const kind=ts.SyntaxKind[n.kind];d.loopKinds[kind]=(d.loopKinds[kind]||0)+1;ld++}
        if(ts.isIfStatement(n))d.ifs++;
        if(ts.isSwitchStatement(n))d.switches++;
        if(ts.isTryStatement(n)){d.tries++;if(n.finallyBlock)d.finally++}
        if(ts.isBreakStatement(n)){d.breaks++;if(n.label)d.labeledBreaks++}
        if(ts.isContinueStatement(n)){d.continues++;if(n.label)d.labeledContinues++}
        if(ts.isYieldExpression(n)){d.yields++;if(ld)d.loopYield++}
        if(ts.isThrowStatement(n))d.throws++;
        if(ts.isReturnStatement(n))d.returns++;
        ts.forEachChild(n,c=>direct(c,ld));
      }
      direct(generator.body);
    }
    done++;
  }
  process.stdout.write(repo.repo+' '+repo.analysis_files.length+' files; '+done+' with resolved imports\n');
}
const out={method:'tracked .ts/.tsx/.mts/.cts; declarations excluded; tim-smart_lalph/repos/effect excluded; all 30 present .pins.tsv repos; TS local symbol binding no dependencies or typecheck',typescript:ts.version,sourceDigest:hash.digest('hex'),repoPinDigest:inv.selected_repo_pins_sha256,files,calls,refs,gens,errors,imports,aliasHits};
fs.writeFileSync(process.env.Q9_OUTPUT||'/tmp/effect-q9-research/scan.json',JSON.stringify(out)+'\n');
process.stdout.write(JSON.stringify({files:files.length,calls:calls.length,refs:refs.length,gens:gens.length,parseErrorFiles:errors.length,importedFiles:new Set(imports.map(i=>i.repo+'/'+i.file)).size,sourceDigest:out.sourceDigest})+'\n');
