"""Build a local typography study from Lean's program-content and SVG projections."""
import argparse
import json
from pathlib import Path
import xml.etree.ElementTree as ET


PAGE = r'''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Graph leaves · typography and meaning</title>
<link rel="stylesheet" href="look.css"><style>
@font-face{font-family:JetBrains Mono;src:url(/vendor/fonts/jetbrains-mono/jetbrains-mono-latin-wght-normal.woff2);font-weight:100 900}
@font-face{font-family:Source Serif 4;src:url(/vendor/fonts/source-serif-4/source-serif-4-latin-opsz-normal.woff2);font-weight:200 900}
@font-face{font-family:Source Serif 4;src:url(/vendor/fonts/source-serif-4/source-serif-4-latin-opsz-italic.woff2);font-weight:200 900;font-style:italic}
*{box-sizing:border-box}body{--bg:#14110d;--fg:#ece6dc;--muted:#b7ada0;--line:#51493f;--panel:#1d1914;--accent:#e2bb81;
margin:0;background:var(--bg);color:var(--fg);font:15px/1.55 system-ui}
body[data-look=paper]{--bg:#f5f0e6;--fg:#29251e;--muted:#655b4e;--line:#b8aa95;--panel:#eee7da;--accent:#755326}
main{max-width:1480px;margin:auto;padding:26px 30px 50px}.eyebrow{font:11px 'JetBrains Mono',monospace;letter-spacing:.16em;color:var(--muted)}
h1{font:500 38px/1.1 'Source Serif 4',serif;letter-spacing:-.02em;margin:10px 0 12px}h2{font-size:17px;margin:0 0 6px}h3{font-size:14px;margin:0}
p{margin:6px 0 14px;max-width:900px}.subtle{color:var(--muted);font-size:13px}.controls{display:flex;align-items:end;gap:14px;flex-wrap:wrap;margin:20px 0}
label{display:grid;gap:5px;font-size:12px;color:var(--muted)}select,button{background:var(--panel);color:var(--fg);border:1px solid var(--line);border-radius:5px;padding:8px 10px;font:13px system-ui;max-width:100%}
button{cursor:pointer}a{color:var(--accent)}:focus-visible{outline:2px solid var(--accent);outline-offset:4px}
.workspace{display:grid;grid-template-columns:minmax(0,1.25fr) minmax(300px,.85fr);align-items:start;gap:22px}.panel{border:1px solid var(--line);border-radius:7px;min-width:0;padding:18px}
.head{display:flex;align-items:baseline;justify-content:space-between;gap:12px}.tag{font:10px 'JetBrains Mono',monospace;border:1px solid var(--line);border-radius:3px;padding:3px 6px;white-space:nowrap}
.canvas{height:560px;overflow:auto;margin-top:12px}.canvas svg{display:block;width:100%;max-width:calc(var(--svg-width) * 1.5);height:auto;max-height:560px;margin:auto}
.canvas.actual svg{width:var(--svg-width);max-width:none;max-height:none}
.leaf{height:106px;width:100%;overflow:hidden}.leaf svg{display:block;width:100%;height:100%}
.compare{border-top:1px solid var(--line);padding:15px 0 8px}.compare:first-of-type{margin-top:12px}.compare p{margin:0 0 4px}
.leaf svg .e4-text{fill:var(--fg)}
body[data-face=code] .e4-face-name{font-family:'JetBrains Mono',monospace;font-size:13.288px;font-weight:650;font-style:normal}
body[data-face=book] .e4-face-name{font-family:'Source Serif 4',serif;font-size:15px;font-weight:600;font-style:normal}
.e4-face-data{font-variant-ligatures:none}.selected-outline{fill:none;stroke:var(--accent);stroke-width:1.5;stroke-dasharray:4 3;pointer-events:none}
.fields{margin-top:20px;display:grid;gap:12px}.field{display:grid;grid-template-columns:115px minmax(0,1fr);gap:12px;border-top:1px solid var(--line);padding-top:10px}
.field dt{font-size:12px;color:var(--muted)}.field dd{margin:0;overflow-wrap:anywhere;white-space:pre-wrap;font:12px/1.6 'JetBrains Mono',monospace}
.field dd.prose{font-family:system-ui;font-size:13px}.facts{margin-top:22px;display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:24px;border-top:1px solid var(--line);padding-top:20px}
.facts p{font-size:13px;color:var(--muted)}#node{max-width:320px}.empty{font-family:system-ui;color:var(--muted)}.flag{color:var(--accent)}
details{margin-top:18px}summary{cursor:pointer;font-size:13px}pre{white-space:pre-wrap;overflow-wrap:anywhere;font:12px/1.6 'JetBrains Mono',monospace}
@media(max-width:1000px){main{padding:22px 20px}.workspace{grid-template-columns:1fr}.canvas{height:410px}.facts{grid-template-columns:1fr;gap:8px}.compare-grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:16px}.compare{border-top:0}.leaf{height:115px}.compare p{min-height:42px}}
@media(max-width:620px){main{padding:18px 14px}h1{font-size:32px}.compare-grid{grid-template-columns:1fr;gap:0}.compare{border-top:1px solid var(--line)}.compare p{min-height:0}.leaf{height:110px}.field{grid-template-columns:92px minmax(0,1fr)}.canvas{height:380px}.panel{padding:14px}}
</style><body data-look="dark" data-face="code"><main>
<div class="eyebrow">PROGRAM GRAPH / LEAF STUDY 01</div><h1>Read the operation. Inspect its meaning.</h1>
<p class="subtle">Real program structure, with three content treatments. The heading identifies the operation; the second line answers one reading task.
Operand text and typing observations remain beside the selected leaf.</p>
<div class="controls"><label>Program<select id="case"></select></label><label>Graph content<select id="mode"><option value="arguments">Operation + arguments</option><option value="types">Operation + type</option><option value="source">Current labels</option></select></label>
<label>Operation face<select id="face"><option value="code">Code emphasis</option><option value="book">Book face</option></select></label>
<label>Look<select id="look"><option value="dark">Dark</option><option value="paper">Paper</option></select></label><button id="scale" aria-pressed="false">Actual size</button></div>
<div class="workspace"><section class="panel"><div class="head"><h2 id="title"></h2><span class="tag">STATIC STRUCTURE</span></div>
<p class="subtle" id="description"></p><div id="overview" class="canvas"></div><p class="subtle" id="view-status"></p>
<a id="svg-file" target="_blank" rel="noopener">Open generated SVG</a></section>
<section class="panel"><div class="head"><h2>One leaf, three readings</h2><span class="tag">CONTENT COMPARISON</span></div>
<div class="controls"><label>Selected source occurrence<select id="node"></select></label></div>
<div class="compare-grid"><div class="compare"><h3>Current labels</h3><p class="subtle">Operation and arguments above the type.</p><div class="leaf" id="source"></div></div>
<div class="compare"><h3>Operation + arguments</h3><p class="subtle">Identify the step, then read its operand expressions.</p><div class="leaf" id="arguments"></div></div>
<div class="compare"><h3>Operation + type</h3><p class="subtle">Inspect the typing observation at this address.</p><div class="leaf" id="types"></div></div></div>
<dl class="fields" id="fields"></dl><details><summary>Full source label and checker detail</summary><pre id="full-source"></pre></details>
</section></div>
<div class="facts"><section><h2>Typography carries role</h2><p>The exact operation name anchors the leaf. Operand expressions retain their delimiters. Explicit A, E, and R fields separate the type observations.</p></section>
<section><h2>Shape carries structure</h2><p>The production connectors and region boundaries show structural relationships. Text treatment changes box width through the existing layout.</p></section>
<section><h2>State needs evidence</h2><p>A static fail operation is not a failed run. A checker refusal is labeled separately. Selection uses its own dashed outline.</p></section></div>
<details><summary>Source basis and open typography work</summary><p class="subtle">The local semiotics review compares Iverson, Green–Blackwell, Larkin–Simon, Moody, and Lamport.
It supports explicit roles and task-dependent detail. This study does not establish a preferred typeface through a user study.</p>
<p class="subtle">Row clips contain proportional text. Character-based fitting does not measure glyph ink; long labels retain their full text in the inspector.
Semantic piece fitting, binding navigation, and variable-height leaves remain follow-up design questions.</p>
<a href="/docs/research/2026-10-13-graph-semiotics-research.md">Read the local research note</a></details>
</main><script>
const data=__DATA__, $=id=>document.getElementById(id), NS='http://www.w3.org/2000/svg';let selected=null,serial=0;
for(const [i,c]of data.cases.entries())$('case').add(new Option(c.name,i));
const current=()=>data.cases[+$('case').value];
function mount(id,mode,node){const host=$(id), c=current(), frame=c.modes[mode];host.innerHTML=frame.svg;
const svg=host.querySelector('svg');svg.dataset.look=$('look').value;svg.setAttribute('role','img');
const title=document.createElementNS(NS,'title'),desc=document.createElementNS(NS,'desc');
title.id='view-title-'+(++serial);title.textContent=(node?node.ctor:c.name)+' — '+mode;
desc.id='view-desc-'+serial;desc.textContent=node?node.source+'; '+node.typeStatus:c.description+'; static program structure';
svg.prepend(desc);svg.prepend(title);svg.setAttribute('aria-labelledby',title.id);svg.setAttribute('aria-describedby',desc.id);
const ids=new Map();svg.querySelectorAll('[id]').forEach(el=>{if(el===title||el===desc)return;const old=el.id;el.id=id+'-'+serial+'-'+old;ids.set(old,el.id)});
svg.querySelectorAll('*').forEach(el=>{for(const a of [...el.attributes]){let value=a.value;for(const [old,next]of ids)value=value.replaceAll('url(#'+old+')','url(#'+next+')');if(value!==a.value)el.setAttribute(a.name,value)}});
if(node){const p=frame.nodes.find(x=>x.key===node.key),b=p.bounds;
const width=Math.max(...Object.values(c.modes).map(m=>{const v=m.nodes.find(x=>x.key===node.key).bounds;return v[2]-v[0]}))+16;
svg.setAttribute('viewBox',[(b[0]+b[2]-width)/2,b[1]-10,width,b[3]-b[1]+20].join(' '))}
else{host.style.setProperty('--svg-width',frame.width+'px');const p=frame.nodes.find(x=>x.key===selected);if(p){const b=p.bounds,r=document.createElementNS(NS,'rect');for(const [k,v]of Object.entries({x:b[0]-3,y:b[1]-3,width:b[2]-b[0]+6,height:b[3]-b[1]+6,rx:6,class:'selected-outline'}))r.setAttribute(k,v);svg.append(r)}}}
function field(label,value,prose=false){const row=document.createElement('div');row.className='field';const dt=document.createElement('dt'),dd=document.createElement('dd');dt.textContent=label;dd.textContent=value;if(prose)dd.className='prose';row.append(dt,dd);$('fields').append(row)}
function inspect(){const c=current(),n=c.nodes.find(n=>n.key===selected)||c.nodes[0];if(!n)return;selected=n.key;$('node').value=n.key;
for(const mode of ['source','arguments','types'])mount(mode,mode,n);mount('overview',$('mode').value);
$('fields').replaceChildren();field('Source address',n.key);field('Operation',n.ctor);if(n.constructor!==n.ctor)field('Constructor',n.constructor);
field('Arguments',n.args.length?n.args.map((s,i)=>(i+1)+' · '+n.argKinds[i]+': '+s).join('\n'):'No non-child arguments');
field('Typing',n.typeStatus,true);if(n.answer!==null){field('A · answer type',n.answer);field('E · error type',n.error);field('R · requires',n.requires)}
if(n.refusal)field('Checker refusal',n.refusal,true);field('Runtime result','No runtime observation in this view',true);
$('full-source').textContent=n.source+'\n'+(n.typeText||'No displayed effect type')+(n.refusal?'\n'+n.refusal:'');
$('svg-file').href=c.modes[$('mode').value].file;$('view-status').textContent=c.nodes.length+' visible operation occurrences · '+($('scale').getAttribute('aria-pressed')==='true'?'actual logical size':'fitted overview, capped at 1.5×; comparisons use equal scale');}
function draw(){const c=current();$('title').textContent=c.name;$('description').textContent=c.description;$('node').replaceChildren();for(const n of c.nodes)$('node').add(new Option(n.ctor+'  '+n.key,n.key));if(!c.nodes.some(n=>n.key===selected))selected=c.nodes.find(n=>n.ctor==='awaitFiber')?.key||c.nodes[0]?.key;inspect()}
$('case').addEventListener('change',()=>{selected=null;draw()});$('node').addEventListener('change',()=>{selected=$('node').value;inspect()});$('mode').addEventListener('change',inspect);
$('face').addEventListener('change',()=>document.body.dataset.face=$('face').value);$('look').addEventListener('change',()=>{document.body.dataset.look=$('look').value;inspect()});
$('scale').addEventListener('click',()=>{const on=$('scale').getAttribute('aria-pressed')!=='true';$('scale').setAttribute('aria-pressed',on);$('overview').classList.toggle('actual',on);inspect()});
$('overview').addEventListener('click',e=>{const key=e.target.closest('[data-key]')?.dataset.key;if(current().nodes.some(n=>n.key===key)){selected=key;inspect()}});draw();
</script></body></html>'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    directory = args.directory.resolve()
    data = json.loads((directory / 'manifest.json').read_text(encoding='utf-8'))
    for case in data['cases']:
        for frame in case['modes'].values():
            path = (directory / frame['file']).resolve()
            if not path.is_relative_to(directory):
                raise ValueError('SVG path leaves the output directory')
            svg = path.read_text(encoding='utf-8')
            root = ET.fromstring(svg)
            if root.tag != '{http://www.w3.org/2000/svg}svg':
                raise ValueError('Expected SVG root')
            if frame['width'] <= 0 or frame['height'] <= 0:
                raise ValueError('Expected positive dimensions')
            frame['svg'] = svg
    payload = json.dumps(data, ensure_ascii=False).replace('<', '\\u003c')
    (directory / 'index.html').write_text(PAGE.replace('__DATA__', payload), encoding='utf-8')
    print(f"leaf-study: {len(data['cases'])} programs, {sum(len(c['modes']) for c in data['cases'])} checked SVG inputs")


if __name__ == '__main__':
    main()
