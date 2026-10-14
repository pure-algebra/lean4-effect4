"""Build an inspector for the production SVG region and packing specimens."""
import argparse
import json
from pathlib import Path
import xml.etree.ElementTree as ET


PAGE = r'''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Compound graph and packing inspection</title><style>
*{box-sizing:border-box}body{margin:0;background:#15120f;color:#eee8df;font:15px/1.5 system-ui}
main{max-width:1450px;margin:auto;padding:24px}h1{font-size:29px;margin:5px 0}h2{font-size:18px;margin:0}
p{max-width:950px;color:#c3bbae}.eyebrow{font:12px monospace;letter-spacing:.12em;color:#edbd77}
button,select{color:inherit;background:#2c261f;border:1px solid #75644d;border-radius:5px;padding:8px 12px;cursor:pointer}
button[aria-pressed=true]{background:#725531}.controls{display:flex;align-items:center;gap:10px;flex-wrap:wrap;margin:18px 0}
.workspace{display:grid;grid-template-columns:minmax(0,1.6fr) minmax(280px,1fr);gap:18px}
.panel{border:1px solid #504539;border-radius:8px;padding:16px;min-width:0}
.drawing{height:560px;overflow:hidden;position:relative;background:#17140f;border-radius:4px}
.drawing svg{width:100%;height:100%}.drawing.paper{background:#f5f0e6}
#detail{height:280px;margin:12px 0}.stats{font:13px monospace;color:#e4ba7a;margin:12px 0}
#selection{white-space:pre-wrap;font:13px/1.5 monospace;min-height:84px;overflow-wrap:anywhere}
table{width:100%;border-collapse:collapse;font:13px monospace}td,th{text-align:left;padding:8px;border-bottom:1px solid #504539}
.packed{margin-top:18px}.packed .drawing{height:480px}.hint{font-size:13px;color:#aea597}a{color:#edbd77}
@media(max-width:850px){.workspace{grid-template-columns:1fr}.drawing{height:420px}}
</style><main><div class="eyebrow">REGION PROJECTION · PROVENANCE · COMPONENT PACKING</div>
<h1>Compound nodes, with the original graph retained</h1>
<p>Collapse a region before layout. Every original edge remains in the projection record, including hidden internal edges and parallel connections.
Select a node to inspect its members and its boundary connections.</p>
<div class="controls"><label for="case">Display</label><select id="case"></select>
<button id="cycle">Cycle views</button><label for="look">Look</label><select id="look"><option value="dark">Dark</option><option value="paper">Paper</option></select>
<label for="zoom">Detail zoom</label><select id="zoom"><option value="2">2×</option><option value="8" selected>8×</option><option value="20">20×</option></select></div>
<div class="workspace"><section class="panel"><h2 id="title"></h2><div class="stats" id="stats"></div><div id="overview" class="drawing"></div>
<p class="hint" id="description"></p></section><section class="panel"><h2>Node and connection inspection</h2>
<div class="controls"><label for="node">Node</label><select id="node"></select><label for="focus">Focus</label><select id="focus"><option value="node">Node body</option><option value="incoming">Incoming contact</option><option value="outgoing">Outgoing contact</option></select></div>
<div id="detail" class="drawing"></div><div id="contact-status" class="hint"></div><div id="selection"></div><details><summary>All member keys</summary><pre id="members" style="max-height:200px;overflow:auto"></pre></details><p class="hint">Selection follows an original member through collapse and expansion. A newly selected compound uses its first member.</p><p class="hint">A collapsed node shows view adjacency. A path through it does not establish an original path between its members.</p></section></div>
<section class="panel packed"><div class="controls"><h2>Pack independently drawn components</h2><label for="packing">Canvas target</label><select id="packing"></select></div>
<div id="pack-stats" class="stats"></div><div id="packed" class="drawing"></div><a id="packed-file" target="_blank" rel="noopener">Open full-size packed SVG</a>
<p class="hint">Stable shelves pack resolved geometry envelopes with a margin. Components keep their connector geometry. Text ink remains unmeasured.</p></section>
<section class="panel packed"><h2>Measured operation costs</h2><p class="hint">These measurements cover region preparation, edge projection, and rectangle packing. They do not measure full layered layout or browser frame rates.</p>
<pre id="measurements" style="overflow:auto"></pre></section>
<p class="hint">The graph, projection, packing, and SVG output run in Lean. This page selects generated artifacts and inspection crops.
<a href="../advanced-graph-cleanup/motion.html">Advanced flow motion and fork inspection</a></p>
</main><script>
const data=__DATA__;
const byId=id=>document.getElementById(id), caseSelect=byId('case'), packingSelect=byId('packing');
let currentNode=null,selectedMember=null,timer=null;
for(const [i,c] of data.cases.entries())caseSelect.add(new Option(c.title,i));
for(const [i,p] of data.packing.entries())packingSelect.add(new Option(p.title,i));
function insert(id,svg,crop){const el=byId(id);el.innerHTML=svg;el.classList.toggle('paper',byId('look').value==='paper');el.dataset.look=byId('look').value;
const root=el.querySelector('svg');root.dataset.look=byId('look').value;if(crop)root.setAttribute('viewBox',crop.join(' '));}
function inspect(){const c=data.cases[+caseSelect.value],n=c.nodes.find(x=>x.key===currentNode)||c.nodes.find(x=>selectedMember!==null&&x.members.includes(selectedMember))||c.nodes[0];if(!n)return;
currentNode=n.key;if(!n.members.includes(selectedMember))selectedMember=n.members[0]??null;
byId('node').value=n.key;const z=+byId('zoom').value,focus=byId('focus').value;
let cx=(n.bounds[0]+n.bounds[2])/2,cy=(n.bounds[1]+n.bounds[3])/2;
byId('contact-status').textContent='Node body';
if(focus!=='node'){const contact=c.contacts.find(p=>p.item===n.key&&p.side===(focus==='incoming'?'target':'source'));
if(contact){cx=contact.point[0];cy=contact.point[1];byId('contact-status').textContent=focus+' contact';}
else byId('contact-status').textContent='No '+focus+' contact; showing the node body.';}
const w=byId('detail').clientWidth/z,h=byId('detail').clientHeight/z;
insert('detail',c.svg,[cx-w/2,cy-h/2,w,h]);
const boundary=c.edges.filter(e=>!e.hidden&&(e.source===n.key||e.target===n.key));
byId('selection').textContent=n.label+'\n'+n.origin+'\nMembers ('+n.members.length+'): '+n.members.slice(0,12).join(', ')+(n.members.length>12?' …':'')+'\nVisible edge occurrences: '+boundary.map(e=>'#'+e.occurrence+' '+e.key).join(', ');
byId('members').textContent=n.members.join('\n');}
function drawCase(){const c=data.cases[+caseSelect.value];byId('title').textContent=c.title;
byId('node').replaceChildren();for(const n of c.nodes)byId('node').add(new Option(n.label,n.key));
byId('stats').textContent=c.originalNodes+' original nodes → '+c.nodes.length+' visible nodes · '+c.edges.length+' original edges · '+c.edges.filter(e=>e.hidden).length+' hidden internal edges';
byId('description').textContent=c.description;insert('overview',c.svg);inspect();}
function drawPacking(){const p=data.packing[+packingSelect.value];insert('packed',p.svg);
byId('packed-file').href=p.file;
byId('pack-stats').textContent=p.count+' components · '+p.rows+' shelves · '+p.width+' × '+p.height+' logical pixels · '+p.oversize+' oversize items';}
caseSelect.addEventListener('change',drawCase);packingSelect.addEventListener('change',drawPacking);
byId('zoom').addEventListener('change',inspect);byId('focus').addEventListener('change',inspect);
byId('node').addEventListener('change',()=>{currentNode=byId('node').value;inspect()});
byId('look').addEventListener('change',()=>{drawCase();drawPacking()});
byId('overview').addEventListener('click',e=>{const el=e.target.closest('[data-key]');if(el&&data.cases[+caseSelect.value].nodes.some(n=>n.key===el.dataset.key)){currentNode=el.dataset.key;inspect();}});
byId('cycle').addEventListener('click',function(){if(timer){clearInterval(timer);timer=null;this.textContent='Cycle views';}
else{this.textContent='Pause';timer=setInterval(()=>{caseSelect.value=(+caseSelect.value+1)%data.cases.length;drawCase()},1800)}});
byId('measurements').textContent=data.measurements;drawCase();drawPacking();
</script></html>'''


def read_svg(directory: Path, name: str) -> str:
    path = (directory / name).resolve()
    if not path.is_relative_to(directory.resolve()):
        raise ValueError(f"SVG path leaves output directory: {name}")
    source = path.read_text(encoding="utf-8")
    root = ET.fromstring(source)
    if root.tag != "{http://www.w3.org/2000/svg}svg":
        raise ValueError(f"Not an SVG root: {path}")
    return source[source.index("<svg"):]


def measurements(paths: list[Path]) -> str:
    packing: dict[int, list[float]] = {}
    regions = []
    for path in paths:
        for line in path.read_text(encoding="utf-8-sig").splitlines():
            if line.startswith("{"):
                record = json.loads(line)
                if "prepare_ns" in record and "project_ns" in record:
                    regions.append(record)
            cells = line.split(",")
            if len(cells) == 9 and all(x.isdecimal() for x in cells):
                count, repetitions, elapsed = map(int, cells[:3])
                packing.setdefault(count, []).append(elapsed / repetitions / 1_000_000)
    result = []
    if packing:
        result.append("PACKING · input generation + shelf packing + digest")
        for count, times in sorted(packing.items()):
            result.append(f"{count:>7,} rectangles   {min(times):8.3f}–{max(times):.3f} ms per call")
    if regions:
        result.append("\nREGIONS · preparation / projection, including timed input rotation")
        for r in regions:
            result.append(f"{r['vertices']:>7,} vertices / {r['input_edges']:>6,} edges   "
                          f"{r['prepare_ns'] / 1_000_000:8.3f} / {r['project_ns'] / 1_000_000:.3f} ms")
    return "\n".join(result) or "No measurement files supplied."


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path)
    parser.add_argument("--measurements", type=Path, action="append", default=[])
    args = parser.parse_args()
    data = json.loads((args.directory / "manifest.json").read_text(encoding="utf-8"))
    for case in data["cases"] + data["packing"]:
        case["svg"] = read_svg(args.directory, case["file"])
    data["measurements"] = measurements(args.measurements)
    encoded = json.dumps(data, ensure_ascii=False).replace("</", "<\\/")
    css = (args.directory / "look.css").read_text(encoding="utf-8")
    page = PAGE.replace("__DATA__", encoded).replace("</style>", css + "</style>", 1)
    target = args.directory / "index.html"
    target.write_text(page, encoding="utf-8")
    print(f"{target}: {len(data['cases'])} graph views, {len(data['packing'])} packing views")


if __name__ == "__main__":
    main()
