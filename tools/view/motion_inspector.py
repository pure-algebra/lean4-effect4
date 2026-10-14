#!/usr/bin/env python3
"""Build a self-contained motion inspector from actual emitted graph SVG frames.

  python tools/view/motion_inspector.py SEQUENCE_ROOT --out motion.html
  python tools/view/motion_inspector.py AFTER --compare BEFORE --out motion.html
  python tools/view/motion_inspector.py --self-test

A sequence directory contains SVGs and look.css or the existing player index.html.
Optional motion.json supplies title, description, overview, and ordered frames
[{name, label, time_ms}]. Without it, the existing player's pics order is used.
An input root may contain several sequence directories. Contacts come from the
actual final connector caps. Crops change viewports, never source path data.
Only trusted local generated SVGs belong to this inspection tool.
"""

import argparse
import json
import math
from pathlib import Path
import re
import sys
import xml.etree.ElementTree as ET

from check_connectors import cubic_contours, keyed_paths
from inspect_svg import PAGE as CONTACT_PAGE, load_directory


KINDS = ("fork", "join", "node")


def node_keys(text):
    """A painted node owns its ground shape; bars and dummy ports do not."""
    keys = set()

    def walk(element, key=""):
        key = element.get("data-key", key)
        if key and key != "ground" and element.tag.rsplit("}", 1)[-1] in ("path", "rect") and \
                "e4-fill-ground" in element.get("class", "").split():
            keys.add(key)
        for child in element:
            walk(child, key)

    walk(ET.fromstring(text))
    return keys


def contacts(text):
    """Read surface-cut centres from the emitted two-side contour format."""
    found = {}
    nodes = node_keys(text)
    for key, paths in keyed_paths(ET.fromstring(text)).items():
        # Legacy comparisons can have collars after the body. Read its first body.
        for path_index, data in paths:
            try:
                contours = cubic_contours(data)
            except ValueError:
                continue
            if len(contours) != 1:
                continue
            cs = contours[0].cubics
            if len(cs) < 6 or len(cs) % 2:
                continue
            n = len(cs) // 2 - 1
            source, target = key.split("→", 1)
            for side, endpoint, cap in (("source", source, cs[-1]), ("target", target, cs[n])):
                centre = [float((cap[0][axis] + cap[3][axis]) / 2) for axis in range(2)]
                kind = "fork" if re.search(r"/fork(?:/|$)", endpoint) else \
                    "join" if re.search(r"/(?:join|end)(?:/|$)", endpoint) else \
                    "node" if endpoint in nodes else "pass"
                identity = key + "::" + side
                found[identity] = {"id": identity, "kind": kind, "key": key, "side": side,
                                   "label": f"{side} {endpoint}", "point": centre,
                                   "path": path_index, "cubics": len(cs)}
            break
    return found


def finite_view(value):
    return isinstance(value, list) and len(value) == 4 and \
        all(isinstance(x, (float, int)) and not isinstance(x, bool) and math.isfinite(x) for x in value) and \
        value[2] > 0 and value[3] > 0


def order_frames(frames, manifest=None, player=""):
    by_name = {frame["name"]: frame for frame in frames}
    if manifest and "frames" in manifest:
        rows = manifest["frames"]
    else:
        match = re.search(r"const pics\s*=\s*(\[.*?\]);", player, re.S)
        if match:
            rows = [{"name": row[0] + ".svg"} for row in json.loads(match.group(1))]
        else:
            rows = [{"name": frame["name"]} for frame in frames]
    if not isinstance(rows, list) or not rows:
        raise ValueError("empty or invalid frame sequence")
    names = [row.get("name") for row in rows]
    if len(set(names)) != len(names) or set(names) != set(by_name):
        raise ValueError("sequence must name every input SVG exactly once")
    out, previous = [], -1.0
    for index, row in enumerate(rows):
        time = row.get("time_ms", index * 1000 / 30)
        if not isinstance(time, (int, float)) or isinstance(time, bool) or not math.isfinite(time) or time < 0:
            raise ValueError("frame time must be a finite nonnegative number")
        if time <= previous:
            raise ValueError("frame times must increase strictly")
        frame = dict(by_name[row["name"]])
        frame.update(label=str(row.get("label", row["name"])), time_ms=time,
                     contacts=contacts(frame["text"]))
        # The inspector uses keyed contacts instead of the generic endpoint menu.
        frame.pop("features", None)
        out.append(frame)
        previous = time
    # Final geometry owns classification when earlier samples have no node body yet.
    final_kinds = {identity: contact["kind"] for identity, contact in out[-1]["contacts"].items()}
    for frame in out:
        for identity, contact in frame["contacts"].items():
            contact["kind"] = final_kinds.get(identity, "pass")
    return out


def sequence(directory):
    css = next((p for p in (directory / "look.css", directory.parent / "look.css") if p.exists()), None)
    data = load_directory(directory, css)
    manifest_file = directory / "motion.json"
    manifest = json.loads(manifest_file.read_text(encoding="utf-8")) if manifest_file.exists() else {}
    if not isinstance(manifest, dict):
        raise ValueError(f"{directory}: motion.json must be an object")
    player_file = directory / "index.html"
    player = player_file.read_text(encoding="utf-8") if player_file.exists() else ""
    data["frames"] = order_frames(data["frames"], manifest, player)
    data["title"] = str(manifest.get("title", directory.name))
    data["description"] = str(manifest.get("description", "Recorded rendering samples; no runtime execution claim."))
    view = manifest.get("overview", data["frames"][-1]["view"])
    if not finite_view(view):
        raise ValueError(f"{directory}: invalid overview viewport")
    data["overview"] = view
    data["choices"] = [c for c in data["frames"][-1]["contacts"].values() if c["kind"] in KINDS]
    if not data["choices"]:
        raise ValueError(f"{directory}: final frame has no selected connector contacts")
    return data


def directories(inputs):
    out = []
    for directory in inputs:
        if any(directory.glob("*.svg")):
            out.append(directory)
        else:
            children = [p for p in sorted(directory.iterdir()) if p.is_dir() and any(p.glob("*.svg"))]
            if not children:
                raise ValueError(f"{directory}: no SVG sequence directories")
            out.extend(children)
    if len({directory.name for directory in out}) != len(out):
        raise ValueError("sequence directory names must be distinct")
    priority = ["nested-forks", "wide-race", "race-loop", "await-all", "nested-scopes", "handler-scope"]
    return sorted(out, key=lambda p: (priority.index(p.name) if p.name in priority else len(priority), p.name))


def payload_for(inputs, compare=None, label="Production", compare_label="Comparison"):
    scenes = []
    for directory in directories(inputs):
        primary = sequence(directory)
        variants = [{"role": label, **primary}]
        if compare:
            baseline_dir = compare / directory.name if (compare / directory.name).is_dir() else compare
            baseline = sequence(baseline_dir)
            if [f["name"] for f in primary["frames"]] != [f["name"] for f in baseline["frames"]]:
                raise ValueError(f"{directory.name}: comparison frame sequences differ")
            if [f["time_ms"] for f in primary["frames"]] != [f["time_ms"] for f in baseline["frames"]]:
                raise ValueError(f"{directory.name}: comparison frame times differ")
            variants.append({"role": compare_label, **baseline})
        scenes.append({"id": directory.name, "title": primary["title"],
                       "description": primary["description"], "choices": primary["choices"], "variants": variants})
    return {"scenes": scenes}


def svg_helpers():
    """Reuse the existing inspector's ID isolation and unchanged-path embedding."""
    return CONTACT_PAGE[CONTACT_PAGE.index("const urlRefs="):CONTACT_PAGE.index("function sync()")]


PAGE = r'''<!doctype html>
<html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Graph motion inspector</title><style>
*{box-sizing:border-box}body{margin:0;background:#17191d;color:#edf0f5;font:14px system-ui}
header{padding:18px 20px 12px;border-bottom:1px solid #454b56}h1{font-size:24px;margin:0 0 6px}
p{margin:4px 0 10px;max-width:105ch;color:#c8ced8}.controls{display:flex;flex-wrap:wrap;align-items:center;gap:8px 14px;margin-top:12px}
button,select,input{font:inherit}button,select{background:#252932;color:#edf0f5;border:1px solid #6d7889;border-radius:5px;padding:5px 9px}
button{cursor:pointer}button:focus-visible,select:focus-visible,input:focus-visible{outline:2px solid #f2bd68;outline-offset:2px}
label{display:inline-flex;align-items:center;gap:6px}#scrub{flex:1 1 260px;accent-color:#f2bd68}#position{font:13px monospace;min-width:19ch}
main{padding:16px 20px}.variants{display:grid;grid-template-columns:repeat(auto-fit,minmax(min(100%,340px),1fr));gap:12px}
.crops{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:12px;margin-top:16px}.card{min-width:0;border:1px solid #454b56;border-radius:7px;padding:10px;background:#1d2026}
h2{font-size:15px;margin:0 0 9px}.card select{width:100%;min-width:0;margin-bottom:8px;font-size:12px}.card input[type=number]{width:72px}
.crop-controls{display:flex;flex-wrap:wrap;gap:6px;font-size:12px;margin-bottom:8px}.crop-controls button{padding:3px 7px}
.caption{font:12px monospace;color:#c8ced8;margin:7px 0 0;overflow-wrap:anywhere}.active{border-color:#f2bd68}
.host{display:block;min-width:0}.overview-host{min-height:300px}.crop-host{min-height:240px}.role{display:block;font-size:12px;color:#c8ced8;margin:2px 0 7px}
details{margin-top:12px}summary{cursor:pointer}pre{white-space:pre-wrap;overflow-wrap:anywhere;font-size:11px;color:#c8ced8}
#failure{color:#ffc2bc;white-space:pre-wrap}footer{padding:10px 20px 20px;color:#c8ced8;font-size:12px}
@media(max-width:850px){.crops{grid-template-columns:1fr}.overview-host{min-height:250px}header,main{padding-left:12px;padding-right:12px}h1{font-size:21px}}
</style><header><h1>Advanced graph flows in motion</h1><p id="description"></p>
<div class="controls"><label>Flow <select id="scene" aria-label="Flow"></select></label>
<button id="play">Play reveal</button><button id="back" aria-label="Previous sample">◀</button><button id="next" aria-label="Next sample">▶</button>
<button id="first">Start</button><button id="last">End</button><span id="position" aria-live="polite"></span>
<label>Speed <select id="speed"><option value="0.25">¼×</option><option value="0.5" selected>½×</option><option value="1">1×</option><option value="2">2×</option></select></label>
<label><input id="loop" type="checkbox" checked>Loop</label><label>Look <select id="look"><option value="dark">Dark</option><option value="paper">Paper</option></select></label>
<label>Detail zoom <select id="zoom"><option value="4">4×</option><option value="8" selected>8×</option><option value="20">20×</option></select></label></div>
<div class="controls"><input id="scrub" type="range" min="0" step="1" aria-label="Motion sample"><span id="sampleLabel"></span></div>
</header><main><section aria-label="Full graph"><h2>Full graph · click to centre the selected close-up</h2><div id="overview" class="variants"></div></section>
<section id="crops" class="crops" aria-label="Synchronized close-ups"></section><p id="failure" role="alert"></p>
<details><summary>Frame geometry and source</summary><pre id="geometry"></pre></details></main>
<footer>One emitted frame drives every view. Close-ups change the viewport; source SVG paths stay unchanged. Keyboard: Space pauses or plays, arrows step, Home/End freeze the endpoints.</footer>
<script id="payload" type="application/json">__PAYLOAD__</script><script>
'use strict';
const payload=JSON.parse(document.getElementById('payload').textContent),$=id=>document.getElementById(id);
const state={scene:0,index:0,look:'dark',zoom:8,active:0,panels:[],playing:false,mediaTime:0};
let serial=0,raf=0,origin=0,mediaOrigin=0,views=[];
__SVG_HELPERS__
const current=()=>payload.scenes[state.scene],frames=()=>current().variants[0].frames;
const byId=(id)=>current().choices.find(c=>c.id===id);
const centreCrop=(p,w=288/state.zoom,h=288/state.zoom)=>[p[0]-w/2,p[1]-h/2,w,h];
function zoomCrop(crop,previous,next){
 const w=crop[2]*previous/next,h=crop[3]*previous/next;
 return [crop[0]+(crop[2]-w)/2,crop[1]+(crop[3]-h)/2,w,h];
}
function mount(parent,variant,panel){
 const wrap=document.createElement('div'),label=document.createElement('span');label.className='role';label.textContent=variant.role+' · '+variant.title;wrap.append(label);
 const host=document.createElement('div');host.className='host '+(panel===null?'overview-host':'crop-host');host.dataset.role=variant.role;wrap.append(host);parent.append(wrap);
 const shadow=host.attachShadow({mode:'open'}),style=document.createElement('style');style.textContent=`
 :host{display:block}.viewport{overflow:auto;overflow-anchor:none;background:#fff;border-radius:3px}.viewport svg{display:block;max-width:none}
 .full{height:300px}.full svg{width:100%;height:100%}.detail{max-height:320px;min-height:240px}
 @media(max-width:850px){.full{height:250px}}`;
 shadow.append(style);const viewport=document.createElement('div');viewport.className='viewport '+(panel===null?'full':'detail');shadow.append(viewport);
 views.push({variant,panel,host,viewport});
}
function setup(){
 pause();views=[];$('overview').replaceChildren();$('crops').replaceChildren();const scene=current();
 $('description').textContent=scene.title+' · '+scene.description;$('scene').value=state.scene;
 state.index=frames().length-1;state.panels=[];$('scrub').max=state.index;
 scene.variants.forEach(v=>mount($('overview'),v,null));
 ['fork','join','node'].forEach((kind,index)=>{
  const choices=scene.choices.filter(c=>c.kind===kind),pool=choices.length?choices:scene.choices;
  const chosen=pool[0],card=document.createElement('section');card.className='card';card.dataset.panel=index;
  const title=document.createElement('h2');title.textContent=(index+1)+'. '+kind[0].toUpperCase()+kind.slice(1)+' contact';card.append(title);
  const selector=document.createElement('select');selector.setAttribute('aria-label',kind+' close-up contact');
  pool.forEach(c=>selector.add(new Option(c.label+' · '+c.key,c.id)));card.append(selector);
  const toolbar=document.createElement('div');toolbar.className='crop-controls';card.append(toolbar);
  const follow=document.createElement('input');follow.type='checkbox';const fl=document.createElement('label');fl.append(follow,' Follow visible endpoint');toolbar.append(fl);
  const focus=document.createElement('button');focus.textContent='Select crop';focus.onclick=()=>{state.active=index;updateActive();};toolbar.append(focus);
  const inputs=[];['x','y','w','h'].forEach((name,i)=>{const input=document.createElement('input');input.type='number';input.step='any';input.setAttribute('aria-label',kind+' crop '+name);if(i>1)input.min='0.01';inputs.push(input);});
  const coords=document.createElement('div');coords.className='crop-controls';coords.append(...inputs);const apply=document.createElement('button');apply.textContent='Apply';coords.append(apply);card.append(coords);
  const pair=document.createElement('div');pair.className='variants';card.append(pair);scene.variants.forEach(v=>mount(pair,v,index));
  const caption=document.createElement('p');caption.className='caption';card.append(caption);$('crops').append(card);
  const panel={kind,id:chosen.id,crop:centreCrop(chosen.point),follow:false,inputs,caption,card};state.panels.push(panel);
  selector.onchange=()=>{panel.id=selector.value;panel.crop=centreCrop(byId(panel.id).point,panel.crop[2],panel.crop[3]);render();};
  follow.onchange=()=>{panel.follow=follow.checked;render();};
  apply.onclick=()=>{const values=inputs.map(i=>Number(i.value));if(values.every(Number.isFinite)&&values[2]>0&&values[3]>0){panel.crop=values;panel.follow=false;follow.checked=false;render();}else $('failure').textContent='Use finite crop coordinates and positive sizes.';};
  if(!choices.length)title.textContent+=' · no '+kind+' port; choose another endpoint';
 });
 updateActive();render();
}
function updateActive(){state.panels.forEach((p,i)=>p.card.classList.toggle('active',i===state.active));}
function render(){
 try{
  const scene=current(),primary=frames()[state.index];$('failure').textContent='';$('scrub').value=state.index;
  $('position').textContent='sample '+(state.index+1)+' / '+frames().length;$('sampleLabel').textContent=primary.label;
  document.querySelector('main').dataset.frame=primary.name;document.querySelector('main').dataset.scene=scene.id;
  state.panels.forEach(p=>{const actual=primary.contacts[p.id];if(p.follow&&actual)p.crop=centreCrop(actual.point,p.crop[2],p.crop[3]);p.inputs.forEach((el,i)=>el.value=+p.crop[i].toFixed(4));
   p.caption.textContent=byId(p.id).key+' · '+(actual?'emitted path '+actual.path+', '+actual.cubics+' cubics':'not emitted in this sample')+' · crop '+p.crop.map(x=>+x.toFixed(3)).join(' ');});
  for(const view of views){
   const frame=view.variant.frames[state.index],crop=view.panel===null?view.variant.overview:state.panels[view.panel].crop;
   const signature=JSON.stringify([state.zoom,...crop]),left=view.viewport.scrollLeft,top=view.viewport.scrollTop;
   const svg=svgFor(frame,view.variant,state.look,crop);view.viewport.replaceChildren(svg);view.host.dataset.frame=frame.name;
   if(view.panel!==null&&view.cropSignature!==signature){
    view.viewport.scrollLeft=Math.max(0,(view.viewport.scrollWidth-view.viewport.clientWidth)/2);
    view.viewport.scrollTop=Math.max(0,(view.viewport.scrollHeight-view.viewport.clientHeight)/2);
   }else{view.viewport.scrollLeft=left;view.viewport.scrollTop=top;}
   view.cropSignature=signature;
   view.viewport.style.background=getComputedStyle(svg).getPropertyValue('--e4-color-ground').trim()||'transparent';
   if(view.panel===null){svg.addEventListener('click',e=>{const point=new DOMPoint(e.clientX,e.clientY).matrixTransform(svg.getScreenCTM().inverse()),p=state.panels[state.active];p.crop=centreCrop([point.x,point.y],p.crop[2],p.crop[3]);p.follow=false;p.card.querySelector('input[type=checkbox]').checked=false;render();});}
   else svg.addEventListener('mousemove',e=>{const point=new DOMPoint(e.clientX,e.clientY).matrixTransform(svg.getScreenCTM().inverse());view.host.title='SVG '+point.x.toFixed(3)+', '+point.y.toFixed(3);});
  }
  $('geometry').textContent=scene.variants.map(v=>{const f=v.frames[state.index];return v.role+' · '+v.label+'\n'+f.name+' · '+f.label+' · time '+f.time_ms+' ms\n'+f.paths+' paths · '+f.ids+' IDs · '+f.refs+' local references\nSHA256 '+f.sha256;}).join('\n\n');
 }catch(error){pause();$('failure').textContent=error.stack;throw error;}
}
function pause(){state.playing=false;cancelAnimationFrame(raf);$('play').textContent='Play reveal';}
function show(index){pause();state.index=Math.max(0,Math.min(frames().length-1,index));state.mediaTime=frames()[state.index].time_ms;render();}
function play(){
 if(state.playing){pause();return;}if(state.index===frames().length-1)state.index=0;
 state.playing=true;origin=performance.now();mediaOrigin=frames()[state.index].time_ms;state.mediaTime=mediaOrigin;$('play').textContent='Pause';render();raf=requestAnimationFrame(tick);
}
function tick(now){
 if(!state.playing)return;const fs=frames(),tail=fs.length>1?fs[fs.length-1].time_ms-fs[fs.length-2].time_ms:33;
 let target=mediaOrigin+(now-origin)*Number($('speed').value),index=state.index;
 if(target>fs[fs.length-1].time_ms+tail){if(!$('loop').checked){show(fs.length-1);return;}origin=now;mediaOrigin=fs[0].time_ms;target=mediaOrigin;index=0;}
 while(index+1<fs.length&&fs[index+1].time_ms<=target)index++;state.mediaTime=target;if(index!==state.index){state.index=index;render();}
 raf=requestAnimationFrame(tick);
}
payload.scenes.forEach((s,i)=>$('scene').add(new Option(s.title,String(i))));
$('scene').onchange=()=>{state.scene=Number($('scene').value);setup();};$('play').onclick=play;
$('back').onclick=()=>show(state.index-1);$('next').onclick=()=>show(state.index+1);$('first').onclick=()=>show(0);$('last').onclick=()=>show(frames().length-1);
$('scrub').oninput=()=>show(Number($('scrub').value));$('look').onchange=()=>{state.look=$('look').value;render();};$('zoom').onchange=()=>{const next=Number($('zoom').value);state.panels.forEach(p=>p.crop=zoomCrop(p.crop,state.zoom,next));state.zoom=next;render();};
$('speed').onchange=()=>{if(state.playing){origin=performance.now();mediaOrigin=state.mediaTime;}};
document.addEventListener('keydown',e=>{if(e.target.closest('input,select,button'))return;if(e.code==='Space'){e.preventDefault();play();}else if(e.key==='ArrowLeft'){e.preventDefault();show(state.index-1);}else if(e.key==='ArrowRight'){e.preventDefault();show(state.index+1);}else if(e.key==='Home'){e.preventDefault();show(0);}else if(e.key==='End'){e.preventDefault();show(frames().length-1);}});
setup();
</script></html>'''


def page_text(payload):
    encoded = json.dumps(payload, ensure_ascii=True, separators=(",", ":")).replace("<", "\\u003c").replace("&", "\\u0026")
    return PAGE.replace("__PAYLOAD__", encoded).replace("__SVG_HELPERS__", svg_helpers())


def self_test():
    svg = '<svg xmlns="http://www.w3.org/2000/svg" width="10" height="10"><g data-key="x/fork/0→y/join/0"><path class="e4-fill-ink" d="M0,0C0,1 0,2 0,3C0,4 0,5 0,6C0,6 2,6 2,6C2,5 2,4 2,3C2,2 2,1 2,0C2,0 0,0 0,0Z"/></g></svg>'
    points = contacts(svg)
    assert {p['kind'] for p in points.values()} == {'fork', 'join'}
    assert [p['point'] for p in points.values()] == [[1.0, 0.0], [1.0, 6.0]]
    frames = [{"name": "001.svg", "text": svg}, {"name": "002.svg", "text": svg}]
    ordered = order_frames(frames, {"frames": [{"name": "002.svg", "time_ms": 0}, {"name": "001.svg", "time_ms": 10}]})
    assert [f['name'] for f in ordered] == ['002.svg', '001.svg']
    assert order_frames(frames, player='const pics = [["002",1],["001",1]];')[0]['name'] == '002.svg'
    for rows in [[{"name": "001.svg"}], [{"name": "001.svg"}, {"name": "001.svg"}],
                 [{"name": "001.svg", "time_ms": 1}, {"name": "002.svg", "time_ms": 1}]]:
        try:
            order_frames(frames, {"frames": rows})
        except ValueError:
            pass
        else:
            raise AssertionError('invalid frame sequence admitted')
    assert finite_view([0, 0, 10, 10]) and not finite_view([0, 0, 0, 10])
    text = page_text({"scenes": [], "control": "</script>"})
    assert "__PAYLOAD__" not in text and "__SVG_HELPERS__" not in text and '\\u003c/script>' in text
    assert 'function namespace' in text and 'Path data changed' in text
    node_svg = svg.replace('x/fork/0→y/join/0', 'x/fork/0→node').replace('</svg>', '<rect data-key="node" class="e4-fill-ground" x="0" y="6" width="3" height="3"/></svg>')
    assert node_keys(node_svg) == {'node'}
    assert contacts(node_svg)['x/fork/0→node::target']['kind'] == 'node'
    assert contacts(svg.replace('x/fork/0→y/join/0', 'x/fork/0→dummy'))['x/fork/0→dummy::target']['kind'] == 'pass'
    early = node_svg.replace('<rect data-key="node" class="e4-fill-ground" x="0" y="6" width="3" height="3"/>', '')
    stable = order_frames([{'name': '001.svg', 'text': early}, {'name': '002.svg', 'text': node_svg}])
    assert stable[0]['contacts']['x/fork/0→node::target']['kind'] == 'node'
    assert contacts(svg.replace('x/fork/0→y/join/0', 'plain→y/fork/0'))['plain→y/fork/0::target']['kind'] == 'fork'
    return {"controls": 14, "result": "pass"}


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directories", type=Path, nargs="*")
    parser.add_argument("--compare", type=Path)
    parser.add_argument("--label", default="Production", help="label for the input version")
    parser.add_argument("--compare-label", default="Comparison", help="label for the comparison version")
    parser.add_argument("--out", type=Path, default=Path("motion-inspector.html"))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            print(json.dumps(self_test()))
        if args.directories:
            payload = payload_for(args.directories, args.compare, args.label, args.compare_label)
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(page_text(payload), encoding="utf-8")
            print(json.dumps({"output": str(args.out), "flows": len(payload["scenes"]),
                              "samples": sum(len(s["variants"][0]["frames"]) for s in payload["scenes"]),
                              "contacts": sum(len(s["choices"]) for s in payload["scenes"]),
                              "bytes": args.out.stat().st_size}))
        elif not args.self_test:
            parser.error("provide sequence directories or --self-test")
    except (OSError, ValueError, ET.ParseError, AssertionError) as error:
        print(f"motion inspector: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
