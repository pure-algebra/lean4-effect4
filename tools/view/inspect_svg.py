#!/usr/bin/env python3
"""Validate generated SVG files and inspect their unchanged paths in a browser.

Usage:
  python tools/view/inspect_svg.py tools/view/out/language-graphs --zoom 20 \
      --crop '148 480 24 38' --out tools/view/out/inspect.html
  python tools/view/inspect_svg.py AFTER --compare BEFORE --out comparison.html
  python tools/view/inspect_svg.py --self-test

The checks cover XML, IDs, local references and SVG path grammar. They do not
check CSS grammar, path topology or geometric contact. Pixel samples are browser
observations. Only trusted local generated SVG files should be inspected.
"""

import argparse
import hashlib
from html.parser import HTMLParser
import json
import math
from pathlib import Path
import re
import sys
import xml.etree.ElementTree as ET


SVG = "http://www.w3.org/2000/svg"
NUMBER = re.compile(r"[+-]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][+-]?[0-9]+)?")
URL_REF = re.compile(r"url\(\s*(['\"]?)#([^\s)'\"]+)\1\s*\)")
ARITY = {"M": 2, "L": 2, "H": 1, "V": 1, "C": 6, "S": 4, "Q": 4, "T": 2, "A": 7}
WSP = " \t\r\n"


def path_points(data):
    """Parse all path commands, returning command endpoints in path coordinates."""
    pos, command, current, start = 0, None, (0.0, 0.0), (0.0, 0.0)
    points = []
    have_number = False
    last_flag = False

    def space():
        nonlocal pos
        old = pos
        while pos < len(data) and data[pos] in WSP:
            pos += 1
        return pos != old

    def number(flag=False, first=False):
        nonlocal pos, have_number, last_flag
        separated = space()
        if pos < len(data) and data[pos] == ",":
            if first or not have_number:
                raise ValueError(f"unexpected comma at {pos}")
            pos += 1
            space()
            separated = True
        if pos >= len(data):
            raise ValueError("incomplete path command")
        # Signs and a second decimal point can delimit numbers without whitespace.
        # Arc flags consume one character, so their following flag/coordinate can touch.
        if have_number and not separated and not last_flag and data[pos] not in "+-.":
            raise ValueError(f"missing number separator at {pos}")
        if flag:
            if data[pos] not in "01":
                raise ValueError(f"arc flag must be 0 or 1 at {pos}")
            value = float(data[pos])
            pos += 1
        else:
            match = NUMBER.match(data, pos)
            if not match:
                raise ValueError(f"expected number at {pos}")
            value = float(match.group())
            pos = match.end()
            if not math.isfinite(value):
                raise ValueError("nonfinite path number")
        have_number, last_flag = True, flag
        return value

    while True:
        before_space = pos
        space()
        if pos == len(data):
            break
        explicit = data[pos].isalpha()
        if not explicit:
            pos = before_space
        if explicit:
            command = data[pos]
            pos += 1
            have_number = last_flag = False
            if command.upper() not in (*ARITY, "Z"):
                raise ValueError(f"unknown path command {command}")
            if not points and command.upper() != "M":
                raise ValueError("path must begin with moveto")
            if command.upper() == "Z":
                current = start
                points.append([*current, "close"])
                command = None
                continue
        if command is None:
            raise ValueError(f"expected path command at {pos}")
        kind = command.upper()
        values = [number(kind == "A" and i in (3, 4), explicit and i == 0)
                  for i in range(ARITY[kind])]
        if kind == "A" and (values[0] < 0 or values[1] < 0):
            raise ValueError("negative arc radius")
        x, y = current
        relative = command.islower()
        if kind == "H":
            current = (values[0] + (x if relative else 0), y)
        elif kind == "V":
            current = (x, values[0] + (y if relative else 0))
        else:
            current = (values[-2] + (x if relative else 0), values[-1] + (y if relative else 0))
        if not all(map(math.isfinite, current)):
            raise ValueError("nonfinite path endpoint")
        points.append([*current, "start" if kind == "M" else "endpoint"])
        if kind == "M":
            start = current
            command = "l" if relative else "L"
    return points


def validate_svg(text, name="SVG"):
    """Reject malformed XML, duplicate IDs, broken local links and invalid paths."""
    if re.search(r"<!DOCTYPE|<!ENTITY", text, re.I):
        raise ValueError(f"{name}: declarations are outside generated SVG")
    root = ET.fromstring(text)
    if root.tag != f"{{{SVG}}}svg":
        raise ValueError(f"{name}: expected SVG namespace and root")
    ids, refs, features = set(), [], []
    path_index = 0
    for element in root.iter():
        identity = element.get("id")
        if identity is not None:
            if not identity or any(c.isspace() for c in identity) or identity in ids:
                raise ValueError(f"{name}: empty, spaced or duplicate ID {identity!r}")
            ids.add(identity)
        for key, value in element.attrib.items():
            refs.extend(match.group(2) for match in URL_REF.finditer(value))
            local = key.rsplit("}", 1)[-1]
            if local == "href" and value.startswith("#"):
                refs.append(value[1:])
            if local in ("aria-labelledby", "aria-describedby"):
                refs.extend(value.split())
        if element.tag == f"{{{SVG}}}style":
            refs.extend(match.group(2) for match in URL_REF.finditer(element.text or ""))
        if element.tag == f"{{{SVG}}}path":
            try:
                points = path_points(element.get("d", ""))
            except ValueError as error:
                raise ValueError(f"{name}: path {path_index}: {error}") from error
            label = element.get("data-key") or element.get("id") or element.get("class", "path")
            seen = set()
            for x, y, kind in points:
                if (x, y) not in seen:
                    features.append({"path": path_index, "x": x, "y": y,
                                     "label": f"{label} / p{path_index} {kind} ({x:g}, {y:g})"})
                    seen.add((x, y))
            path_index += 1
    missing = sorted(set(refs) - ids)
    if missing:
        raise ValueError(f"{name}: missing local IDs {', '.join(missing)}")
    raw_view = root.get("viewBox")
    if raw_view:
        view = [float(v) for v in re.split(r"[\s,]+", raw_view.strip())]
    else:
        view = [0, 0, float(root.get("width", "0")), float(root.get("height", "0"))]
    if len(view) != 4 or not all(map(math.isfinite, view)) or min(view[2:]) <= 0:
        raise ValueError(f"{name}: invalid viewport")
    return {"name": name, "text": text, "view": view, "features": features,
            "paths": path_index, "ids": len(ids), "refs": len(refs),
            "sha256": hashlib.sha256(text.encode()).hexdigest()}


class Styles(HTMLParser):
    def __init__(self):
        super().__init__()
        self.active = False
        self.parts = []

    def handle_starttag(self, tag, attrs):
        if tag == "style":
            self.active = True

    def handle_endtag(self, tag):
        if tag == "style":
            self.active = False

    def handle_data(self, data):
        if self.active:
            self.parts.append(data)


def load_directory(directory, css_file=None, need_css=True):
    files = sorted(directory.glob("*.svg"))
    if not files:
        raise ValueError(f"no SVG files in {directory}")
    frames = [validate_svg(p.read_bytes().decode("utf-8"), p.name) for p in files]
    if css_file:
        css = css_file.read_text(encoding="utf-8")
    elif (directory / "index.html").exists():
        parser = Styles()
        parser.feed((directory / "index.html").read_text(encoding="utf-8"))
        css = "\n".join(parser.parts)
        # Generated player CSS follows the SVG token/class rules with body rules.
        # Keep only the SVG rules; the inspector supplies its own page layout.
        css = re.split(r"(?m)^body\s*\{", css, maxsplit=1)[0]
    elif need_css:
        raise ValueError(f"{directory}: supply --css or generated index.html for exact theme rules")
    else:
        css = ""
    if need_css and not css.strip():
        raise ValueError("empty SVG theme CSS")
    return {"label": str(directory), "css": css, "frames": frames}


PAGE = r'''<!doctype html>
<html lang="en"><meta charset="utf-8"><title>SVG contact inspection</title>
<style>
*{box-sizing:border-box}body{margin:0;padding:16px;background:#202124;color:#eee;font:14px system-ui}
header{position:sticky;top:0;background:#202124;z-index:2;padding:8px 0}h1{font-size:20px;margin:0 0 8px}
.controls{display:flex;flex-wrap:wrap;gap:8px;align-items:center;margin:8px 0}input,select,button{font:inherit}
input[type=number]{width:88px}select#feature{max-width:660px}button{cursor:pointer}small{color:#ccc}
.grid{display:grid;grid-template-columns:repeat(auto-fit,minmax(420px,1fr));gap:12px}
.panel{min-width:0;border:1px solid #62646a;padding:10px}.scroll{overflow:auto;max-height:65vh;background:var(--e4-color-ground)}
.scroll svg{display:block;max-width:none;flex:none}.full svg{width:100%;height:auto}.full{max-height:32vh;overflow:auto}
.detail{margin-top:8px}h2{font-size:15px;margin:0 0 8px}canvas{display:block;max-width:none;image-rendering:pixelated}
output{display:block;font:12px monospace;white-space:pre-wrap;margin:8px 0}.probe{border-top:1px solid #62646a;margin-top:12px;padding-top:8px}
</style>
<header><h1>SVG contact inspection</h1><small>Actual SVG paths, unchanged. Full view fits the panel; details use CSS pixels per SVG unit. Raster probes are browser observations.</small>
<div class="controls"><label>Frame <select id="frame"></select></label><label>Look <select id="look"><option>both</option><option>dark</option><option>paper</option></select></label>
<label>Zoom <select id="zoom"><option>4</option><option>8</option><option>20</option></select>×</label><button id="gap">Bar contact preset</button><button id="link">Copy crop URL</button></div>
<div class="controls" id="crop"><label>x <input id="x" type="number" step="any"></label><label>y <input id="y" type="number" step="any"></label><label>width <input id="w" type="number" step="any" min="0.01"></label><label>height <input id="h" type="number" step="any" min="0.01"></label><button id="apply">Apply crop</button>
<select id="feature" aria-label="Path endpoint or junction"><option value="">Choose path endpoint / junction</option></select></div><output id="status"></output></header>
<main id="panels" class="grid"></main><script id="payload" type="application/json">__PAYLOAD__</script>
<script>
'use strict';
const payload=JSON.parse(document.getElementById('payload').textContent), $=id=>document.getElementById(id);
const params=new URLSearchParams(location.search), state={frame:params.get('frame')||payload.sets[0].frames[0].name,
 look:params.get('look')||payload.look,zoom:Number(params.get('zoom')||payload.zoom),crop:payload.crop};
if(params.has('crop'))state.crop=params.get('crop').trim().split(/[ ,]+/).map(Number);
if(![4,8,20].includes(state.zoom))state.zoom=8;if(!['dark','paper','both'].includes(state.look))state.look='both';
if(!state.crop||state.crop.length!==4||!state.crop.every(Number.isFinite)||state.crop[2]<=0||state.crop[3]<=0)state.crop=[148,480,24,38];
let serial=0, details=[];
const urlRefs=(value,ids)=>value.replace(/url\(\s*(['"]?)#([^\s)'" ]+)\1\s*\)/g,(_,q,id)=>`url(#${ids.get(id)||id})`);
function namespace(svg,prefix){
 const ids=new Map();for(const el of [svg,...svg.querySelectorAll('[id]')])if(el.id){ids.set(el.id,prefix+el.id);el.id=prefix+el.id;}
 for(const el of [svg,...svg.querySelectorAll('*')]){
  for(const attr of [...el.attributes]){let v=urlRefs(attr.value,ids);
   if(attr.localName==='href'&&v.startsWith('#'))v='#'+(ids.get(v.slice(1))||v.slice(1));
   if(['aria-labelledby','aria-describedby'].includes(attr.localName))v=v.split(/\s+/).map(id=>ids.get(id)||id).join(' ');
   if(v!==attr.value)el.setAttributeNS(attr.namespaceURI,attr.name,v);
  }
  if(el.localName==='style')el.textContent=urlRefs(el.textContent,ids);
 }
}
function svgFor(frame,set,look,crop){
 const doc=new DOMParser().parseFromString(frame.text,'image/svg+xml'),svg=document.importNode(doc.documentElement,true);
 if(svg.localName!=='svg'||doc.querySelector('parsererror'))throw Error('Browser rejected SVG XML');
 const ds=[...svg.querySelectorAll('path')].map(p=>p.getAttribute('d'));namespace(svg,'inspect'+(++serial)+'-');
 svg.setAttribute('data-look',look);svg.classList.add('e4-view');
 const style=document.createElementNS('http://www.w3.org/2000/svg','style');style.textContent=set.css;svg.prepend(style);
 const view=crop||frame.view;svg.setAttribute('viewBox',view.join(' '));
 if(crop){svg.setAttribute('width',view[2]*state.zoom);svg.setAttribute('height',view[3]*state.zoom);}
 else {svg.setAttribute('width',frame.view[2]);svg.setAttribute('height',frame.view[3]);}
 if(ds.some((d,i)=>d!==svg.querySelectorAll('path')[i].getAttribute('d')))throw Error('Path data changed');return svg;
}
function sync(){for(const [id,v]of [['x',state.crop[0]],['y',state.crop[1]],['w',state.crop[2]],['h',state.crop[3]],['zoom',state.zoom],['look',state.look],['frame',state.frame]])$(id).value=v;
 const q=new URLSearchParams({frame:state.frame,look:state.look,zoom:state.zoom,crop:state.crop.join(' ')});history.replaceState(null,'','?'+q);
}
function localPoint(svg,event){return new DOMPoint(event.clientX,event.clientY).matrixTransform(svg.getScreenCTM().inverse());}
function panel(set,frame,look){
 const div=document.createElement('section');div.className='panel';div.dataset.look=look;
 // SVG style elements otherwise affect every panel in the document.
 const content=div.attachShadow({mode:'open'}),layout=document.createElement('style');layout.textContent=`
 .scroll{overflow:auto;max-height:65vh}.scroll svg{display:block;max-width:none}.full svg{width:100%;height:auto}
 .full{max-height:32vh}.detail{margin-top:8px}h2{font:15px system-ui;margin:0 0 8px}
 output{display:block;font:12px monospace;white-space:pre-wrap;margin:8px 0}
 .probe{overflow:auto;border-top:1px solid #62646a;margin-top:12px;padding-top:8px}
 canvas{display:block;max-width:none;image-rendering:pixelated}button{font:14px system-ui;cursor:pointer}`;content.append(layout);
 const title=document.createElement('h2');title.textContent=`${set.label} · ${frame.name} · ${look}`;content.append(title);
 const full=document.createElement('div');full.className='scroll full';const fullSvg=svgFor(frame,set,look,null);full.append(fullSvg);content.append(full);
 const wrap=document.createElement('div');wrap.className='scroll detail';const svg=svgFor(frame,set,look,state.crop);wrap.append(svg);content.append(wrap);
 const read=document.createElement('output');read.textContent='Click full view to center the crop. Move over detail for SVG coordinates.';content.append(read);
 fullSvg.addEventListener('click',e=>{const p=localPoint(fullSvg,e);state.crop=[p.x-state.crop[2]/2,p.y-state.crop[3]/2,...state.crop.slice(2)];render();});
 svg.addEventListener('mousemove',e=>{const p=localPoint(svg,e);read.textContent=`SVG (${p.x.toFixed(4)}, ${p.y.toFixed(4)}) · ${e.target.getAttribute('data-key')||e.target.localName}`;});
 const probe=document.createElement('div');probe.className='probe';const button=document.createElement('button');button.textContent='Rasterize this crop / probe pixels';probe.append(button);content.append(probe);
 button.addEventListener('click',async()=>{button.disabled=true;try{
  await document.fonts.ready;const copy=svg.cloneNode(true),w=Math.ceil(state.crop[2]*state.zoom),h=Math.ceil(state.crop[3]*state.zoom);
  if(w*h>16000000)throw Error('Crop exceeds 16 million probe pixels');
  copy.setAttribute('width',w);copy.setAttribute('height',h);const image=new Image(),blob=new Blob([new XMLSerializer().serializeToString(copy)],{type:'image/svg+xml'}),url=URL.createObjectURL(blob);
  try{await new Promise((resolve,reject)=>{image.onload=resolve;image.onerror=()=>reject(Error('SVG rasterization failed'));image.src=url;});
   const canvas=document.createElement('canvas');canvas.width=w;canvas.height=h;const ctx=canvas.getContext('2d',{willReadFrequently:true});
   ctx.fillStyle=getComputedStyle(svg).getPropertyValue('--e4-color-ground').trim()||'white';ctx.fillRect(0,0,w,h);ctx.drawImage(image,0,0,w,h);
   probe.querySelector('canvas')?.remove();probe.append(canvas);const sample=document.createElement('output');probe.querySelector('output')?.remove();probe.append(sample);
   canvas.addEventListener('mousemove',e=>{const r=canvas.getBoundingClientRect(),x=Math.floor((e.clientX-r.left)*w/r.width),y=Math.floor((e.clientY-r.top)*h/r.height),rgba=ctx.getImageData(x,y,1,1).data;
    sample.textContent=`pixel (${x}, ${y}) SVG (${(state.crop[0]+(x+.5)*state.crop[2]/w).toFixed(4)}, ${(state.crop[1]+(y+.5)*state.crop[3]/h).toFixed(4)}) RGBA ${[...rgba].join(', ')}`;});
  }finally{URL.revokeObjectURL(url);}
 }catch(e){read.textContent=e.message;}finally{button.disabled=false;}});
 $('panels').append(div);details.push({set,frame,svg,fullSvg});
}
function render(){sync();$('panels').replaceChildren();details=[];for(const set of payload.sets){const frame=set.frames.find(f=>f.name===state.frame);if(!frame)continue;
 for(const look of state.look==='both'?['dark','paper']:[state.look])panel(set,frame,look);}
 const first=details[0];if(!first)throw Error('Frame missing from all directories');
 $('feature').replaceChildren(new Option('Choose path endpoint / junction',''));
 first.frame.features.forEach((f,i)=>$('feature').add(new Option(f.label,String(i))));
 const ids=[...document.querySelectorAll('[id]'),...details.flatMap(d=>[...d.svg.querySelectorAll('[id]'),...d.fullSvg.querySelectorAll('[id]')])].map(el=>el.id);if(new Set(ids).size!==ids.length)throw Error('Duplicate embedded ID');
 $('status').textContent=`XML / IDs / local references / path grammar passed · ${first.frame.paths} paths · ${first.frame.ids} IDs · crop ${state.crop.join(' ')} · ${state.zoom} CSS px/unit\nSource SHA256 ${first.frame.sha256}`;
}
for(const f of payload.sets[0].frames)$('frame').add(new Option(f.name,f.name));
if(!payload.sets[0].frames.some(f=>f.name===state.frame))state.frame=payload.sets[0].frames[0].name;
$('frame').onchange=()=>{state.frame=$('frame').value;render();};$('look').onchange=()=>{state.look=$('look').value;render();};$('zoom').onchange=()=>{state.zoom=Number($('zoom').value);render();};
$('apply').onclick=()=>{const c=['x','y','w','h'].map(id=>Number($(id).value));if(c.every(Number.isFinite)&&c[2]>0&&c[3]>0){state.crop=c;render();}else $('status').textContent='Enter a finite crop with positive width and height.';};
$('gap').onclick=()=>{state.crop=[148,480,24,38];render();};$('link').onclick=async()=>{try{await navigator.clipboard.writeText(location.href);}catch{prompt('Copy crop URL',location.href);}};
$('feature').onchange=()=>{if($('feature').value==='')return;const first=details[0],f=first.frame.features[Number($('feature').value)],path=first.fullSvg.querySelectorAll('path')[f.path];
 const p=new DOMPoint(f.x,f.y).matrixTransform(path.getScreenCTM()).matrixTransform(first.fullSvg.getScreenCTM().inverse());state.crop=[p.x-state.crop[2]/2,p.y-state.crop[3]/2,...state.crop.slice(2)];render();};
try{render();}catch(e){$('status').textContent=e.stack;throw e;}
</script></html>'''


def self_test():
    good = ["", "M0,0C1,2 3,4 5,6Z", "m1 2 3 4h-2v.5s1 2 3 4q1 2 3 4t5 6z",
            "M.5.5L1e2-2E-2", "M0 0A10 20 0 0110 20", "M0 0A10 20 0 0 1 10 20"]
    bad = ["L0 0", "M,0 0", "M0,,0", "M0 0,", "M0 0Z1 2", "M0 0C1 2 3",
           "M0 0R1 2", "M0 0L1e999 2", "M0 0A1 2 3 2 0 4 5", "M0 0A-1 2 3 0 0 4 5",
           "M0 0L1 2 garbage", "M0 0Z,", "M0 0L", "M0 0 L 1, 2, 3"]
    for data in good:
        path_points(data)
    for data in bad:
        try:
            path_points(data)
        except ValueError:
            pass
        else:
            raise AssertionError(f"accepted invalid path {data!r}")
    svg = f'<svg xmlns="{SVG}" viewBox="0 0 10 10"><clipPath id="c"/><path d="M0 0L1 1" clip-path="url(#c)"/></svg>'
    validate_svg(svg)
    for text in [svg.replace('id="c"', 'id="d"'), svg.replace('<path', '<g id="c"/><path'),
                 svg.replace('M0 0L1 1', 'M0,,0'), svg[:-1], svg.replace('0 0 10 10', '0 0 0 10')]:
        try:
            validate_svg(text)
        except (ValueError, ET.ParseError):
            pass
        else:
            raise AssertionError("accepted invalid SVG control")
    assert path_points("m1 2 3 4h-2v.5z")[-1][:2] == [1, 2]
    assert "__PAYLOAD__" in PAGE
    print(f"self-test passed: {len(good)} valid paths, {len(bad)} refused paths, 5 refused SVG controls")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("directory", type=Path, nargs="?")
    parser.add_argument("--compare", type=Path, help="baseline directory; matching names share a crop")
    parser.add_argument("--out", type=Path, default=Path("inspect-svg.html"))
    parser.add_argument("--css", type=Path, help="SVG theme CSS instead of generated index.html styles")
    parser.add_argument("--crop", default="148 480 24 38", help="x y width height, in SVG units")
    parser.add_argument("--zoom", type=int, choices=[4, 8, 20], default=8)
    parser.add_argument("--look", choices=["both", "dark", "paper"], default="both")
    parser.add_argument("--validate-only", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        if args.directory is None:
            return
    if args.directory is None:
        parser.error("directory is required unless --self-test")
    try:
        crop = [float(v) for v in re.split(r"[ ,]+", args.crop.strip())]
        if len(crop) != 4 or not all(map(math.isfinite, crop)) or min(crop[2:]) <= 0:
            raise ValueError("crop needs four finite numbers and positive width/height")
        sets = [load_directory(args.directory, args.css, not args.validate_only)]
        if args.compare:
            sets.append(load_directory(args.compare, args.css, not args.validate_only))
        for group in sets:
            print(f"validated {len(group['frames'])} SVG files / {sum(f['paths'] for f in group['frames'])} paths / "
                  f"{sum(f['ids'] for f in group['frames'])} IDs / {sum(f['refs'] for f in group['frames'])} local references: {group['label']}")
        if not args.validate_only:
            data = json.dumps({"sets": sets, "crop": crop, "zoom": args.zoom, "look": args.look}, ensure_ascii=True)
            args.out.parent.mkdir(parents=True, exist_ok=True)
            args.out.write_text(PAGE.replace("__PAYLOAD__", data.replace("<", "\\u003c").replace("&", "\\u0026")), encoding="utf-8")
            print(f"inspection HTML: {args.out.resolve()}")
    except (ValueError, ET.ParseError, OSError) as error:
        print(f"SVG inspection refused: {error}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
