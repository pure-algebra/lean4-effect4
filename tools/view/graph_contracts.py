"""Present the actual GraphContractProbe SVGs with synchronized finite samples."""
import argparse
import json
from pathlib import Path

PAGE = r'''<!doctype html><html lang="en"><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Graph service contract probes</title>
<style>
*{box-sizing:border-box}body{margin:0;padding:28px;background:#14110d;color:#ece6dc;font:15px/1.5 system-ui}
main{max-width:1280px;margin:auto}h1{font-size:29px;margin:4px 0}h2{font-size:18px;margin:0 0 6px}
p{max-width:960px;color:#c9c0b2}.eyebrow{color:#e9b96f;font:12px monospace;letter-spacing:.12em}
.controls{display:flex;gap:12px;align-items:center;margin:22px 0;flex-wrap:wrap}
input{width:min(420px,60vw)}button,select{background:#302a21;border:1px solid #61533f;color:inherit;padding:9px 16px;border-radius:5px;cursor:pointer}a{color:#e9b96f}
.grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:20px}.card{border:1px solid #48433c;padding:18px;border-radius:8px}
.picture{height:340px;display:flex;justify-content:center}.picture svg{width:100%;height:100%}.crop{height:200px;background:#14110d;border:1px solid #48433c}
.crop svg{width:100%;height:100%}.status{font:13px monospace;color:#f1bc75;min-height:42px}small{color:#aaa093}
@media(max-width:800px){.grid{grid-template-columns:1fr}}
</style><main>
<div class="eyebrow">PRODUCTION CONNECTORS · FINITE CONTROLS</div>
<h1>Graph service contracts before the aesthetic pass</h1>
<p>Compare the retained defect controls with the repaired graph services. The red rectangle marks the allocated canvas.
Five sampled moments show a rendering transition, not scheduler execution.</p>
<div class="controls"><label>Version <select id="version"><option value="after">Current</option><option value="before">Before</option></select></label><button id="play">Play samples</button><label for="time">Move</label>
<input id="time" type="range" min="0" max="4" value="2" step="1"><output id="moment"></output></div>
<div class="grid">
<section class="card"><h2>Moving fork docking</h2><div class="status" id="fork-status"></div>
<div class="picture" id="fork"></div><small>Close-up: source port and bar</small><div class="crop" id="fork-crop"></div>
<p>Explicit port membership now makes the points follow their moving bar. The close-up follows the source contact.</p></section>
<section class="card"><h2>Swapping node positions</h2><div class="status" id="swap-status"></div>
<div class="picture" id="swap"></div><small>Close-up: allocated node boxes</small><div class="crop" id="swap-crop"></div>
<p>A conservative movement check selects an endpoint-family transition when node paths may overlap. The old family shrinks, relocation occurs while hidden, then the new family grows.</p></section>
<section class="card"><h2>Self-loop canvas</h2><div class="status" id="loop-status"></div>
<div class="picture" id="loop"></div><small>Close-up: right edge of the allocated canvas</small><div class="crop" id="loop-crop"></div>
<p>Layout reserves the loop's control hull. Drawing then fits the actual stroke envelopes without moving return lanes. Text metrics remain unmeasured.</p></section>
</div><p><a href="../advanced-graph-cleanup/motion.html">Inspect advanced flows and logical contacts in motion</a></p>
<p><small>Source: tools/view/GraphContractProbe.lean. These are finite rendering controls. Node separation does not establish edge, label, or region clearance.</small></p>
</main><script>
const versions=__FRAMES__, times=[0,250,500,750,1000];
const slider=document.getElementById('time'); let timer=null;
const version=document.getElementById('version');if(!versions.before)version.querySelector('[value=before]').remove();
function paint(id,name,crop){const e=document.getElementById(id);e.innerHTML=versions[version.value][name];
const svg=e.querySelector('svg');if(crop)svg.setAttribute('viewBox',crop.join(' '));}
function draw(){const t=times[+slider.value];document.getElementById('moment').textContent=t+'/1000';
paint('fork','fork-'+t);paint('swap','swap-'+t);paint('loop','loop');
paint('fork-crop','fork-'+t,[48,50+80*t/1000,40,110]);
paint('swap-crop','swap-'+t,[20,90,220,80]);paint('loop-crop','loop',[60,10,140,90]);
const before=version.value==='before';
document.getElementById('fork-status').textContent=before?(t===1000?'Target: ports meet their bar.':'Ports and target bar occupy different heights.'):'Ports remain on their moving bar.';
document.getElementById('swap-status').textContent=before?(t===500?'Midpoint: two boxes occupy the same place.':t===250||t===750?'Intermediate boxes partially overlap.':'Endpoint: boxes are separated.'):(t===500?'Hidden relocation: no overlapping boxes.':'Separated endpoint family.');
document.getElementById('loop-status').textContent=before?'Loop extends beyond its allocation.':'Loop control hull fits its allocation.';}
slider.addEventListener('input',draw);version.addEventListener('change',draw);document.getElementById('play').addEventListener('click',function(){
if(timer){clearInterval(timer);timer=null;this.textContent='Play samples';}
else{this.textContent='Pause';timer=setInterval(()=>{slider.value=(+slider.value+1)%5;draw()},800)}});draw();
</script></html>'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, nargs="?", default=Path("tools/view/out/graph-contracts"))
    parser.add_argument("--before", type=Path)
    args = parser.parse_args()
    names = [f"{case}-{t}" for case in ("fork", "swap") for t in (0, 250, 500, 750, 1000)] + ["loop"]
    frames = {"after": {name: (args.directory / f"{name}.svg").read_text(encoding="utf-8") for name in names}}
    if args.before:
        frames["before"] = {name: (args.before / f"{name}.svg").read_text(encoding="utf-8") for name in names}
    encoded = json.dumps(frames, ensure_ascii=False).replace("</", "<\\/")
    target = args.directory / "index.html"
    target.write_text(PAGE.replace("__FRAMES__", encoded), encoding="utf-8")
    print(target)


if __name__ == "__main__":
    main()
