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
input{width:min(420px,60vw)}button{background:#302a21;border:1px solid #61533f;color:inherit;padding:9px 16px;border-radius:5px;cursor:pointer}
.grid{display:grid;grid-template-columns:repeat(3,minmax(0,1fr));gap:20px}.card{border:1px solid #48433c;padding:18px;border-radius:8px}
.picture{height:340px;display:flex;justify-content:center}.picture svg{width:100%;height:100%}.crop{height:200px;background:#14110d;border:1px solid #48433c}
.crop svg{width:100%;height:100%}.status{font:13px monospace;color:#f1bc75;min-height:42px}small{color:#aaa093}
@media(max-width:800px){.grid{grid-template-columns:1fr}}
</style><main>
<div class="eyebrow">PRODUCTION CONNECTORS · FINITE CONTROLS</div>
<h1>Graph service contracts before the aesthetic pass</h1>
<p>These use the current renderer. They expose layout and motion gaps independently of connector smoothness.
The red rectangle marks the allocated canvas. Five sampled moments show a linear move, not scheduler execution.</p>
<div class="controls"><button id="play">Play samples</button><label for="time">Move</label>
<input id="time" type="range" min="0" max="4" value="2" step="1"><output id="moment"></output></div>
<div class="grid">
<section class="card"><h2>Moving fork docking</h2><div class="status" id="fork-status"></div>
<div class="picture" id="fork"></div><small>Close-up: source port and bar</small><div class="crop" id="fork-crop"></div>
<p>The ports interpolate while the bar immediately takes its target position. Group motion needs explicit port membership.</p></section>
<section class="card"><h2>Swapping node positions</h2><div class="status" id="swap-status"></div>
<div class="picture" id="swap"></div><small>Close-up: allocated node boxes</small><div class="crop" id="swap-crop"></div>
<p>Both endpoints have separated boxes. Direct interpolation overlaps them at the midpoint; the endpoint law does not cover clearance.</p></section>
<section class="card"><h2>Self-loop canvas</h2><div class="status">Allocation check accepts; curve leaves canvas.</div>
<div class="picture" id="loop"></div><small>Close-up: right edge of the allocated canvas</small><div class="crop" id="loop-crop"></div>
<p>Layout reserves space for back lanes but omits the self-loop's horizontal reach. Painted bounds need a separate check.</p></section>
</div><p><small>Source: tools/view/GraphContractProbe.lean. These bounded controls reproduce known gaps; they are not general geometry theorems.</small></p>
</main><script>
const frames=__FRAMES__, times=[0,250,500,750,1000];
const slider=document.getElementById('time'); let timer=null;
function paint(id,name,crop){const e=document.getElementById(id);e.innerHTML=frames[name];
const svg=e.querySelector('svg');if(crop)svg.setAttribute('viewBox',crop.join(' '));}
function draw(){const t=times[+slider.value];document.getElementById('moment').textContent=t+'/1000';
paint('fork','fork-'+t);paint('swap','swap-'+t);paint('loop','loop');
paint('fork-crop','fork-'+t,[48,50+80*t/1000,40,110]);
paint('swap-crop','swap-'+t,[20,90,220,80]);paint('loop-crop','loop',[60,10,140,90]);
document.getElementById('fork-status').textContent=t===1000?'Target: ports meet their bar.':'Ports and target bar occupy different heights.';
document.getElementById('swap-status').textContent=t===500?'Midpoint: two boxes occupy the same place.':t===250||t===750?'Intermediate boxes partially overlap.':'Endpoint: boxes are separated.';}
slider.addEventListener('input',draw);document.getElementById('play').addEventListener('click',function(){
if(timer){clearInterval(timer);timer=null;this.textContent='Play samples';}
else{this.textContent='Pause';timer=setInterval(()=>{slider.value=(+slider.value+1)%5;draw()},800)}});draw();
</script></html>'''


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("directory", type=Path, nargs="?", default=Path("tools/view/out/graph-contracts"))
    args = parser.parse_args()
    names = [f"{case}-{t}" for case in ("fork", "swap") for t in (0, 250, 500, 750, 1000)] + ["loop"]
    frames = {name: (args.directory / f"{name}.svg").read_text(encoding="utf-8") for name in names}
    encoded = json.dumps(frames, ensure_ascii=False).replace("</", "<\\/")
    target = args.directory / "index.html"
    target.write_text(PAGE.replace("__FRAMES__", encoded), encoding="utf-8")
    print(target)


if __name__ == "__main__":
    main()
