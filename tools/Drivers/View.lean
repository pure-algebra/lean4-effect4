import Tools.View.Build
import Tools.View.Run
import Tools.View.Specimen
import Tools.View.FlowSpecimen
import Tools.View.GraphCheck
import Tools.View.Tokens
import Tools.View.Output
import Tools.View.SvgOut
import Effect4.Store.Domain.ProgramWire

/-!
# The view driver: frames of a program built by edits

    lake env lean --run tools/Drivers/View.lean [FLAGS] build NAME OUT      a corpus program, built top-down
    lake env lean --run tools/Drivers/View.lean [FLAGS] run NAME OUT        a corpus program, run step by step
    lake env lean --run tools/Drivers/View.lean [FLAGS] session FILE OUT    the frames of a request file
    lake env lean --run tools/Drivers/View.lean [FLAGS] specimen OUT        a graph built one edge at a time
    lake env lean --run tools/Drivers/View.lean [FLAGS] flows OUT           the program graph's cases, one program a page
    lake env lean --run tools/Drivers/View.lean looks DIR OUT               every look of DIR, side by side
    lake env lean --run tools/Drivers/View.lean gallery DIR                 the list of every kept run of DIR

The flags: `--motion N`, the pictures of motion between two frames (default 20; 1 draws none);
`--plain`, no marks; `--look LOOK`, the look (`Tools.View.Look`): a token file, or the name of
one in `tools/view/looks/` (default: the dark look, the base of every other).

`NAME` is a program of the wire corpus (`Effect4.Program.Wire.Corpus.all`). `FILE` holds one
session request a line, as `tools/Drivers/Session.lean` reads them. For each frame the driver
writes three outputs of one list of calls (`docs/research/2026-10-09-visual-pipeline.md`):

- `NNN.draw`, the device calls at the ratio 2 in the look, which `tools/view/draw` replays to
  pixels;
- `NNN.svg`, the same calls at the ratio 1, with the look's classes and values;
- `frames.txt`, every frame as characters.

`looks` reads every token file of `DIR` over the dark look. For each look, and for the dark look
itself, it writes `OUT/NAME/`: the look's whole token file and its CSS, and two pages in the look,
the graph specimen's last frame and pFork's last frame built, as `.draw` and `.svg`. `OUT/index.html`
shows the looks side by side, and `OUT/looks.css` holds every look's custom properties and the
class rules. It reports whether each look comes back from its own written token file.

Between two frames it writes `N - 1` pictures of motion (`Tools.View.sample`), named after the frame
they lead to: `002-001.draw` comes before `002.draw` in a sorted listing. It reports the splice
check of each spliced edit: the lines outside the edited subtree keep their text, type and note.

`build` also writes `requests.jsonl`, the requests it ran, so the session driver replays them.

Every run also writes `index.html`, its player: the run's pictures in its own look, stepped as the
window steps them (Right or Space plays the motion to the next frame, Left steps back, Home and
End, P plays every frame), and `run.json`, what the gallery lists. With `--gallery DIR` a run kept
at `DIR/runs/ID/` also rewrites `DIR/index.html`, the list of every kept run, newest first; the
command `gallery DIR` rewrites it alone. `--label TEXT` names the run there (`v` writes its commit
and time).
-/

open Tools.View Tools.View.Build

/-- A page's width, in logical pixels. -/
def width : Int := 1280

/-- A frame's number, in three digits. -/
def frameName (i : Nat) : String :=
  let s := toString i
  "".pushn '0' (3 - s.length) ++ s

/-- Write one picture's stream (ratio 2) and SVG (ratio 1), in a look. The SVG is a typed tree
(`Tools.View.SvgOut`); a picture that the content model or XML refuses stops the run with its name
and the reason. -/
def writePicture (L : Look) (out : System.FilePath) (name : String) (W H : Int) (calls : List (Keyed Call)) :
    IO Unit := do
  IO.FS.writeFile (out / s!"{name}.draw")
    ("\n".intercalate (stream L W.toNat H.toNat 2 (lowerAll 2 calls)) ++ "\n")
  match SvgOut.fileText (SvgOut.picture L W.toNat H.toNat 1 (lowerAll 1 calls)) with
  | .ok text => IO.FS.writeFile (out / s!"{name}.svg") (text ++ "\n")
  | .error why => throw (IO.userError s!"{name}.svg: {why}")

/-- Write one page, in a look, on a stroke cache (`Laid.StrokeCache`); answer the cache. -/
def writePage (L : Look) (out : System.FilePath) (name : String) (g : Page)
    (cache : Laid.StrokeCache := {}) : IO Laid.StrokeCache := do
  let drawing := pageDrawingCached L width g cache
  writePicture L out name drawing.size.1 drawing.size.2 drawing.calls
  pure drawing.cache

/-- The page rules a player and the gallery share, over a look's custom properties. -/
def pageRules : String :=
  "body { margin: 0; padding: 16px 16px 48px; background: var(--e4-color-ground); color: var(--e4-color-ink); font-family: var(--e4-font-name-family); }\n" ++
  "a { color: var(--e4-color-ink); }\n" ++
  "h1 { font-family: var(--e4-font-title-family); font-weight: var(--e4-font-title-weight); font-size: 22px; margin: 0; }\n" ++
  ".meta { font-family: var(--e4-font-data-family); font-size: 13px; opacity: 0.75; }\n" ++
  "header { display: flex; flex-wrap: wrap; gap: 8px 20px; align-items: baseline; margin-bottom: 12px; }\n" ++
  "button { font: inherit; font-size: 14px; color: var(--e4-color-ink); background: transparent; border: 1px solid var(--e4-color-rule); border-radius: 4px; padding: 2px 10px; cursor: pointer; }\n" ++
  "img { display: block; max-width: 100%; height: auto; border: 1px solid var(--e4-color-rule); }\n"

/-- **A run's player**: its pictures in order, a frame's motion pictures before it, stepped as
`play` steps them. Picture `k` of a step's `n` stands at `k/n` of the look's step. A scrubber reads
any picture, a rate of one, a half or a quarter slows a step, a strip shows every frame at one
scale, and five moments of the current step stand beside it (decisions row 362, DS-2). Every
picture is drawn at the scale of the run's largest, from the top left, in a box of one height, so a
kept mark stays in place from frame to frame and nothing below it moves. Nothing
loops, and under a reduced-motion preference a step shows its end frame alone (row 354 (5)). The
picture stands inline (DS-3): a look switch redraws it in the dark look, the paper look or both
side by side, through the class rules (`Tokens.rules`), which change colours and families and no
place; the key under the pointer is named, and a click copies `title · picture · key` for the
chat. Each inline pane owns its SVG IDs and local references. A scale selector fits the largest
picture or shows logical pixels at 100, 150 or 200 percent inside scrolling panes.
The current picture names itself in data attributes for an agent that reads the page. -/
def playerPage (L paper : Look) (title label : String) (pics : List (String × Bool)) (gallery : Bool) :
    String :=
  let list := ",".intercalate (pics.map fun (n, f) => s!"[\"{n}\",{if f then 1 else 0}]")
  "<!doctype html>\n<html lang=\"en\" data-look=\"" ++ escape L.name ++ "\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>" ++ escape title ++ "</title>\n" ++
  "<style>\n" ++ Tokens.css L ++ (if L.name == "dark" then "" else Tokens.css {}) ++
  (if L.name == "paper" then "" else Tokens.css paper) ++ Tokens.rules ++ pageRules ++
  "html { scrollbar-gutter: stable; }\n" ++
  ".pic { display: flex; gap: 12px; overflow: hidden; }\n" ++
  ".pane { flex: 1 1 0; min-width: 0; height: 100%; overflow: auto; border: 1px solid var(--e4-color-rule); box-sizing: border-box; }\n" ++
  ".pane svg { display: block; max-width: none; height: auto; }\n" ++
  "#pos { display: inline-block; min-width: 24ch; font-variant-numeric: tabular-nums; }\n" ++
  "#moments { min-height: 76px; }\n" ++
  ".pic [data-key] { cursor: copy; }\n" ++
  "#under { min-height: 1.4em; margin: 6px 0 0; }\n" ++
  ".controls { display: flex; flex-wrap: wrap; align-items: center; gap: 8px 14px; margin: 0 0 12px; }\n" ++
  ".controls label { display: inline-flex; align-items: center; gap: 6px; }\n" ++
  "#scrub { flex: 1 1 240px; accent-color: var(--e4-color-ink); }\n" ++
  "select { font: inherit; font-size: 13px; color: var(--e4-color-ink); background: var(--e4-color-ground); border: 1px solid var(--e4-color-rule); border-radius: 4px; padding: 1px 4px; }\n" ++
  "button:focus-visible, select:focus-visible, input:focus-visible, .strip img:focus-visible { outline: 2px solid var(--e4-color-ink); outline-offset: 2px; }\n" ++
  ".strips { display: grid; grid-template-columns: minmax(0, 1fr); gap: 10px; margin-top: 14px; }\n" ++
  ".strip { position: relative; display: flex; gap: 8px; overflow-x: auto; padding: 4px 2px 6px; align-items: flex-start; }\n" ++
  ".strip img { height: 68px; width: auto; max-width: none; cursor: pointer; opacity: 0.6; }\n" ++
  ".strip img[aria-current=\"true\"] { opacity: 1; outline: 2px solid var(--e4-color-ink); outline-offset: 2px; }\n" ++
  ".strip-label { font-family: var(--e4-font-data-family); font-size: 12px; opacity: 0.7; }\n" ++
  "</style>\n</head>\n<body>\n<header>" ++
  (if gallery then "<a href=\"../../index.html\">Studio</a>" else "") ++
  "<h1>" ++ escape title ++ "</h1><span class=\"meta\">" ++ escape label ++ " · " ++ escape L.name ++
  "</span></header>\n" ++
  "<div class=\"controls\"><span><button id=\"back\" aria-label=\"previous frame\">◀</button> " ++
  "<button id=\"next\" aria-label=\"next frame\">▶</button> <button id=\"all\">play all</button></span>" ++
  "<span class=\"meta\" id=\"pos\" aria-live=\"polite\"></span>" ++
  "<label class=\"meta\">speed <select id=\"rate\"><option value=\"1\">1×</option><option value=\"0.5\">½×</option>" ++
  "<option value=\"0.25\">¼×</option></select></label>" ++
  "<label class=\"meta\">look <select id=\"lookSel\"><option value=\"\">as drawn</option>" ++
  "<option value=\"dark\">dark</option><option value=\"paper\">paper</option>" ++
  "<option value=\"both\">dark beside paper</option></select></label>" ++
  "<label class=\"meta\">scale <select id=\"scaleSel\"><option value=\"fit\">fit</option>" ++
  "<option value=\"1\">actual size</option><option value=\"1.5\">150%</option>" ++
  "<option value=\"2\">200%</option></select></label>" ++
  "<input id=\"scrub\" type=\"range\" min=\"0\" max=\"" ++ toString (pics.length - 1) ++ "\" step=\"1\" value=\"0\" aria-label=\"picture\"></div>\n" ++
  "<main data-pictures=\"" ++ toString pics.length ++ "\"><div id=\"pic\" class=\"pic\" role=\"img\"></div>" ++
  "<p class=\"meta\" id=\"under\" aria-live=\"polite\"></p></main>\n" ++
  "<div class=\"strips\"><div><span class=\"strip-label\">frames</span><nav class=\"strip\" id=\"strip\" aria-label=\"frames\"></nav></div>\n" ++
  "<div><span class=\"strip-label\">this step at 0, ¼, ½, ¾ and its end</span><div class=\"strip\" id=\"moments\"></div></div></div>\n" ++
  "<script>\n" ++
  "const pics = [" ++ list ++ "];\nconst step = " ++ toString L.motion.step ++ ";\nconst title = " ++
  (Lean.Json.str title).compress ++ ";\n" ++
  "const frames = pics.map((p, i) => p[1] ? i : -1).filter(i => i >= 0);\n" ++
  "const reduce = matchMedia('(prefers-reduced-motion: reduce)');\n" ++
  "const $ = id => document.getElementById(id);\n" ++
  "const pic = $('pic'), pos = $('pos'), scrub = $('scrub'), rate = $('rate'), strip = $('strip'), moments = $('moments');\n" ++
  "const lookSel = $('lookSel'), scaleSel = $('scaleSel'), under = $('under');\n" ++
  "const cache = new Map();\n" ++
  "const load = n => { if (!cache.has(n)) cache.set(n, fetch(n + '.svg').then(r => r.text())); return cache.get(n); };\n" ++
  "let paneSerial = 0;\n" ++
  "const pane = (text, look) => { const d = document.createElement('div'); d.className = 'pane'; d.innerHTML = text; const v = d.querySelector('svg');\n" ++
  "  if (!v) return d; const prefix = 'e4-player-svg-' + paneSerial++ + '-', ids = new Map();\n" ++
  "  const nodes = [v, ...v.querySelectorAll('*')];\n" ++
  "  nodes.forEach(n => { if (n.hasAttribute('id')) { const id = n.getAttribute('id'); ids.set(id, prefix + id); n.setAttribute('id', prefix + id); } });\n" ++
  "  nodes.forEach(n => [...n.attributes].forEach(a => { if (a.localName === 'id') return;\n" ++
  "    let value = a.value.replace(/url\\(\\s*(['\"]?)#([^'\"\\s)]+)\\1\\s*\\)/g, (whole, quote, id) => ids.has(id) ? 'url(#' + ids.get(id) + ')' : whole);\n" ++
  "    if (a.localName === 'href' && value.startsWith('#') && ids.has(value.slice(1))) value = '#' + ids.get(value.slice(1));\n" ++
  "    if (a.localName === 'aria-labelledby' || a.localName === 'aria-describedby') value = value.split(/\\s+/).map(id => ids.get(id) || id).join(' ');\n" ++
  "    if (value !== a.value) n.setAttributeNS(a.namespaceURI, a.name, value); }));\n" ++
  "  if (look) v.setAttribute('data-look', look); return d; };\n" ++
  "async function draw(i) { const text = await load(pics[i][0]); if (at !== i) return; const mode = lookSel.value;\n" ++
  "  pic.classList.toggle('both', mode === 'both');\n" ++
  "  pic.replaceChildren(...(mode === 'both' ? [pane(text, 'dark'), pane(text, 'paper')] : [pane(text, mode)])); fit(); }\n" ++
  "let maxW = 0, maxH = 0;\n" ++
  "const dims = t => { const m = /<svg[^>]*?\\swidth=\"([0-9.]+)\"[^>]*?\\sheight=\"([0-9.]+)\"/.exec(t); return m ? [+m[1], +m[2]] : [0, 0]; };\n" ++
  "function fit() { if (!maxW) return; const both = lookSel.value === 'both';\n" ++
  "  const cap = innerHeight * 0.68, available = (pic.clientWidth - (both ? 12 : 0)) / (both ? 2 : 1) - 2;\n" ++
  "  const k = scaleSel.value === 'fit' ? Math.max(0.01, Math.min(available / maxW, cap / maxH)) : +scaleSel.value;\n" ++
  "  pic.dataset.scale = scaleSel.value; pic.style.height = Math.ceil(Math.min(maxH * k, cap) + 2) + 'px';\n" ++
  "  pic.querySelectorAll('svg').forEach(v => { v.style.width = (+v.getAttribute('width')) * k + 'px';\n" ++
  "    v.style.height = (+v.getAttribute('height')) * k + 'px'; }); }\n" ++
  "addEventListener('resize', fit);\n" ++
  "scaleSel.onchange = fit;\n" ++
  "const keyAt = e => { const k = e.target.closest('[data-key]'); return k ? k.getAttribute('data-key') : ''; };\n" ++
  "pic.addEventListener('mousemove', e => { const k = keyAt(e); under.textContent = k ? 'key ' + k + ' (click copies)' : ''; });\n" ++
  "pic.addEventListener('click', async e => { const k = keyAt(e); if (!k) return;\n" ++
  "  const note = title + ' · ' + pics[at][0] + ' · ' + k;\n" ++
  "  try { await navigator.clipboard.writeText(note); under.textContent = 'copied: ' + note; }\n" ++
  "  catch (err) { under.textContent = note; } });\n" ++
  "lookSel.onchange = () => draw(at);\n" ++
  "let at = 0, timer = 0, chain = false, momentsOf = -1;\n" ++
  "const reached = i => frames.filter(j => j <= i).length;\n" ++
  "const thumb = (i, alt) => { const t = document.createElement('img'); t.src = pics[i][0] + '.svg'; t.alt = alt;\n" ++
  "  t.dataset.index = i; t.dataset.picture = pics[i][0]; t.tabIndex = 0;\n" ++
  "  t.onclick = t.onkeydown = e => { if (e.type === 'keydown' && e.key !== 'Enter') return; stop(); chain = false; show(i); }; return t; };\n" ++
  "frames.forEach((i, k) => strip.append(thumb(i, 'frame ' + (k + 1))));\n" ++
  "function showMoments(i) { const end = frames.find(j => j >= i); if (end === momentsOf) return; momentsOf = end;\n" ++
  "  const prev = frames.filter(j => j < end).pop();\n" ++
  "  if (end === undefined || prev === undefined || end - prev < 2) { moments.replaceChildren(); return; }\n" ++
  "  moments.replaceChildren(...[0, 0.25, 0.5, 0.75, 1].map(q => thumb(prev + Math.round(q * (end - prev)), 'moment ' + q * 1000 + ' per mille'))); }\n" ++
  "function show(i) { at = i; const f = reached(i); draw(i);\n" ++
  "  pic.dataset.picture = pics[i][0]; pic.dataset.frame = f; pic.setAttribute('aria-label', title + ', frame ' + f + ' of ' + frames.length);\n" ++
  "  pos.textContent = 'frame ' + f + ' of ' + frames.length + (pics[i][1] ? '' : ', moving'); scrub.value = i;\n" ++
  "  strip.querySelectorAll('img').forEach(t => { const on = +t.dataset.index === frames[Math.max(0, f - 1)];\n" ++
  "    t.setAttribute('aria-current', String(on));\n" ++
  "    if (on && (t.offsetLeft < strip.scrollLeft || t.offsetLeft + t.offsetWidth > strip.scrollLeft + strip.clientWidth))\n" ++
  "      strip.scrollLeft = t.offsetLeft - 8; });\n" ++
  "  showMoments(i); }\n" ++
  "function stop() { cancelAnimationFrame(timer); clearTimeout(timer); timer = 0; }\n" ++
  "function next() { stop(); const end = frames.find(j => j > at); if (end === undefined) { chain = false; return; }\n" ++
  "  const span = step / +rate.value;\n" ++
  "  if (reduce.matches) { show(end); if (chain) timer = setTimeout(next, span); return; }\n" ++
  "  const start = at, n = end - start, t0 = performance.now();\n" ++
  "  const tick = t => { const k = Math.min(n, Math.ceil((t - t0) * n / span)); if (k > 0 && start + k !== at) show(start + k);\n" ++
  "    if (k < n) timer = requestAnimationFrame(tick); else if (chain) timer = setTimeout(next, span); };\n" ++
  "  timer = requestAnimationFrame(tick); }\n" ++
  "function back() { stop(); chain = false; const p = frames.filter(j => j < at).pop(); show(p === undefined ? 0 : p); }\n" ++
  "function all() { chain = true; if (at === frames[frames.length - 1]) show(0); next(); }\n" ++
  "$('next').onclick = () => { chain = false; next(); };\n" ++
  "$('back').onclick = back; $('all').onclick = all;\n" ++
  "scrub.oninput = () => { stop(); chain = false; show(+scrub.value); };\n" ++
  "document.addEventListener('keydown', e => {\n" ++
  "  if (e.target.closest('select, input')) return;\n" ++
  "  if (e.key === 'ArrowRight' || e.key === ' ') { e.preventDefault(); chain = false; next(); }\n" ++
  "  else if (e.key === 'ArrowLeft') back();\n" ++
  "  else if (e.key === ',') { stop(); chain = false; show(Math.max(0, at - 1)); }\n" ++
  "  else if (e.key === '.') { stop(); chain = false; show(Math.min(pics.length - 1, at + 1)); }\n" ++
  "  else if (e.key === 'Home') { stop(); chain = false; show(0); }\n" ++
  "  else if (e.key === 'End') { stop(); chain = false; show(frames[frames.length - 1]); }\n" ++
  "  else if (e.key === 'p' || e.key === 'P') all(); });\n" ++
  "Promise.all(pics.map(p => load(p[0]))).then(ts => { ts.forEach(t => { const [w, h] = dims(t);\n" ++
  "  maxW = Math.max(maxW, w); maxH = Math.max(maxH, h); }); fit(); });\nshow(0);\n</script>\n</body>\n</html>\n"

/-- One kept run, as the gallery lists it: its folder and what its `run.json` says. -/
structure KeptRun where
  id : String
  title : String
  label : String
  look : String
  frames : Nat
  last : String

/-- The kept runs of `dir/runs/`, newest first: a run's folder name begins with its time. -/
def keptRuns (dir : System.FilePath) : IO (List KeptRun) := do
  let runs := dir / "runs"
  unless ← runs.isDir do return []
  let mut out : Array KeptRun := #[]
  for e in ← runs.readDir do
    let file := e.path / "run.json"
    unless ← file.pathExists do continue
    let some j := (Lean.Json.parse (← IO.FS.readFile file)).toOption | continue
    let str (k : String) := (j.getObjValAs? String k).toOption.getD ""
    let run : KeptRun := {
      id := e.fileName
      title := str "title"
      label := str "label"
      look := str "look"
      frames := (j.getObjValAs? Nat "frames").toOption.getD 0
      last := str "last" }
    out := out.push run
  pure (out.toList.mergeSort fun a b => decide (b.id ≤ a.id))

/-- The pages the studio links beside its entries, when they exist: a label and a path from the
studio's folder. The looks and the PC's probes stand in the folder; the documents stand under the
repository's `.lake/gen`, reached from the folder when it lies inside the working directory. -/
def studioLinks (dir : System.FilePath) : IO (List (String × String)) := do
  let mut links : Array (String × String) := #[]
  if ← (dir / "looks" / "index.html").pathExists then links := links.push ("looks", "looks/index.html")
  for (label, file) in [("marks", "glyphs.html"), ("cells", "cells.html"),
      ("tube studies", "tubes.html"), ("peg vocabulary", "tube-glyphs.html"),
      ("program pegs", "program-pegs.html")] do
    if ← (dir / "docs" / file).pathExists then links := links.push (label, "docs/" ++ file)
  let probes := dir / "probes"
  if ← probes.isDir then
    let pages := (← probes.readDir).filter (·.fileName.endsWith ".html")
    for e in pages.qsort (fun a b => a.fileName < b.fileName) do
      links := links.push ("probe " ++ (e.fileName.dropEnd 5).toString, "probes/" ++ e.fileName)
  let cwd := (← IO.currentDir).toString
  let here := (← IO.FS.realPath dir).toString
  if here.startsWith (cwd ++ "/") then
    let up := String.join (((here.drop (cwd.length + 1)).toString.splitOn "/").map fun _ => "../")
    for (label, file) in [("site", ".lake/gen/site/index.html"),
        ("semantics", ".lake/gen/site/semantics/index.html"),
        ("architecture map", ".lake/gen/architecture-map.html")] do
      if ← (System.FilePath.mk file).pathExists then links := links.push (label, up ++ file)
  return links.toList

/-- **The studio** (decisions row 362): every kept entry, newest first, its last picture linking to
its player, and the looks, the probes and the documents a click away. Each entry carries its
fields as data attributes, for an agent that reads the page. The page asks for `index.json` every
two seconds and reloads when a newer entry has come. When the document specimen exists
(`tools/view/v -d`), its dark and paper pages stand side by side above the entries, each reloaded
when its file is written again, and both when the page's rules (`page.css`) change. -/
def galleryPage (runs : List KeptRun) (links : List (String × String)) : String :=
  let card (r : KeptRun) : String :=
    "<section data-entry=\"" ++ escape r.id ++ "\" data-title=\"" ++ escape r.title ++ "\" data-look=\"" ++
    escape r.look ++ "\" data-frames=\"" ++ toString r.frames ++ "\" data-label=\"" ++ escape r.label ++
    "\"><a href=\"runs/" ++ escape r.id ++ "/index.html\"><img loading=\"lazy\" src=\"runs/" ++
    escape r.id ++ "/" ++ escape r.last ++ ".svg\" alt=\"" ++ escape r.title ++ ", picture " ++ escape r.last ++
    "\"></a><h2><a href=\"runs/" ++ escape r.id ++ "/index.html\">" ++ escape r.title ++
    "</a></h2><p class=\"meta\">" ++ escape r.label ++ " · " ++ escape r.look ++ " · " ++
    toString r.frames ++ " frames</p></section>\n"
  let nav := " · ".intercalate (links.map fun (label, href) =>
    "<a href=\"" ++ escape href ++ "\">" ++ escape label ++ "</a>")
  let newest := (Lean.Json.str ((runs.head?.map (·.id)).getD "")).compress
  "<!doctype html>\n<html lang=\"en\" data-look=\"dark\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>Studio</title>\n<style>\n" ++
  Tokens.css {} ++ pageRules ++
  "main { display: grid; grid-template-columns: repeat(auto-fill, minmax(360px, 1fr)); gap: 20px; }\n" ++
  "nav { font-family: var(--e4-font-data-family); font-size: 13px; }\n" ++
  "h2 { font-family: var(--e4-font-data-family); font-size: 15px; margin: 8px 0 2px; }\n" ++
  "h2 a { text-decoration: none; }\nsection img { max-height: 320px; object-fit: contain; object-position: left top; }\n" ++
  ".docs { margin: 0 0 28px; }\n.docs h2 { margin: 0 0 8px; }\n" ++
  ".pair { display: grid; grid-template-columns: repeat(2, minmax(0, 1fr)); gap: 12px; }\n" ++
  ".pair iframe { width: 100%; height: 62vh; border: 1px solid var(--e4-color-rule); border-radius: 4px; background: transparent; }\n" ++
  "@media (max-width: 900px) { .pair { grid-template-columns: minmax(0, 1fr); } }\n" ++
  "</style>\n</head>\n<body>\n<header><h1>Studio</h1><nav>" ++ nav ++ "</nav><span class=\"meta\">" ++
  toString runs.length ++ " entries, newest first; the page reloads when one comes</span></header>\n<main>\n" ++
  String.join (runs.map card) ++ "</main>\n<script>\nconst newest = " ++ newest ++ ";\n" ++
  "const stamps = new Map();\n" ++
  "const stamp = async src => { try { const r = await fetch(src, { method: 'HEAD', cache: 'no-cache' });\n" ++
  "  return r.ok ? r.headers.get('Last-Modified') : null; } catch (e) { return null; } };\n" ++
  "async function docs() { if (!(await stamp('docs/specimen-dark.html'))) return;\n" ++
  "  const box = document.createElement('section'); box.className = 'docs'; box.setAttribute('aria-label', 'document specimen');\n" ++
  "  box.innerHTML = '<h2>Document specimen <span class=\"meta\">dark beside paper; reloads when written (v -d) and when page.css changes</span></h2>' +\n" ++
  "    '<div class=\"pair\"><iframe data-watch src=\"docs/specimen-dark.html\" title=\"the specimen in the dark look\"></iframe>' +\n" ++
  "    '<iframe data-watch src=\"docs/specimen-paper.html\" title=\"the specimen in the paper look\"></iframe></div>';\n" ++
  "  document.querySelector('header').after(box); }\n" ++
  "const rules = '../../Tools/Document/page.css';\n" ++
  "async function watch() { const frames = [...document.querySelectorAll('iframe[data-watch]')];\n" ++
  "  const r = frames.length ? await stamp(rules) : null; const restyle = r && stamps.has(rules) && stamps.get(rules) !== r;\n" ++
  "  if (r) stamps.set(rules, r);\n" ++
  "  for (const f of frames) { const m = await stamp(f.getAttribute('src'));\n" ++
  "    if (restyle || (m && stamps.has(f) && stamps.get(f) !== m)) f.contentWindow.location.reload();\n" ++
  "    if (m) stamps.set(f, m); } }\n" ++
  "docs().then(watch);\n" ++
  "setInterval(async () => {\n  try {\n" ++
  "    const index = await (await fetch('index.json', { cache: 'no-cache' })).json();\n" ++
  "    if ((index.entries[0] || '') !== newest) location.reload();\n  } catch (e) {}\n  watch();\n}, 2000);\n" ++
  "</script>\n</body>\n</html>\n"

/-- Rewrite `dir/index.html`, the studio, and `dir/index.json`, its entries newest first, which
the studio asks for to know when to reload. -/
def writeGallery (dir : System.FilePath) : IO Unit := do
  let runs ← keptRuns dir
  IO.FS.createDirAll dir
  IO.FS.writeFile (dir / "index.html") (galleryPage runs (← studioLinks dir))
  IO.FS.writeFile (dir / "index.json")
    ((Lean.Json.mkObj [("entries", .arr (runs.map fun r => Lean.Json.str r.id).toArray)]).compress ++ "\n")
  IO.println s!"view: {runs.length} kept entries in {dir / "index.html"}"

/-- A located graph refusal at the driver boundary. -/
def graphRefusal (r : GraphCheck.Refusal) : String :=
  let site := match r.site with
    | .canvas => "canvas" | .node => "node" | .edge => "edge"
    | .placed => "placed" | .route => "route" | .region => "region"
    | .mark => "mark" | .attachment => "attachment"
  let field := match r.field with
    | .key => "key" | .source => "source" | .target => "target"
    | .vertex i => s!"vertex[{i}]" | .width => "width" | .height => "height"
    | .x => "x" | .y => "y" | .right => "right" | .bottom => "bottom"
    | .length => "length" | .downward i => s!"downward[{i}]"
  let reason := match r.reason with
    | .emptyKey => "empty key" | .duplicateKey => "duplicate key"
    | .endpointOutside p n => s!"endpoint {p} outside {n} nodes"
    | .unresolvedKey key => s!"unresolved key {key}"
    | .tooShort => "route has fewer than two vertices"
    | .negative v => s!"negative value {v}"
    | .outside far bound => s!"extent {far} exceeds {bound}"
    | .doesNotDescend => "segment does not descend"
    | .notPoint => "attachment names a node"
    | .offMark => "point is outside its declared mark"
  s!"{site}[{r.index}].{field}: {reason}"

/-- Write each frame's outputs into `out`, with `motion - 1` pictures before each frame after the
first: the moments of the step from the frame before (`sample`). Each step's moment at its end is
the next frame by `sample_end`, so no check repeats it. One stroke cache threads the frames and the
moments between them, so a route that only moved reuses its stroke (`Connector.cached_eq`).
Report the splice check: the lines outside each spliced edit's subtree keep their text, type and
note (`keptUnchanged`). -/
def writeFrames (L : Look) (out : System.FilePath) (frames : List Build.Frame) (motion : Nat)
    (title label : String := "") (gallery : Bool := false) : IO Unit := do
  for (f, i) in frames.zipIdx do
    if let some graph := f.page.graph then
      match GraphCheck.laid graph.laid with
      | .ok () => pure ()
      | .error refusal => throw (IO.userError s!"view: frame {i + 1}: {graphRefusal refusal}")
      unless graph.laid.boxesApart do
        throw (IO.userError s!"view: frame {i + 1}: graph boxes overlap")
  IO.FS.createDirAll out
  let mut pics : Array (String × Bool) := #[]
  let mut text : Array String := #[]
  let mut prev : Option Page := none
  let mut kept := 0
  let mut same := 0
  let mut spliced := 0
  let mut cache : Laid.StrokeCache := {}
  for (f, i) in frames.zipIdx do
    let g := f.page
    let name := frameName (i + 1)
    if let some g0 := prev then
      let transition := preparePageMotion L.motion g0 g
      for k in List.range' 1 (motion - 1) do
        cache ← writePage L out s!"{name}-{frameName k}" (transition.sample (k * 1000 / motion)) cache
        pics := pics.push (s!"{name}-{frameName k}", false)
      if f.spliced then
        if let some a := f.edit then
          let (n, k) := keptUnchanged g0 g (Program.bracket a)
          kept := kept + n
          same := same + k
          spliced := spliced + 1
    cache ← writePage L out name g cache
    pics := pics.push (name, true)
    text := text ++ (pageText g).toArray ++ #[""]
    prev := some g
  IO.FS.writeFile (out / "frames.txt") ("\n".intercalate text.toList)
  IO.FS.writeFile (out / "index.html") (playerPage L (← Tokens.lookFile "paper") title label pics.toList gallery)
  IO.FS.writeFile (out / "run.json") (Lean.Json.compress (Lean.Json.mkObj [
    ("title", title), ("label", label), ("look", L.name), ("frames", frames.length),
    ("last", (pics.toList.getLast?.map (·.1)).getD "")]) ++ "\n")
  let graphs := frames.filterMap fun f => f.page.graph.map (·.laid)
  IO.println s!"view: {frames.length} frames in {out}, {motion - 1} between each two"
  IO.println s!"C\tkept-lines-unchanged\t{spliced} spliced edits\t{same} of {kept} lines"
  IO.println s!"C\tgraph-boxes-apart\t{graphs.length} graphs\t{(graphs.filter Laid.boxesApart).length} apart"
  IO.println s!"C\tgraph-edges-descend\t{graphs.length} graphs\t{(graphs.filter Laid.edgesDescend).length} descend"
  IO.println s!"C\tgraph-admitted\t{graphs.length} graphs\t{graphs.length} admitted"
  IO.println s!"C\tgraph-dims-valid\t{graphs.length} graphs\t{(graphs.filter Laid.dimsValid).length} valid"

/-- Read a request file: one JSON object a line; a blank line is skipped. -/
def readRequests (file : System.FilePath) : IO (List Tools.Session.Request) := do
  let lines ← IO.FS.lines file
  let mut out : Array Tools.Session.Request := #[]
  for line in lines do
    let line := line.trimAscii.toString
    if line.isEmpty then continue
    match Lean.Json.parse line >>= Tools.Session.Request.fromJson? with
    | .ok r => out := out.push r
    | .error e => throw (IO.userError s!"view: a request does not read: {e}")
  return out.toList

/-- The settings of a run: the pictures of motion between two frames (`--motion N`, default 20;
1 draws none), whether the marks are drawn (`--plain` draws none), and the look (`--look`). -/
structure Settings where
  motion : Nat := 20
  marks : Bool := true
  look : Option String := none
  /-- The run's name in the gallery (`--label`). -/
  label : String := ""
  /-- The folder whose list of kept runs the run rewrites (`--gallery`). -/
  gallery : Option String := none

/-- Read the flags before the command. -/
def settingsOf : List String → Settings × List String
  | "--motion" :: n :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with motion := n.toNat?.getD 20 }, rest)
  | "--plain" :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with marks := false }, rest)
  | "--look" :: l :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with look := some l }, rest)
  | "--label" :: l :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with label := l }, rest)
  | "--gallery" :: d :: rest =>
    let (st, rest) := settingsOf rest
    ({ st with gallery := some d }, rest)
  | rest => ({}, rest)

/-- The frames, with the settings' marks. -/
def withMarks (st : Settings) (frames : List Build.Frame) : List Build.Frame :=
  frames.map fun f => { f with page := { f.page with marks := st.marks } }

/-- The folder of the looks. -/
def looksDir : System.FilePath := "tools/view/looks"

/-- A look's name: its file's name without `.tokens.json`. -/
def lookName (path : System.FilePath) : String := (path.fileName.getD "look").replace ".tokens.json" ""

/-- A look's token file read over the dark look; a refusal names the token and the reason. -/
def readLookFile (path : System.FilePath) : IO Look := do
  match Tokens.parseLook {} (lookName path) (← IO.FS.readFile path) with
  | .ok L => pure L
  | .error why => throw (IO.userError s!"view: the look {path} is refused at {why}")

/-- The look a `--look` names: the dark look by default or by name, a file of `tools/view/looks/`
by its name, or a token file by its path. -/
def lookOf : Option String → IO Look
  | none | some "dark" => pure {}
  | some l => readLookFile (if l.endsWith ".json" then l else looksDir / s!"{l}.tokens.json")

/-- The token files of a folder, in order of name. -/
def lookFiles (dir : System.FilePath) : IO (List System.FilePath) := do
  let entries ← dir.readDir
  let files := entries.toList.filter (·.fileName.endsWith ".tokens.json") |>.map (·.path)
  pure (files.mergeSort fun a b => decide (a.toString ≤ b.toString))

/-- The page of the looks side by side, in the dark look's own properties. -/
def looksIndex (looks : List Look) : String :=
  let figure (L : Look) : String :=
    s!"<section><h2>{escape L.name}</h2><p>{escape L.description}</p>" ++
    s!"<p class=\"files\"><a href=\"{L.name}/{L.name}.tokens.json\">tokens</a> · <a href=\"{L.name}/{L.name}.css\">css</a></p>" ++
    s!"<div class=\"pair\"><img src=\"{L.name}/specimen.svg\" alt=\"the graph specimen in {escape L.name}\"><img src=\"{L.name}/program.svg\" alt=\"pFork built, in {escape L.name}\"></div></section>\n"
  "<!doctype html>\n<html lang=\"en\" data-look=\"dark\">\n<head>\n<meta charset=\"utf-8\">\n" ++
  "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>Looks</title>\n" ++
  "<link rel=\"stylesheet\" href=\"looks.css\">\n<style>\n" ++
  "body { margin: 0; padding: 24px 16px 48px; background: var(--e4-color-ground); color: var(--e4-color-ink); font-family: var(--e4-font-name-family); }\n" ++
  "h1 { font-family: var(--e4-font-title-family); font-weight: var(--e4-font-title-weight); margin: 0 0 4px; }\n" ++
  "h2 { font-family: var(--e4-font-data-family); font-size: 15px; margin: 32px 0 2px; }\n" ++
  "p { margin: 0 0 6px; max-width: 72ch; font-style: var(--e4-font-label-style); }\n" ++
  ".files a { color: var(--e4-color-ink); font-family: var(--e4-font-data-family); font-size: 13px; font-style: normal; }\n" ++
  ".pair { display: grid; grid-template-columns: repeat(auto-fit, minmax(320px, 1fr)); gap: 12px; align-items: start; }\n" ++
  ".pair img { width: 100%; height: auto; border: 1px solid var(--e4-color-rule); }\n" ++
  "</style>\n</head>\n<body>\n<h1>Looks</h1>\n" ++
  "<p>Each look is a token file of the W3C design-token format, read over the dark look. The same two pages are drawn in each.</p>\n" ++
  String.join (looks.map figure) ++ "</body>\n</html>\n"

/-- Write every look of `dir`, and the dark look, side by side into `out`. -/
def writeLooks (dir out : System.FilePath) : IO UInt32 := do
  let files ← lookFiles dir
  let looks := ({} : Look) :: (← files.mapM readLookFile)
  let specimens ← match Tools.View.Specimen.checkedFrames with
    | .ok frames => pure frames
    | .error refusal => throw (IO.userError s!"view: specimen: {graphRefusal refusal}")
  let some specimen := specimens.getLast? | throw (IO.userError "view: the specimen has no frame")
  let some program := (List.lookup "pFork" Effect4.Program.Wire.Corpus.all >>= Build.requests).bind
      fun reqs => (Build.frames "pFork" reqs).getLast?.map (·.page)
    | throw (IO.userError "view: pFork has no frame built")
  IO.FS.createDirAll out
  for L in looks do
    let dirL := out / L.name
    IO.FS.createDirAll dirL
    IO.FS.writeFile (dirL / s!"{L.name}.tokens.json") (Tokens.render L)
    IO.FS.writeFile (dirL / s!"{L.name}.css") (Tokens.css L)
    let _ ← writePage L dirL "specimen" specimen
    let _ ← writePage L dirL "program" program
  IO.FS.writeFile (out / "looks.css") (String.join (looks.map Tokens.css) ++ Tokens.rules)
  IO.FS.writeFile (out / "index.html") (looksIndex looks)
  let back := looks.filter (Tokens.roundTrips {})
  IO.println s!"view: {looks.length} looks in {out}"
  IO.println s!"C\tlook-round-trip\t{looks.length} looks\t{back.length} come back from their token files"
  return if back.length == looks.length then 0 else 1

/-- Write a run's frames under the settings, then the gallery's list if one is named. -/
def keep (st : Settings) (L : Look) (out : System.FilePath) (frames : List Build.Frame) (title : String) :
    IO UInt32 := do
  writeFrames L out frames st.motion title st.label st.gallery.isSome
  if let some g := st.gallery then writeGallery g
  return 0

def main (args : List String) : IO UInt32 := do
  let (st, args) := settingsOf args
  if let ["looks", dir, out] := args then return ← writeLooks dir out
  if let ["gallery", dir] := args then
    writeGallery dir
    return 0
  let L ← lookOf st.look
  match args with
  | ["build", name, out] =>
    match List.lookup name Effect4.Program.Wire.Corpus.all with
    | none =>
      IO.eprintln s!"view: no corpus program {name}; the programs are {Effect4.Program.Wire.Corpus.all.map (·.1)}"
      return 2
    | some p =>
      match Build.requests p with
      | none =>
        IO.eprintln s!"view: a sub-program of {name} has no type, so it has no hole row"
        return 1
      | some reqs =>
        IO.FS.createDirAll out
        IO.FS.writeFile (System.FilePath.mk out / "requests.jsonl")
          ("\n".intercalate (reqs.map fun r => r.toJson.compress) ++ "\n")
        keep st L out (withMarks st (Build.frames name reqs)) s!"{name}, built"
  | ["run", name, out] =>
    match List.lookup name Effect4.Program.Wire.Corpus.all with
    | none =>
      IO.eprintln s!"view: no corpus program {name}; the programs are {Effect4.Program.Wire.Corpus.all.map (·.1)}"
      return 2
    | some p =>
      match Tools.View.Run.frames name p with
      | none =>
        IO.eprintln s!"view: {name} is not admitted, so it does not run"
        return 1
      | some pages =>
        keep st L out (withMarks st (pages.map fun page => ({ page } : Build.Frame))) s!"{name}, run"
  | ["specimen", out] => do
    let specimens ← match Tools.View.Specimen.checkedFrames with
      | .ok frames => pure frames
      | .error refusal => throw (IO.userError s!"view: specimen: {graphRefusal refusal}")
    keep st L out (specimens.map fun page => ({ page } : Build.Frame)) "graph specimen"
  | ["flows", out] =>
    keep st L out (Tools.View.FlowSpecimen.frames.map fun page => ({ page } : Build.Frame))
      "program graph cases"
  | ["session", file, out] =>
    keep st L out (withMarks st (Build.frames file (← readRequests file)))
      ((System.FilePath.mk file).fileStem.getD file)
  | _ =>
    IO.eprintln ("usage: view [--motion N] [--plain] [--look LOOK] [--label TEXT] [--gallery DIR] " ++
      "(build NAME | run NAME | session FILE | specimen | flows) OUT\n       view looks DIR OUT\n       view gallery DIR")
    return 2
