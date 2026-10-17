(* Kit_view — an animated page of a program's runs at every budget, and its paths (hand-written).

   What it is: one self-contained HTML page (no network, no script library) that plays a run's
   frames, the call tree's run at budgets 0, 1, 2, …, as one growing tube, and draws every frame as
   a row of the chain and every explored path as a row of its own. The frames and paths are the
   kit's (Kit.frames, Kit.explore); this module only lays them out. Every label is written here,
   in OCaml, so the page reads no program or value JSON.
   Depends on: Kit, Eff_types, Eff_json_text.

   Behaviours it holds itself to:
   V1  The page is one file: its style and its script are inline, and its data is one JSON value
       in the script.                                                   by construction
   V2  A frame is drawn from its steps alone, so a frame that extends the one before draws as the
       one before with circles added (Kit B3).                          by construction
   V3  The page names a cut as a cut, never as a divergence: the verdict of an unsettled run says
       it is a finite probe.                                            by construction *)

open Eff_types
module J = Eff_json_text

(* A short text of a value, for a label. *)
let rec value_text (v : val_) : string =
  match v with
  | Val_unit -> "()"
  | Val_bool b -> string_of_bool b
  | Val_nat n -> string_of_int n
  | Val_negInt n -> string_of_int (- (n + 1))
  | Val_str s -> Printf.sprintf "%S" s
  | Val_bytes d -> Printf.sprintf "<%d bytes>" (List.length d)
  | Val_list xs -> "[" ^ String.concat ", " (List.map value_text xs) ^ "]"
  | Val_pair (a, b) -> "(" ^ value_text a ^ ", " ^ value_text b ^ ")"
  | Val_none -> "none"
  | Val_some a -> "some " ^ value_text a
  | Val_ctor (i, args) -> Printf.sprintf "ctor %d [%s]" i (String.concat ", " (List.map value_text args))
  | Val_ref _ -> "<ref>"
  | Val_handle (k, n) -> Printf.sprintf "<handle %d %d>" k n
  | Val_float _ -> "<float>"

let err_text = function
  | Err_boom -> "boom"
  | Err_tag n -> Printf.sprintf "tag %d" n
  | Err_tagged (t, m) -> Printf.sprintf "%s: %s" t m
  | Err_text s -> Printf.sprintf "%S" s
  | Err_payload v -> value_text v

let exit_text (ex : Kit.exit) =
  match ex with
  | Exit_success v -> "ok " ^ value_text v
  | Exit_failure (Reason_fail (e, _) :: _) -> "failed " ^ err_text e
  | Exit_failure (Reason_die _ :: _) -> "died"
  | Exit_failure (Reason_interrupt _ :: _) -> "interrupted"
  | Exit_failure [] -> "failed"

let row_name (app : Kit.app) i =
  match List.nth_opt app.Kit_gen.rows i with Some (r : row) -> r.name | None -> Printf.sprintf "row %d" i

let step_json app : Kit.step -> J.t = function
  | Kit.Step_called (i, v, ex) ->
    J.Object [ ("kind", J.String "call"); ("text", J.String (Printf.sprintf "%s(%s) → %s" (row_name app i) (value_text v) (exit_text ex))) ]
  | Kit.Step_celled (_, v) -> J.Object [ ("kind", J.String "cell"); ("text", J.String ("cell → " ^ value_text v)) ]

let stop_json app : Kit.stop -> J.t = function
  | Kit.Stop_finished ex -> J.Object [ ("kind", J.String "finished"); ("text", J.String ("finished: " ^ exit_text ex)) ]
  | Kit.Stop_cut -> J.Object [ ("kind", J.String "cut"); ("text", J.String "cut by the budget") ]
  | Kit.Stop_waiting (i, v) ->
    J.Object [ ("kind", J.String "waiting"); ("text", J.String (Printf.sprintf "waiting on %s(%s)" (row_name app i) (value_text v))) ]

let run_json app steps stop extra =
  J.Object (extra @ [ ("steps", J.Array (List.map (step_json app) steps)); ("stop", stop_json app stop) ])

(* The page's data: the frames, the settled budget, the paths. *)
let data ~title ~(app : Kit.app) ~(frames : 's Kit.run list) ~(settled : 's Kit.settled) ~(paths : Kit.path list) : J.t =
  J.Object
    [ ("title", J.String title);
      ("frames", J.Array (List.mapi (fun k (f : 's Kit.run) -> run_json app f.steps f.stop [ ("budget", J.Int k) ]) frames));
      ("verdict",
       J.String
         (match settled with
          | Kit.Settled { budget; run } ->
            Printf.sprintf "Settles at budget %d: %s. Every larger budget gives the same run." budget
              (match run.stop with
               | Kit.Stop_finished ex -> "finished, " ^ exit_text ex
               | Kit.Stop_waiting (i, v) -> Printf.sprintf "waiting on %s(%s)" (row_name app i) (value_text v)
               | Kit.Stop_cut -> "cut")
          | Kit.Unsettled { limit; _ } ->
            Printf.sprintf "Cut at every budget up to %d: a finite probe, not a divergence." limit));
      ("paths", J.Array (List.map (fun (p : Kit.path) -> run_json app p.steps p.stop []) paths)) ]

let style = {|
:root { --ground:#fbfaf7; --panel:#fff; --ink:#1f2328; --muted:#6a6f76; --line:#d7d4cc; --tube:#e9e4d8;
  --edge:#9b927f; --call:#2f6f8f; --cell:#7a5b9a; --finished:#2e7d4f; --cut:#b0563b; --wait:#b08a2e; }
@media (prefers-color-scheme: dark) { :root { --ground:#16181b; --panel:#1d2024; --ink:#e8e6e1; --muted:#9aa0a6;
  --line:#343840; --tube:#2b2f35; --edge:#6f7680; --call:#6fb3d2; --cell:#b897d6; --finished:#6cc08f; --cut:#e08a6f; --wait:#e0be6f; } }
* { box-sizing: border-box; }
body { margin:0; background:var(--ground); color:var(--ink); font:15px/1.45 ui-sans-serif,-apple-system,"Segoe UI",sans-serif; }
main { max-width:1040px; margin:0 auto; padding:24px 16px 48px; }
h1 { font-size:22px; margin:0 0 6px; }
.lead { color:var(--muted); margin:0 0 16px; max-width:72ch; }
.card { background:var(--panel); border:2px solid var(--line); border-radius:14px; padding:14px 16px; margin-bottom:16px; }
.card h2 { font-size:13px; text-transform:uppercase; letter-spacing:.06em; color:var(--muted); margin:0 0 8px; }
.controls { display:flex; align-items:center; gap:12px; flex-wrap:wrap; }
.controls button { border:2px solid var(--line); background:var(--panel); color:var(--ink); border-radius:10px; padding:4px 12px; font:inherit; cursor:pointer; min-width:72px; }
.controls input { flex:1 1 240px; accent-color:var(--ink); }
.budget { font-variant-numeric:tabular-nums; min-width:9ch; }
.verdict { margin-top:10px; }
svg { display:block; width:100%; height:auto; }
.tube { fill:var(--tube); stroke:var(--edge); stroke-width:2; }
.step { stroke:var(--panel); stroke-width:2; transition:opacity .35s ease, transform .35s ease; }
.step.call { fill:var(--call); } .step.cell { fill:var(--cell); }
.step.new { opacity:0; transform:scale(.4); }
.lab { fill:var(--muted); font:11px ui-monospace,Menlo,monospace; }
.now rect.band { fill:var(--line); opacity:.35; }
.detail { font:13px/1.5 ui-monospace,Menlo,monospace; margin-top:8px; min-height:1.5em; overflow-wrap:anywhere; }
.legend { display:flex; gap:16px; flex-wrap:wrap; font-size:13px; color:var(--muted); margin-top:8px; }
.legend i { display:inline-block; width:10px; height:10px; border-radius:50%; margin-right:6px; vertical-align:-1px; }
|}

let script = {|
const NS = "http://www.w3.org/2000/svg";
function el(n, a, p) { const e = document.createElementNS(NS, n); for (const k in a) e.setAttribute(k, a[k]); if (p) p.appendChild(e); return e; }
function tube(g, run, y, unit, shown, detail) {
  const r = unit / 2, x0 = 16, len = run.steps.length * unit * 1.5 + unit * 1.2;
  el("rect", { class: "tube", x: x0, y: y - r - 3, rx: r + 3, width: len + unit * .4, height: unit + 6 }, g);
  run.steps.forEach((s, i) => {
    const cx = x0 + unit + i * unit * 1.5;
    const c = el("circle", { class: "step " + s.kind + (i >= shown ? " new" : ""), cx, cy: y, r: r - 1,
      style: "transform-origin:" + cx + "px " + y + "px" }, g);
    el("title", {}, c).textContent = s.text;
    if (detail) c.addEventListener("mouseenter", () => { detail.textContent = s.text; });
  });
  const cx = x0 + len + unit * .4 + r + 6, k = run.stop.kind;
  const cap = k === "finished" ? el("circle", { cx, cy: y, r: r + 2, fill: "var(--finished)" }, g)
    : k === "cut" ? el("circle", { cx, cy: y, r: r + 1, fill: "none", stroke: "var(--cut)", "stroke-width": 2, "stroke-dasharray": "3 3" }, g)
    : el("circle", { cx, cy: y, r: r + 1, fill: "none", stroke: "var(--wait)", "stroke-width": 3 }, g);
  el("title", {}, cap).textContent = run.stop.text;
  return cx + r + 8;
}
function rows(svg, runs, label, now, pick) {
  const h = 22; svg.replaceChildren(); let wide = 360;
  runs.forEach((run, i) => {
    const g = el("g", { class: i === now ? "now" : "" }, svg);
    if (i === now) el("rect", { class: "band", x: 0, y: i * h + 2, width: 1000, height: h, rx: 6 }, g);
    el("text", { class: "lab", x: 4, y: i * h + 17 }, g).textContent = label(i);
    const end = tube(el("g", { transform: "translate(48,0)" }, g), run, i * h + 13, 12, run.steps.length, null);
    const lab = el("text", { class: "lab", x: end + 52, y: i * h + 17 }, g);
    lab.textContent = run.stop.text;
    wide = Math.max(wide, end + 52 + 7 * run.stop.text.length + 8);
    if (pick) { g.style.cursor = "pointer"; g.addEventListener("click", () => pick(i)); }
  });
  svg.querySelectorAll("rect.band").forEach(b => b.setAttribute("width", wide));
  svg.setAttribute("viewBox", "0 0 " + wide + " " + (runs.length * h + 8));
}
const $ = id => document.getElementById(id);
const slider = $("slider"), frame = $("frame"), detail = $("detail"), play = $("play");
let k = 0, last = 0, timer = null;
function render() {
  const f = DATA.frames[k];
  $("budget").textContent = "budget " + k;
  frame.replaceChildren();
  const end = tube(frame, f, 50, 20, last, detail);
  el("text", { class: "lab", x: end, y: 55 }, frame).textContent = f.stop.text;
  const longest = DATA.frames[DATA.frames.length - 1].steps.length * 30 + 120;
  frame.setAttribute("viewBox", "0 0 " + Math.max(360, longest + 8 * f.stop.text.length) + " 100");
  requestAnimationFrame(() => frame.querySelectorAll(".step.new").forEach(c => c.classList.remove("new")));
  last = f.steps.length;
  detail.textContent = f.steps.length ? f.steps[f.steps.length - 1].text : "no step yet";
  rows($("chain"), DATA.frames, i => "k=" + i, k, setK);
}
function setK(i) { k = i; slider.value = i; render(); }
function stop() { if (timer) clearInterval(timer); timer = null; play.textContent = "Play"; }
play.addEventListener("click", () => {
  if (timer) return stop();
  if (k >= DATA.frames.length - 1) { last = 0; setK(0); }
  play.textContent = "Pause";
  timer = setInterval(() => { if (k >= DATA.frames.length - 1) return stop(); setK(k + 1); }, 650);
});
slider.addEventListener("input", () => { stop(); k = Number(slider.value); render(); });
document.title = DATA.title; $("title").textContent = DATA.title; $("verdict").textContent = DATA.verdict;
slider.max = DATA.frames.length - 1;
if (DATA.paths.length) rows($("paths"), DATA.paths, i => "#" + (i + 1), -1, null); else $("pathsCard").hidden = true;
render();
|}

let body = {|
<main>
  <h1 id="title"></h1>
  <p class="lead">Each frame is the program's call tree run at budget <code>k</code>: every loop tests at most
  <code>k</code> times and definitions nest at most <code>k</code> deep. A frame only extends the one before,
  so the frames play as one growing run. A cut is the budget's end, never a divergence.</p>
  <section class="card">
    <h2>Frame</h2>
    <div class="controls"><button id="play">Play</button>
      <input type="range" id="slider" min="0" max="0" value="0" aria-label="Budget"><span class="budget" id="budget"></span></div>
    <svg id="frame" viewBox="0 0 1000 100" role="img" aria-label="The run at the chosen budget"></svg>
    <div class="detail" id="detail"></div>
    <div class="legend"><span><i style="background:var(--call)"></i>host call</span>
      <span><i style="background:var(--cell)"></i>cell</span><span><i style="background:var(--finished)"></i>finished</span>
      <span><i style="border:2px solid var(--wait)"></i>waiting</span><span><i style="border:2px dashed var(--cut)"></i>cut by the budget</span></div>
    <div class="verdict" id="verdict"></div>
  </section>
  <section class="card"><h2>Every budget</h2><svg id="chain" role="img" aria-label="Every frame, one row a budget"></svg></section>
  <section class="card" id="pathsCard"><h2>Every path, its replies drawn from the rows' types</h2>
    <svg id="paths" role="img" aria-label="Every explored path"></svg></section>
</main>
|}

(* `</` inside the data would end the script element: write it as `<\/`. *)
let script_safe (s : string) =
  let b = Buffer.create (String.length s) in
  String.iteri (fun i c -> if c = '/' && i > 0 && s.[i - 1] = '<' then Buffer.add_string b "\\/" else Buffer.add_char b c) s;
  Buffer.contents b

let page (data : J.t) : string =
  String.concat ""
    [ "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n";
      "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n<title>Budget frames</title>\n";
      "<style>"; style; "</style>\n</head>\n<body>"; body; "<script>\nconst DATA = ";
      script_safe (J.render data); ";\n"; script; "</script>\n</body>\n</html>\n" ]
