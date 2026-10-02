import Lean

/-!
Render the existing semantics report's selected feature/proof view. This module owns
presentation only: evidence and statuses come from the v2 report, never graph reachability.
The strict host schema owns the complete report contract. This reader checks required local
fields, identities, node evidence/body variants, edge consumer kinds and graph references.
It does not repeat unknown-key rejection, cross-report claim joins or dependency-cycle checks.
-/
namespace Tools.ProofMapHtml
open Lean

structure Premise where
  name : String
  statement : String
  deriving FromJson

structure Node where
  id : String
  title : String
  kind : String
  status : String
  «module» : String
  path : String
  line : Nat
  levels : Array String
  evidence : Option String
  statement : String
  body : Option String
  premises : Array Premise
  axioms : Array String
  claims : Array String
  omittedReferences : Nat
  deriving FromJson

structure Feature where
  id : String
  title : String
  concepts : Array String
  «syntax» : Array String
  judgments : Array String
  rules : Array String
  requires : Array String
  boundary : String
  deriving FromJson

structure Edge where
  «from» : String
  to : String
  kind : String
  deriving FromJson

structure Work where
  id : String
  title : String
  features : Array String
  after : Array String
  source : String
  reason : String
  deriving FromJson

structure Literature where
  work : String
  locator : String
  «use» : String
  deriving FromJson

structure MapData where
  scope : String
  literature : Array Literature
  features : Array Feature
  nodes : Array Node
  edges : Array Edge
  work : Array Work
  deriving FromJson

private def nonblank (s : String) : Bool := !s.trimAscii.toString.isEmpty

private def unique (label : String) (ids : Array String) : Except String Unit := do
  unless ids.all nonblank do throw s!"proofMap {label}: blank identifier"
  unless ids.toList.eraseDups.length == ids.size do throw s!"proofMap {label}: duplicate identifier"

/-- Local rendering contract only; evidence validation and status derivation remain the
semantics producer's job, and the host schema checks the complete report joins. -/
def decode (report : Json) : Except String MapData := do
  unless (← report.getObjValAs? String "format") == "effect4-semantics-report" do
    throw "proofMap: expected effect4-semantics-report"
  unless (← report.getObjValAs? Nat "schemaVersion") == 2 do
    throw "proofMap: architecture requires semantics report v2; regenerate semantics first"
  let json ← report.getObjVal? "proofMap"
  let data : MapData ← fromJson? json
  unless nonblank data.scope do throw "proofMap: blank extraction scope"
  let nodeIds := data.nodes.map (·.id)
  let featureIds := data.features.map (·.id)
  let workIds := data.work.map (·.id)
  unique "nodes" nodeIds
  unique "features" featureIds
  unique "work" workIds
  -- Option-valued fields are mandatory JSON keys with explicit null when absent.
  for node in (← json.getObjValAs? (Array Json) "nodes") do
    discard <| node.getObjVal? "body"
    discard <| node.getObjVal? "evidence"
  for node in data.nodes do
    unless ["theorem", "definition", "goal"].contains node.kind do
      throw s!"proofMap node {node.id}: unknown kind {node.kind}"
    unless (node.kind == "definition" && node.status == "defined") ||
        (node.kind == "theorem" && node.status == "proved") ||
        (node.kind == "goal" && ["proved", "wanted"].contains node.status) do
      throw s!"proofMap node {node.id}: invalid kind/status combination"
    unless nonblank node.title && nonblank node.statement do
      throw s!"proofMap node {node.id}: blank title or statement"
    if let some body := node.body then
      unless nonblank body do throw s!"proofMap node {node.id}: blank definition body"
    if node.kind == "definition" then
      unless node.evidence.isNone do
        throw s!"proofMap node {node.id}: definition evidence must be null"
    else
      unless node.body.isNone do
        throw s!"proofMap node {node.id}: non-definition body must be null"
      let expected := if node.kind == "theorem" then node.id
        else node.id ++ (if node.status == "proved" then ".checked" else ".wanted")
      unless node.evidence == some expected do
        throw s!"proofMap node {node.id}: {node.kind}/{node.status} evidence must name {expected}"
  for feature in data.features do
    unless nonblank feature.title && nonblank feature.boundary do
      throw s!"proofMap feature {feature.id}: blank title or boundary"
    for id in feature.«syntax» ++ feature.judgments ++ feature.rules do
      unless nodeIds.contains id do throw s!"proofMap feature {feature.id}: unknown node {id}"
    for id in feature.requires do
      unless featureIds.contains id do throw s!"proofMap feature {feature.id}: unknown prerequisite {id}"
  for edge in data.edges do
    unless ["proof-reference", "definition-reference", "statement-reference", "ledger-prerequisite"].contains edge.kind do
      throw s!"proofMap edge: unknown kind {edge.kind}"
    unless nodeIds.contains edge.«from» && nodeIds.contains edge.to do
      throw s!"proofMap edge: unknown endpoint {edge.«from»} -> {edge.to}"
    if let some consumer := data.nodes.find? (fun node => node.id == edge.to) then
      if edge.kind == "proof-reference" &&
          (consumer.kind == "definition" || consumer.status != "proved") then
        throw s!"proofMap edge {edge.«from»} -> {edge.to}: proof-reference consumer must be proved"
      if edge.kind == "definition-reference" && consumer.kind != "definition" then
        throw s!"proofMap edge {edge.«from»} -> {edge.to}: definition-reference consumer must be a definition"
      if edge.kind == "ledger-prerequisite" then
        unless consumer.kind == "goal" &&
            data.nodes.any (fun node => node.id == edge.«from» && node.kind == "goal") do
          throw s!"proofMap edge {edge.«from»} -> {edge.to}: ledger prerequisites must connect goals"
  for item in data.work do
    if nodeIds.contains item.id then throw s!"proofMap work {item.id}: collides with declaration"
    unless nonblank item.title && nonblank item.source && nonblank item.reason do
      throw s!"proofMap work {item.id}: blank title, source or reason"
    for id in item.features do
      unless featureIds.contains id do throw s!"proofMap work {item.id}: unknown feature {id}"
    for id in item.after do
      unless nodeIds.contains id || workIds.contains id do
        throw s!"proofMap work {item.id}: unknown ordering reference {id}"
  return data

private def esc (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;"
    |>.replace "\"" "&quot;" |>.replace "'" "&#39;"

/-- JSON script data is escaped for HTML's raw-text parser, including closing script tags. -/
def scriptData (json : Json) : String :=
  json.compress.replace "&" "\\u0026" |>.replace "<" "\\u003c" |>.replace ">" "\\u003e"

private def safePath (path : String) : Bool :=
  ["src/", "tools/", "Test/", "docs/"].any (fun start => path.startsWith start) &&
    !(path.splitOn "/").contains ".." && !(path.splitOn "/").contains "." &&
    !path.contains '\\' && !path.contains ':' && !path.contains '#' && !path.contains '?'

private def sourceLink (path : String) (line : Nat := 0) : String :=
  let label := esc path ++ if line == 0 then "" else s!":{line}"
  if safePath path then
    "<a href=\"../../" ++ esc path ++ (if line == 0 then "" else s!"#L{line}") ++ "\">" ++ label ++ "</a>"
  else label

private def names (ids : Array String) : String :=
  if ids.isEmpty then "none selected" else String.intercalate ", " (ids.toList.map esc)

private def status (node : Node) : String :=
  if node.status == "wanted" then "Open formal goal; no proof supplied"
  else if node.status == "defined" then "Definition"
  else if node.premises.isEmpty then "Checked theorem"
  else "Checked conditional theorem; hypotheses retained"

/-- Complete text view survives disabled JavaScript and exposes every selected statement. -/
private def fallback (data : MapData) : String := Id.run do
  let mut out := "<details class=\"pm-fallback\"><summary>All selected features, declarations and work as text</summary><p>Same report data as the diagrams. Selection is not a complete census; connections do not propagate proof status.</p>"
  for feature in data.features do
    out := out ++ "<h4>" ++ esc feature.title ++ "</h4><p>" ++ esc feature.boundary ++ "</p>" ++
      "<p>Authored prerequisites: " ++ names feature.requires ++ "</p><p>Concepts: " ++ names feature.concepts ++
      "</p><p>Syntax sorts / constructors: " ++ names feature.«syntax» ++ "</p><p>Judgments / supporting definitions: " ++ names feature.judgments ++
      "</p><p>Rules / theorems / formal goals: " ++ names feature.rules ++ "</p>"
  for node in data.nodes do
    out := out ++ "<details><summary>" ++ esc node.title ++ " · " ++ status node ++ "</summary>" ++
      "<code class=\"pm-exact-name\">" ++ esc node.id ++ "</code><p>" ++ sourceLink node.path node.line ++
      "</p><p>Module: " ++ esc node.«module» ++ "</p><p>Evidence: " ++ esc (node.evidence.getD "none") ++
      "</p><h5>Proposition-valued premises</h5>"
    for premise in node.premises do
      out := out ++ "<p><code>" ++ esc premise.name ++ "</code></p><pre>" ++ esc premise.statement ++ "</pre>"
    if node.premises.isEmpty then
      out := out ++ "<p>No top-level proposition-valued binders; retain other binders and nested conditions in the full statement.</p>"
    out := out ++ "<h5>Full statement</h5><pre>" ++ esc node.statement ++ "</pre>"
    if let some body := node.body then
      out := out ++ "<h5>Definition body · nested conditions</h5><pre>" ++ esc body ++ "</pre>"
    out := out ++ "<p>Universe parameters: " ++ names node.levels ++ "</p><p>Transitive axioms: " ++ names node.axioms ++
      "</p><p>Claims: " ++ names node.claims ++ s!"</p><p>References outside this selection: {node.omittedReferences}.</p></details>"
  out := out ++ "<h4>Connections · prerequisite → consumer</h4><ul>"
  for edge in data.edges do
    out := out ++ "<li>" ++ esc edge.«from» ++ " → " ++ esc edge.to ++ " · " ++ esc edge.kind ++ "</li>"
  out := out ++ "</ul><h4>Proposed work · not formal goals</h4>"
  for item in data.work do
    out := out ++ "<article><h5>" ++ esc item.title ++ "</h5><p>" ++ esc item.reason ++ "</p><p>" ++
      sourceLink item.source ++ "</p><p>Planned after: " ++ names item.after ++ "</p></article>"
  return out ++ "</details>"

private def css : String := r##"
#proof-map .pm-boundary { border-left: 3px solid var(--tools); padding: 8px 12px; background: var(--panel); color: var(--ink-2); }
#proof-map h4 { margin: 8px 0; font-size: 15px; } #proof-map h5 { margin: 20px 0 6px; font-size: 13px; }
#proof-map button, #proof-map select { font: inherit; color: var(--ink); background: var(--panel); border: 1px solid var(--rule); border-radius: 4px; }
#proof-map button { cursor: pointer; padding: 5px 9px; } #proof-map select { padding: 7px; max-width: 100%; }
#proof-map button:hover, #proof-map button:focus-visible, #proof-map select:focus-visible { border-color: var(--accent); outline: 2px solid var(--accent); outline-offset: 2px; }
#proof-map .pm-feature-graph, #proof-map .pm-graph { max-height: 620px; overflow: auto; }
#proof-map .pm-feature-graph svg, #proof-map .pm-graph svg { max-width: none; }
#proof-map .pm-feature-graph { margin-top: 12px; }
#proof-map .pm-controls { display: flex; gap: 10px; flex-wrap: wrap; align-items: center; margin-top: 20px; }
#proof-map .pm-switches { display: flex; gap: 8px 18px; flex-wrap: wrap; width: 100%; border: 1px solid var(--rule); border-radius: 4px; margin: 6px 0; padding: 10px 12px; }
#proof-map .pm-switches legend { font-size: 12px; color: var(--ink-2); } #proof-map .pm-switches label { font-size: 12px; display: inline-flex; align-items: center; gap: 5px; }
#proof-map .pm-counts { font-size: 13px; color: var(--ink-2); }
#proof-map .pm-roles { display: flex; flex-wrap: wrap; gap: 10px 20px; margin: 10px 0 16px; } #proof-map .pm-roles > div { flex: 1 1 190px; }
#proof-map .pm-roles strong { display: block; font-size: 12px; margin-bottom: 4px; }
#proof-map .pm-inline-button { display: inline-block; margin: 2px 4px 2px 0; font: 11px var(--mono); overflow-wrap: anywhere; text-align: left; }
#proof-map .pm-columns { display: grid; grid-template-columns: minmax(0, 1fr) minmax(280px, 350px); gap: 16px; align-items: start; }
#proof-map .pm-detail { padding: 14px; border: 1px solid var(--rule); border-radius: 6px; background: var(--panel); max-height: 620px; overflow: auto; font-size: 13px; overflow-wrap: anywhere; }
#proof-map pre { white-space: pre-wrap; overflow-wrap: anywhere; font: 13px/1.55 var(--mono); }
#proof-map .pm-exact-name { display: block; margin: 8px 0; font-size: 11px; overflow-wrap: anywhere; }
#proof-map .pm-meta { font-size: 12px; color: var(--ink-2); }
#proof-map .pm-badge { border: 1px solid var(--rule); border-radius: 4px; padding: 3px 7px; display: inline-block; font-size: 12px; margin: 4px 0; }
#proof-map dl { margin: 0; } #proof-map dt { font: 12px var(--mono); margin-top: 10px; font-weight: 600; } #proof-map dd { margin: 4px 0 0; white-space: pre-wrap; font: 13px/1.5 var(--mono); }
#proof-map .pm-node { cursor: pointer; } #proof-map .pm-node rect { fill: var(--panel); stroke: var(--rule); stroke-width: 1.5; }
#proof-map .pm-node.pm-context rect { stroke-dasharray: 3 3; } #proof-map .pm-node.pm-open rect { stroke: var(--tools); stroke-dasharray: 7 3; }
#proof-map .pm-node.pm-work-node rect { stroke: var(--tools); stroke-dasharray: 2 4; }
#proof-map .pm-node.pm-selected rect, #proof-map .pm-node:focus rect { stroke: var(--accent); stroke-width: 3; }
#proof-map .pm-node:hover rect { stroke: var(--accent); } #proof-map .pm-node-title { font-size: 12px; font-weight: 600; fill: var(--ink); }
#proof-map .pm-node-status { font-size: 11px; fill: var(--ink-2); } #proof-map .pm-node-name { font: 10px var(--mono); fill: var(--ink-2); }
#proof-map .pm-edge { fill: none; stroke: var(--laws); stroke-width: 1.4; opacity: .8; } #proof-map .pm-arrow { fill: var(--laws); }
#proof-map .pm-edge.pm-definition-reference { stroke: var(--runtime); } #proof-map .pm-arrow.pm-definition-reference { fill: var(--runtime); }
#proof-map .pm-edge.pm-statement-reference { stroke: var(--ink-3); stroke-dasharray: 2 4; } #proof-map .pm-arrow.pm-statement-reference { fill: var(--ink-3); }
#proof-map .pm-edge.pm-ledger-prerequisite { stroke: var(--tests); stroke-dasharray: 7 3; } #proof-map .pm-arrow.pm-ledger-prerequisite { fill: var(--tests); }
#proof-map .pm-edge.pm-work-order, #proof-map .pm-edge.pm-feature-prerequisite { stroke: var(--tools); stroke-dasharray: 5 4; }
#proof-map .pm-arrow.pm-work-order, #proof-map .pm-arrow.pm-feature-prerequisite { fill: var(--tools); }
#proof-map .pm-connections, #proof-map .pm-hidden-connections, #proof-map .pm-fallback { margin-top: 18px; } #proof-map summary { cursor: pointer; color: var(--accent); }
#proof-map .pm-connections ul, #proof-map .pm-hidden-connections ul { font: 11px/1.7 var(--mono); overflow-wrap: anywhere; }
#proof-map .pm-work { margin-top: 22px; } #proof-map .pm-work-item { border-top: 1px solid var(--rule); padding: 10px 0; font-size: 13px; }
#proof-map .pm-work-title { text-align: left; } #proof-map .pm-empty { padding: 18px; }
#proof-map .pm-fallback { font-size: 13px; } #proof-map .pm-fallback td { overflow-wrap: anywhere; }
@media (max-width: 850px) { #proof-map .pm-columns { grid-template-columns: 1fr; } #proof-map .pm-detail { max-height: none; } }
@media print { #proof-map .pm-interface, #proof-map .pm-feature-overview { display: none; } #proof-map .pm-fallback { display: block; } }
"##

private def script : String := r##"
(() => {
  'use strict';
  const root = document.getElementById('proof-map');
  const data = JSON.parse(document.getElementById('proof-map-data').textContent);
  const nodes = new Map(data.nodes.map(n => [n.id, n]));
  const features = new Map(data.features.map(f => [f.id, f]));
  const work = new Map(data.work.map(w => [w.id, w]));
  const kinds = [
    ['proof-reference', 'Proof-body reference'],
    ['definition-reference', 'Definition-body reference'],
    ['statement-reference', 'Statement vocabulary'],
    ['ledger-prerequisite', 'Declared ledger prerequisite'],
    ['work-order', 'Work order (proposed)']
  ];
  let selected = features.has('denotation') ? 'denotation' : data.features[0]?.id;
  let active = null;
  const el = (tag, text, cls) => {
    const e = document.createElement(tag);
    if (text !== undefined) e.textContent = text;
    if (cls) e.className = cls;
    return e;
  };
  const svgEl = (tag, attrs, text) => {
    const e = document.createElementNS('http://www.w3.org/2000/svg', tag);
    for (const [key, value] of Object.entries(attrs || {})) e.setAttribute(key, String(value));
    if (text !== undefined) e.textContent = text;
    return e;
  };
  const safePath = path => typeof path === 'string' && /^(src|tools|Test|docs)\//.test(path)
    && !path.split('/').some(p => p === '..' || p === '.') && !/[\\:#?\x00-\x1f]/.test(path);
  const sourceLink = (path, line) => {
    if (!safePath(path)) return el('span', path || 'No source location recorded');
    const a = el('a', path + (line > 0 ? ':' + line : ''));
    a.href = '../../' + path.split('/').map(encodeURIComponent).join('/') + (line > 0 ? '#L' + line : '');
    return a;
  };
  const status = n => n.kind === 'work' ? 'Proposed work' : n.status === 'wanted' ? 'Open formal goal'
    : n.status === 'defined' ? 'Definition' : n.premises.length ? 'Checked · conditional' : 'Checked theorem';
  const button = (label, onClick, cls) => {
    const b = el('button', label, cls); b.type = 'button'; b.addEventListener('click', onClick); return b;
  };
  const shortName = id => id.split('.').slice(-2).join('.');
  // Condense direct-reference cycles for layout only. This does not validate proof dependencies.
  function positions(items, edges, width, height) {
    const ids = new Set(items.map(n => n.id));
    const next = new Map(items.map(n => [n.id, []]));
    for (const e of edges) if (ids.has(e.from) && ids.has(e.to) && e.from !== e.to) next.get(e.from).push(e.to);
    let index = 0;
    const indices = new Map(), low = new Map(), stack = [], onStack = new Set(), groups = [], group = new Map();
    function visit(id) {
      indices.set(id, index); low.set(id, index++); stack.push(id); onStack.add(id);
      for (const to of next.get(id)) {
        if (!indices.has(to)) { visit(to); low.set(id, Math.min(low.get(id), low.get(to))); }
        else if (onStack.has(to)) low.set(id, Math.min(low.get(id), indices.get(to)));
      }
      if (low.get(id) === indices.get(id)) {
        const members = []; let popped;
        do { popped = stack.pop(); onStack.delete(popped); group.set(popped, groups.length); members.push(popped); } while (popped !== id);
        groups.push(members);
      }
    }
    for (const n of items) if (!indices.has(n.id)) visit(n.id);
    const rank = groups.map(() => 0);
    for (let pass = 0; pass < groups.length; pass++) {
      let changed = false;
      for (const e of edges) {
        const a = group.get(e.from), b = group.get(e.to);
        if (a === undefined || b === undefined || a === b) continue;
        if (rank[b] < rank[a] + 1) { rank[b] = rank[a] + 1; changed = true; }
      }
      if (!changed) break;
    }
    const rows = new Map(), out = new Map();
    for (const n of items) {
      const col = rank[group.get(n.id)], row = rows.get(col) || 0;
      rows.set(col, row + 1); out.set(n.id, {x: 24 + col * (width + 76), y: 30 + row * (height + 24)});
    }
    return {out, width: Math.max(360, 96 + (Math.max(0, ...rank) + 1) * (width + 76) - 76),
      height: Math.max(140, 60 + Math.max(0, ...rows.values()) * (height + 24) - 24)};
  }
  function graph(host, items, edges, onPick, label, featureGraph = false) {
    host.replaceChildren();
    if (!items.length) { host.append(el('p', 'No selected declarations. See the work items and scope below.', 'pm-empty')); return; }
    const w = featureGraph ? 210 : 248, h = featureGraph ? 74 : 104;
    const layout = positions(items, edges, w, h);
    const svg = svgEl('svg', {viewBox: `0 0 ${layout.width} ${layout.height}`, width: layout.width,
      height: layout.height, role: 'group', 'aria-label': label});
    svg.style.minWidth = layout.width + 'px';
    const defs = svgEl('defs');
    const markerPrefix = featureGraph ? 'pm-feature-arrow-' : 'pm-proof-arrow-';
    for (const [kind] of [...kinds, ['feature-prerequisite']]) {
      const marker = svgEl('marker', {id: markerPrefix + kind, markerWidth: 8, markerHeight: 8,
        refX: 7, refY: 4, orient: 'auto', markerUnits: 'strokeWidth'});
      marker.append(svgEl('path', {d: 'M0,0 L8,4 L0,8 Z', class: 'pm-arrow pm-' + kind})); defs.append(marker);
    }
    svg.append(defs);
    for (const e of edges) {
      const a = layout.out.get(e.from), b = layout.out.get(e.to);
      if (!a || !b) continue;
      let d;
      if (e.from === e.to) d = `M${a.x+w-18},${a.y} C${a.x+w+35},${a.y-28} ${a.x+w+35},${a.y+h+25} ${a.x+w-18},${a.y+h}`;
      else if (b.x > a.x) d = `M${a.x+w},${a.y+h/2} C${a.x+w+42},${a.y+h/2} ${b.x-42},${b.y+h/2} ${b.x},${b.y+h/2}`;
      else d = `M${a.x+w},${a.y+h/2} C${a.x+w+40},${a.y+h/2} ${b.x+w+40},${b.y+h/2} ${b.x+w},${b.y+h/2}`;
      const path = svgEl('path', {d, class: 'pm-edge pm-' + e.kind, 'marker-end': `url(#${markerPrefix+e.kind})`});
      path.append(svgEl('title', {}, `${e.from} → ${e.to} (${e.kind})`)); svg.append(path);
    }
    for (const n of items) {
      const p = layout.out.get(n.id);
      const cls = 'pm-node' + (n.id === (featureGraph ? selected : active) ? ' pm-selected' : '')
        + (!featureGraph && n.status === 'wanted' ? ' pm-open' : '') + (n.context ? ' pm-context' : '')
        + (n.kind === 'work' ? ' pm-work-node' : '');
      const g = svgEl('g', {transform: `translate(${p.x},${p.y})`, class: cls, role: 'button', tabindex: 0,
        'aria-label': `${n.title}. ${featureGraph ? 'Authored feature; select to inspect' : status(n)}. ${n.id}`});
      g.append(svgEl('title', {}, n.title + '\n' + n.id));
      g.append(svgEl('rect', {width: w, height: h, rx: 5}));
      const words = n.title.match(/.{1,29}(?:\s|$)|\S{1,29}/g) || [n.title];
      words.slice(0, 2).forEach((s, i) => g.append(svgEl('text', {x: 12, y: 21+i*17, class: 'pm-node-title'}, s.trim() + (i === 1 && words.length > 2 ? '…' : ''))));
      g.append(svgEl('text', {x: 12, y: featureGraph ? 61 : 64, class: 'pm-node-status'}, featureGraph ? 'Authored feature' : status(n)));
      if (!featureGraph) g.append(svgEl('text', {x: 12, y: 87, class: 'pm-node-name'},
        (n.context ? '↳ ' : '') + (shortName(n.id).length > 33 ? shortName(n.id).slice(0, 32) + '…' : shortName(n.id))));
      const pick = () => onPick(n.id);
      g.addEventListener('click', pick);
      g.addEventListener('keydown', e => { if (e.key === 'Enter' || e.key === ' ') { e.preventDefault(); pick(); } });
      svg.append(g);
    }
    host.append(svg);
  }
  function showNode(id) {
    active = id;
    const n = nodes.get(id), proposed = work.get(id), panel = root.querySelector('.pm-detail');
    panel.replaceChildren();
    if (!n && !proposed) { panel.append(el('p', 'Select a declaration to inspect its exact statement and evidence.')); return; }
    panel.append(el('h4', n ? n.title : proposed.title));
    panel.append(el('p', n ? status(n) : 'Proposed work · not a formal goal', 'pm-badge'));
    const exact = el('code', id, 'pm-exact-name'); panel.append(exact);
    if (!n) {
      panel.append(el('p', proposed.reason)); panel.append(sourceLink(proposed.source, 0));
      panel.append(el('p', 'Planned after: ' + (proposed.after.join(', ') || 'No ordering recorded'))); return;
    }
    panel.append(sourceLink(n.path, n.line));
    panel.append(el('p', `Module: ${n.module}`, 'pm-meta'));
    panel.append(el('p', `Evidence: ${n.evidence || 'No proof evidence (definition)'}`, 'pm-meta'));
    if (n.status === 'wanted') panel.append(el('p', 'The placeholder records this goal. It does not prove it, even when upstream nodes are checked.', 'pm-boundary'));
    if (n.status === 'proved' && n.premises.length) panel.append(el('p', 'This theorem proves a conditional statement. Its premises are retained below; this view does not discharge them.', 'pm-boundary'));
    panel.append(el('h5', 'Proposition-valued premises'));
    if (n.premises.length) {
      const dl = el('dl');
      for (const p of n.premises) { dl.append(el('dt', p.name || '(unnamed)')); dl.append(el('dd', p.statement)); }
      panel.append(dl);
    } else panel.append(el('p', 'No top-level proposition-valued binders. Other binders and nested conditions remain in the full statement.', 'pm-meta'));
    panel.append(el('h5', 'Full statement')); panel.append(el('pre', n.statement));
    if (n.body !== null) { panel.append(el('h5', 'Definition body · nested conditions')); panel.append(el('pre', n.body)); }
    panel.append(el('p', 'Universe parameters: ' + (n.levels.join(', ') || 'none'), 'pm-meta'));
    panel.append(el('p', 'Transitive axioms: ' + (n.axioms.join(', ') || 'none'), 'pm-meta'));
    panel.append(el('p', 'Claim links: ' + (n.claims.join(', ') || 'none selected'), 'pm-meta'));
    panel.append(el('p', `${n.omittedReferences} direct references outside the selected node set. This is not a complete proof census.`, 'pm-meta'));
  }
  const interfaceHost = root.querySelector('.pm-interface');
  const selector = el('select'); selector.id = 'pm-feature-select';
  for (const f of data.features) { const o = el('option', f.title); o.value = f.id; selector.append(o); }
  selector.value = selected || ''; selector.addEventListener('change', () => choose(selector.value));
  const controls = el('div', undefined, 'pm-controls');
  const label = el('label', 'Feature'); label.htmlFor = selector.id; controls.append(label, selector);
  const fieldset = el('fieldset', undefined, 'pm-switches'); fieldset.append(el('legend', 'Connections shown'));
  const toggles = new Map();
  for (const [kind, title] of kinds) {
    const l = el('label'), input = el('input'); input.type = 'checkbox';
    input.checked = kind !== 'statement-reference' && kind !== 'work-order';
    input.addEventListener('change', render); toggles.set(kind, input); l.append(input, document.createTextNode(title)); fieldset.append(l);
  }
  controls.append(fieldset);
  const viewControls = el('fieldset', undefined, 'pm-switches'); viewControls.append(el('legend', 'Graph scope'));
  for (const [kind, title] of [['context-neighbors', 'Context neighbors'], ['focus-step', 'Focus selected step']]) {
    const l = el('label'), input = el('input'); input.type = 'checkbox'; input.checked = false;
    input.addEventListener('change', render); toggles.set(kind, input); l.append(input, document.createTextNode(title)); viewControls.append(l);
  }
  controls.append(viewControls); interfaceHost.append(controls);
  const summary = el('div', undefined, 'pm-feature-summary'); interfaceHost.append(summary);
  const columns = el('div', undefined, 'pm-columns'), graphHost = el('div', undefined, 'scroll pm-graph');
  graphHost.tabIndex = 0; graphHost.setAttribute('aria-label', 'Selected graph; scroll horizontally when needed');
  const detail = el('aside', undefined, 'pm-detail'); detail.setAttribute('aria-live', 'polite');
  columns.append(graphHost, detail); interfaceHost.append(columns);
  const connectionText = el('details', undefined, 'pm-connections'); connectionText.append(el('summary', 'Visible connections as text'));
  const connectionList = el('ul'); connectionText.append(connectionList); interfaceHost.append(connectionText);
  const hiddenText = el('details', undefined, 'pm-hidden-connections'); hiddenText.append(el('summary', 'Recorded connections hidden from this graph'));
  hiddenText.append(el('p', 'Connections hidden by the scope or kind switches remain recorded here. Enable context neighbors to place other-feature endpoints in the diagram.', 'pm-meta'));
  const hiddenList = el('ul'); hiddenText.append(hiddenList); interfaceHost.append(hiddenText);
  const workHost = el('div', undefined, 'pm-work'); interfaceHost.append(workHost);
  function render() {
    const feature = features.get(selected);
    summary.replaceChildren(); connectionList.replaceChildren(); hiddenList.replaceChildren(); workHost.replaceChildren();
    if (!feature) { summary.append(el('p', 'No features are selected in this report.')); return; }
    summary.append(el('h3', feature.title)); summary.append(el('p', feature.boundary, 'pm-boundary'));
    const own = new Set([...feature.syntax, ...feature.judgments, ...feature.rules]);
    const owned = [...own].map(id => nodes.get(id));
    const checked = owned.filter(n => n.status === 'proved').length, open = owned.filter(n => n.status === 'wanted').length;
    summary.append(el('p', `${own.size} selected declarations · ${checked} checked theorem${checked===1?'':'s'} · ${open} open goal${open===1?'':'s'} · ${owned.filter(n=>n.status==='defined').length} definitions. No status is inferred from connections.`, 'pm-counts'));
    const coverage = el('div', undefined, 'pm-roles');
    for (const [key, title] of [['syntax','Syntax sorts / constructors'],['judgments','Judgments / supporting definitions'],['rules','Rules / theorems / formal goals']]) {
      const box = el('div'); box.append(el('strong', title));
      for (const id of feature[key]) box.append(button(shortName(id), () => {showNode(id); render();}, 'pm-inline-button'));
      if (!feature[key].length) box.append(el('span', 'None selected', 'pm-meta')); coverage.append(box);
    }
    summary.append(coverage);
    if (feature.requires.length) summary.append(el('p', 'Authored feature prerequisites: ' + feature.requires.map(id => features.get(id).title).join('; '), 'pm-meta'));
    const selectedWork = data.work.filter(w => w.features.includes(selected));
    const recorded = data.edges.filter(e => own.has(e.to) || own.has(e.from));
    const showContext = toggles.get('context-neighbors').checked;
    let edges = recorded.filter(e => toggles.get(e.kind)?.checked && (showContext || (own.has(e.from) && own.has(e.to))));
    const included = new Set(own);
    for (const e of edges) { included.add(e.from); included.add(e.to); }
    const plannedIds = new Set();
    if (toggles.get('work-order').checked) {
      const addWork = id => {
        if (plannedIds.has(id)) return;
        plannedIds.add(id);
        for (const dep of work.get(id).after) {
          if (!showContext && !own.has(dep) && !selectedWork.some(w => w.id === dep)) continue;
          edges.push({from: dep, to: id, kind: 'work-order'});
          if (work.has(dep)) addWork(dep); else included.add(dep);
        }
      };
      for (const w of selectedWork) addWork(w.id);
    }
    // Include every selected connection, without inventing transitive proof edges.
    let items = [...included].map(id => ({...nodes.get(id), context: !own.has(id)}));
    for (const id of plannedIds) items.push({...work.get(id), kind:'work', premises:[], status:'planned', context:!selectedWork.some(w=>w.id===id)});
    if (!items.some(n => n.id === active)) active = feature.rules.find(id => nodes.get(id).status === 'wanted') || feature.rules[0] || items[0]?.id;
    if (toggles.get('focus-step').checked && active) {
      edges = edges.filter(e => e.from === active || e.to === active);
      const nearby = new Set([active]);
      for (const e of edges) { nearby.add(e.from); nearby.add(e.to); }
      items = items.filter(n => nearby.has(n.id));
    }
    summary.append(el('p', `Graph shows ${items.length} nodes and ${edges.length} connections. ${showContext ? 'Context neighbors included.' : 'Only this feature; other-feature connections remain in the text below.'} ${toggles.get('focus-step').checked ? 'Focused on the selected step and its incident connections.' : 'All feature steps shown.'}`, 'pm-graph-counts'));
    graph(graphHost, items, edges, id => {showNode(id); render();}, `Selected declaration graph for ${feature.title}; prerequisites point to consumers`);
    const hidden = recorded.filter(e => !edges.includes(e));
    for (const e of hidden) hiddenList.append(el('li', `${e.from} → ${e.to} · ${e.kind}`));
    if (!hidden.length) hiddenList.append(el('li', 'All recorded feature connections are currently visible.'));
    for (const e of edges) connectionList.append(el('li', `${e.from} → ${e.to} · ${e.kind}`));
    if (!edges.length) connectionList.append(el('li', 'No connections of the enabled kinds are recorded for this selection.'));
    showNode(active);
    workHost.append(el('h4', 'Remaining work · proposals, not declared goals'));
    if (!selectedWork.length) workHost.append(el('p', 'No work items are selected here. This does not establish completion.', 'pm-meta'));
    for (const w of selectedWork) {
      const item = el('article', undefined, 'pm-work-item');
      item.append(button(w.title, () => showNode(w.id), 'pm-work-title'), el('p', w.reason), sourceLink(w.source, 0));
      item.append(el('p', 'Planned after: ' + (w.after.join(', ') || 'No ordering recorded'), 'pm-meta')); workHost.append(item);
    }
  }
  const featureHost = root.querySelector('.pm-feature-graph');
  function choose(id) {
    selected = id; selector.value = id; active = null;
    graph(featureHost, data.features, data.features.flatMap(f => f.requires.map(from => ({from, to:f.id, kind:'feature-prerequisite'}))), choose,
      'Authored feature prerequisite map; these arrows do not prove conservative extension', true);
    render();
  }
  interfaceHost.hidden = false;
  if (selected) choose(selected); else render();
})();
"##

/-- The mandatory v2 graph, rendered without reading the environment a second time. -/
def render (report : Json) : Except String String := do
  let data ← decode report
  let json ← report.getObjVal? "proofMap"
  let references := String.intercalate "; " (data.literature.toList.map fun ref =>
    esc ref.work ++ " · " ++ esc ref.locator ++ " · " ++ esc ref.«use»)
  return "<section id=\"proof-map\"><style>" ++ css ++ "</style>" ++
    "<h2>Language features and selected proofs</h2><p class=\"lede\">" ++ esc data.scope ++ "</p>" ++
    "<p class=\"pm-boundary\">Selected evidence, not a completion certificate. Checked theorems retain their premises; open goals remain open. Feature prerequisites are authored and do not establish conservative extension.</p>" ++
    "<p class=\"small\">Source: <a href=\"../../generated/semantics.json\">semantics report v2</a>. Method: " ++ references ++ "</p>" ++
    "<details class=\"pm-feature-overview\" open><summary>Feature hierarchy · authored prerequisites</summary><div class=\"scroll pm-feature-graph\" tabindex=\"0\" aria-label=\"Feature hierarchy; scroll horizontally when needed\"></div></details>" ++
    "<p class=\"pm-meta\">Reference arrows point from the referenced declaration to its user; authored prerequisite arrows point toward the consumer. These are not the system map's K1–K5 semantic arrows. Body references include annotations and infrastructure; they are not minimal logical necessities. Statement references show vocabulary, not premise discharge. Dotted outlines mark context outside the chosen feature.</p>" ++
    "<p class=\"pm-meta\">Notation follows <a href=\"semantics.md\">the language judgments</a>: <code>w, w′</code> are worlds; source <code>Γ_env</code> differs from the fiber table <code>w.Γ</code>; language signature <code>Σ</code> differs from the literature's store-typing context. Exact Lean statements retain their own binder names. <code>Fits</code>, <code>TypedProg</code> and <code>MachineTyped</code> remain distinct judgments. See the <a href=\"../ARCHITECTURE.md#proof-and-feature-view\">graph notation and evidence key</a>.</p>" ++
    "<div class=\"pm-interface\" hidden></div><noscript><p>The interactive diagrams need JavaScript. The complete text view below remains available.</p></noscript>" ++
    fallback data ++ "<script id=\"proof-map-data\" type=\"application/json\">" ++ scriptData json ++
    "</script><script>" ++ script ++ "</script></section>"

/-- Missing, stale-version or locally invalid graph data refuses architecture generation. -/
def load (path : System.FilePath := "generated/semantics.json") : IO String := do
  let contents ← IO.FS.readFile path
  let report ← IO.ofExcept (Json.parse contents)
  IO.ofExcept <| (render report).mapError fun why => "architecture semantics input: " ++ why

end Tools.ProofMapHtml
