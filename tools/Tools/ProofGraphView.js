// The proof graph view of the architecture map (tools/Tools/Architecture.lean), an ES module.
// It reads the semantics report embedded in the page (#pg-data, written by `make gen-semantics`)
// and the role register's Lean areas (#pg-areas). Nothing is declared here: every node, edge,
// status, concept, role and lane comes from those two.
//
// Three views, each a canonical drawing of one structure the corpus defines:
//
// - Overview: the requirements of the system map's §8 against the ten concepts of
//   docs/core/semantics.md, the corpus's two organizing axes. A cell holds the theorems a
//   requirement rests on, transitively, whose concept is the column's. No edges.
// - Graph: the Hasse diagram of the dependency order (its transitive reduction, the minimal
//   drawing of a partial order), in lanes by architectural area, the role register's layering:
//   Laws areas from the face (Api) down to the lowest, then the runtime areas. Laid out by
//   d3-dag's Sugiyama method with the lanes as rank constraints.
// - Concepts: the quotient of the dependency graph by concept, as a directed chord diagram: a
//   ribbon from one concept to another carries the edges from its theorems to the other's.
//
// The three labels stay apart (docs/core/controlled-english.md, W22): evidence status is the
// card's stroke and fill (proved, modulo its goals, planned goal), the concept is the hue, the
// proof role is the chip.
import * as d3 from 'https://cdn.jsdelivr.net/npm/d3@7.9.0/+esm';
import { graphStratify, sugiyama, layeringSimplex, decrossTwoLayer, coordSimplex, coordGreedy } from 'https://cdn.jsdelivr.net/npm/d3-dag@1.1.0/+esm';

// pg-validate:begin
// The report's plan, checked before anything is drawn: the fields the drawings read, and every
// reference between nodes. A report that fails is shown as unavailable with its problems, never
// drawn as an empty or partial graph. scripts/check-proofgraph-input.mjs runs this block on the
// generated report and on broken copies of it.
function validatePlan(report) {
  const problems = [];
  const isArr = (v) => Array.isArray(v);
  const isStr = (v) => typeof v === 'string' && v.length > 0;
  if (!report || typeof report !== 'object') return ['the semantics report is missing'];
  const plan = report.plan;
  if (!plan || typeof plan !== 'object') return ['the report has no plan section'];
  if (!isArr(plan.requirements)) problems.push('plan.requirements is not a list');
  if (!isArr(plan.nodes)) problems.push('plan.nodes is not a list');
  if (problems.length) return problems;
  const conceptNames = new Set((isArr(report.concepts) ? report.concepts : [])
    .filter((c) => c && isStr(c.id)).map((c) => c.id));
  const requirementIds = new Set(plan.requirements.filter((r) => r && isStr(r.id)).map((r) => r.id));
  const names = new Set();
  for (const n of plan.nodes) {
    if (!n || !isStr(n.name)) { problems.push('a plan node has no name'); continue; }
    if (names.has(n.name)) problems.push(`plan node ${n.name} appears twice`);
    names.add(n.name);
    if (!['proved', 'modulo', 'goal'].includes(n.status)) problems.push(`plan node ${n.name} has status ${n.status}`);
  }
  // A field the drawings read must be present with its type. An empty list is a value. An absent
  // list is a broken report, because the view would draw it as empty and hide edges or open work.
  const list = (where, value) => {
    if (value === undefined) { problems.push(`${where} is missing`); return false; }
    if (!isArr(value)) { problems.push(`${where} is not a list`); return false; }
    return true;
  };
  // A reference names a plan node, in the shape that the drawings read at its field. A
  // requirement's top and placed entries are objects with a name. Every other reference is the
  // name itself. The other shape at a field is refused here, before the model is built.
  const references = (where, value, asObject) => {
    if (!list(where, value)) return;
    for (const t of value) {
      const shaped = asObject ? (t !== null && typeof t === 'object' && isStr(t.name)) : isStr(t);
      if (!shaped) { problems.push(`${where} has an entry that is not ${asObject ? 'an object with a name' : 'a name'}`); continue; }
      const name = asObject ? t.name : t;
      if (!names.has(name)) problems.push(`${where} names ${name}, which is not a plan node`);
    }
  };
  const known = (where, value) => references(where, value, false);
  const knownItems = (where, value) => references(where, value, true);
  for (const n of plan.nodes) {
    if (!n || !isStr(n.name)) continue;
    if (typeof n.statement !== 'string') problems.push(`${n.name}'s statement is missing`);
    if (typeof n.module !== 'string') problems.push(`${n.name}'s module is missing`);
    list(`${n.name}'s axioms`, n.axioms);
    // The plan retains explicit placement even for goals and modules outside the population.
    // Validate it before the model uses it as a fallback for a node with no named claim.
    const placed = n.placement;
    if (placed !== null) {
      if (!placed || typeof placed !== 'object' || isArr(placed)) {
        problems.push(`${n.name}'s placement is missing or is not an object or null`);
      } else {
        if (!isStr(placed.concept) || !conceptNames.has(placed.concept))
          problems.push(`${n.name}'s placement names unknown concept ${placed.concept}`);
        if (placed.requirement !== null && (!isStr(placed.requirement) || !requirementIds.has(placed.requirement)))
          problems.push(`${n.name}'s placement names unknown requirement ${placed.requirement}`);
      }
    }
    const brought = n.broughtIn;
    if (!brought || typeof brought !== 'object') problems.push(`${n.name}'s dependency summary is missing`);
    else {
      known(`${n.name}'s nearest nodes`, brought.nearest);
      for (const key of ['lemmas', 'definitions']) {
        if (typeof brought[key] !== 'number') problems.push(`${n.name}'s count of ${key} is missing`);
      }
    }
    known(`${n.name}'s goals`, n.restsOn);
  }
  for (const r of plan.requirements) {
    if (!r || !isStr(r.id) || !isStr(r.title) || !isStr(r.status)) { problems.push('a requirement lacks its id, title or status'); continue; }
    knownItems(`${r.id}'s top nodes`, r.top);
    knownItems(`${r.id}'s placed nodes`, r.placed);
    known(`${r.id}'s next goals`, r.next);
    list(`${r.id}'s open parts`, r.openParts);
  }
  known('the next goals', plan.next);
  known('the unplaced goals', plan.unplacedGoals);
  return problems;
}
// pg-validate:end

const root = document.getElementById('pg');
const report = JSON.parse(document.getElementById('pg-data').textContent);
const areaRows = JSON.parse((document.getElementById('pg-areas') || { textContent: '[]' }).textContent);
const problems = validatePlan(report);
if (problems.length) {
  root.innerHTML = `<div class="pg-unavailable" role="alert"><b>The proof graph is unavailable.</b> The semantics report fails ${problems.length} check(s); regenerate it with <code>make gen-semantics</code>.<ul>${problems.slice(0, 20).map((p) => `<li>${String(p).replace(/&/g, '&amp;').replace(/[<]/g, '&lt;')}</li>`).join('')}</ul></div>`;
  throw new Error(`proof graph: ${problems.length} problem(s) in the semantics report: ${problems[0]}`);
}
const plan = report.plan;
const short = (n) => n.split('.').pop();
const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/[<]/g, '&lt;').replace(/>/g, '&gt;');
// card sizes; a foundation is a theorem the proofs of HUB or more others reach first
const CW = 214, CH = 30, REQW = 250, GAPX = 14, GAPY = 92, FRAME = REQW + 140, HUB = 6, LANEHEAD = 34;

// ---------------------------------------------------------------- the model
// pg-model:begin
const conceptIds = (report.concepts || []).map((c) => c.id);
const conceptTitle = Object.fromEntries((report.concepts || []).map((c) => [c.id, c.title]));
// ten hues spaced around the wheel in the concepts' document order, muted for paper and ink
const hue = (c) => Math.round(((conceptIds.indexOf(c) + 0.5) * 360) / Math.max(1, conceptIds.length));
const conceptColour = (c) => (c && conceptIds.includes(c) ? `hsl(${hue(c)} 48% 54%)` : 'var(--ink-3)');
const ROLE = { inversion: 'INV', canonicalForms: 'CAN', weakening: 'WK', substitution: 'SUB', progress: 'PROG',
  preservation: 'PRES', monotonicity: 'MONO', transitivity: 'TRANS', antisymmetry: 'ANTI', decidability: 'DEC',
  adequacy: 'ADEQ', simulation: 'SIM', compatibility: 'COMP', fundamentalProperty: 'FUND' };
const placement = Object.fromEntries(((report.placement || {}).declarations || []).map((d) => [d.name, d.concept]));
const claimsOf = {};
for (const c of report.claims || []) {
  const st = c.status || {};
  const w = st.witness || st.goal || (st.counterexample && st.counterexample.witness);
  if (w && w.name) (claimsOf[w.name] = claimsOf[w.name] || []).push(c);
}
// a module's area: the role register's longest prefix naming it
const areaOf = (m) => {
  let best = null;
  for (const a of areaRows) if ((m === a.prefix || m.startsWith(a.prefix + '.')) && (!best || a.prefix.length > best.prefix.length)) best = a;
  return best;
};
const nodes = new Map();
const reqs = plan.requirements.map((r) => r.id);
for (const r of plan.requirements) {
  nodes.set('req:' + r.id, { id: 'req:' + r.id, kind: 'requirement', label: r.id, title: r.title, status: r.status,
    openParts: r.openParts || [], next: r.next || [], out: [...(r.top || []), ...(r.placed || [])].map((t) => t.name) });
}
for (const n of plan.nodes) {
  const claims = claimsOf[n.name] || [];
  nodes.set(n.name, { id: n.name, kind: n.kind, label: short(n.name), status: n.status, module: n.module,
    area: areaOf(n.module || ''), statement: n.statement || '', axioms: n.axioms || [], restsOn: n.restsOn || [],
    out: ((n.broughtIn || {}).nearest || []), lemmas: (n.broughtIn || {}).lemmas || 0,
    definitions: (n.broughtIn || {}).definitions || 0, claims,
    concept: (claims[0] && claims[0].concept) || (n.placement && n.placement.concept) || placement[n.name] || null,
    role: claims[0] ? claims[0].role : null });
}
const parentsOf = new Map([...nodes.keys()].map((k) => [k, []]));
for (const n of nodes.values()) for (const t of n.out) parentsOf.get(t).push(n.id);
const down = (id) => nodes.get(id).out;
const up = (id) => parentsOf.get(id);
const reach = (start, next) => {
  const seen = new Set([start]); const todo = [start];
  while (todo.length) for (const m of next(todo.pop())) if (!seen.has(m)) { seen.add(m); todo.push(m); }
  return seen;
};
const theorems = [...nodes.values()].filter((n) => n.kind !== 'requirement');
const statusOf = (n) => (n.kind === 'requirement' ? (n.status === 'proved' ? 'proved' : 'req') : n.status);
const statusWord = (s) => (s === 'goal' ? 'planned goal' : s === 'modulo' ? 'modulo its goals' : s);

// pg-model:end

// ---------------------------------------------------------------- the controls
const bar = root.querySelector('.pg-bar');
const canvas = root.querySelector('.pg-canvas');
const panel = root.querySelector('.pg-panel');
bar.innerHTML =
  `<div class="pg-tabs" role="tablist"><button role="tab" data-view="overview">Overview</button><button role="tab" data-view="graph">Graph</button><button role="tab" data-view="concepts">Concepts</button></div>` +
  `<select aria-label="Requirement"><option value="">All requirements</option>${plan.requirements.map((r) => `<option value="${esc(r.id)}">${esc(r.id)} · ${esc(r.title.length > 44 ? r.title.slice(0, 43) + '…' : r.title)}</option>`).join('')}</select>` +
  `<label><input type="checkbox" class="pg-frontier"> The frontier only</label>` +
  `<label class="gc"><input type="checkbox" class="pg-orphans"> Claims no requirement reaches</label>` +
  `<label class="g" title="Draw every edge the proofs give, not only the covering ones"><input type="checkbox" class="pg-all"> Implied edges</label>` +
  `<input type="search" placeholder="Find a declaration" aria-label="Find a declaration">` +
  `<button type="button" class="pg-fit g">Fit</button><span class="pg-counts"></span>`;
const reqSel = bar.querySelector('select');
const frontierBox = bar.querySelector('.pg-frontier');
const orphanBox = bar.querySelector('.pg-orphans');
const allBox = bar.querySelector('.pg-all');
const search = bar.querySelector('input[type=search]');
const tally = (k) => theorems.filter((n) => n.status === k).length;
bar.querySelector('.pg-counts').innerHTML =
  `<b>${reqs.length}</b> requirements, ${plan.requirements.filter((r) => r.status !== 'proved').length} open · ` +
  `<b>${tally('proved')}</b> proved · <b>${tally('modulo')}</b> modulo · <b>${tally('goal')}</b> planned goals`;
const legend = document.createElement('div');
legend.className = 'pg-legend';
const usedRoles = [...new Set(theorems.map((n) => n.role).filter(Boolean))];
legend.innerHTML =
  `<div><em>Evidence status</em><span class="st proved">proved</span><span class="st modulo">modulo its goals</span><span class="st goal">planned goal</span><span class="st req">requirement</span></div>` +
  `<div><em>Concept</em>${conceptIds.map((c) => `<span class="cc" style="--c:${conceptColour(c)}" title="${esc(conceptTitle[c] || '')}">${esc(c)}</span>`).join('')}</div>` +
  `<div class="g"><em>Proof role</em>${usedRoles.map((r) => `<span class="rl"><b>${ROLE[r] || r}</b> ${esc(r)}</span>`).join('')}</div>` +
  `<div class="g"><em>Foundation</em><span class="fd"><b>n →</b> a theorem the proofs of n others reach first (n ≥ ${HUB}); its incoming edges are drawn along a selection</span></div>`;
bar.after(legend);

let view = 'overview';
let selected = null;
const setView = (v) => {
  view = v;
  for (const b of bar.querySelectorAll('.pg-tabs button')) b.setAttribute('aria-selected', String(b.dataset.view === v));
  root.dataset.view = v;
  render();
};
for (const b of bar.querySelectorAll('.pg-tabs button')) b.addEventListener('click', () => setView(b.dataset.view));

// ---------------------------------------------------------------- the visible subgraph
const visible = () => {
  let ids = new Set(nodes.keys());
  const fromReqs = new Set();
  for (const r of reqs) for (const a of reach('req:' + r, down)) fromReqs.add(a);
  if (reqSel.value) ids = reach('req:' + reqSel.value, down);
  else if (!orphanBox.checked) ids = new Set([...ids].filter((i) => fromReqs.has(i)));
  if (frontierBox.checked) {
    const hot = new Set();
    for (const n of theorems) if (n.status === 'goal') for (const a of reach(n.id, up)) hot.add(a);
    ids = new Set([...ids].filter((i) => hot.has(i)));
  }
  return ids;
};
// the covering edges of the dependency order among `ids`: u → v stays unless v is reached from
// another child of u (the transitive reduction of a DAG is unique)
const reduce = (ids) => {
  const kids = (u) => down(u).filter((v) => ids.has(v));
  const below = new Map();
  const desc = (u) => {
    if (below.has(u)) return below.get(u);
    const s = new Set();
    below.set(u, s);
    for (const v of kids(u)) { s.add(v); for (const w of desc(v)) s.add(w); }
    return s;
  };
  const edges = [];
  for (const u of ids) {
    if (u.startsWith('req:')) continue;
    const ks = kids(u);
    for (const v of ks) {
      const implied = ks.some((w) => w !== v && desc(w).has(v));
      if (allBox.checked || !implied) edges.push({ from: u, to: v });
    }
  }
  return edges;
};

// ---------------------------------------------------------------- the overview: requirements × concepts
const overview = () => {
  const cols = [...conceptIds, null];
  const rows = plan.requirements.filter((r) => !reqSel.value || r.id === reqSel.value);
  const order = ['goal', 'modulo', 'proved'];
  let html = '<div class="pg-matrix"><table><thead><tr><th class="rq">Requirement</th>' +
    cols.map((c) => (c ? `<th class="cn" title="${esc(conceptTitle[c] || c)}"><span style="--c:${conceptColour(c)}">${esc(c)}</span></th>` : '<th class="cn"><span>no concept</span></th>')).join('') +
    '<th class="ops">Open parts</th></tr></thead><tbody>';
  for (const r of rows) {
    const under = [...reach('req:' + r.id, down)].filter((i) => !i.startsWith('req:')).map((i) => nodes.get(i))
      .filter((n) => !frontierBox.checked || n.status !== 'proved');
    html += `<tr><th class="rq"><a data-go="req:${esc(r.id)}"><b>${esc(r.id)}</b></a> <span class="pg-badge ${r.status === 'proved' ? 'proved' : 'open'}">${esc(r.status)}</span><div class="rt">${esc(r.title)}</div></th>`;
    for (const c of cols) {
      const here = under.filter((n) => (n.concept || null) === c)
        .sort((a, b) => order.indexOf(a.status) - order.indexOf(b.status) || a.label.localeCompare(b.label));
      html += `<td>${here.map((n) => `<a class="dot ${n.status}" data-go="${esc(n.id)}" title="${esc(n.label)} · ${esc(statusWord(n.status))}" aria-label="${esc(n.label)}, ${esc(statusWord(n.status))}"></a>`).join('')}</td>`;
    }
    html += `<td class="ops">${(r.openParts || []).length ? `<a data-go="req:${esc(r.id)}">${r.openParts.length}</a>` : '—'}</td></tr>`;
  }
  html += '</tbody></table><p class="hint">A dot is a theorem the requirement rests on, through its proofs, in the column of its concept. Select one to see it in the graph; select a requirement for its open parts, the parts not yet stated as goals.</p></div>';
  canvas.innerHTML = html;
};

// ---------------------------------------------------------------- the graph: Hasse diagram in lanes
const laneKey = (a) => (a ? `${a.column}:${a.layer}` : 'none');
const laneOrder = (key) => {
  if (key === 'none') return 99;
  const [col, layer] = key.split(':');
  const base = { laws: 0, runtime: 10, tools: 20, tests: 30 }[col] ?? 40;
  return base + (9 - Number(layer));
};
const svg = d3.create('svg').attr('role', 'img')
  .attr('aria-label', 'The proof graph: requirements, theorems and planned goals; an edge runs from a theorem to the theorems its proof covers');
const viewG = svg.append('g');
const gLanes = viewG.append('g');
const gEdges = viewG.append('g');
const gNodes = viewG.append('g');
const zoom = d3.zoom().scaleExtent([0.06, 2.5]).on('zoom', (ev) => viewG.attr('transform', ev.transform));
svg.call(zoom).on('dblclick.zoom', null);
const line = d3.line().curve(d3.curveMonotoneX);
let reqCentre = null;
const fit = (animate = true) => {
  const b = viewG.node().getBBox();
  if (!b.width || !b.height) return;
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const k = Math.min(1.2, 0.94 * Math.min(w / b.width, h / b.height));
  const t = d3.zoomIdentity.translate((w - b.width * k) / 2 - b.x * k, (h - b.height * k) / 2 - b.y * k).scale(k);
  (animate ? svg.transition().duration(450) : svg).call(zoom.transform, t);
};
// the opening view: the whole drawing when it is legible, otherwise a legible scale on the frame
const openView = () => {
  const b = viewG.node().getBBox();
  const w = canvas.clientWidth, h = canvas.clientHeight;
  if (0.94 * Math.min(w / b.width, h / b.height) >= 0.62 || reqCentre === null) return fit(false);
  const s = 0.7;
  svg.call(zoom.transform, d3.zoomIdentity.translate(24 - b.x * s, h / 2 - reqCentre * s).scale(s));
};
const layoutGraph = (ids, edges) => {
  const ths = [...ids].filter((i) => !i.startsWith('req:'));
  const pos = new Map(); const links = [];
  const lanes = new Map();
  if (ths.length) {
    const parentIds = new Map(ths.map((i) => [i, []]));
    for (const e of edges) parentIds.get(e.to).push(e.from);
    // lanes as rank constraints. A rank stays only where no path from a node of a later lane
    // reaches it, through ranked or unranked nodes alike: the constraints are then satisfiable.
    // A node that would break the order floats between the lanes.
    const rank = new Map(ths.map((i) => [i, laneOrder(laneKey(nodes.get(i).area))]));
    const indeg = new Map(ths.map((i) => [i, parentIds.get(i).length]));
    const kidsOf = new Map(ths.map((i) => [i, []]));
    for (const e of edges) kidsOf.get(e.from).push(e.to);
    const bound = new Map();
    const level = new Map();
    const queue = ths.filter((i) => indeg.get(i) === 0);
    while (queue.length) {
      const v = queue.shift();
      const ps = parentIds.get(v);
      const lb = Math.max(-Infinity, ...ps.map((p) => (rank.has(p) ? rank.get(p) : bound.get(p))));
      if (rank.has(v) && rank.get(v) < lb) rank.delete(v);
      bound.set(v, rank.has(v) ? rank.get(v) : lb);
      level.set(v, ps.length ? 1 + Math.max(...ps.map((p) => level.get(p))) : 0);
      for (const c of kidsOf.get(v)) { indeg.set(c, indeg.get(c) - 1); if (indeg.get(c) === 0) queue.push(c); }
    }
    // d3-dag puts equal ranks in one layer, so a lane's rank is refined by the longest-path level
    // (densely renumbered within the lane): equal ranks then share a lane and a level, which no
    // path joins, and every path strictly increases the rank
    const levelsOf = new Map();
    for (const [i, r] of rank) (levelsOf.get(r) || levelsOf.set(r, new Set()).get(r)).add(level.get(i));
    const dense = new Map([...levelsOf].map(([r, ls]) => [r, new Map([...ls].sort((x, y) => x - y).map((l, j) => [l, j]))]));
    for (const [i, r] of rank) rank.set(i, r * 1000 + dense.get(r).get(level.get(i)));
    const dag = graphStratify()(ths.map((id) => ({ id, parentIds: parentIds.get(id) })));
    const base = (layering) => sugiyama().nodeSize([CH + GAPX, CW]).gap([0, GAPY]).layering(layering).decross(decrossTwoLayer());
    const ranked = layeringSimplex().rank((node) => rank.get(node.data.id));
    root.dataset.layout = 'ranked';
    try { base(ranked).coord(coordSimplex())(dag); }
    catch (err) {
      root.dataset.layout = 'ranked, greedy coordinates: ' + err;
      try { base(ranked).coord(coordGreedy())(dag); }
      catch (err2) { root.dataset.layout = 'unranked: ' + err2; base(layeringSimplex()).coord(coordGreedy())(dag); }
    }
    root.dataset.floating = String(ths.length - rank.size);
    for (const node of dag.nodes()) pos.set(node.data.id, { x: FRAME + node.y, y: node.x + LANEHEAD });
    for (const l of dag.links()) links.push({ from: l.source.data.id, to: l.target.data.id, pts: l.points.map(([x, y]) => [FRAME + y, x + LANEHEAD]) });
    for (const i of ths) {
      const k = laneKey(nodes.get(i).area), p = pos.get(i);
      const lane = lanes.get(k) || { key: k, min: Infinity, max: -Infinity, titles: new Set() };
      lane.min = Math.min(lane.min, p.x); lane.max = Math.max(lane.max, p.x);
      if (nodes.get(i).area) lane.titles.add(nodes.get(i).area.title);
      lanes.set(k, lane);
    }
  }
  const frame = [...ids].filter((i) => i.startsWith('req:')).sort((a, b) => reqs.indexOf(a.slice(4)) - reqs.indexOf(b.slice(4)));
  const ys = [...pos.values()].map((p) => p.y);
  const top = ys.length ? Math.min(...ys) : LANEHEAD, bottom = ys.length ? Math.max(...ys) : LANEHEAD;
  const step = Math.max(CH + 16, frame.length > 1 ? (bottom - top) / (frame.length - 1) : 0);
  const start = (top + bottom) / 2 - (step * (frame.length - 1)) / 2;
  frame.forEach((id, i) => pos.set(id, { x: REQW / 2, y: start + i * step }));
  return { pos, links, lanes: [...lanes.values()].sort((a, b) => a.min - b.min) };
};
const graph = () => {
  canvas.innerHTML = '';
  canvas.appendChild(svg.node());
  svg.attr('width', canvas.clientWidth).attr('height', canvas.clientHeight);
  gLanes.selectAll('*').remove(); gEdges.selectAll('*').remove(); gNodes.selectAll('*').remove();
  const ids = visible();
  if (!ids.size) return;
  const edges = reduce(ids);
  const { pos, links, lanes } = layoutGraph(ids, edges);
  const reqYs = [...pos].filter(([k]) => k.startsWith('req:')).map(([, p]) => p.y);
  reqCentre = reqYs.length ? (Math.min(...reqYs) + Math.max(...reqYs)) / 2 : null;
  const ys = [...pos.values()].map((p) => p.y);
  const yTop = Math.min(...ys) - CH, yBottom = Math.max(...ys) + CH;
  // the lanes: one band per architectural area, labelled with the role register's titles
  lanes.forEach((lane, i) => {
    const x0 = lane.min - CW / 2 - GAPY / 3, x1 = lane.max + CW / 2 + GAPY / 3;
    gLanes.append('rect').attr('class', 'pg-lane' + (i % 2 ? ' odd' : '')).attr('x', x0).attr('y', yTop - LANEHEAD)
      .attr('width', x1 - x0).attr('height', yBottom - yTop + LANEHEAD).attr('rx', 10);
    gLanes.append('text').attr('class', 'pg-lane-title').attr('x', x0 + 12).attr('y', yTop - LANEHEAD + 20)
      .text([...lane.titles].join(' · ') || 'other');
  });
  gLanes.append('text').attr('class', 'pg-lane-title').attr('x', 0).attr('y', yTop - LANEHEAD + 20).text('Requirements (system map §8)');
  // a foundation's incoming edges are drawn along a selection only
  const uses = new Map();
  for (const e of edges) uses.set(e.to, (uses.get(e.to) || 0) + 1);
  const foundation = (id) => (uses.get(id) || 0) >= HUB;
  const edge = (a, b, d, frameEdge) => gEdges.append('path').attr('d', d)
    .attr('class', 'pg-edge' + (nodes.get(b).kind === 'goal' ? ' rests' : '') + (frameEdge ? ' frame' : '') + (!frameEdge && foundation(b) ? ' found' : ''))
    .attr('data-from', a).attr('data-to', b);
  for (const id of ids) {
    if (!id.startsWith('req:')) continue;
    const pa = pos.get(id);
    for (const t of nodes.get(id).out) {
      if (!pos.has(t)) continue;
      const pb = pos.get(t), x1 = pa.x + REQW / 2, x2 = pb.x - CW / 2, dx = Math.max(60, (x2 - x1) * 0.45);
      edge(id, t, `M${x1},${pa.y} C${x1 + dx},${pa.y} ${x2 - dx},${pb.y} ${x2},${pb.y}`, true);
    }
  }
  for (const l of links) {
    const pa = pos.get(l.from), pb = pos.get(l.to);
    const pts = l.pts.slice();
    pts[0] = [pa.x + CW / 2, pa.y]; pts[pts.length - 1] = [pb.x - CW / 2, pb.y];
    edge(l.from, l.to, line(pts), false);
  }
  for (const [id, p] of pos) {
    const n = nodes.get(id);
    const w = n.kind === 'requirement' ? REQW : CW;
    const g = gNodes.append('g').attr('class', `pg-node ${statusOf(n)}`).attr('transform', `translate(${p.x - w / 2},${p.y - CH / 2})`)
      .attr('tabindex', 0).attr('role', 'button').attr('data-id', id)
      .attr('aria-label', n.kind === 'requirement' ? `${n.label}: ${n.title}, ${n.status}` : `${n.id}, ${statusWord(n.status)}`);
    g.append('title').text(n.kind === 'requirement' ? `${n.label}: ${n.title}` : `${n.id} (${statusWord(n.status)})`);
    g.append('rect').attr('class', 'card').attr('width', w).attr('height', CH).attr('rx', n.kind === 'requirement' ? CH / 2 : 6);
    if (n.kind === 'requirement') {
      g.append('text').attr('class', 'rid').attr('x', 14).attr('y', CH / 2 + 4).text(n.label);
      g.append('text').attr('class', 'rtitle').attr('x', 46).attr('y', CH / 2 + 4).text(n.title.length > 30 ? n.title.slice(0, 29) + '…' : n.title);
    } else {
      g.append('rect').attr('class', 'stripe').attr('width', 5).attr('height', CH).attr('rx', 2).attr('fill', conceptColour(n.concept));
      g.append('text').attr('class', 'name').attr('x', 13).attr('y', CH / 2 + 4).text(n.label.length > 24 ? n.label.slice(0, 23) + '…' : n.label);
      if (n.role) g.append('text').attr('class', 'role').attr('x', w - 8).attr('y', CH / 2 + 3.5).attr('text-anchor', 'end').text(ROLE[n.role] || n.role);
      if (foundation(id)) g.append('text').attr('class', 'uses').attr('x', -6).attr('y', CH / 2 + 3.5).attr('text-anchor', 'end').text(`${uses.get(id)} →`);
    }
    g.on('click', (ev) => { ev.stopPropagation(); select(id, false); })
      .on('keydown', (ev) => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); select(id, false); } });
  }
  openView();
  if (selected && pos.has(selected)) highlight(selected);
};
svg.on('click', () => clearSelection());
const highlight = (id) => {
  const ups = reach(id, up), downs = reach(id, down);
  gNodes.selectAll('.pg-node').classed('dim', function () { const k = this.dataset.id; return !ups.has(k) && !downs.has(k); })
    .classed('sel', function () { return this.dataset.id === id; });
  gEdges.selectAll('.pg-edge').each(function () {
    const a = this.dataset.from, b = this.dataset.to;
    const on = (downs.has(a) && downs.has(b)) || (ups.has(a) && ups.has(b));
    d3.select(this).classed('dim', !on).classed('hot', on);
  });
};

// ---------------------------------------------------------------- the concepts: a quotient by concept
const concepts = () => {
  canvas.innerHTML = '';
  const ids = visible();
  const keys = conceptIds;
  const index = new Map(keys.map((c, i) => [c, i]));
  const m = keys.map(() => keys.map(() => 0));
  const within = keys.map(() => 0);
  for (const u of ids) {
    const nu = nodes.get(u);
    if (nu.kind === 'requirement' || !index.has(nu.concept)) continue;
    for (const v of nu.out) {
      if (!ids.has(v)) continue;
      const nv = nodes.get(v);
      if (!index.has(nv.concept)) continue;
      if (nu.concept === nv.concept) within[index.get(nu.concept)]++;
      else m[index.get(nu.concept)][index.get(nv.concept)]++;
    }
  }
  // an arc's length counts every edge from its concept's theorems, within the concept as well
  // (the quotient's self-loop, not drawn as a ribbon), and at least one for a concept present
  const present = new Set([...ids].map((i) => nodes.get(i).concept).filter((c) => index.has(c)));
  const sized = m.map((row, i) => row.map((v, j) => (i === j ? Math.max(within[i], present.has(keys[i]) ? 1 : 0) : v)));
  const W = canvas.clientWidth, H = canvas.clientHeight;
  const outer = Math.min(W, H) / 2 - 150, inner = outer - 12;
  const chords = d3.chordDirected().padAngle(0.07).sortSubgroups(d3.descending)(sized);
  const s = d3.select(canvas).append('svg').attr('class', 'pg-chord').attr('viewBox', [-W / 2, -H / 2, W, H])
    .attr('role', 'img').attr('aria-label', 'The concepts, and the dependencies between their theorems, as a directed chord diagram');
  const ribbon = d3.ribbonArrow().radius(inner - 2).padAngle(1 / inner);
  const arc = d3.arc().innerRadius(inner).outerRadius(outer);
  s.append('g').selectAll('path').data(chords.filter((d) => d.source.index !== d.target.index)).join('path').attr('class', 'pg-ribbon')
    .attr('d', ribbon).attr('fill', (d) => conceptColour(keys[d.source.index]))
    .append('title').text((d) => `${keys[d.source.index]} → ${keys[d.target.index]}: ${d.source.value} edges`);
  const groups = s.append('g').selectAll('g').data(chords.groups).join('g').attr('class', 'pg-arc');
  groups.append('path').attr('d', arc).attr('fill', (d) => conceptColour(keys[d.index]));
  groups.append('text').attr('class', 'pg-arc-label')
    .each((d) => { d.angle = (d.startAngle + d.endAngle) / 2; })
    .attr('dy', '0.32em')
    .attr('transform', (d) => `rotate(${(d.angle * 180) / Math.PI - 90}) translate(${outer + 10}) ${d.angle > Math.PI ? 'rotate(180)' : ''}`)
    .attr('text-anchor', (d) => (d.angle > Math.PI ? 'end' : null))
    .text((d) => keys[d.index]);
  groups.append('title').text((d) => `${keys[d.index]}: ${conceptTitle[keys[d.index]] || ''} · ${within[d.index]} edges within`);
  groups.on('mouseenter', (ev, d) => s.selectAll('.pg-ribbon').classed('dim', (c) => c.source.index !== d.index && c.target.index !== d.index))
    .on('mouseleave', () => s.selectAll('.pg-ribbon').classed('dim', false))
    .on('click', (ev, d) => showConcept(keys[d.index], m, within, index));
  s.append('text').attr('class', 'pg-chord-note').attr('y', H / 2 - 16).attr('text-anchor', 'middle')
    .text('A ribbon runs from the concept whose theorems use to the concept whose theorems are used; its width counts the edges. An arc counts all its edges, those within included.');
};

// ---------------------------------------------------------------- the panel
const pathOf = (m) => {
  const rel = m.split('.').join('/') + '.lean';
  if (m.startsWith('Effect4.') || m.startsWith('OCaml5.')) return 'src/' + rel;
  if (m.startsWith('Test.')) return rel;
  return 'tools/' + rel;
};
const link = (id) => (nodes.has(id) ? `<a data-go="${esc(id)}">${esc(id.startsWith('req:') ? id.slice(4) : short(id))}</a>` : esc(short(id)));
const list = (xs) => (xs.length ? `<ul>${xs.map((x) => `<li>${link(x)}</li>`).join('')}</ul>` : '<span class="hint">none</span>');
const badge = (s, cls = s) => `<span class="pg-badge ${esc(cls)}">${esc(s)}</span>`;
const showSummary = () => {
  const next = plan.next || [];
  panel.innerHTML = `<h4>The plan</h4><p class="sub">${esc(report.producer || 'the semantics report')}</p>` +
    `<dl><dt>Next goals (${next.length})</dt><dd>${list(next)}</dd>` +
    `<dt>Goals no requirement reaches (${(plan.unplacedGoals || []).length})</dt><dd>${list(plan.unplacedGoals || [])}</dd>` +
    `<dt>Requirements</dt><dd><ul class="reqs">${plan.requirements.map((r) => `<li>${link('req:' + r.id)} ${badge(r.status, r.status === 'proved' ? 'proved' : 'open')} ${esc(r.title)}</li>`).join('')}</ul></dd></dl>` +
    `<p class="hint">Overview: requirements against concepts. Graph: the covering dependencies, in lanes by architectural area. Concepts: the dependencies between concepts.</p>`;
};
const showConcept = (c, m, within, index) => {
  const i = index.get(c);
  const here = theorems.filter((n) => n.concept === c);
  const outs = conceptIds.map((d, j) => [d, m[i][j]]).filter(([, v]) => v).sort((a, b) => b[1] - a[1]);
  const ins = conceptIds.map((d, j) => [d, m[j][i]]).filter(([, v]) => v).sort((a, b) => b[1] - a[1]);
  panel.innerHTML = `<h4>${esc(c)}</h4><p class="sub">${esc(conceptTitle[c] || '')}</p>` +
    `${badge(`${here.filter((n) => n.status === 'proved').length} proved`, 'proved')}${badge(`${here.filter((n) => n.status === 'modulo').length} modulo`, 'modulo')}${badge(`${here.filter((n) => n.status === 'goal').length} goals`, 'goal')}` +
    `<dl><dt>Its theorems use (edges)</dt><dd>${outs.length ? `<ul>${outs.map(([d, v]) => `<li>${esc(d)} · ${v}</li>`).join('')}</ul>` : '<span class="hint">none</span>'}</dd>` +
    `<dt>Used by (edges)</dt><dd>${ins.length ? `<ul>${ins.map(([d, v]) => `<li>${esc(d)} · ${v}</li>`).join('')}</ul>` : '<span class="hint">none</span>'}</dd>` +
    `<dt>Edges within</dt><dd>${within[i]}</dd><dt>Theorems (${here.length})</dt><dd>${list(here.map((n) => n.id))}</dd></dl>`;
};
const show = (id) => {
  const n = nodes.get(id);
  if (n.kind === 'requirement') {
    panel.innerHTML = `<h4>${esc(n.label)}</h4><p class="sub">${esc(n.title)}</p>${badge(n.status, n.status === 'proved' ? 'proved' : 'open')}` +
      `<dl><dt>Top nodes</dt><dd>${list(n.out)}</dd><dt>Next goals</dt><dd>${list(n.next)}</dd>` +
      `<dt>Open parts, not yet stated as goals (${n.openParts.length})</dt><dd>${n.openParts.length ? `<ul>${n.openParts.map((p) => `<li>${esc(p)}</li>`).join('')}</ul>` : '<span class="hint">none</span>'}</dd></dl>`;
    return;
  }
  const path = n.module ? pathOf(n.module) : '';
  const claims = n.claims.map((c) => `<li><b>${esc(c.id)}</b> · ${esc(c.role)}: ${esc(c.title)}${(c.contestedBy || []).length ? ` <span class="hint">· contested by ${c.contestedBy.map((r) => esc(r.id)).join(', ')}</span>` : ''}</li>`).join('');
  panel.innerHTML = `<h4>${esc(n.id)}</h4><p class="sub">${path ? `<a href="../../${esc(path)}">${esc(path)}</a>` : ''}${n.area ? ` · ${esc(n.area.title)}` : ''}</p>` +
    badge(statusWord(n.status), n.status) +
    (n.concept ? `<span class="pg-badge" style="border-color:${conceptColour(n.concept)};color:${conceptColour(n.concept)}">${esc(n.concept)}</span>` : '') +
    (n.role ? `<span class="pg-badge">${esc(n.role)}</span>` : '') +
    `<dl><dt>Statement</dt><dd><pre>${esc(n.statement)}</pre></dd>` +
    (n.status === 'modulo' ? `<dt>Rests on</dt><dd>${list(n.restsOn)}</dd>` : '') +
    `<dt>Axioms</dt><dd>${n.axioms.length ? n.axioms.map(esc).join(', ') : '<span class="hint">none</span>'}</dd>` +
    `<dt>Its proof reaches first</dt><dd>${list(n.out)}</dd>` +
    `<dt>Reached first by</dt><dd>${list(up(id))}</dd>` +
    `<dt>Brings in</dt><dd>${n.lemmas} lemmas · ${n.definitions} definitions of the tree</dd>` +
    (claims ? `<dt>Claims</dt><dd><ul>${claims}</ul></dd>` : '') + `</dl>`;
};
const clearSelection = () => {
  selected = null;
  gNodes.selectAll('.pg-node').classed('dim', false).classed('sel', false);
  gEdges.selectAll('.pg-edge').classed('dim', false).classed('hot', false);
  showSummary();
};
const select = (id, centre = true) => {
  selected = id;
  show(id);
  if (view !== 'graph') return;
  if (gNodes.select(`[data-id="${CSS.escape(id)}"]`).empty()) { reqSel.value = ''; frontierBox.checked = false; orphanBox.checked = true; graph(); }
  highlight(id);
  if (centre) {
    const g = gNodes.select(`[data-id="${CSS.escape(id)}"]`).node();
    if (g) {
      const mm = /translate\(([-\d.]+),([-\d.]+)\)/.exec(g.getAttribute('transform'));
      const k = Math.max(0.6, d3.zoomTransform(svg.node()).k);
      const t = d3.zoomIdentity.translate(canvas.clientWidth / 2 - (+mm[1] + CW / 2) * k, canvas.clientHeight / 2 - (+mm[2] + CH / 2) * k).scale(k);
      svg.transition().duration(450).call(zoom.transform, t);
    }
  }
};
root.addEventListener('click', (ev) => {
  const a = ev.target.closest('a[data-go]');
  if (!a) return;
  ev.preventDefault();
  const id = a.getAttribute('data-go');
  if (canvas.contains(a) && view === 'overview' && !id.startsWith('req:')) { selected = id; setView('graph'); select(id); return; }
  select(id);
});

// ---------------------------------------------------------------- search, filters, render
search.addEventListener('keydown', (ev) => {
  if (ev.key !== 'Enter') return;
  const q = search.value.trim().toLowerCase();
  if (!q) return;
  const keys = [...nodes.keys()];
  const hit = keys.find((k) => k.toLowerCase() === q || k.toLowerCase().endsWith('.' + q)) || keys.find((k) => k.toLowerCase().includes(q));
  if (hit) { if (view !== 'graph') setView('graph'); select(hit); }
});
const render = () => {
  if (view === 'overview') overview();
  else if (view === 'graph') graph();
  else concepts();
  if (!selected) showSummary();
};
for (const c of [reqSel, frontierBox, orphanBox, allBox]) c.addEventListener('change', render);
bar.querySelector('.pg-fit').addEventListener('click', () => fit());
window.addEventListener('resize', () => { if (view === 'graph') svg.attr('width', canvas.clientWidth).attr('height', canvas.clientHeight); });
setView('overview');
