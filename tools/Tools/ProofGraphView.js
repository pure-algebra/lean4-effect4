// The proof graph view of the architecture map (tools/Tools/Architecture.lean), an ES module.
// It reads the semantics report embedded in the page (#pg-data, written by `make gen-semantics`)
// and draws the requirements, their top nodes, the claims' witnesses and the planned goals.
// Nothing is declared here: every node, edge, status, concept and role comes from the report.
//
// The drawing keeps the corpus's three labels apart (docs/core/controlled-english.md, W22):
// evidence status is the card's stroke and fill (proved, modulo its goals, planned goal);
// the concept is the hue (the ten concepts of docs/core/semantics.md, in its order);
// the proof role is the chip (the registry's `Role`). The requirements of the system map's §8
// are the frame, so they open the graph on the left and the evidence flows to the right.
// Layout: d3-dag's Sugiyama method (layering, crossing reduction, coordinate assignment).
import * as d3 from 'https://cdn.jsdelivr.net/npm/d3@7.9.0/+esm';
import { graphStratify, sugiyama, layeringSimplex, decrossTwoLayer, coordSimplex, coordGreedy } from 'https://cdn.jsdelivr.net/npm/d3-dag@1.1.0/+esm';

const root = document.getElementById('pg');
const report = JSON.parse(document.getElementById('pg-data').textContent);
const plan = report.plan || { requirements: [], nodes: [], next: [], unplacedGoals: [] };
const short = (n) => n.split('.').pop();
const esc = (s) => String(s).replace(/&/g, '&amp;').replace(/[<]/g, '&lt;').replace(/>/g, '&gt;');
// card and column sizes; a foundation is a theorem the proofs of HUB or more others reach first
const CW = 214, CH = 30, REQW = 250, GAPX = 14, GAPY = 96, FRAME = REQW + 150, HUB = 6;

// --- the model ---
const conceptIds = (report.concepts || []).map((c) => c.id);
const conceptTitle = Object.fromEntries((report.concepts || []).map((c) => [c.id, c.title]));
// ten hues spaced around the wheel in the concepts' document order, muted to sit on paper and ink
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
const nodes = new Map();
const reqs = plan.requirements.map((r) => r.id);
for (const r of plan.requirements) {
  nodes.set('req:' + r.id, { id: 'req:' + r.id, kind: 'requirement', label: r.id, title: r.title, status: r.status,
    openParts: r.openParts || [], next: r.next || [], out: (r.top || []).map((t) => t.name) });
}
for (const n of plan.nodes) {
  const claims = claimsOf[n.name] || [];
  nodes.set(n.name, { id: n.name, kind: n.kind, label: short(n.name), status: n.status, module: n.module,
    statement: n.statement || '', axioms: n.axioms || [], restsOn: n.restsOn || [],
    out: ((n.broughtIn || {}).nearest || []), lemmas: (n.broughtIn || {}).lemmas || 0,
    definitions: (n.broughtIn || {}).definitions || 0, claims,
    concept: (claims[0] && claims[0].concept) || placement[n.name] || null,
    role: claims[0] ? claims[0].role : null });
}
for (const n of nodes.values()) n.out = n.out.filter((t) => nodes.has(t));
const parentsOf = new Map([...nodes.keys()].map((k) => [k, []]));
for (const n of nodes.values()) for (const t of n.out) parentsOf.get(t).push(n.id);
const reach = (start, next) => {
  const seen = new Set([start]); const todo = [start];
  while (todo.length) for (const m of next(todo.pop())) if (!seen.has(m)) { seen.add(m); todo.push(m); }
  return seen;
};
const down = (id) => nodes.get(id).out;
const up = (id) => parentsOf.get(id);

// --- the controls ---
const bar = root.querySelector('.pg-bar');
const canvas = root.querySelector('.pg-canvas');
const panel = root.querySelector('.pg-panel');
bar.innerHTML =
  `<select aria-label="Requirement"><option value="">All requirements</option>${plan.requirements.map((r) => `<option value="${esc(r.id)}">${esc(r.id)} · ${esc(r.title.length > 48 ? r.title.slice(0, 47) + '…' : r.title)}</option>`).join('')}</select>` +
  `<label><input type="checkbox" class="pg-frontier"> The frontier only</label>` +
  `<label><input type="checkbox" class="pg-orphans"> Claims no requirement reaches</label>` +
  `<input type="search" placeholder="Find a declaration" aria-label="Find a declaration">` +
  `<button type="button" class="pg-fit">Fit</button><span class="pg-counts"></span>`;
const reqSel = bar.querySelector('select');
const frontierBox = bar.querySelector('.pg-frontier');
const orphanBox = bar.querySelector('.pg-orphans');
const search = bar.querySelector('input[type=search]');
const tally = (k) => [...nodes.values()].filter((n) => n.kind !== 'requirement' && n.status === k).length;
bar.querySelector('.pg-counts').innerHTML =
  `<b>${reqs.length}</b> requirements, ${plan.requirements.filter((r) => r.status !== 'proved').length} open · ` +
  `<b>${tally('proved')}</b> proved · <b>${tally('modulo')}</b> modulo · <b>${tally('goal')}</b> planned goals`;
const legend = document.createElement('div');
legend.className = 'pg-legend';
const usedRoles = [...new Set([...nodes.values()].map((n) => n.role).filter(Boolean))];
legend.innerHTML =
  `<div><em>Evidence status</em><span class="st proved">proved</span><span class="st modulo">modulo its goals</span><span class="st goal">planned goal</span><span class="st req">requirement</span></div>` +
  `<div><em>Concept</em>${conceptIds.map((c) => `<span class="cc" style="--c:${conceptColour(c)}" title="${esc(conceptTitle[c] || '')}">${esc(c)}</span>`).join('')}</div>` +
  `<div><em>Proof role</em>${usedRoles.map((r) => `<span class="rl"><b>${ROLE[r] || r}</b> ${esc(r)}</span>`).join('')}</div>` +
  `<div><em>Foundation</em><span class="fd"><b>n →</b> a theorem the proofs of n others reach first (n ≥ ${HUB}); its incoming edges are drawn along a selection</span></div>`;
bar.after(legend);

// --- the visible subgraph ---
const visible = () => {
  let ids = new Set(nodes.keys());
  const fromReqs = new Set();
  for (const r of reqs) for (const a of reach('req:' + r, down)) fromReqs.add(a);
  if (reqSel.value) ids = reach('req:' + reqSel.value, down);
  else if (!orphanBox.checked) ids = new Set([...ids].filter((i) => fromReqs.has(i)));
  if (frontierBox.checked) {
    const hot = new Set();
    for (const n of nodes.values()) if (n.status === 'goal') for (const a of reach(n.id, up)) hot.add(a);
    ids = new Set([...ids].filter((i) => hot.has(i)));
  }
  return ids;
};

// --- layout ---
// The theorems and goals are laid out by d3-dag's Sugiyama method, computed top-down and drawn
// left to right. The requirements stay out of it: they are the frame, a column in the system
// map's order R1 to R13 on the left, whatever order would cross fewer edges.
const layout = (ids) => {
  const theorems = [...ids].filter((i) => !i.startsWith('req:'));
  const pos = new Map();
  const links = [];
  if (theorems.length) {
    const set = new Set(theorems);
    const dag = graphStratify()(theorems.map((id) => ({ id, parentIds: up(id).filter((p) => set.has(p)) })));
    const base = sugiyama().nodeSize([CH + GAPX, CW]).gap([0, GAPY]).layering(layeringSimplex()).decross(decrossTwoLayer());
    try { base.coord(coordSimplex())(dag); } catch { base.coord(coordGreedy())(dag); }
    for (const node of dag.nodes()) pos.set(node.data.id, { x: FRAME + node.y, y: node.x });
    for (const l of dag.links()) links.push({ from: l.source.data.id, to: l.target.data.id, pts: l.points.map(([x, y]) => [FRAME + y, x]) });
  }
  const frame = [...ids].filter((i) => i.startsWith('req:')).sort((a, b) => reqs.indexOf(a.slice(4)) - reqs.indexOf(b.slice(4)));
  const ys = [...pos.values()].map((p) => p.y);
  const top = ys.length ? Math.min(...ys) : 0, bottom = ys.length ? Math.max(...ys) : 0;
  const step = Math.max(CH + 16, frame.length > 1 ? (bottom - top) / (frame.length - 1) : 0);
  const start = (top + bottom) / 2 - (step * (frame.length - 1)) / 2;
  frame.forEach((id, i) => pos.set(id, { x: REQW / 2, y: start + i * step }));
  return { pos, links };
};

// --- drawing ---
const svg = d3.select(canvas).append('svg').attr('role', 'img')
  .attr('aria-label', 'The proof graph: requirements, theorems and planned goals; an edge runs from a node to the nodes its proof reaches first');
const view = svg.append('g');
const gEdges = view.append('g').attr('class', 'pg-edges');
const gNodes = view.append('g').attr('class', 'pg-nodes');
const zoom = d3.zoom().scaleExtent([0.08, 2.5]).on('zoom', (ev) => view.attr('transform', ev.transform));
svg.call(zoom).on('dblclick.zoom', null);
let selected = null;
let reqCentre = null;
const line = d3.line().curve(d3.curveMonotoneX);
// the whole drawing, from its drawn bounds
const fit = (animate = true) => {
  const b = view.node().getBBox();
  if (!b.width || !b.height) return;
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const k = Math.min(1.2, 0.94 * Math.min(w / b.width, h / b.height));
  const t = d3.zoomIdentity.translate((w - b.width * k) / 2 - b.x * k, (h - b.height * k) / 2 - b.y * k).scale(k);
  (animate ? svg.transition().duration(450) : svg).call(zoom.transform, t);
};
// the opening view: the whole drawing when it is legible, otherwise a legible scale anchored on
// the requirements, the frame the evidence flows from
const open = () => {
  const b = view.node().getBBox();
  const w = canvas.clientWidth, h = canvas.clientHeight;
  const k = 0.94 * Math.min(w / b.width, h / b.height);
  if (k >= 0.62 || !reqCentre) return fit(false);
  const s = 0.72;
  svg.call(zoom.transform, d3.zoomIdentity.translate(24 - b.x * s, h / 2 - reqCentre * s).scale(s));
};
const status = (n) => (n.kind === 'requirement' ? (n.status === 'proved' ? 'proved' : 'req') : n.status);
const draw = () => {
  const ids = visible();
  gEdges.selectAll('*').remove(); gNodes.selectAll('*').remove();
  if (!ids.size) return;
  const { pos, links } = layout(ids);
  // a foundation: a theorem the proofs of six or more visible theorems reach first. Its incoming
  // edges are drawn only along a selection; its card says how many reach it.
  const uses = new Map();
  for (const l of links) uses.set(l.to, (uses.get(l.to) || 0) + 1);
  const foundation = (id) => (uses.get(id) || 0) >= HUB;
  svg.attr('width', canvas.clientWidth).attr('height', canvas.clientHeight);
  const reqYs = [...pos].filter(([k]) => k.startsWith('req:')).map(([, p]) => p.y);
  reqCentre = reqYs.length ? (Math.min(...reqYs) + Math.max(...reqYs)) / 2 : null;
  const edge = (a, b, d) => gEdges.append('path').attr('d', d)
    .attr('class', 'pg-edge' + (nodes.get(b).kind === 'goal' ? ' rests' : '') + (a.startsWith('req:') ? ' frame' : '')
      + (!a.startsWith('req:') && foundation(b) ? ' found' : ''))
    .attr('data-from', a).attr('data-to', b);
  // the frame's edges: from a requirement to each top node it names, a smooth horizontal curve
  for (const id of ids) {
    if (!id.startsWith('req:')) continue;
    const pa = pos.get(id);
    for (const t of nodes.get(id).out) {
      if (!pos.has(t)) continue;
      const pb = pos.get(t), x1 = pa.x + REQW / 2, x2 = pb.x - CW / 2, dx = Math.max(60, (x2 - x1) * 0.45);
      edge(id, t, `M${x1},${pa.y} C${x1 + dx},${pa.y} ${x2 - dx},${pb.y} ${x2},${pb.y}`);
    }
  }
  // the evidence's edges: d3-dag's routes, ending at the cards' sides
  for (const l of links) {
    const pa = pos.get(l.from), pb = pos.get(l.to);
    const pts = l.pts.slice();
    pts[0] = [pa.x + CW / 2, pa.y]; pts[pts.length - 1] = [pb.x - CW / 2, pb.y];
    edge(l.from, l.to, line(pts));
  }
  for (const [id, p] of pos) {
    const n = nodes.get(id);
    const w = n.kind === 'requirement' ? REQW : CW;
    const g = gNodes.append('g').attr('class', `pg-node ${status(n)}`).attr('transform', `translate(${p.x - w / 2},${p.y - CH / 2})`)
      .attr('tabindex', 0).attr('role', 'button').attr('data-id', id)
      .attr('aria-label', n.kind === 'requirement' ? `${n.label}: ${n.title}, ${n.status}` : `${n.id}, ${n.status}`);
    g.append('title').text(n.kind === 'requirement' ? `${n.label}: ${n.title}` : `${n.id} (${n.status})`);
    g.append('rect').attr('class', 'card').attr('width', w).attr('height', CH).attr('rx', n.kind === 'requirement' ? CH / 2 : 6);
    if (n.kind === 'requirement') {
      g.append('text').attr('class', 'rid').attr('x', 14).attr('y', CH / 2 + 4).text(n.label);
      const t = n.title.length > 30 ? n.title.slice(0, 29) + '…' : n.title;
      g.append('text').attr('class', 'rtitle').attr('x', 46).attr('y', CH / 2 + 4).text(t);
    } else {
      g.append('rect').attr('class', 'stripe').attr('width', 5).attr('height', CH).attr('rx', 2).attr('fill', conceptColour(n.concept));
      const label = n.label.length > 24 ? n.label.slice(0, 23) + '…' : n.label;
      g.append('text').attr('class', 'name').attr('x', 13).attr('y', CH / 2 + 4).text(label);
      if (n.role) {
        g.append('text').attr('class', 'role').attr('x', w - 8).attr('y', CH / 2 + 3.5).attr('text-anchor', 'end').text(ROLE[n.role] || n.role);
      }
      if (foundation(id)) {
        g.classed('foundation', true);
        g.append('text').attr('class', 'uses').attr('x', -6).attr('y', CH / 2 + 3.5).attr('text-anchor', 'end').text(`${uses.get(id)} →`);
      }
    }
    g.on('click', (ev) => { ev.stopPropagation(); select(id, false); })
      .on('keydown', (ev) => { if (ev.key === 'Enter' || ev.key === ' ') { ev.preventDefault(); select(id, false); } });
  }
  open();
  if (selected && pos.has(selected)) highlight(selected); else { selected = null; showSummary(); }
};
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
const clear = () => {
  selected = null;
  gNodes.selectAll('.pg-node').classed('dim', false).classed('sel', false);
  gEdges.selectAll('.pg-edge').classed('dim', false).classed('hot', false);
  showSummary();
};
svg.on('click', clear);

// --- the panel ---
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
    `<p class="hint">Select a card for its statement, its axioms, the goals it rests on and what its proof brings in. Scroll to zoom, drag to pan.</p>`;
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
  panel.innerHTML = `<h4>${esc(n.id)}</h4><p class="sub">${path ? `<a href="../../${esc(path)}">${esc(path)}</a>` : ''}</p>` +
    badge(n.status === 'goal' ? 'planned goal' : n.status, n.status) +
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
const select = (id, centre = true) => {
  selected = id;
  if (gNodes.select(`[data-id="${CSS.escape(id)}"]`).empty()) { reqSel.value = ''; frontierBox.checked = false; orphanBox.checked = true; draw(); }
  highlight(id); show(id);
  if (centre) {
    const g = gNodes.select(`[data-id="${CSS.escape(id)}"]`).node();
    if (g) {
      const m = /translate\(([-\d.]+),([-\d.]+)\)/.exec(g.getAttribute('transform'));
      const k = Math.max(0.6, d3.zoomTransform(svg.node()).k);
      const t = d3.zoomIdentity.translate(canvas.clientWidth / 2 - (+m[1] + CW / 2) * k, canvas.clientHeight / 2 - (+m[2] + CH / 2) * k).scale(k);
      svg.transition().duration(450).call(zoom.transform, t);
    }
  }
};
panel.addEventListener('click', (ev) => {
  const a = ev.target.closest('a[data-go]');
  if (a) { ev.preventDefault(); select(a.getAttribute('data-go')); }
});

// --- search and filters ---
search.addEventListener('keydown', (ev) => {
  if (ev.key !== 'Enter') return;
  const q = search.value.trim().toLowerCase();
  if (!q) return;
  const keys = [...nodes.keys()];
  const hit = keys.find((k) => k.toLowerCase() === q || k.toLowerCase().endsWith('.' + q)) || keys.find((k) => k.toLowerCase().includes(q));
  if (hit) select(hit);
});
for (const c of [reqSel, frontierBox, orphanBox]) c.addEventListener('change', draw);
bar.querySelector('.pg-fit').addEventListener('click', () => fit());
window.addEventListener('resize', () => { svg.attr('width', canvas.clientWidth).attr('height', canvas.clientHeight); });
draw();
