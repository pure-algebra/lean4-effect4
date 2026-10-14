#!/usr/bin/env node
// Host-only oracle. D3 owns the curve calculation; no production dependency.
import { readFileSync, mkdirSync, writeFileSync } from 'node:fs';
import { resolve, dirname, join, relative, isAbsolute, sep } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';

const here = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const options = { package: join(here, 'out/d3-oracle/node_modules/d3-shape'), python: 'python', curve: 'basis', guides: 'knots', shape: [] };
for (let i = 0; i < args.length; i++) {
  const key = args[i].replace(/^--/, '');
  if (!['source', 'output', 'package', 'python', 'curve', 'guides', 'shape'].includes(key) || !args[i + 1]) {
    throw new Error('Usage: node d3_curve_study.mjs --source DIR --output DIR [--package D3_SHAPE_DIR] [--curve basis|natural|catmullRom] [--guides controls|knots] [--shape RELATIVE_SVG]');
  }
  if (key === 'shape') options.shape.push(args[++i]);
  else options[key] = args[++i];
}
if (!options.source || !options.output) throw new Error('--source and --output are required');
options.source = resolve(options.source);
options.output = resolve(options.output);
options.package = resolve(options.package);
function contains(parent, child) {
  const rel = relative(parent, child);
  return rel === '' || (!isAbsolute(rel) && rel !== '..' && !rel.startsWith('..' + sep));
}
if (contains(options.source, options.output) || contains(options.output, options.source)) {
  throw new Error('Source and output must be separate trees, without an ancestor or descendant relationship');
}
const pkg = JSON.parse(readFileSync(join(options.package, 'package.json'), 'utf8'));
if (pkg.name !== 'd3-shape' || pkg.version !== '3.2.0') throw new Error('Expected pinned d3-shape@3.2.0');
const d3 = await import(pathToFileURL(join(options.package, 'src/index.js')).href);
const factory = { basis: d3.curveBasis, natural: d3.curveNatural, catmullRom: d3.curveCatmullRom }[options.curve];
if (!factory) throw new Error('Unknown curve');
if (!['controls', 'knots'].includes(options.guides)) throw new Error('Unknown guide strategy');
function helper(mode, input) {
  const result = spawnSync(options.python, [join(here, 'd3_curve_study.py'), mode, options.source, options.output], {
    input: input === undefined ? undefined : JSON.stringify(input), encoding: 'utf8',
    env: { ...process.env, PYTHONUTF8: '1' }, maxBuffer: 256 * 1024 * 1024,
  });
  if (result.status !== 0) throw new Error(result.stderr || result.stdout || 'Python helper failed');
  return JSON.parse(result.stdout);
}
function side(points) {
  let current, start;
  const commands = [];
  const context = {
    moveTo(x, y) { if (start) throw new Error('Multiple side contours'); current = start = [x, y]; },
    lineTo(x, y) {
      const end = [x, y];
      const lerp = (t) => current.map((v, i) => v + t * (end[i] - v));
      commands.push({ kind: 'line', points: [current, lerp(1 / 3), lerp(2 / 3), end] });
      current = end;
    },
    bezierCurveTo(x1, y1, x2, y2, x, y) {
      const end = [x, y];
      commands.push({ kind: 'curve', points: [current, [x1, y1], [x2, y2], end] });
      current = end;
    },
    closePath() { throw new Error('Unexpected closed side'); },
  };
  const curve = factory(context);
  curve.lineStart();
  for (const p of points) curve.point(...p);
  curve.lineEnd();
  if (start.some((v, i) => v !== points[0][i]) || current.some((v, i) => v !== points.at(-1)[i])) {
    throw new Error('D3 changed a side endpoint');
  }
  return commands;
}
const records = helper('extract', { guides: options.guides });
for (const record of records) {
  const right = record.guides[0], left = record.guides[1].toReversed();
  if (right.length !== left.length) throw new Error('Unpaired guide points');
  // Remove only duplicates present on both sides at the same forward index.
  const keep = right.map((p, i) => i === 0 ||
    !(p.every((v, j) => v === right[i - 1][j]) && left[i].every((v, j) => v === left[i - 1][j])));
  const guides = [right.filter((_, i) => keep[i]), left.filter((_, i) => keep[i]).toReversed()];
  record.removed_guide_pairs = keep.filter(x => !x).length;
  record.sides = guides.map(side);
  if (record.sides[0].length !== record.sides[1].length) throw new Error('D3 produced unequal side lengths');
  delete record.guides;
}
const sourceBytes = readFileSync(join(options.package, `src/curve/${options.curve}.js`));
const metadata = { library: pkg.name, version: pkg.version, license: pkg.license, author: pkg.author.name,
  curve: options.curve, source_sha256: createHash('sha256').update(sourceBytes).digest('hex'),
  source_url: `https://github.com/d3/d3-shape/blob/v3.2.0/src/curve/${options.curve}.js`,
  license_notice: readFileSync(join(options.package, 'LICENSE'), 'utf8'),
  guides: options.guides,
  guide_policy: options.guides === 'controls'
    ? 'whole original Bezier control polygon; remove only paired consecutive duplicates'
    : 'original side knots plus first/last endpoint tangent guides; remove only paired consecutive duplicates',
  line_policy: 'convert D3 lineTo to a linear cubic with controls at one-third and two-thirds',
  serialization: 'Python repr round-trip double decimal after JavaScript arithmetic; no quantization',
  shape_comparison: 'local-chord backtracking depends on subdivision; original/candidate counts do not prove an improvement',
  source: options.source, output: options.output, shape_files: options.shape };
mkdirSync(options.output, { recursive: true });
writeFileSync(join(options.output, 'oracle-metadata.json'), JSON.stringify(metadata, null, 2) + '\n');
const report = helper('write', { records, metadata });
console.log(JSON.stringify(report.summary, null, 2));
