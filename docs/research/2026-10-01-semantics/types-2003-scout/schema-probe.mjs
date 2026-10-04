import { readFileSync } from 'node:fs';
import { createRequire } from 'node:module';
import { pathToFileURL } from 'node:url';
const root = '/Users/pooks/Dev/lean4-effect4-gemini';
const schemaPath = `${root}/ts/eff/semantics.ts`;
const require = createRequire(schemaPath);
const { Schema } = await import(pathToFileURL(require.resolve('effect')).href);
const { LiteratureRef, decodeSemanticsReport } = await import(pathToFileURL(schemaPath).href);
const refs = JSON.parse(readFileSync(new URL('./literature-refs.json', import.meta.url), 'utf8'));
const base = JSON.parse(readFileSync(`${root}/generated/semantics.json`, 'utf8'));
const decodeRefs = Schema.decodeUnknownSync(Schema.Array(LiteratureRef), { onExcessProperty: 'error' });
const cases = [];
function check(name, expected, fn) {
  let accepted = false, reason = null;
  try { fn(); accepted = true; } catch (e) { reason = String(e.message).slice(0,500); }
  cases.push({ name, expected, accepted, reason });
  if (accepted !== expected) throw new Error(`control failed: ${name}`);
}
check('current selected report', true, () => decodeSemanticsReport(base));
check('three proposed reference shapes', true, () => decodeRefs(refs));
check('blank source', false, () => decodeRefs([{ ...refs[0], work: '' }]));
check('unknown relation', false, () => decodeRefs([{ ...refs[0], relation: 'provesEverything' }]));
check('unmodeled verified flag', false, () => decodeRefs([{ ...refs[0], verified: true }]));
const unknown = structuredClone(base);
unknown.claims[0].literature = [{ work: 'NO-SUCH-SOURCE-VISIBILITY-PROBE', locator: 'NO-SUCH-LOCATOR', relation: 'analogy' }];
check('unknown source currently accepted by full report decoder', true, () => decodeSemanticsReport(unknown));
console.log(JSON.stringify({ effect: require('effect/package.json').version, cases, boundary: 'Bun runtime decoder probe, no TypeScript compiler run or evidence revalidation' }, null, 2));
