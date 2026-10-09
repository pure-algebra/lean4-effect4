import { surveySource } from '/Users/pooks/.codex/worktrees/module-semaphore/lean4-effect4/tools/ModuleSurvey/survey.mjs';
const fixtures = {
  className: `import * as E from './Effect.ts'; export const C = class E { m() { E.succeed(1); } };`,
  switchScope: `import * as E from './Effect.ts'; export function f(k) { switch (k) { case 1: const E = {succeed(){}}; E.succeed(); break; } }`,
  computedKeys: `import * as E from './Effect.ts'; export class C { [E.succeed(1)]() { E.succeed(2); } [E.succeed(3)] = E.succeed(4); } export const obj = { [E.succeed(5)](){ E.succeed(6) } };`,
  defaultParam: `import * as E from './Effect.ts'; export function f(x = E.succeed(1)) { var E = {}; }`,
  runtimeEnum: `import * as E from './Effect.ts'; export enum Status { X = E.succeed(1) }`,
  nestedHelpers: `import * as E from './Effect.ts'; export function f() { function helper(){ return E.succeed(1); } return helper(); }`,
  separateOwner: `import * as E from './Effect.ts'; const f = () => E.succeed(1), g = () => E.succeed(2);`,
  exportMark: `import * as E from './Effect.ts'; const local = () => E.succeed(1); export {local}; export default function main(){ return E.succeed(2); }`,
  unicodeOffsets: `// 🦑 café\nimport * as E from './Effect.ts'; export function f(k) { return E[k](1); }`,
};
for (const [name,source] of Object.entries(fixtures)) {
 const r=surveySource('Tiny.ts',source);
 console.log(JSON.stringify({name,definitions:r.definitions,calls:r.calls.map(c=>({...c,text:source.slice(c.start,c.end)})),unresolved:r.unresolved}));
}
