export const meta = {
  name: 'coherence-audit',
  description: 'Model six core areas from their semantics, find the bloat and the misused pattern behind it, verify each finding adversarially, and plan the minimal refactor',
  whenToUse: 'The broad coherence audit of the Lean session core, the LCNF lowering and the OCaml estate (owner, 2026-10-19); plan in docs/research/2026-10-20-coherence-audit/plan.md',
  phases: [
    { title: 'Model and find', detail: 'six mappers, one per area: model, inventory, map, root cause, minimal target' },
    { title: 'Verify', detail: 'one adversarial verifier per area, started as soon as its mapper finishes' },
    { title: 'Plan', detail: 'one synthesis: root causes, ranked cuts, slices in order, owner decisions' },
  ],
}

const ROOT = '/Users/pooks/Dev/lean4-effect4'
const OUT = (args && args.outDir) || 'docs/research/2026-10-20-coherence-audit'
const ABS = `${ROOT}/${OUT}`

const AREAS = [
  {
    key: 'lean-session',
    title: 'the Lean session face',
    scope: ['src/Effect4/Tool/', 'src/Effect4/Laws/Tool/', 'src/Effect4/Api.lean', 'src/Effect4/Api/', 'src/Effect4/Run/', 'src/Effect4/Laws/Run/', 'tools/Drivers/'],
    focus: 'the agent\'s session and tool face: the protocol, serve, the method table, replay and the exchange, the codec profile at the wire, the host session, the runner and the kit. Its concepts are host-session-protocol, exact-codecs and typed editing (docs/core/semantics.md).',
  },
  {
    key: 'lean-program',
    title: 'the Lean program core',
    scope: ['src/Effect4/Program/', 'src/Effect4/Data/'],
    focus: 'typing and checking, located refusals, admission, and authoring: sketches, documents, the source session, fills and suggestions; journals and replay. Read src/Effect4/Laws/Program/ only to find the consumers of a definition, not to audit proofs.',
  },
  {
    key: 'lean-data',
    title: 'the Lean data plane',
    scope: ['src/Effect4/Store/', 'src/Effect4/Laws/Store/', 'src/Effect4/Schema/'],
    focus: 'canonical carriers, shapes, the JSON and binary codecs and their laws, digests, the store domain (nodes, kinds, words) and the schema documents. Its concept is exact-codecs: write, read, retraction, exactness.',
  },
  {
    key: 'lowering',
    title: 'the lowering compiler',
    scope: ['src/OCaml5/', 'scripts/generate.py', 'scripts/lib/', 'ocaml/gen/ (hand files only; judge generated files through their generator)', 'ocaml/gen/interface/', 'ocaml/lcnf/', 'ocaml/tools/', 'ocaml/gen/roots.json'],
    focus: 'the LCNF route: translation, builtin rows, native constructors, type rows, externs, export classes, identity and the closure, the interface tool and the generators. Judge what the generator emits that no consumer needs, knowledge written by hand that the generator owns, and the numeric plan of decisions row 417 (1), E6.',
  },
  {
    key: 'ocaml-store',
    title: 'the OCaml store',
    scope: ['ocaml/engine/cas/'],
    focus: 'the content-addressed store: nodes, packs, the control file, the index, caches, checkpoints and the write-ahead log, under E4_disk. Start from docs/research/2026-10-19-quality-review/coherence.md, which modeled this area and found its first surplus. Seat R1 changed this area on 2026-10-19: read its receipt (docs/research/2026-10-19-quality-review/receipt-r1-store.md) if it exists, and audit the code as it is now.',
  },
  {
    key: 'ocaml-engine',
    title: 'the OCaml engine and kit',
    scope: ['ocaml/engine/ (without cas/)', 'ocaml/engine/kit/', 'ocaml/engine/test/', 'ocaml/eff/', 'ocaml/clock/'],
    focus: 'the scheduler, the engine and its host boundary, the kit, the eff CLI, the MCP server, the test harness, the exact clock, and the program wire. Judge each hand module against the generated owner it should call, as the kit should call E4_engine.check_answer (coherence.md §6).',
  },
]

log('Out of this run, by plan: src/Effect4/Machine and Laws/Machine, the program proofs (Laws/Program, 613 files), ts/, harness/ and rocq/. Proof bloat gets its own run.')

const FINDINGS_SCHEMA = {
  type: 'object',
  properties: {
    area: { type: 'string' },
    head: { type: 'string', description: 'the output of git rev-parse --short HEAD when you started' },
    model: { type: 'string', description: 'the area\'s minimal model in the semantics\' terms: sorts, operations, observations, boundaries; each with the semantics.md concept it serves' },
    inventory: { type: 'string', description: 'the modules, types and definitions by owner, with each counting command and its result' },
    findings: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string', description: '<area>-<n>' },
          title: { type: 'string' },
          kind: { type: 'string', enum: ['two-owners', 'parallel-type', 'no-consumer', 'casework-over-fold', 'swallowed-or-raised-refusal', 'wrapper-or-one-off', 'misplaced-owner', 'other'] },
          misuse: { type: 'string', description: 'the modeling error: the case or pattern misused, so this surplus could exist' },
          where: { type: 'string', description: 'files and declaration names' },
          evidence: { type: 'string', description: 'the commands and their output' },
          target: { type: 'string', description: 'the minimal shape, as signatures' },
          observation: { type: 'string', description: 'what stays equal, on which fragment, and how that is checked' },
          deletes: { type: 'string' },
          adds: { type: 'string' },
          netLines: { type: 'number', description: 'the net line change, negative for a deletion; measured where possible' },
          consumers: { type: 'string', description: 'every caller the change reaches, from a repository-wide search' },
          rulingConflict: { type: 'string', description: 'a decisions row this contradicts, or "none"' },
          size: { type: 'string', enum: ['XS', 'S', 'M', 'L'] },
        },
        required: ['id', 'title', 'kind', 'misuse', 'where', 'evidence', 'target', 'observation', 'deletes', 'adds', 'netLines', 'consumers', 'rulingConflict', 'size'],
      },
    },
    notCovered: { type: 'string', description: 'what in the scope you did not read or judge, and why' },
  },
  required: ['area', 'head', 'model', 'inventory', 'findings', 'notCovered'],
}

const VERDICTS_SCHEMA = {
  type: 'object',
  properties: {
    area: { type: 'string' },
    verdicts: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string' },
          verdict: { type: 'string', enum: ['confirmed', 'amended', 'refuted'] },
          reason: { type: 'string' },
          evidence: { type: 'string', description: 'the commands you ran and their output' },
          amendedTarget: { type: 'string', description: 'the corrected target when amended, else empty' },
          overEngineered: { type: 'boolean', description: 'true when the target adds more than it removes or invents a framework' },
        },
        required: ['id', 'verdict', 'reason', 'evidence', 'amendedTarget', 'overEngineered'],
      },
    },
    missed: {
      type: 'array',
      description: 'surplus the mapper missed, at most five, each with its evidence',
      items: { type: 'string' },
    },
  },
  required: ['area', 'verdicts', 'missed'],
}

const READ_FIRST = `Read these first, all under ${ROOT}:
- docs/core/semantics.md (the concepts and their required properties), docs/core/system-map.md, and docs/core/controlled-english.md §3 (the dictionary; one meaning per word);
- docs/core/decisions.md, rows 391 (the lowering is trusted), 414 to 417 (the API, waves 1 and 2, and the quality review's rulings);
- ocaml/STANDARDS.md and ocaml/README.md for an OCaml area;
- docs/research/2026-10-19-quality-review/coherence.md: the method applied to one area, with the existing owners it found;
- docs/research/2026-10-19-quality-review/codex-review/README.md and wave3.md beside it: the findings already known;
- docs/research/2026-10-20-coherence-audit/plan.md: why this audit runs and its method.`

const RULES = `Rules:
- Read-only on every tracked file. Write only the area files your task names, and probes under ${ABS}/probes/<your area>/.
- Never run make, lake build Test, make gen-semantics or tsc. Never run a git command that changes state (add, commit, stash, checkout, reset, worktree).
- Run a Lean probe only as: cd ${ROOT} && python3 /private/tmp/seams-lean-one.py lake env lean <file>. Never pass a thread count; never send its stderr to /dev/null. If that script is missing, run no Lean and mark the probe unrun.
- Build OCaml only when a probe needs it, and only into a separate build folder: cd ${ROOT}/ocaml && opam exec --switch=effect4 -- dune build --build-dir ${ABS}/probes/_build-<your area>. Never touch ocaml/_build.
- The shell is zsh: it does not split an unquoted variable into words. Quote "===" and similar.
- Start no subagent.
- Write in short, plain sentences. Cite a declaration by its name and its path, never by a line number.`

function mapPrompt(area) {
  return `You are the mapper for ${area.title} in the Effect4 repository at ${ROOT}, in a coherence audit the owner asked for on 2026-10-19.

The owner's principle: bloat is a modeling error. If a construct exists that the desired behavior does not need, we modeled the system wrongly, or misused a case or a pattern. Elegance is minimality with respect to the desired behavior, so over-engineering is as wrong as bloat. This codebase separates semantics (what must be observed) from mechanism (how), and that separation is your tool.

Your scope: ${area.scope.join(', ')}.
Your focus: ${area.focus}

${READ_FIRST}

Then do these steps in order.
1. Model. Write the area's minimal model in the semantics' terms: the sorts it carries, the operations a client or an agent needs, the observations that must hold (judgments, laws, refusals), and its boundaries (host, wire, disk, generated code). This is the desired behavior. A construct is justified only by an observation it serves, a measured need, or a boundary.
2. Inventory. List the modules, types and definitions, with counts from commands (git ls-files, wc -l, grep). In OCaml, a file whose first lines say GENERATED is judged through its generator, not as hand code.
3. Map. Put each construct against the model element it realizes. Look for six kinds of surplus:
   - one fact with two owners: a hand copy of Lean, two types with the same arms, two parsers of one format, two checkers or two logs of one promise;
   - a construct with no consumer outside its own tests: search the whole repository, including scripts/, tools/, ts/, harness/, the Makefile and ocaml/gen/roots.json, before you say so; an option that only tests set counts;
   - casework where the model has a fold, a table or an algebra (AGENTS.md: free object, algebra and fold, exact embedding, located refusal, monoid action, a table passed as data);
   - a failure the model calls a refusal, which the code swallows or raises;
   - a wrapper that only renames, or a one-off helper beside a shared one;
   - a definition away from its owner: Lean meaning written in OCaml, or the generator's knowledge written by hand.
4. Root cause. For each finding, name the modeling error in misuse: the case or the pattern we misused, so the surplus could exist. Examples: "the generated face was not used, so a hand twin grew"; "the generated refusal type was not reached, so a second error type grew"; "built before its consumer". Use the same words for findings that share a cause, so the plan can remove the cause once.
5. Minimal target. Give the smallest shape that keeps every observation, as signatures, with what it deletes and what it adds, measured. A target that adds more lines or constructs than it removes is not a finding. A new abstraction must replace at least two existing owners. Add no generic framework, no generic judgment record (decisions row 414 (2)), no new program syntax and no gate lane. Prefer deletion.
6. Evidence. Every claim carries its command and its output. Two constructs are duplicates only when they serve one observation: show it, by a grep of their arms, a #guard, or a probe. Two constructs that serve different observations, boundaries or measured needs are not duplicates: keep them, and say why if a reader might think otherwise.
7. Rulings. Search docs/core/decisions.md for a row that rules on each construct. A finding that contradicts a ruling names the row in rulingConflict; it becomes the owner's decision.
8. Known items. The Codex review, coherence.md and wave3.md already list some findings. Repeat one only when your model changes its target, and say so. Spend your effort on what they missed.

Depth before breadth: a few findings with a root cause, a minimal target and evidence are worth more than many observations. Twenty findings at most.

Write ${ABS}/${area.key}.md: the model, the inventory, the findings in the order of their net deletion, and what you did not cover. Then return the structured result.

${RULES}`
}

function verifyPrompt(area, found) {
  return `You are the adversarial verifier for ${area.title} in the Effect4 repository at ${ROOT}, in the coherence audit described in ${ABS}/plan.md. The mapper's model and findings are below and in ${ABS}/${area.key}.md.

Your job is to refute. For each finding, try each of these, and keep the evidence:
1. Rerun its evidence commands, or your own. Missing or wrong evidence refutes the finding.
2. The duplicate claim: do the two constructs serve one observation? Or do they serve different observations, different boundaries, or a measured need written somewhere? Different observations refute "two owners".
3. The consumer claim: search the whole repository, including tests, scripts/, tools/, ts/, harness/, rocq/, the Makefile, ocaml/gen/roots.json and the generated recipes. A consumer the mapper missed refutes "no consumer".
4. The target: does it keep every observation of the model? Look for a counterexample input, a law it breaks, or a consumer it breaks. If the target is right in spirit but wrong in a detail, amend it.
5. Over-engineering: does the target add more than it removes, invent a framework, or add a type that one existing type covers? If so, set overEngineered and amend or refute.
6. Rulings: does it contradict a decisions row the mapper did not name?

Default to refuted when you cannot find evidence either way. Then list at most five surplus constructs the mapper missed in this area, each with its evidence.

Write ${ABS}/${area.key}.verify.md with each verdict and its evidence. Then return the structured result.

${RULES}

The mapper's result:
${JSON.stringify(found, null, 1)}`
}

function synthPrompt(done) {
  const kept = done.map(r => {
    const byId = new Map((r.verdicts ? r.verdicts.verdicts : []).map(v => [v.id, v]))
    const findings = (r.found.findings || []).map(f => ({ ...f, verdict: byId.get(f.id) || null }))
      .filter(f => !f.verdict || f.verdict.verdict !== 'refuted')
    const refuted = (r.found.findings || []).filter(f => byId.get(f.id) && byId.get(f.id).verdict === 'refuted')
      .map(f => ({ id: f.id, title: f.title, reason: byId.get(f.id).reason }))
    return {
      area: r.area,
      head: r.found.head,
      model: r.found.model,
      notCovered: r.found.notCovered,
      findings,
      refuted,
      missed: r.verdicts ? r.verdicts.missed : [],
    }
  })
  return `You are the synthesis of the coherence audit of the Effect4 repository at ${ROOT}. Read ${ABS}/plan.md for its purpose and method, and the area notes in ${ABS} (<area>.md and <area>.verify.md) for detail. The verified results are below: refuted findings are removed and listed apart, and an amended verdict replaces its finding's target.

The owner's principle: bloat is a modeling error, and elegance is minimality with respect to the desired behavior. The owner wants the misused cases and patterns found and removed, not findings patched one by one, and no over-engineering.

Write ${ABS}/README.md, in short plain sentences, citing declarations by name and path:
1. The one thing to know.
2. The root causes. Group the findings by their misuse across all areas. For each cause, state the design rule that removes the whole class (a rule for how we build, not a new gate), its findings, and the net lines they delete. Merge findings in two areas that are one fact, such as a Lean codec and its OCaml twin.
3. The ranked cuts: a table of id, area, what goes, net lines, size and verdict, ordered by root cause and then by net deletion.
4. The refactor plan: slices with disjoint file ownership, in order, each with its observations and red controls. Fold the open repair wave into it: seat R1's remaining items, R2, R3 and E6 (docs/research/2026-10-19-quality-review/wave3.md), and the open log question (coherence.md §5). Say which of those the audit changes. The owner's current rule is one seat at a time as a subagent in the main checkout (decisions row 417 (5)).
5. What the audit did not cover: the areas out of scope, each mapper's notCovered, and the refuted findings with their reasons.
6. The decisions only the owner can make, with a recommendation each, including every finding with a rulingConflict.

Check your own report for over-engineering before you finish: every slice must delete more than it adds, or name the observation that justifies its additions.

Write only ${ABS}/README.md. Then return its first section and the slice list as your final text.

${RULES}

The verified results:
${JSON.stringify(kept, null, 1)}`
}

phase('Model and find')
const results = await pipeline(
  AREAS,
  area => agent(mapPrompt(area), { label: `map:${area.key}`, phase: 'Model and find', schema: FINDINGS_SCHEMA }),
  (found, area) => found
    ? agent(verifyPrompt(area, found), { label: `verify:${area.key}`, phase: 'Verify', schema: VERDICTS_SCHEMA })
      .then(verdicts => ({ area: area.key, found, verdicts }))
    : null,
)

const done = results.filter(Boolean)
const dropped = AREAS.filter(a => !done.some(r => r.area === a.key)).map(a => a.key)
if (dropped.length) log(`No verified result for: ${dropped.join(', ')}. The synthesis reports them as not covered.`)
for (const r of done) {
  const n = (r.found.findings || []).length
  const refuted = r.verdicts ? r.verdicts.verdicts.filter(v => v.verdict === 'refuted').length : 0
  log(`${r.area}: ${n} findings, ${refuted} refuted, ${r.verdicts ? r.verdicts.missed.length : 0} missed by the mapper`)
}

phase('Plan')
const plan = await agent(synthPrompt(done), { label: 'plan', phase: 'Plan' })

return {
  outDir: OUT,
  areas: done.map(r => ({
    area: r.area,
    head: r.found.head,
    findings: (r.found.findings || []).length,
    refuted: r.verdicts ? r.verdicts.verdicts.filter(v => v.verdict === 'refuted').length : null,
    missed: r.verdicts ? r.verdicts.missed.length : null,
  })),
  dropped,
  plan,
}
