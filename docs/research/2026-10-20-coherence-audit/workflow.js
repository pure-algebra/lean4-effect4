export const meta = {
  name: 'coherence-audit',
  description: 'Three agents read the core against the project\'s organizing principle: two conceptual readers (the Lean core; the compiler and the OCaml estate), then one adversarial synthesis that plans the refactor',
  whenToUse: 'The conceptual coherence audit the owner asked for on 2026-10-19; plan and orientation in docs/research/2026-10-20-coherence-audit/',
  phases: [
    { title: 'Read', detail: 'two readers in parallel, each mapping its side of the system onto the organizing principle' },
    { title: 'Synthesize', detail: 'one adversarial synthesis: check each departure, group by root cause, plan the moves' },
  ],
}

const ROOT = '/Users/pooks/Dev/lean4-effect4'
const OUT = (args && args.outDir) || 'docs/research/2026-10-20-coherence-audit'
const ABS = `${ROOT}/${OUT}`

const READERS = [
  {
    key: 'lean-core',
    title: 'the Lean core that the session stands on',
    scope: 'src/Effect4/Tool, src/Effect4/Api.lean and src/Effect4/Api/, src/Effect4/Run, src/Effect4/Program, src/Effect4/Data, src/Effect4/Store and src/Effect4/Schema, with tools/Drivers/Session.lean. Read the matching Laws folders only to see which constructions a definition is proved against.',
    focus: 'The session face (the protocol and its method table, serve, replay and journals, the exchange, documents and their editing actions, the codec profile at the wire, refusals) and the program and data plane under it (typing and checking, admission, authoring, carriers, shapes, codecs, digests, schema documents).',
  },
  {
    key: 'compiler-estate',
    title: 'the compiler and the OCaml estate, as one system',
    scope: 'src/OCaml5 (the LCNF route: translation, builtin rows, natives, type rows, externs, export classes, identity, the closure), the generators (scripts/generate.py, scripts/lib), and ocaml/ in the large: the engine, the store, the kit, eff, the clock, the lcnf runtime and the hand files of ocaml/gen.',
    focus: 'Read it as one compiler with one runtime: what Lean owns, what the tables and the generator emit, what hand OCaml holds (host code, or a carrier that LCNF code replaces), and where the boundary between them sits. Judge the engineering pedigree too: Jane Street, compiler-libs, and tables as data in the style of MLIR ODS and Cranelift ISLE.',
  },
]

log('Out of this run by plan: the machine (src/Effect4/Machine and its laws), the program proofs (Laws/Program), ts/, harness/ and rocq/.')

const READER_SCHEMA = {
  type: 'object',
  properties: {
    area: { type: 'string' },
    head: { type: 'string', description: 'the output of git rev-parse --short HEAD when you started' },
    patternMap: { type: 'string', description: 'a markdown table: each pattern of orientation.md §3 and §4, where this area honours it, and where it departs' },
    strengths: { type: 'array', items: { type: 'string' }, description: 'where the area already exhibits the patterns cleanly, which a refactor must keep' },
    departures: {
      type: 'array',
      items: {
        type: 'object',
        properties: {
          id: { type: 'string', description: '<area>-<n>' },
          pattern: { type: 'string', description: 'the pattern of the organizing principle it departs from' },
          title: { type: 'string' },
          misuse: { type: 'string', description: 'the modeling error: the case or the pattern we misused, so this could grow' },
          evidence: { type: 'string', description: 'two to five representative declarations or modules, by name and path, with a count from a command where size matters' },
          move: { type: 'string', description: 'the conceptual move that restores coherence: what collapses into what, and which construction or arrow kind it becomes an instance of' },
          collapses: { type: 'string', description: 'what goes, in kind and rough size' },
          keeps: { type: 'string', description: 'what must stay because it serves a distinct observation, boundary or measured need' },
          overEngineeringRisk: { type: 'string', description: 'how the move could add more than it removes, and how to avoid that' },
          rulingConflict: { type: 'string', description: 'a decisions row it contradicts, or "none"' },
          size: { type: 'string', enum: ['S', 'M', 'L'] },
        },
        required: ['id', 'pattern', 'title', 'misuse', 'evidence', 'move', 'collapses', 'keeps', 'overEngineeringRisk', 'rulingConflict', 'size'],
      },
    },
    notCovered: { type: 'string' },
  },
  required: ['area', 'head', 'patternMap', 'strengths', 'departures', 'notCovered'],
}

const RULES = `Rules:
- Read-only on every tracked file. Write only the file your task names, and any probe under ${ABS}/probes/<your area>/.
- Never run make, lake build Test, make gen-semantics or tsc. Never run a git command that changes state.
- A Lean probe runs only as: cd ${ROOT} && python3 /private/tmp/seams-lean-one.py lake env lean <file>, with no thread count and no stderr sent to /dev/null; if that script is missing, run no Lean.
- An OCaml probe builds only into a separate folder: cd ${ROOT}/ocaml && opam exec --switch=effect4 -- dune build --build-dir ${ABS}/probes/_build-<your area>.
- The shell is zsh: it does not split an unquoted variable into words.
- Start no subagent.
- Write in short, plain sentences. Cite a declaration by its name and its path, never by a line number.`

function readerPrompt(r) {
  return `You are one of two readers in a coherence audit of the Effect4 repository at ${ROOT}, asked for by the owner on 2026-10-19. You read ${r.title}.

The owner's principle: bloat is a modeling error. If something exists that the desired behaviour does not need, we modeled the system wrongly, or misused a case or a pattern. Elegance is minimality with respect to the desired behaviour, so over-engineering is as wrong as bloat. The owner wants this audit done conceptually, at the level of patterns and constructions, not as a list of specific line-level defects. Codex's quality review already lists specifics; cite one only as an instance of a departure you name.

Orient first. Read these, in order, before you open any code:
1. ${ABS}/orientation.md, in full: the project's philosophy, pedagogy, inspirations, the failure modes on record, and the questions a reviewer asks. It is your frame.
2. ${ROOT}/docs/research/history/coherence-principle.md: the organizing principle as first written, with its arrow kinds and literature.
3. ${ROOT}/docs/core/system-map.md, sections 4 to 6 and 10.
4. ${ROOT}/docs/core/semantics.md, section 1, and the concepts your area serves.
5. ${ROOT}/ocaml/STANDARDS.md, if your area holds OCaml.
6. ${ABS}/plan.md and ${ROOT}/docs/research/2026-10-19-quality-review/coherence.md: why this audit runs, and the method applied once to the store.
7. ${ROOT}/docs/research/2026-10-19-quality-review/receipt-r1-store.md, if you read OCaml: seat R1's repair of the store, and its open items O1 to O4. O1 and O2 are one rule with no owner: where a scan counts as reaching the published end.

Your scope: ${r.scope}
Your focus: ${r.focus}

Read your scope at the level of its modules and their roles: what each module is for, which sort it carries, which arrow kind each main function is, and which construction it belongs to. Measure with commands (git ls-files, wc -l, grep) where size matters, but do not audit line by line.

Then produce:
1. A pattern map. For each pattern of orientation.md sections 3 and 4 — one free object per sort, the five arrow kinds with their obligations, the five constructions, tables as data with generation as a fixed point, one located refusal per judgment, one owner per fact, the host boundary, deep modules — say where your area honours it, with one or two representative declarations, and where it departs.
2. Strengths: where the area already exhibits the patterns cleanly. A refactor must keep these; the owner wants the coherence of patterns, ideas and inspirations maintained.
3. Departures, at most ten, each at the level of a pattern. For each: the pattern, the modeling error that let it grow, two to five representative declarations as evidence, the conceptual move (what collapses into what, and which construction or arrow kind it becomes an instance of), what goes, what must stay because it serves a distinct observation, boundary or measured need, and how the move could over-engineer.

Hold to the orientation's lessons:
- Lack of a consumer is not a metric; coherence of the algebra is. Code built toward a known consumer is not bloat for lacking one.
- Two constructs are one fact only when they serve one observation. Name the observation.
- A move that adds a framework, a generic judgment record (decisions row 414 (2)) or new program syntax is not a move. A move must remove more than it adds.
- Respect the rulings in docs/core/decisions.md; a move that contradicts one names the row.

Write ${ABS}/${r.key}.md: the pattern map, the strengths, the departures, and what you did not cover. Then return the structured result.

${RULES}`
}

function synthPrompt(readings) {
  return `You are the synthesis of a three-agent coherence audit of the Effect4 repository at ${ROOT}, asked for by the owner on 2026-10-19. Two readers mapped the system onto its organizing principle: the Lean core, and the compiler with the OCaml estate. Their results are below, and their notes are in ${ABS} (lean-core.md, compiler-estate.md).

Orient first: read ${ABS}/orientation.md in full, then ${ABS}/plan.md, ${ROOT}/docs/research/history/coherence-principle.md, ${ROOT}/docs/core/system-map.md sections 4 to 6 and 10, and ${ROOT}/docs/research/2026-10-19-quality-review/coherence.md. Read ${ROOT}/docs/research/2026-10-19-quality-review/codex-review/README.md, wave3.md and receipt-r1-store.md beside it for the specific defects, the open repair wave and the store seat's open items (O1 to O4), and docs/core/decisions.md rows 391 and 414 to 417.

Step 1, adversarial. For each departure, try to refute it before you keep it:
- Does it argue from consumer counts, where the orientation says coherence is the measure?
- Does it call two constructs one fact when they serve different observations, boundaries or measured needs?
- Is its move over-engineered: a framework, a generic record, new syntax, or more added than removed?
- Does it contradict a ruling it does not name?
- Do its named declarations exist and do what it says? Open them and check.
Mark each departure kept, amended or rejected, with the reason.

Step 2, synthesis. Write ${ABS}/README.md, in short plain sentences, citing declarations by name and path:
1. The one thing to know.
2. The picture: how the core sits against the organizing principle today, as one table across both readings.
3. The root causes: the kept departures grouped by the pattern misused. For each cause, one design rule in the project's vocabulary that removes the whole class (a rule for how we build, not a new gate), and the departures it covers.
4. The refactor, as an ordered set of conceptual moves. For each move: what collapses into what, which construction or arrow kind it becomes an instance of, what it deletes in kind and rough size, and which observations stay. Order the moves so each makes the next smaller. Fold in the open repair wave: seat R1's open items O1 to O4 (receipt-r1-store.md), R2, R3, E6, the log question of coherence.md section 5 with the receipt's commit costs, and the public JSON spelling of decisions row 417 (4). Say how each move subsumes, reshapes or leaves each of them.
5. What to preserve: the strengths both readers found, which no move may break.
6. The rejected and amended departures, with reasons.
7. The decisions only the owner can make — meaning, supported domain or representation — each with a recommendation.

Before you finish, check your own plan against the orientation's section 10 questions and for over-engineering: every move must remove more than it adds, or name the observation that justifies what it adds.

Write only ${ABS}/README.md. Return its first two sections and the list of moves as your final text.

${RULES}

The readers' results:
${JSON.stringify(readings, null, 1)}`
}

phase('Read')
const readings = (await parallel(READERS.map(r => () =>
  agent(readerPrompt(r), { label: `read:${r.key}`, phase: 'Read', schema: READER_SCHEMA }),
))).filter(Boolean)

const missing = READERS.filter(r => !readings.some(x => x.area === r.key || (x.area || '').includes(r.key))).map(r => r.key)
if (missing.length) log(`No reading returned for: ${missing.join(', ')}. The synthesis reports it as not covered.`)
for (const x of readings) log(`${x.area}: ${(x.departures || []).length} departures, ${(x.strengths || []).length} strengths`)

phase('Synthesize')
const plan = await agent(synthPrompt(readings), { label: 'synthesize', phase: 'Synthesize' })

return {
  outDir: OUT,
  readings: readings.map(x => ({ area: x.area, head: x.head, departures: (x.departures || []).length, strengths: (x.strengths || []).length })),
  missing,
  plan,
}
