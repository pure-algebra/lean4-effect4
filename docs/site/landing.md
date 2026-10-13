# Effect4

Effect4 makes Effect-style computations explicit, inspectable program data, and Lean defines their structure, their execution rules and their construction checks (`README.md`). The product is Effect codegen: a program syntax (`Eff`) that prints as Effect TypeScript and reads back. A compiler takes it to the frame machine of Effect rc.112, and a reference fiber machine runs those frames.

The site serves two readers: a person who writes or reviews Effect programs, and an agent that reads the same pages as JSON. Effect TypeScript rc.112 is the first target and the behavioural reference, never the owner of the semantics.

Each property of the runtime carries its formal evidence (`docs/core/semantics.md`). That evidence includes theorems that are {proved}, theorems proved {modulo} open goals, and planned {goal} markers whose proofs remain in progress.

## Guides {#guides}

- [How to read this site](guides/reading/): explains page structure, status marks, margin outlines, and JSON exports.
- [The fiber machine on one page](guides/machine/): summarizes fibers, frames, decision tapes, execution frontiers, and resource scopes.
- [What the evidence means](guides/evidence/): defines theorem statuses, planned goals, axiom boundaries, and observation scopes.

## Formal semantics and requirements {#semantics}

- [Semantics evidence](semantics/): lists claims across the ten semantic concepts with Lean statements and dependency status.
- [System requirements](semantics/plan/): the requirements R1 to R14, from program syntax to deterministic replay, each with the goals it rests on.
- [Document specimen](specimen/): displays every kind of block and every status mark, as the pages draw them.
- [Contents](contents/): indexes every page across the documentation site.

## Machine contracts and exports {#contracts}

Every documentation page exports structured JSON using the `effect4-document/1` schema:
- Read [the first page of the semantics](semantics/document.json) for one page's document: its title, its parts and its blocks.
- Read [site.json](site.json) for every page with its title and the keys of its parts.
- Read [report.json](semantics/report.json) for the semantics report: each claim with its status, and the plan of goals.
