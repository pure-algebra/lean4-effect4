# Effect4

Effect4 is Effect's runtime written in Lean as a model with defined semantics. A program is data: a typed term that Lean checks, runs on a reference machine, lowers to OCaml and prints as TypeScript.

Each claim about that runtime carries its evidence. The evidence is a theorem that is {proved}, a theorem proved {modulo} named goals, or a planned {goal} whose proof is to come.

## Start here {#start}

- [Semantics evidence](semantics/): every claim by concept, its status and its Lean statement, and the plan of goals that the open requirements rest on.
- [Document specimen](specimen/): every kind of block and status mark, as the pages draw them.
- [Contents](contents/): every page of the site.

## For a framework {#contract}

Every page is also its document as JSON, in the format `effect4-document/1`: see [the first page of the semantics](semantics/document.json). The pages and their parts are in [site.json](site.json). The report behind the semantics pages is [report.json](semantics/report.json).
