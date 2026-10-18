# `eff mcp` tool list: 353,485 → 40,069 bytes of schema

2026-10-18. Measured and built on `8a08e0415` (`refactor/phase1-phase3`), rebased onto `7c65506b2`
(Laws and research only), then merged with `3997e571c`. That merge brings in Codex's MCP repair
(`bb95dbacb`): `kit_mcp` rewritten on Yojson.Raw with the 2025-06-18 lifecycle, `test_mcp` at 52
controls, and `scripts/check-mcp-protocol.py`. Branch `claude/mcp-schema-size`. Not pushed.

## The measure

From `ocaml/`, after `opam exec --switch=effect4 -- dune build`. Since `bb95dbacb` the server
answers `tools/list` only after the MCP handshake. At `8a08e0415` the `tools/list` line alone
was enough.

```bash
printf '%s\n' '{"jsonrpc":"2.0","id":0,"method":"initialize","params":{"protocolVersion":"2025-06-18","capabilities":{},"clientInfo":{"name":"measure","version":"1"}}}' '{"jsonrpc":"2.0","method":"notifications/initialized"}' '{"jsonrpc":"2.0","id":1,"method":"tools/list"}' | _build/default/engine/kit/bin/eff.exe mcp | tail -1 > tools.json
python3 -c 'import json; print(sum(len(json.dumps(t["inputSchema"])) for t in json.load(open("tools.json"))["result"]["tools"]))'
```

| | tools | sum of `len(json.dumps(inputSchema))` | reply line |
| --- | --- | --- | --- |
| before (`8a08e0415`) | 19 | 353,485 | 326,793 bytes |
| after (merged with `3997e571c`) | 20 (19 methods + `describe`) | 40,069 | 41,251 bytes |

Per tool, before → after: `dry` 102,714 → 398; `restore` 56,442 → 12,143; `play` 46,520 → 12,172;
`open` 34,862 → 2,567; `edit` 34,658 → 4,053; `suggest` 31,960 → 1,334; `fill` 31,445 → 837;
`preview` 12,306 → 3,804; `describe` 183; the other eleven are unchanged (83–760 each).

`describe` answers cost only when an agent asks: `Eff` 22,867 (also `Stmt`, `ActionTerm`,
`LayerTerm`, which reach it), `CauseTerm` 7,199, `Term` 6,481, `Ty` 3,867, `Val` 2,387.

## Why it was large (measured on the before reply)

1. **The program's grammar, copied into six tools.** The shape document's table (`Eff` 12,961,
   `Ty` 5,229, `ActionTerm` 4,276, `LayerTerm` 3,400, `Term` 2,719, `Val` 2,520, …) is 30,720 bytes
   in each of `open`, `edit`, `fill`, `suggest`, `restore`, `dry`: about 184 KB, half the total.
   MCP gives each tool a standalone schema, so `$defs` cannot be shared across tools.
2. **Repeated inlining inside one tool.** A non-recursive shape was spelled at every place it
   appears: in `dry`, the reply's `Exit`/`Cause` (4.8 KB) six times, the run decision (7.5 KB)
   three times, the wire command (19.7 KB) twice, and a one-field id object 66 times.
3. **`dry` holds an `Action`**, so it repeated every action tool's arguments.
4. **The nullary cases of a mixed sum** were one full object each (`Eff`'s `perform` op has
   about 40). About 27 KB in all.

The list-family rule was not a cause: the four list families are about 50 bytes each.

## The options, measured

Prototype transforms of the before reply, measured the same way (scripts kept local):

| option | total |
| --- | --- |
| nullary cases in one branch | 326,538 |
| shared shapes by `$ref` (two or more places) | 229,578 |
| both, and `"type":"object"` once per sum: every exact compaction | 196,480 |
| the grammar left to a `describe` tool | 158,042 |
| `describe` and the exact compactions | 60,661 |
| and `dry`'s action by reference to the action tools (landed, Lean) | 40,069 |

- **A compact recursive Eff.** The grammar has 29 `Eff` cases (40 `perform` ops), 29 `Ty` cases and
  17 `ActionTerm` cases. Compacted, it is still about 23 KB, and six copies make about 140 KB.
  Without moving the grammar out of the tools, no exact encoding gets below that.
- **A program as an opaque string.** Rejected. The agent would have to escape a program inside
  JSON text, and the server would need a second reader. The program stays a JSON object
  argument. Its schema is named, and the agent fetches it.
- **MCP's own mechanisms** (`~/Dev/refs/ocaml-tooling/mcp-spec`, 2026-07-28). `inputSchema` is a
  standalone 2020-12 schema. `tools/list` pagination and the new `ttlMs`/`cacheScope` caching do
  not change what a client loads. A resource could hold the grammar as well as a tool can, but
  every client gives its model tools. So the grammar comes from a tool.

## What landed

`src/Effect4/Tool/Methods.lean`:

- a mixed sum is `{"type":"object","oneOf":[…]}`, and its nullary cases share one branch whose
  `_tag` is an `enum`;
- a structure or sum written in two or more places is written once under `$defs`, by its own name
  (`definitionsOf`). It counts once inside its holder, so a shape written in one place stays in that place;
- a table definition written as an object (`onDemand`: the grammar) is a `$defs` entry that points
  to `describe`, and `describe` answers it as a standalone schema document (`Methods.describe`,
  exported as `Tool.Native.describe`);
- a sum whose cases are tools (`dry`'s `Action`) is its `_tag` enum, with a pointer to the action
  tools' schemas.

`ocaml/engine/kit/kit_mcp.ml` (Codex's rewrite) lists `describe` after the methods and answers
it from Lean's table (M5). The answer is `structuredContent` plus identical JSON text, as for
every tool. Any other arguments get -32602. `test_mcp.ml` C2 and C5 check this (57 controls).
`scripts/check-mcp-protocol.py` now also calls `describe`: it checks one valid call against the
official `CallToolResult` schema, and one unknown name against -32602.

**Exactness, as claimed.** A method's schema is exact except at the `describe` pointers and at
`dry`'s action. Put each `describe` answer in place of its pointer, and the action tools' schemas
in place of `dry`'s action: the result agrees with the old exact schema. This is a finite probe,
not a proof (`validate.py`, Draft 2020-12, `jsonschema` 4.26.0). The output was the same before and
after the merge:

```text
V1 20 tool schemas, 8 describe answers, 19 resolved: valid 2020-12
V2 47 calls (open 3+/0-, doc 6+/0-, edit 10+/0-, history 3+/0-, run 2+/2-, start 1+/0-, fill 1+/0-, suggest 1+/0-, preview 1+/0-, restore 1+/0-, dry 16+/0-): 47 agree across old, new and resolved
V3 1316 mutations: resolved agrees with old on all; new accepts all old accepts; 917 accepted by the new schema only (inside a describe pointer or dry's action)
V4 475 instances drawn from the old schemas: valid against new and resolved
PASS
```

The calls are every fixture request (`ocaml/engine/test/kit/tool-requests.jsonl`,
`tool-numbers.jsonl`, `Test/fixtures/session/requests.jsonl`), including the two out-of-range ids
that every schema refuses, plus a live session's `start`, `run`, `fill`, `suggest`, `preview` and
`restore` (the record the server printed), and `dry` around each action. The server's exact
reader is unchanged, so the server still refuses anything a pointer lets through.

## Lowering trap met (follow-up)

The OCaml route binds a function's one empty array (`Lcnf_array.with_capacity 0`) once. OCaml's
value restriction then fixes it to the first item type it meets. A Lean function that builds
lists of two item types through `filterMap`/`flatMap` therefore fails to compile in OCaml.
`Methods.groups` is kept apart from `entries`, and every list `definitionsOf` builds holds pairs,
so the problem is not hit here. The route itself is not fixed.

## Commands and results

- `python3 /private/tmp/seams-lean-one.py lake build Effect4.Tool.Native Test.Program.ToolMethodsControls`:
  733 jobs, success (the controls' guards included).
- `python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only lcnf`: PASS;
  `api_gen.ml`, `api_gen.mli` and `closure-api_gen.tsv` regenerated.
- `#axiom_audit Effect4.Tool.Methods Effect4.Tool.Native Test.Program.ToolMethodsControls`:
  234 declarations within `[propext, Quot.sound]`, 0 planned goals, before and after the merge.
- `cd ocaml && opam exec --switch=effect4 -- dune test --force engine/test/kit`: all pass; test_mcp
  57 of 57 at the merged tree.
- `uv run --with jsonschema==4.25.1 python scripts/check-mcp-protocol.py --binary ocaml/_build/default/engine/kit/bin/eff.exe --schema ~/Dev/refs/ocaml-tooling/mcp-spec/schema/2025-06-18/schema.json`:
  PASS, 69 schema checks, 20 tools.
- `python3 /private/tmp/seams-lean-one.py make check-ocaml`: exit 0. Its `gen-lcnf` step regenerated
  the same three files. The `ocaml` lane ran (`PASS ocaml: recorded b1a459382d51`: dune tests,
  interface and sealing checks, gen-check C1–C4). `native` and `compiler` came from shared results,
  because their inputs did not change. The `Error:` lines in the log are the sealing check's
  planted hostile clients, each refused as expected. At the merged tree the gate ran again: exit 0,
  `PASS ocaml: recorded fd5399a5c83b`, with `native` and `compiler` from shared results.
- After the gate, two pairs of redundant parentheses came out of `Methods.lean`. Then: narrow build
  again, and `lake exe lcnfgen --one 1` gives an `api_gen.ml` and `closure-api_gen.tsv`
  byte-identical to the committed ones.
- `python3 docs/research/2026-10-18-mcp-schema-size/validate.py BEFORE.json ocaml/_build/default/engine/kit/bin/eff.exe`:
  PASS, as above. BEFORE.json is the `tools/list` reply of `eff mcp` built at `8a08e0415`.

Not run: `lake build Test`, the batteries sweep and `make gen-semantics` (`generated/semantics.md`
was not regenerated).
