# MCP stdio receipt

The one thing to know first: protocol controls establish finite evidence for stdio MCP 2025-06-18.
They do not establish every protocol trace or later-version conformance.

Base: `cd2cea0de813ed2e22ecf53f1c0eb6c20468b131`.
Code commit: `bb95dbacbdee5ea269e8585f8dbd655afb18e786`.
Final integrated code: `4b2193074201161b1b378f164afe6f062bedf375`.

Changed files: `kit_mcp.ml`, `kit_mcp.mli`, its dune dependency, `test_mcp.ml`, and `scripts/check-mcp-protocol.py`.
The original native regression run reports fifteen failures against the previous transport.
The integral-notation controls report six failures before the exact numeric predicate lands.
The subprocess trace catches the previous internal-error classification for malformed tool numbers.
The final native suite passes 52 controls, with zero failures.
The official-schema trace passes 61 checks over 15 messages and 13 replies.
It discovers 19 tools and retains request ID `18446744073709551616` exactly.

The focused audit is `python3 /private/tmp/seams-lean-one.py lake build Drivers.AbstractionsMcpAudit`.
It passes with 748 jobs and 73 declarations within `[propext, Quot.sound]`.
No declaration depends on a planned goal, and no planned goal appears in that audit.
The combined audit repeats the same 73-declaration result.

Run the native controls from `ocaml/engine/test/kit/`:

```sh
opam exec --switch=effect4 -- dune exec --root ../../.. engine/test/kit/test_mcp.exe
```

Run the schema probe from the worktree root:

```sh
uv run --with jsonschema==4.25.1 python scripts/check-mcp-protocol.py --binary ocaml/_build/default/engine/kit/bin/eff.exe --schema /Users/pooks/Dev/refs/ocaml-tooling/mcp-spec/schema/2025-06-18/schema.json
```

The final integrated gate is `PATH=/private/tmp/abstractions-lean-bin:$PATH make check-ocaml LAKE=lake`.
It exits zero and records `51a359f1f372`, with `gen-check: PASS`.
`git:6c09715f0:docs/research/2026-10-18-codex-abstractions/validation/check-ocaml.log` contains that final output.
The earlier isolated MCP gate also passes; its log is `git:6c09715f0:docs/research/2026-10-18-codex-abstractions/mcp/check-ocaml.log`.
`controls.log` and `schema.json` contain the final integrated protocol observations.

No Lean semantic law changes in this slice.
MCP framing and native JSON parsing remain host-tested boundaries.
The official schema disallows null error IDs; base JSON-RPC requires null without a usable request ID.
Native malformed-envelope controls check those errors separately from the identified schema trace.
