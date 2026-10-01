# C producer root amendment, authorized by the owner

The completed LCNF run emits `and fork_record = Placeholder_fork_record` in the engine. `dune build` fails at the newly authorized spawn transcription because its literal needs the actual record. The generator emits full data definitions from constructed/destructed types or explicit `--types`; the engine replaces both spawn bodies, so their constructor no longer brings this type into that set. Its existing explicit `Origin` entry is the same mechanism.

The owner replied “Yes—include the ForkRecord type root.” The applied amendment adds exactly `Effect4.Machine.ForkRecord` to the engine artifact's `types` list in `ocaml/gen/roots.json`. Keep Origin and every other recipe field unchanged. The concrete one-line insertion is `roots-amendment.patch`. Regenerate through `make gen-lcnf`, then complete the remaining prescribed checks. No generator implementation change and no hand-edited generated output.

Measured failure: `dune.log`, command/result in `dune.command.json` / `dune.result.json`.
