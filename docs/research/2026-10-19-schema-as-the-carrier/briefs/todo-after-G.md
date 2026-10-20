# Brief: the to-do project after moves J and G

Status: brief, 2026-10-20, from the coordinator to one Opus seat. The to-do project is the
owner's dogfood of the library from outside it (`docs/research/2026-10-19-todo-as-a-user/`,
`findings.md` and `receipt.md`). Move G changed the codec's public shape, so the project's
typed comparison no longer compiles. Repair it, and run the comparison again.

## 1. Where you work

- The project `/Users/pooks/Dev/effect4-todo`, branch `main`, head `689b0a9`, its own Git
  repository, never pushed. It requires the library by path (`lakefile.toml`,
  `require effect4 from "../lean4-effect4"`), at the library's HEAD on `refactor/phase1-phase3`.
- The library `/Users/pooks/Dev/lean4-effect4` is read-only for you. Read
  `docs/research/2026-10-19-schema-as-the-carrier/receipt-G.md` and `briefs/G.md` there, and
  `AGENTS.md` in full.
- Your scratch folder is
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/2cfa2789-af6f-4183-90be-cdd7f2934e64/scratchpad/todo`.
- Every Lean command runs from inside the project through the runner, one at a time, never with
  a thread count: `python3 /private/tmp/seams-lean-one.py lake build`,
  `python3 /private/tmp/seams-lean-one.py lake exe todo …`. Never a bare `lake build` in the
  library, never `lake build Test`, `make build`, `make check-full` or `make gen-semantics`
  anywhere. Never write `2>/dev/null` on a Lean command. Never `tsc`, only tsgo 7. Never
  `git add -A`, never `git push`.
- OCaml runs only as `opam exec --switch=effect4 -- dune …`. Never install into or pin the
  switch.

## 2. The change

1. `Todo/Host.lean`, `typedJson`: `Ty.encode` now takes the module's key names first,
   `Ty.encode names t v` (`receipt-G.md`, the one thing to know). Take the names from the built
   program's signature as the faces probe does:
   `(nativeSignature b.table).keyNames` (`docs/research/2026-10-19-schema-as-the-carrier/probe/Faces.lean`,
   `typedJson`). Read `Effect4.Program.Native` for `nativeSignature` and the `Api.Built` fields.
2. Nothing else in the project should need a change. If `lake build` finds another breakage
   from the library's HEAD, repair it the same way and record it.
3. Run the README's steps again, in its order: `lake build`, `lake exe todo`, the typed
   comparison `lake exe todo --typed | diff - <(bun ts/run.ts --typed) && echo SAME`, and the
   plain comparison with `ts/lean-lines.ts`. Record each result. The native side
   (`ocaml/todo_gen.ml`) is lowered from the project's own Lean and does not reach the codec.
   So rerun its build and its comparison only if `lake build` rebuilt `Todo.Host`.
4. If a typed line differs between the faces, do not patch the output. Record the two lines
   and the case in the receipt; the coordinator reads it against the library's probe.

## 3. The commit and the receipt

- Commit in the project by explicit paths, when every step passes. The message's first line:
  `The typed comparison under the module's key names (after move G)`. The last line:
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- Append a short section to the library's `docs/research/2026-10-19-todo-as-a-user/receipt.md`,
  the one library file you may edit. It records the project's new commit, the command results,
  and the one line a user must now write (the key names argument). Keep its language under `python3 -I scripts/check-language.py
  --show <file>` clean. Do not commit in the library; the coordinator commits that file.
- Reply with the project's head commit, each command's one-line result, and anything that did
  not finish. Keep the reply under 30 lines.
