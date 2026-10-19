# Quality review at 3471cbe35

The public kit can return a wrong integer result after accepting a host reply that the engine refuses.

This report reviews `3471cbe35e3f91949170e2147dbe46f75cb795fd` in an isolated worktree.
The worktree is `/Users/pooks/.codex/worktrees/quality-review-3471/lean4-effect4`.
All written evidence lives in this report's `probes/` directory.
No tracked source changes, commits, pushes or merges form part of this review.

## A1 checkpoint

Evidence status: finite host probes and Lean evaluations. Scope: the pinned generated code and its public kit.

`probes/a1.ml` sends a wire-decoded program and wire-decoded negative integer through `Kit.run`.
The reply is `Store.Val.negInt 4611686018427387903`, which represents `−2^62`.
The program computes `−1 − reply`.
The kit returns `NegInt 0`, which represents `−1`.
Lean returns `some (Val.nat 4611686018427387903)`.
The default cross-check records disagreement but retains the wrong finished result.
Both a native host and an in-memory tape reach this behaviour.

The path runs `Program.intNeg` through raw `Nat.add` before `Program.intAdd` takes a subtraction branch.
That branch never calls `Profile.grow`.
Ordinary addition at the profile limit and at `max_int` refuses in the controls.
This finding therefore does not claim that ordinary program addition bypasses the checked arithmetic.

The JSON parser represents the large reply magnitude as a numeral, which carrier reading refuses.
The node reader accepts full float payloads but retains bytes, without constructing the lowered float carrier.
`Eff_val.decode_exact` refuses float frames.
The tested JSON and stored-node paths therefore do not establish a silent high-bit float entry.

The native float carrier cannot distinguish every binary64 pattern.
Converting `−0.5` and `0.5` through `Int64.to_int` produces identical carriers and identical encoded digests.
That conversion is a probe of the representation gap, not a production conversion discovered in the tree.
The exact 64-bit carrier belongs in E6 alongside exact naturals.

`probes/a1_size.py` measures 128 builtin rows: 45 domain rows, six approximate rows, two unsound rows and 75 exact rows.
The brief's single-line measurement misses two domain rows whose declarations span lines.
The catalogue has 39 directly named Nat, Int, UInt64 and USize rows, including the two standalone equality instances.
This excludes other rows with numeric crossings, such as array indices, string positions and profile arithmetic.

`probes/A1Fields.lean` measures 19 constructor fields containing Nat after reducing outer aliases, across the program-type recipe.
That count includes `List Nat` as one field and excludes machine fields outside that recipe.
The source census finds 53 hand consumer candidate files.
These are candidates, not a promised edit count.
`probes/a1-size.json` lists their paths and the generated numeric token counts.
`Native.ctorValue` and `Translate.letValueExpr` also construct numeric expressions outside the builtin table.

The baseline `bench_todo` allocates 23,824 words per host call for the lowered reference repository.
The typed lowered model allocates 23,378 words per call.
`probes/a1-bench-before.log` retains every stage.
No full Zarith switch exists in the pinned tree, and this review changes no tracked source.
There is no after measurement and no measured overhead claim.

Decision 12: retain exact naturals and integers everywhere as the target direction.
Use an exact word carrier for UInt64 too.
Until E6 lands, apply the engine's input checks to the call-tree route before evaluation.
The current refusal crossings do not justify treating all generated arithmetic as bounded safely.

## Review in progress

A1 precedes every remaining angle. Parts A2–A10, B and C follow this checkpoint.
