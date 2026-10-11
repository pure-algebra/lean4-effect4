# Acceptance checks for the foundation slices

Status: required controls and commands; results belong in each implementation receipt.
Base: `faad3e9e`.
The compiler pin is `leanprover/lean4:v4.33.1`.
No command below is reported as run by this document.

## Controls

| ID | Slice | Required observation |
| --- | --- | --- |
| A01 | P0/P1/P2 | Lawful `List<A> -> Option<A>` admits `some 1` at the natural instance; `none` remains admitted. |
| A02 | P1 | Identical empty runtime lists retain distinct natural and string request instances. |
| A03 | P1 | A different fitting environment cannot impersonate the checker's retained environment. |
| A04 | P1 | Defining and referenced layer occurrences select matching static instances. |
| A05 | P1/P2 | Repeated loop iterations and two fibers may share an origin while retaining distinct dynamic keys. |
| A06 | P1 | Appending rows transports a certificate through an extension law; changed source, services, or table cannot reuse unchecked metadata. |
| A07 | P2a/P2b | Missing, conflicting, or wrong-origin metadata refuses through the declared boundary; accepted source coverage proves these cases unreachable. |
| A08 | P2a/P2b | Interruption during registration yields no final live-token claim. |
| A09 | P2/P4 | Duplicate, stale, retired, wrong-session, wrong-call, and wrong-token replies refuse independently. |
| A10 | P2a/P2b | Current typed failures use instance columns; reserved defects remain refused. |
| A11 | P2a/P2b | `.ofRefGet` does not inherit a heap-declaration proof from current-value membership. |
| A12 | P3 | Empty, nonempty, absent-row, malformed-answer, and preloaded-answer cases retain machine agreement. |
| A13 | P3 | An allocating external row relates the resulting allocation state on both machines. |
| A14 | P3 | `run_eq_ref`, `replay_externals`, and typed-result consumers retain their original empty-table scopes. |
| A15 | P0/P4 | Guard consumption with insufficient follow-up fuel does not imply a sufficient raw replay step. |
| A16 | P4 | A command after that application is represented at its actual journal prefix. |
| A17 | P4 | A published exit with pending command work distinguishes machine inspection from a raw fuel-frontier result. |
| A18 | P4 | Zero command fuel and zero compile fuel remain distinct controls. |
| A19 | P4 | Receipt does not run the machine; selected application order remains explicit. |
| A20 | P4 | Cancellation retains an accepted but unapplied completion in retirement data. |
| A21 | P4/P5 | Every command constructor and every phase has a theorem case, including refusals and frontiers. |
| A22 | P5 | A program admission certificate beside an arbitrary machine does not establish session reachability. |
| A23 | P6a/P6b | Inventory records every translation refusal; P6b additionally requires an executable artifact containing the selected keyed-session entry. |
| A24 | P6 | Changed tags, field indices, layouts, externs, or emitted bytes invalidate the corresponding artifact evidence. |
| A25 | P6a inventory; target continuation proof | Reply indexes distinguish unbound, waiting, and received; they retain binding order. |
| A26 | P6b | The selected emitted arithmetic rule matches its reference under explicit input and result bounds. |
| A31 | Target continuation | Intermediate values, store updates, and allocation exceedances produce the declared route refusal once enforcement is implemented. |
| A32 | P2b/P5 | Prepared `.ofExit` state and payload agree with the recorded completion; both success and failure yield `CompletionStrong`. |
| A33 | P3/P5 | Each decision retains the stronger machine relation and equal receipts, not only equal final observations. |
| A34 | P5 | Prefix typing uses an actual world witness and continues after committed insufficient receipts. |
| A27 | Target continuation | Allocation bounds, dense versus sparse keys, and old snapshots retain their declared meanings. |
| A28 | Target continuation | Cached paths use the same stable root and resolver; stale ownership fails the declared invariant. |
| A29 | P7 contract; target continuation proof | Target initialization binds the same program, table, profile, inputs, budgets, and journal as the reference. |
| A30 | P7 contract; target continuation proof | A wrong phase or dropped retired reply falsifies target command correspondence. |

A15–A17 originate as source-derived counterexample candidates from the DI-57 review.
P0 must check them before treating their proposed fuel values as evidence.
An exact natural-number budget is not frozen until that probe checks.
The required distinction remains a contract question even if a candidate needs correction.

The initial P6b equation does not satisfy A31.
P7 retains A27–A31 in the target continuation contract until their implementations and proofs land.

## Narrow commands

Run each command only after its files are present and its prerequisites are built.
Replace the proposed test names below only in the coordinator's recorded brief.
Run one Lake process per worktree.

| Slice | Required narrow checks |
| --- | --- |
| P0b | `LEAN_NUM_THREADS=3 lake build Test.Program.HostCallFoundation`; `LEAN_NUM_THREADS=3 lake build Test.Api.SessionCommandFoundation` |
| P1 | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.CheckedTyping Effect4.Laws.Program.Typed.Denotation Effect4.Laws.Program.Typed.LayerArm Test.Program.HostCallFoundation` |
| P2a/P2b | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Api.HostSession Effect4.Laws.Program.Typed.Commands.Clauses.Async Effect4.Laws.Program.Handles.Hooks Test.Program.HostCallFoundation` |
| P3 | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.RuntimeR Effect4.Laws.Program.Typed.Results Test.Program.TableReferenceFoundation` |
| P4 | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Api.SessionCommand Effect4.Laws.Run Test.Api.SessionCommandFoundation` |
| P5 | `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Api.SessionTyped Test.Api.SessionTypedFoundation` |
| P6a/P6b | `LEAN_NUM_THREADS=3 lake build OCaml5.Lcnf.Translate Conform.Layout.Laws`; these check helpers only; freeze the actual closure, emitter command, and target proof module after P6a |
| P7 | Run the union of changed modules and direct consumers from the integrated diff; record the resolved command before running it |

`SessionCommand`, `SessionTyped`, and the four foundation batteries are proposed module names.
The receipt lists each additional direct consumer that its changed import boundary reaches.
Comment-only changes require no dependent Lean build.

For a new match on a policy family, run `make check-cases`.
For a changed generator input, run `python3 scripts/generate.py --only <family>` with the actual owning family.
The coordinator records that family before editing its input.
For a changed OCaml component, run its named Dune target through `opam exec --switch=effect4 -- dune build`.
TypeScript checks use the repository's pinned tsgo 7 compiler only.

Run `#print axioms` for each new milestone theorem and the retained boundary theorems.
Attach the literal output; the permitted dependency ceiling remains `[propext, Quot.sound]`.
Check no trust escape or prohibited proof fallback enters touched files.
A scoped axiom check does not replace the existing whole-library gate.
The owner decides when to run the whole battery and full sweep.

## Documentation and generated evidence

Run `python3 scripts/check-language.py --strict <touched Markdown files>`.
Run `python3 scripts/check-docs.py` when authority links or referenced targets change.
List exact generated groups, source inputs, consumers, and differences in the receipt.
Never hand-edit generated outputs or silently promote a retained baseline.
Keep receipts scoped to the commands actually run.

## Evidence required before merging a slice

Record the base, head, file list, exact commands, results, and axiom output.
Record each theorem's placement from [proof placement](proof-map.md).
State every remaining premise and every excluded reply or target form.
Link finite controls separately from universal theorems.
Bind target evidence to the exact artifact and toolchain.
Record any counterexample that changes a declaration in the existing register.
An intentional red control passes by rejecting its false claim; an unrelated compile error does not pass it.
