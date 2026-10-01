# Addendum 4 to the slice 6 brief: after the first receipt

Written 2026-09-30, after Codex's [receipt](2026-09-30-seat-codex-slice6-receipt.md) at
`3c2609f4`. Read it with the [brief](2026-09-30-codex-brief-slice6-and-fixes.md) and addenda
[1](2026-09-30-codex-brief-slice6-addendum-1.md), [2](2026-09-30-codex-brief-slice6-addendum-2.md)
and [3](2026-09-30-codex-brief-slice6-addendum-3.md); where they differ, this one wins. The owner
ruled on 2026-09-30: "go on 1 and 2, hold H2 for the synthesis".

**The one thing first.** B, D's independent parts and E are merged into `refactor/phase1-phase3`
as they stand at `3c2609f4`, and `codex/slice6-fixes` is fast-forwarded to the merge commit. The
four scope stops (A, C, F, G) are lifted below, each by the amendment the receipt proposed. H1 has
its ruling. H2 stays stopped until the next addendum. The order is A, C (with D's held users), F,
G, H1.

**Checked by the coordinator before merging.**
- The narrow build the receipt names, rerun in the worktree at `3c2609f4`: 421 jobs, exit 0, no
  warnings, every axiom print at `[propext, Quot.sound]` or less.
- The six retired judgment names have no use under production `Laws/Program/Typed` (0 matches).
- The A and F generated-file diffs are exactly the files the receipt names: the `RunnerDerived`
  codec's new constructor row and arms; the two closure manifests.
- The C reader (`Api/Supervision.lean:346`) and the G fixture (`Test/Program/AuthorContract.lean:267`)
  are as described.
- The H1 witness was read: `Θ(root, 0) = unit`, an `awaitValue` observer, and an emitted resume
  carrying the encoded exit, refused by `TypedProg.pure_inv` in every later world.
- The merge against `7cae243a` (docs only since `74b526d4`) has no conflicts.

## Item A: the generated codec is in scope

The brief's §6 let regeneration change only the four LCNF outputs and the eff, wire and cas
groups. The new refusal `AdmitRefusal.internalHandle` needs its constructor in the generated
`src/Effect4/Api/RunnerDerived.lean` (the `shapeDoc` row, the `toVal` and `ofVal` arms, the `fits`
case: `A/runner-generated.diff`) and in the producer's acceptance fixture
`tools/Effect4Gen/guards/runner.lean`.

1. Both files are permitted. They land as generated (`make gen-derived`), never hand-edited.
2. Apply `A/implementation.patch` on the current head. It was written against `74b526d4`; B has
   since edited `Laws/Program/Admit.lean`, so expect a context shift there and nothing else.
3. Then the fixed order, derived → lcnf → eff → wire → cas, with `LEAN_NUM_THREADS=1`; the two
   runner tests the receipt left unrun (`Test.Api.RunnerContract`, `Test.Run.RunContract`);
   `dune build` through `opam exec --switch=effect4`; `make check-ocaml`.
4. The four repaired admission laws get their own axiom print; the receipt says they have none yet.
5. `E4-HOST-CE-007` becomes REPAIRED at A's landing commit. Row 97's status line is the
   coordinator's.

## Item C: one more reader, and the defaults stay

1. **The reader.** The inline guard `loaded.fibers.map RunFiber.origin = [.root]` at
   `src/Effect4/Api/Supervision.lean:346` joins step 4's checklist. Restate it through the ledger's
   reader (`originOf`) before the field goes.
2. **The defaults stay.** Addendum 1's fallback applies ("if more than about twenty call sites
   outside `Machine/` and `Program/Compile.lean` break, keep the defaults instead"): one laws file
   alone has 37 calls that omit the site (`Laws/Api/Supervision.lean`, the lines the receipt
   lists). Keep the eight defaults in `Machine/Fibers.lean` (304/308/310, 926, 957,
   1428/1440/1451). The removal step is withdrawn; list the 37 callers in the receipt as the
   fallback asks. A later slice may revisit it with a measured count. No `kind` field, as before.
3. Then steps 3–5 as the brief states them, and D's held users with them: the trace user, the four
   ledger facts, the `AgreesUpdates` restatements, the `forkedOf`/`Agrees` move, the M1Trace
   ceiling, and row 94's three-user comparison.
4. The stop rule stays: a reader outside the amended checklist, or a fork made anywhere but
   `spawn`, stops C again.

## Item F: the two closure manifests are in scope

The generator changed `ocaml/gen/closure-api_engine.tsv` and `ocaml/gen/closure-api_gen.tsv`:
the new `Point.layerBuild` row, `provideLayerWithK`'s changed row, and the hashes they move
(`F/generated-manifests.diff`). Both are permitted; they are generated output.

1. Apply `F/implementation.patch` on the current head. It was written against `e1c6a1fc`; E has
   since edited only `Laws/Program/Typed/*`, outside F's paths.
2. Complete the stages the stop cut off: eff → wire → cas; `dune build`; `make check-ocaml`, with
   the prepared `errLeak` engine assertion on both carriers.
3. The run comparison stands as finite evidence (37 truth fixtures and 400 random depth-4
   programs, no run value changed). Say so in the receipt, as the first receipt does.
4. `E4-PROV-CE-005` becomes REPAIRED at F's landing commit. Row 104 is the coordinator's.

## Item G: the third fixture is expected

`Test/Program/AuthorContract.lean:267–268` expects `Api.checkLayer (Layer.value Counter.key
(str "x"))` to succeed with `provides = [Counter.key]`, and `Counter` is declared at `nat`. That is
the gap G closes, met in an existing test.

1. The fixture joins addendum 3's two exceptions. Expect the located refusal
   `valueNotSubtype Counter.key string nat` at `[]`, as `G/AuthorContractProbe.lean` proves it.
   Keep the positive string-carrier `Greeting` fixture at lines 290–292.
2. Then G as addenda 2 and 3 state it: the checker and `LayerHasTy` changes; `leftWins` and
   `rightWins` to `dbBinding`; the two unknown-key controls; the named laws and tests; the corpus
   index regenerated.
3. `E4-PROV-CE-006` becomes REPAIRED at G's landing commit. Row 105 is the coordinator's.
4. The stop rule stays: a fourth in-tree program refused stops G again.
5. While in `Program/Provision.lean`: its header (`:35-41`) still advertises `build_total`, which
   was landed at `f182d2b3` and cut at `b08f3b58` (the model probe found it). Say what the module
   proves today; no proof is asked for.

## Item H1: a token is typed by what its observer delivers (ruling)

**The gap.** The token table `Θ` declares what a waiter will receive on a token. An observer
delivers by its mode (`Machine/Supervision.lean:22`; `Stores.lean:2257–2260`): `awaitValue`
delivers `success (reifyExitVal exit)`, the exit encoded as a value; `joinEffect` delivers
`Prim.ofExit exit`, the exit itself. The checker already types the two deliveries differently
(`Program/Checker.lean:191–196`): `joinEffect` at the fiber's own answer and error types,
`awaitValue` at `EffTy.pure (.exitOf answer error)`. Codex's witness
(`H1/ObserveGap.candidate.lean`, `proposed_step_observe_false`) has `Θ(root, 0) = unit` and an
`awaitValue` observer on a unit-typed fiber: the emitted resume carries the encoded exit, which is
not `unit`, in every later world, because the world order keeps a token's declaration. So the
statement addendum 3 asked for is false as written, before any proof.

**The ruling (owner, 2026-09-30).** A token is typed by what its observer delivers, not by the
fiber it waits on. In the typed state and in the queue fact:
- for an observer `resumeAwait waiter token mode` registered on a fiber of type `ty`,
  `Θ(waiter, token)` is the delivered type: for `joinEffect` it is `ty`; for `awaitValue` it is
  `EffTy.pure (.exitOf ty.answer ty.error)`, the checker's own rule;
- an `observe fiber exit observer` command is admitted only when `interp.exitValue exit mode` fits
  `Θ(waiter, token)`. Put the clause where its proof is one lemma on `reifyExitVal` against
  `Fits` at `.exitOf`: in the generated `RCmdOk` through the observer's payload, or in the state
  part. Say in the receipt which, and why;
- the same clause holds where observers are registered (`Fibers.lean:1118`, `:1591`): at
  registration, the token's declaration is the delivered type. Inspect the other observers
  (`untrackChild`, `dropScopeFinalizer`, `countdown`) under the same connection and say in the
  receipt which carry no payload.

**Register.** Add `E4-SCHED-CE-018`, "a token is typed by what its observer delivers", SEEDED by
`ObserveGap.candidate.lean`, REPAIRED by H1 together with `E4-SCHED-CE-017`.

**Then H1 as addendum 3 states it:** the generated command check on every queued command; the
guard's conditions mirrored on the reference machine; `pending_below` landed as a law (it is in
evidence only today); the controls in `M6Capstone.lean`. Statements only: the 18 command proofs
stay with the M5–M7 brief. The open design point the receipt names, the reference code-site scan,
stays as the receipt leaves it: name it, and do not quantify over every continuation answer.

## Item H2: held

No H2 work until the coordinator's next addendum. The measured cost is accepted as measured:
eight existing bodies (seven from slice 5, one E adapter); `strongExit_of_clean` needs a premise,
because a clean exit may still be `die badName`; part two needs a service-presence argument
(`H2/diagnostics/MissingServiceTransport.lean`). The owner holds the go until the model-probe
synthesis (`docs/research/2026-09-30-model-probe/`) says whether the exit judgment's shape
changes. Nothing in A, C, F, G or H1 depends on it.

## Rows and the register (the coordinator's)

- Rows 95 and 96: landed with the merge (B at `eca77d6a`; E1–E4 at `5e142337`, `c1bcfdf6`,
  `602ab157`, `0c1e9915`).
- Rows 104 and 105: amended as above; they land with F and G.
- Row 106: amended with H1's ruling. Row 107: held.
- Row 110's generic lifts: landed at `75ee115c`, with the guard driver re-derived through them at
  `9dddff27` and the native memo-id user at `e1c6a1fc`.

Codex proposes rows and register lines in the receipt, and never edits `decisions.md`.

## Base and receipt

Work continues on `codex/slice6-fixes` in the same worktree, from the merge commit. Same rules:
narrow builds, commits by explicit paths, `LEAN_NUM_THREADS=1` for regeneration, no push. Update
the receipt in place: a new section "After addendum 4" at the top with its own one thing, the
first receipt's sections kept below as history, and per item the commit, the commands, the axiom
output and what is finite evidence.
