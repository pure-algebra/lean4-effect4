# S0 scout report

The current start/load closure does not compile as OCaml. Generation succeeds while reporting an unknown dependent child type.
The checked source repair keeps the exact annotation sequence. Its native collector and hostile duplicate-field control pass.

## Scope and workspace

- Production worktree: `/Users/pooks/.codex/worktrees/seams/lean4-effect4`.
- Every scout write stays under `/private/tmp/seams-s0-scout`.
- No production source or Git state changes.
- OCaml compiler: 5.1.1, through `opam exec --switch=effect4`.
- Current Lean commands use `/private/tmp/seams-lean-one.py`, then the required launcher with `LEAN_NUM_THREADS=3`.
- The first scout invocation used the launcher alone before its two-slot behavior was discovered. It was interrupted immediately.

## Checked findings

### OCaml interfaces from typed trees

`sig_seal.ml` reads `Cmt_format.Implementation structure.str_type`.
It retains named root values and changes the chosen package declarations to abstract types.
It recurses through functor results without changing carrier module types.
`Printtyp.signature` writes the resulting inferred interface.

`python3 run-seal.py` passes the legitimate memo client and the public-alias client.
It refuses six hostile clients: a forged memo, forged checked value, arbitrary oracle, arbitrary hit rule, record update, and hidden helper.
All command statuses and compiler messages are saved as `sealed-*.json` and `sealed-*.log`.

The public alias remains `type public_alias = memo`. Hiding its representation still prevents construction.
Oracle and HitRule must be abstract too. Their erased proof fields otherwise leave native callbacks that can lie.

`raw_alias.ml` demonstrates why inference alone is insufficient.
Without nominal annotations, its inferred `empty` and `learn` signatures expose ordinary lists even when `memo` is abstract.
Preserve nominal package types on affected root bindings before asking OCaml to infer the interface.
Read those annotations from the original Lean declaration type, not mono LCNF.
Mono has already erased the checked package and its type parameters.

### Real engine interface and linkage

`python3 engine-interface.py` checks the real generated engine, copied to the probe directory.
The inferred interface exports the recipe roots and all current prelude values.
It compiles with the unchanged generated implementation.
The unchanged adapter fails when `program_interp_of` is hidden.
It compiles when that linkage value and the existing step specialization are exposed.
The specialization is a probe control only. D-11 requires replacing it with the named Lean `stepChecked` root.

`read_refs.ml` inventories real value references from OCaml typed trees, including references introduced through `open` and `include`.
`linkage-proposals.json` maps observed missing roots back through the generated closure manifests.
It records callers and distinguishes coverage roots from closure-only helpers.
The complete API inventory needs a fresh full OCaml build; the current native CMT set is partial.

Observed additions for `api_gen`:

- `Effect4.Api.load`
- `Effect4.Program.Decision.decide`
- `Effect4.Program.errOf`
- `Effect4.Program.evalTerm`
- `Effect4.Program.interpOf`
- `Effect4.Machine.reifyExitVal`
- `Effect4.Machine.RunMachine.completedExits`
- `Effect4.Machine.RunMachine.finished`, moved from coverage to roots
- `Effect4.Run.Tree.Eval.badShape`
- `Effect4.Run.Tree.Eval.outside`
- The new `Effect4.Program.stepChecked`

`api_engine` needs `Effect4.Program.interpOf` and the new `Effect4.Program.stepChecked`.
Both instance adapters currently call the compiler-made specialization.
`SeamsS0Step.lean` contains the proposed exact stable wrapper, retaining the adapter's interpreter argument.

### Full checked start/load lowering

`live-before-reader.json` records the complete generator command.
The roots are `Effect4.Live.start` and `Effect4.LiveRecord.restore`.
The imported module is `Effect4.Run.LiveRecord`.
The generator emits 1,542 declarations and exits zero.
It reports `Effect4.Program.ArgF.r : R fam` as unspelled.
It also reports `Effect4.Program.DefRole` as a placeholder; request that type in full.

`live-before-reader-ocaml.json` records the compiler refusal.
The constructor `ArgF_child` expects `lcnf_unknown`, but `view_eff` supplies a program body.
The emitted generic `program_view fam node` also dispatches one erased value to different family types.
This is the R9 dependent boundary that the earlier nondependent checker-port probe did not test.
The full-admission owner must remain. Substituting `Run.Kit.admit` would violate R13.

## Proposed repair

`formation-reader.patch` changes three source owners:

1. `tools/Effect4Gen/LayerView.lean` generates `ArgReader` and one `readArgs_<family>` function per existing family.
2. `src/Effect4/Program/Formation.lean` uses these functions in its existing path fold.
3. `src/Effect4/Laws/Program/Typing/Closed.lean` rewrites the two proof consumers through the exact connector.

`ArgReader` is a carrier of callbacks, not stored syntax.
A child retains its argument position and family. The reader discards only its recursive payload.
Every leaf keeps its value and original argument position.
No new program representation, cast, `Obj`, or `Marshal` is introduced.

The theorem placement precedes proof work:

| Item | Placement |
| --- | --- |
| Concept | `subtyping-algebra`, existing raw-formation property |
| Claim | `raw-formation`, role decidability; the reader connectors are helper steps |
| Observation | Exact ordered annotation sequence, including each original argument index |
| Scope | Every program family, every alphabet, and each existing `ScopedOp` instance |
| Exclusions | No typing, progress, admission-success, or native execution claim |
| Consumers | `Formation.programAnnotations`, `programAnnotations_all`, and full program admission |
| Requirement | R13; the generated signature reader also serves the fold discipline under R4 |

`readArgs_<family>_eq` relates the generated reader to the original view's indexed argument list.
`argumentReader_read` relates each callback to `argumentAnnotations`.
`programAnnotations_eq_view` equates the complete new collector with the original path-fold expression.
The two Closed proofs change only by rewriting this equality; their statements stay unchanged.

A shadow Formation module alone cannot establish a repaired Live closure.
Mono specialization embeds the old collector in dependent modules, so those modules must rebuild after integration.
A native-alphabet collector probe can validate the reader separately while that dependent rebuild waits.

## Interface integration proposal

- Keep translation roots separate from exported roots. Coverage contributes to closure but not to the public interface.
- Include each hand-called value as a root, as D-11 requires.
- Keep prelude values exported until their planned deletion.
- Emit root OCaml names from `Translated.userName` and `Translated.ocamlName`; do not guess names with regexes.
- Add an explicit abstract-type list to the recipe for the checked packages.
- Preserve original nominal types on affected root arguments and results before OCaml inference.
- Fail on an unexpected source/mono parameter mismatch instead of silently erasing the requested annotation.
- Infer an interface from a temporary compilation without the old `.mli`, then install the generated `.mli`.
- Compile both the interface and implementation, and compile hostile clients against the installed interface.
- Keep this reader in an OCaml library with a thin CLI, using `compiler-libs.common`.
- Extend the existing `lcnf` producer; do not add an independent hand-maintained interface producer.

## Evidence status

Typed-tree sealing and the existing engine interface checks are host-tested finite probes.
The original full start/load failure is reproduced with retained source and logs.
The generated reader and both existing Closed proof consumers compile. The collector audit reports 229 declarations within [propext, Quot.sound], with no planned goals.
The native collector compiles and runs its positive path observations and duplicate-field refusal.
The original ten Check package roots retain their nominal types, compile behind the inferred sealed interface, and run ask, learn, memo hit, and bind.
Six hostile native clients are refused: memo alias, checked alias, oracle callback, hit-rule callback, record update, and hidden helper.
The generic value projection has no standalone mono declaration. A source getter retains an erased type argument and fails the source/mono arity check.
The Verdict-specialized accessor preserves the generic Checked representation. Its complete lowering emits 619 declarations with no missing, unknown, or placeholder types.
The stable step wrapper compiles in Lean. Its standalone closure meets the clock-flow refusal and must be tested in the full production artifact.
No result here claims universal native translation correctness.

## Final annotation and regeneration probes

`nominal-roots.patch` adds an explicit nominal-root list and full-value source-type ascriptions.
It expands generated aliases before comparing source and mono arity. A mismatch refuses the root.
The ascriptions keep the original values and introduce no argument wrapper or cast.
`sig_seal.ml` keeps only the last binding of each value before filtering the typed signature.

`staging-hook.patch` applies after the nominal patch.
Its `--stage` driver option changes output destinations without changing the recorded canonical commands.
The producer must stage every artifact, infer and check all interfaces, then publish the whole checked batch.
`regeneration-probe.py` exercises the real engine implementation in an empty stage.
The old interface cannot block inference because it is absent from that stage.
The new interface and implementation compile together. An invalid source refuses and leaves both published files unchanged.

The exact generic getter mismatch is retained in `generic-getter-refusal.txt`.
Source: `{α : Type} → Checked α → α`.
Mono: `Checked.readValue (α : lcErased) (c : Checked lcAny) : lcAny`.
The generator refuses arity 1 versus 2. The parent authorizes a Verdict-specialized source accessor for S0.

The source readback repair is in `formation-reader.patch`.
`reader-Formation.log`, `reader-closed.log`, `reader-native-lower.log`, `reader-audit.log`, and `reader-ocaml-*.log` record its checks.
