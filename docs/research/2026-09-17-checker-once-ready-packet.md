# Ready packet: the type checker written once (ledger item C-P7)

2026-09-17. Coordinator's packet for one Opus seat, to run AFTER the C-P8 seat has finished (both
touch modules that sit under most of the tree; one seat at a time in this checkout). Tracker:
`docs/research/2026-09-17-scout-findings-ledger.md`, row C-P7 (it supersedes E-B4). Compiled probe:
`docs/research/2026-09-17-checker-once-probe.lean` (green, `[propext, Quot.sound]`, under a second,
imports only `Std.Tactic.Do`: `lake env lean docs/research/2026-09-17-checker-once-probe.lean`).

## 1. What and why

Two definitions walk the program in the same order and one theorem keeps them in step:

| today | where | lines |
| --- | --- | --- |
| `effTy`, `layerTy`, `layersTy`, `stmtsTy`, `effsTy`, `actionTy`: the checker, `Option`-valued | `src/Effect4/Program/Typing.lean:282-556` | 275 |
| `explainEff`, `explainLayer`, `explainLayers`, `explainStmts`, `explainEffs`, `explainAction`: the same walk again, asking `effTy` about each child, to name where and why it refused | `src/Effect4/Program/Typing/Blame.lean:118-384` | 267 |
| `explainEff_none_iff` and its five siblings: arm by arm, that the second walk answers `none` exactly when the first answers `some`; 51 copies of one tactic line, at `maxHeartbeats 1600000` | `src/Effect4/Program/Typing/Blame.lean:430-765` | 335 |

602 lines exist only to keep a copy honest. Every change to a typing rule is made twice and proved
a third time (DI-91 and DI-92 both paid this today). The second walk is also quadratic: it calls
`effTy` on a child and then recurses into the same child.

## 2. The design, and why it is not the scout's

The scout proposed `checkEff : … → Except TypeRefusal EffTy` with
`effTy := (checkEff …).toOption`. **That cut is wrong for this tree**, for a reason the scout did
not measure: `effTy`'s unfolding is load-bearing in three places that all assume an `Option`-valued
`do` block.

1. `src/Effect4/Laws/Program/Typing/Inversion.lean`: 66 inversion lemmas, each proved by
   `refine Option.of_triple ?_; simp only [effTy]; mvcgen; all_goals simp_all`, against generated
   `@[spec]` lemmas `effTy_reflect`, `stmtsTy_reflect`, … . Everything downstream (`Sound.lean`,
   `HasTy.lean`, `LoopSound.lean`, `MeaningSound.lean`, `TypedRun.lean`, `ScopedTyping.lean`) goes
   through these inversions, so they are the only proofs that see the checker's body. Other unfold
   sites: `Laws/Codegen/Forms.lean` (5), `Schema/Transform.lean` (4), `Typing.lean` itself (3).
2. `tools/Conform/Effect4/specs.json` names the six checkers as roots; `tools/Conform/Cli/EmitSpecs.lean`
   and `tools/Conform/Spec/Reflect.lean` are written for `Option`-valued functions
   (`Option.spec_reflect`, `Spec.bind_Option`, `Option.of_triple`) and emit the 1,635-line
   `src/Effect4/Laws/Program/Typing/Specs.lean`.
3. `tools/Conform/Effect4/rules.json` names `Effect4.Program.effTy` as the algorithm with
   `"refusal": "Option.none"`; the LCNF rule reader (`tools/Conform/Lcnf/Rules.lean:218-275`) reads
   its arms as `cases Option`.

**The design that leaves all three standing: write the checker once, generic in the carrier of
refusals.** A two-operation class says what a carrier offers beyond its monad:

```lean
class Refusing (F : Type → Type) where
  refuse : {α : Type} → TypeReason → F α          -- refuse here, for this reason
  under  : {α : Type} → Nat → F α → F α           -- this computation is child `i` of the node
instance : Refusing Option where refuse _ := none; under _ x := x
instance : Refusing (Except TypeRefusal) where
  refuse r := .error ⟨[], r⟩
  under i x := x.mapError fun r => { r with path := i :: r.path }
def orRefuse [Monad F] [Refusing F] (reason : TypeReason) : Option α → F α   -- lifts a leaf
```

`checkEff [Monad F] [Refusing F] sig env : Eff Op → F EffTy` and its five siblings are today's arms
with `none` replaced by `refuse <reason>`, each `Option`-valued leaf (`termTy`, `causeTy`,
`EffTy.joinAnswer`, `Decision.arms`, `sig.serviceTy`, …) lifted by `orRefuse <reason>`, and each
recursive call on child `i` wrapped in `under i`. Then:

- `effTy sig env e := checkEff (F := Option) sig env e`: **still an `Option`-valued function with
  the same arms.** The probe shows the old equations hold by `rfl`.
- `explain sig env e := match checkEff (F := Except TypeRefusal) sig env e with | .ok _ => none | .error r => some r`.
- The law is **naturality of one map**, `Except.toOption`-shaped, between the two instances:
  `toOpt (checkEff (F := Except _) …) = checkEff (F := Option) …`. One `simp only` per arm from six
  equations (`toOpt_pure`, `toOpt_bind`, `toOpt_refuse`, `toOpt_under`, `toOpt_orRefuse`,
  `toOpt_ite`), no case analysis on reasons, no heartbeat bump. `explain_none_iff` is then a
  two-case fact about one `Except` value.
- The path is built on the way OUT (`under i` prepends), so the checker's signature gains no path
  argument and no "the path does not affect success" theorem is needed. Started at the root this
  gives exactly `explainEff`'s `p ++ [i]` paths; `Api.explain` is the only caller and starts at `[]`
  (`src/Effect4/Api.lean:116`).

## 3. What the probe already settles

The miniature has a binder (`bind`), a guarded arm (`ite`), an `Option` leaf, and both instances.
All green:

1. The generic checker is accepted by structural recursion (recursive calls sit inside `under i (…)`
   and inside `>>=` continuations).
2. `check_natural`: one `simp only` per arm. `explain_none_iff` from it in three lines, explicit
   lemmas only.
3. The old `Option` equations (`ty_bind`, `ty_ite`) hold by `rfl`.
4. **The project's inversion recipe survives unchanged in shape.** Two variants both work:
   through a per-arm `rfl` equation (`simp only [ty_bind]; mvcgen; …`), and with NO per-arm
   equation: `simp only [ty, check, under_option, refuse_option]; simp only [ty_fold]; mvcgen; …`,
   where `ty_fold : check (F := Option) env e = ty env e := rfl` folds the recursive calls back so
   the generated `_reflect` specs still match. Use the second: it needs three `rfl` lemmas in total
   rather than sixty.
5. `decide +kernel` still evaluates a typing certificate through the instance.
6. The located reason and path come out as the old walk gives them (three `#guard`s).

Also measured: the checker is **not** in the OCaml engine's generated code (`ocaml/gen/api_gen.ml`,
`ocaml/engine/api_engine.ml` name none of the six), so `check-ocaml` and the `lcnf` group are not
in play. `explainEff` is named only by `Blame.lean` itself; its consumers
(`src/Effect4/Api.lean:112-134,439-440`, `src/Effect4/Codegen/Diagnostics.lean`,
`Test/Program/BlameContract.lean`) use `explain`, `blame`, `TypeRefusal`, `TypeReason`.

## 4. What is NOT settled, and is the seat's step 0 (bounded: half a day)

These need the project compiled, which the coordinator could not do while another seat was
building. Do them first, on a scratch copy of the two files if that is quicker, and STOP and report
if either fails; do not start the port.

1. **The specs generator.** With `effTy` and its five siblings now thin definitions over the
   generic checker, does `python3 scripts/generate.py --only specs` still emit the same `_reflect`
   lemmas? `Reflect.lean`'s `optionLeaves` harvests `Option`-valued callees from the roots' BODIES;
   the bodies are now one application of `checkEff`, so the harvest may come back short
   (`termTy_reflect`, `joinAnswer_reflect`, `arms_reflect`, … are the leaves the inversions need).
   If it does: point the roots at the generic six and teach the harvest to see through the
   `orRefuse` lift, or list the leaves in `specs.json`. Acceptance: `Specs.lean` regenerates with
   the same set of `@[spec]` names (the file may differ in order; the set may not shrink).
2. **The LCNF rule reader and the cases policy.** `make check-cases` after the change. The mono
   code of `effTy` will be a specialisation of `checkEff` at `Option`; if the reader no longer
   finds `effTy`'s arms under the name `rules.json` gives, either name the specialisation or mark
   `checkEff` and siblings `@[specialize]` and re-read. New `cases-policy.json` rows for the generic
   definitions are expected and fine; a refusal of the rule extraction is a stop.
3. **Certificate cost.** Time the slowest `decide +kernel` typing certificate before and after
   (`Test/Program/TypedContract.lean` and the corpus certificates); a slowdown over 2x is a report,
   not a stop.

**Fallback if step 0 fails and cannot be repaired inside its half day** (needs the owner's word,
because it trades a theorem for tests): keep both walks, delete only the 335-line law, make
`Api.check`'s verdict `effTy`'s by construction with `explain` as decoration, and rely on
`Test/Program/BlameContract.lean`, which since `1f4edcb9` has a red control for every reason.
Net −335 lines, no cascade, and drift between the walks becomes test-detected, not impossible.

## 5. Steps

Cadence as AGENTS.md: narrow builds, no `make check`, no bare `lake build`, one compiler at a time,
long builds in the background. No `simp_all`/`first`/`try`/`aesop`/bare `simp` in proofs you write
(the existing `all_goals simp_all` tail of the 66 inversion proofs is the type-tooling wave's
recipe; leave it as it is, change only the `simp only` line in front of it).

1. **`src/Effect4/Program/Typing/Refusal.lean` (new, below `Typing.lean`).** Move `TypeReason`,
   `TypeReason.head`, `TypeRefusal`, `selectRefusal` out of `Blame.lean:28-117`; add `Refusing`,
   its two instances, `orRefuse`, and the `rfl` lemmas `under_option`, `refuse_option`,
   `orRefuse_option`. Check first that everything `TypeReason` mentions is defined below
   `Typing.lean`'s mutual block (it names `Ty`, `Term`, `CauseTerm`, `Decision`, row names).
2. **`Typing.lean`: the six checkers become generic.** Keep the ORDER OF CHECKS of `explainEff`
   where it is finer than `effTy`'s (for example `iterate`: `explainEff` names which of three
   conjuncts failed, in a fixed order; write the guard as that sequence of `if … else refuse …`,
   which accepts exactly what the conjunction accepts). The success set must not change by a
   single program: that is what step 4's batteries pin. Define `effTy … := checkEff (F := Option) …`
   and siblings under their present names and signatures, plus the six `_fold` lemmas by `rfl`.
3. **`Blame.lean` shrinks to:** `explain`, `blame`, the naturality kit, `check_natural` for the six
   sorts (one mutual block, one `simp only` per arm), `explain_none_iff`, `blame_none_iff`. Delete
   the six `explain*` walks and the six `*_none_iff` case analyses. Move the law under
   `src/Effect4/Laws/Program/Typing/` if no definition in the core needs it
   (`Api.lean:126-134` uses `explain_none_iff` in two theorems; if those can move to `Laws/` too,
   move them; if not, leave the law where it is and say so).
4. **Port the unfold sites.** `Inversion.lean` (66 proofs, 65 `simp only [<checker>]` lines): replace `simp only [effTy]` (and the
   sibling names) with the two-line form of §3.4. `Laws/Codegen/Forms.lean` (5),
   `Schema/Transform.lean` (4). Narrow builds:
   `lake build Effect4.Program.Typing.Blame Effect4.Laws.Program.Typing.Inversion`, then
   `Effect4.Laws.Program.Typing.Sound Effect4.Laws.Program.Typing.HasTy
   Effect4.Laws.Program.LoopSound Effect4.Laws.Codegen.Forms`, then
   `lake build Test.Program.BlameContract Test.Program.TypedContract
   Test.Program.TypeAlgebraContract Test.Program.LoopSoundContract`.
   **`Test/Program/BlameContract.lean` must pass UNCHANGED**: it pins every reason and path.
5. **Regenerate** `specs` (step 0.1) and run `make check-cases` (step 0.2). Then ONE background
   `lake build Effect4 Effect4Laws Test`.
6. **Receipt** at `docs/research/2026-09-17-checker-once-receipt.md` (what changed per step,
   `git diff --cached --stat`, every command and its result, the axioms of `check_natural` and
   `explain_none_iff`, the certificate timing, anything reverted with its failing goal) and the
   ledger rows C-P7 and E-B4.

Do not commit, do not push, no `git checkout --`/`restore`/`stash`/`reset`, no bypass flags. Leave
the tree green and staged; the coordinator reviews against this packet and commits by step.

## 6. Expected size

Out: the second walk (267) and its law (335). In: `Refusal.lean`'s class, instances and kit (about
50), the reasons threaded into the arms and the finer guard sequences (about 70), naturality
(about 120: some sixty arms, two lines each). **About 360 lines net**, not the scout's 520: the
difference is the naturality block, which the scout's form would not have needed but whose
alternative was re-proving 66 inversions against `Except`. The larger gain is that a typing rule is
written once and the law cannot go stale arm by arm.
