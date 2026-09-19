# Wave 1 reviewed for coherence, and the next slice

2026-09-19, after the four merges (`f8517fa7`, `dfd94366`, `9e20cf9b`, `ee88efe2`) and the two
commits that closed them (`1f1cc8e3` rows 59–66, `ba5286d3` the policy). Evidence words as in the
receipts: **proved** = a theorem built; **measured** = a number read off a run; **open** = named by
a seat and not attempted.

## 1. What the wave proved about the algebra

The wave's thesis was that a constructor's cost is decided by the *shape* of the proofs, not by the
number of them. Three results confirm it and one refutes a route.

**The order is one law.** `sub_eq_args` (generated, `Laws/Program/TyView.lean`): at two members
that are neither the literal rule nor the top, `sub a b = (sameHead a b && argsBelow sub a b)`.
The variance of each recursive position is read off rc.112 (`tools/Tools/Variances.lean`,
eleven controls, the two aliases inferred with their evidence), so `Ty.sub`'s congruence arms are
now *checked against the target's declarations* at generation time: a wrong variance fails the
emitted probe and the arm lemma's own proof. That is the mechanism the owner asked for — the
target's typing as data, not as prose.

**A membership law is a condition on the algebra.** `cata_admits_sub` (`Laws/Program/Admits.lean`,
proved, `[propext, Quot.sound]`): any admission algebra whose fourteen arms satisfy `AdmitsSub`
has a fold that respects `sub`. The proof is `fun_induction Ty.sub` and names no constructor; the
invariant handles (`refOf`, `deferredOf`) need no induction hypothesis because their arm is an
equality — decisions row 44 as a theorem rather than a comment.

**`fun_induction` over the definition's own case list is the shape.** `hasTy_sub` went from 257
lines with sixteen `first` blocks to 79 lines with none (measured), statement byte-identical, by
taking the case list from `Ty.sub` instead of `cases a; cases b`. The top is one `rfl`, each union
rule is one case, the whole complement is one catch-all with `hsub : false = true`. The same move
is available to every proof in the tree that still does `cases a <;> cases b` over `Ty`, and to the
machine proofs that enumerate `SyncOp`/`NativeOp` arms.

**The one-proof route is refuted, honestly.** The single `fun_cases Ty.sub` + `aesop` proof of
`sub_eq_args` closes (A1 true) but reaches `Classical.choice` in the catch-all case, where aesop
instantiates the negative hypotheses classically. The per-head arm lemmas plus a dispatcher that
splits on `sameHead` first (so the catch-all is `rfl`) is what landed, at the ceiling. Two more
traps recorded by the seats: `simp` at `(x == x) = true` for `String`/`Nat` reaches
`Classical.choice` through `LawfulBEq`, `decide (x = x)` reaches nothing; and `Traversals` drops a
recursion's `_f` helper, so an inventory that walks authored definitions only misses every
structural recursion.

## 2. Where the code is not yet coherent (the findings that set the next slice)

Each of these is two spellings of one thing, or a law without its instance. They are ordered by
what they block.

**C1. The engine runs an older algebra than the tree.** `ocaml/gen/api_gen.ml:1475-1490` still
holds `ofName?` as a `List.find?` scan over `all`; the tree's `ofName?` is a string match, and
`AtomRow`/`Spec` do not exist on the OCaml side. Regenerating is blocked: `e4_program_layout.ml`
mirrors sixteen `Ty` constructors against the source's twenty (seat A measured the divergence
recorded in `e4_program_layout.json`, `"engine": 16, "source": 20`), so a regenerated
`api_engine.ml` does not compile. Since L5 the reified machine and its OCaml projection have
disagreed, and the nightly is the only thing that would say so. This is plan 4.2 and 0.7 and it is
first: everything else the wave produced is invisible to the engine until it lands.

**C2. The order's consumers still enumerate constructors.** `sub_trans_core`,
`sub_antisymm_normal`, `sub_normalize_of_sub` (`Laws/Program/TypeAlgebra.lean`) and
`sub_prod_mono` are unchanged, and `Ty.lean:779-808` keeps six hand `sub_*_of_ne` lemmas that
duplicate six of the nine generated arm lemmas (and are missing `refOf`, `deferredOf`, `except`).
What is missing is two generic lemmas, `argsBelow_trans` and `argsBelow_antisymm`, with the triple
measure threaded through `sizeOf_args`, and the literal rule lifted out of the three proofs
(`sub_eq_args` holds only under `litRule = false`; the literal case is `eq_of_sameHead` at empty
argument lists). Then the six are deleted and `sub_prod_mono` reads `sub_args_prod`. One
vocabulary for the order.

**C3. The generic membership law has no instance for the fold it was built for.**
`AdmitsSub Val.hasTy.alg` has fourteen fields; nine are proved and five (`list`, `prod`, `except`,
`exitOf`, `causeOf`) are refused at the same tactic, because `fold_of` emits the value-inspecting
arms through the compiler's `_sparseCasesOn` rather than `Val`'s own matcher, so neither `split`
nor `cases` sees the match. This is a defect of the *generator*, not of the five fields: an algebra
emitted for proofs should read `Val` through `Val.casesOn`/the matcher the hand definition used.
Fix `FoldOf.lean`'s arm emission, and the five fields become the same three lines as `option`.
With the instance, `hasTy_sub` is one line of `cata_admits_sub`; its 25 call sites are all under
`Laws`, so the law can move to `Laws/Program/Admits.lean` and the 79-line direct proof in the core
can go — the core keeps definitions, the Laws keep laws, and membership-respects-`sub` has one
proof.

**C4. Two more `hasTy` laws want their own algebra conditions.** `hasTy_mono` is monotone in the
allocation table, not the type: its condition is `AdmitsExtend` (one field per constructor: the
arm preserves table extension) and `cata_admits_extend`. `hasTy_normalize` is an equality between
the fold at `t` and at `t.normalize`, which needs the union/never/product-distribution facts
beside a congruence-shaped condition. Both are the same pattern as C3 and should be emitted by the
same `TyView` group (a condition structure per law) rather than written by hand.

**C5. The template calculus has two homes.** `Ty.matchTemplateArgs` (the list-level fold of
`matchTemplate`, with `matchTemplateArgs_length`) landed in `Program/NativeAtom.lean` under
`namespace Ty` because `Ty.lean` was another seat's file. It belongs beside `matchTemplate`
(`Ty.lean:501-503`). Plan 1.8's laws (`templateAdmissible`, `Row.wellScoped` by `decide`,
`sub_sound`/`sub_not_complete` named) are not written; `sound_of_poly` is stated at the
substitution the match produced, not at the final σ — the strong form is anchored completeness
(L4) and should be stated as such in the module, which it is.

**C6. Two atom rules are heads where they could be subsumption.** `isSome` and `getOrElse` are
`custom` because "the argument's own head must be the option — not a subtype of one". Under the
literal rule and the top, `mono [option unknown] bool` with `sub` at the parameter would accept
`never` and every `option t`, which is what TypeScript accepts for `isSome(x)`. Whether the head
rule is the target's semantics is exactly the question the tsgo lane answers: the prelude block is
generated from the same table with its cites, so each `Spec` can be checked against
`Parameters<typeof Atoms.isSome>` in the same query kind as the rows. Until that lane exists the
head rule stays; when it exists, `custom` should shrink to the rules that are genuinely their own
(`fst`/`snd`'s column projection, the four cause queries).

**C7. `tagIs` is monomorphic now** (`[string, unknown] → bool`, ruled yes in row 64). It is the
first atom to *use* the top in a signature; L3's twelve atoms should be written the same way
(`unknown` where the target says `unknown`, never a custom rule for "anything").

**C8. The proof estate's shape, measured.** 707 counted `first`/`simp_all`/`try` over 94 sources
after the wave (730 before). The five heaviest: `Laws/Machine/Handles.lean` (11/0/34),
`Laws/Program/Agreement/Machine.lean` (21/1/14), `Laws/Program/Guard/Core.lean` (11/7/12),
`Laws/Machine/Approximation.lean` (11/0/16), `Laws/Program/DenoteR.lean` (2/2/19). These are
machine proofs that enumerate `SyncOp`/`NativeOp`/frame arms — the `refStepOf`/kernel-table and
`row_step` items of Tier 3 are the algebraic answer (one kernel lemma per row, twelve heap arms
become one), and `fun_induction` over `step` is the shape.

**C9. Build time is the wrong axis for "the build improved"; job count and proof shape are the
right ones.** The final landing build ran 155 jobs in 8 minutes on a quiet machine; the first cut's
closure ran 593 jobs over 80 minutes under four concurrent compilers, with single modules at
20–30 minutes (`Codegen.Read` 1793 s). Contention, not the tree, set those numbers. What the wave
changed in the tree: two new library modules, the census module 19 s → 42 s (the inventory), and
`hasTy_sub` 257 → 79 lines. The receipt that matters going forward is the shape count and the
"catchAll false" count for `Ty` (22 today), not wall time.

## 3. Process, in five lines

Seats' worktrees must be created by the coordinator at the base (two of three arrived at
`origin/main`); the base must be green on the battery before dispatch (it was not: the banks'
initializer); a seat's "green" includes one run of the battery with the trust gate (T2's missing
import was caught only by pre-review); shared files (`Makefile`, the manifest, `Test/All.lean`,
`Laws.lean`) get an anchor per seat in the brief; the coordinator does not run a closure build
while seats build. Everything else worked: the receipts, the drafted decisions rows, the octopus
merge with one battery at the end.

## 4. The next slice — three seats, ordered by what unblocks what

The slice's goal in one sentence: **the engine runs the same algebra as the tree, the order and
membership have one proof each, and the typing is checked against the target's compiler.**

### Seat E — the engine catches up with the algebra (C1; plan 4.2, 0.7, 0.10, 4.1, 4.3, 3.6)

1. `ocaml/engine/e4_program_layout.ml` unfrozen to the twenty constructors; `program_structure.py`
   raises on a divergence instead of recording it (4.2); `e4_program.ml of_ty` gets its four arms
   and the generated arity assertion (0.7). Red control: the mirror's own `"engine"/"source"`
   record can no longer differ.
2. `make gen` one pass: `$(GEN)/lcnf` before `$(GEN)/eff`, `gen-lcnf` in the `check-ocaml` job;
   regenerate the four LCNF outputs (the engine generator measured 14m38s; raise `generate.py`'s
   cap or run it as its own step) and `dune build`. Receipt: `api_gen.ml` holds the string-match
   `ofName?` and the `AtomRow`/`Spec` records; the engine's `make check-cases` and `check-ocaml`
   green.
3. Seat I's 0.10 patch (`scratchpad/seat-I-uncommitted-0.10-0.4.v2.patch`, 251 lines): the three
   cite fixes and DI-96…DI-100, regenerated through the now one-pass chain.
4. The closure manifest (4.1) and `Ml.checkModule` fatal (4.3) — the engine's projection becomes
   data the tree holds; `roots.json` (3.6) so each artefact's header is rendered, not typed.

### Seat V — one proof each for the order and for membership (C2, C3, C4, C5)

1. `FoldOf.lean`: emit value-inspecting arms through the matcher the hand definition used, so an
   emitted algebra is `split`-able; regenerate the five folds (`derived` byte-identical except the
   arm spelling); `Val.hasTy_admitsSub` all fourteen fields; `hasTy_sub` becomes
   `cata_admits_sub` applied, in `Laws/Program/Admits.lean`; the direct proof in
   `Program/Typed.lean` deleted; the 25 call sites re-pointed (an import line each).
2. `argsBelow_trans`, `argsBelow_antisymm` (triple measure through `sizeOf_args`); the literal
   rule lifted; `sub_trans_core`, `sub_antisymm_normal`, `sub_normalize_of_sub`, `sub_prod_mono`
   rewritten on `sub_eq_args`; the six `sub_*_of_ne` deleted. Red control: the proof-shape row
   for `TypeAlgebra.lean` falls; no proof under `Laws/Program` names a `Ty` constructor in a
   `cases` over the order (grep `cases a <;> cases b`).
3. `AdmitsExtend` + `cata_admits_extend` for `hasTy_mono`; the congruence condition and the three
   normalisation facts for `hasTy_normalize` — emitted by the `TyView` group as condition
   structures, proved once each by `fun_induction`.
4. `Ty.matchTemplateArgs` moved beside `matchTemplate`; plan 1.8's laws (`templateAdmissible`,
   `Row.wellScoped`, `sub_sound`, `sub_not_complete` with the `option (nat|string)` witness) in
   `Laws/Program/Template.lean`.
5. Hygiene in the files it owns while there: the positional `rcases` and two `all_goals try` in
   `Laws/Program/Decision.lean` (0.8), the trailing `| _ =>` in `syncOpOf_validIn` and
   `MeaningSound.lean` (0.5), the stale line cite in `Progress.lean:159` (0.9), the
   `TypedSources.lean:8-10` docstring (0.4's last item).

### Seat D — one compiler, and the typing checked against it (row 57; plan 0.11, 1.10a, 1.10, 1.11; C6)

The brief in the coordinator's scratchpad (`brief-D.md`) stands, with one addition: the rows
query (1.11) also binds each atom's `Spec` against `Parameters<typeof Atoms.<name>>` /
`ReturnType` from the generated prelude block, so C6 is decided by the target rather than by
taste, and the disagreement table names the atoms whose `custom` rule should become `mono`.

### After the slice (wave 3, named now so nothing is forgotten)

The twelve L3 atoms as rows (2.3, 2.4, 2.6: `inferJoin`, `asList?`, the `mul` clamp, then
`ite`/`some`/`none`/`mul` and the list/arithmetic atoms — each one `Spec` row, one `Shape` or
short block, one prelude line); the bank moves (1.2 checker, Inversion → `Effect4.Inversion`,
Reader, TypedState) with `#auto_census` before each; Tier 3 (`refStepOf` + kernel table,
`row_step`, frame lemmas as terms, the obligation ledger, `NativeOp.kind`), which is where C8's
five heaviest modules get their shape; then the language ledger L2–L7 on top of C3's instance.

## 5. What the coordinator lands itself, before dispatch

The three worktrees at the base `ba5286d3` (green on the battery), each with `.lake` copied from
the main checkout; the briefs with the shared-file anchors written in (Seat E: the OCaml and
`scripts/` estate, `Makefile` lines 100–170; Seat V: `src/Effect4/Laws/Program/*`,
`Program/Typed.lean`, `Program/Ty.lean`, `tools/Effect4Gen/{Fold,View}.lean`, `FoldOf.lean`;
Seat D: `tools/target`, `harness/tsdiag`, `ts/eff`, `scripts/check-truth.py`, the last line of
`GENERATED_PATHS`); and nothing else — the small items are inside the seats that own the files.
