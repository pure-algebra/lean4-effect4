# Synthesis: tooling before building — the state, the patterns, the plan (2026-09-18, evening)

Owner steer, mid-L5: pause; stop implementing; synthesise. "We should be making fundamental
improvements … focus on making our tooling better … the low-hanging fruit and the base things
that make the implementation fast across the board, eliminate drift, automate the stuff we don't
need to be doing ourselves … we can recognise the patterns in the development, the proof
obligations that have continuously arisen, the API shapes … proofs are our code; the math gives us
the structure of the architecture … let's get the typing and the atoms rock solid." This note is
that synthesis, and it is the deliverable of the pause; a review cycle follows it, then the plan
work is folded in.

## 0. What this note stands on

Two later steers, same evening, folded in: *read the sources the research points at, and steal
the API shapes — the principle is to treat everything as data; keep Eff's own proposition in view
(author in Lean, lower into TypeScript on Effect's semantics, a proven fiber machine, programs as
data, fluid composition); we have TypeScript's typing semantics on disk as data and have not used
it* (§4b); and *we add gates and never remove them — the build must improve, not regress; a gate
that does nothing goes* (§5b).

Read in full tonight: `2026-09-18-research-type-algebra.md` (990 lines), `-atoms-terms.md` (1030),
`-proof-engineering.md` §0–§4, §6 and its recommendations (of 1896), `-lcnf-reification.md` §1,
§3, §4, §5 and its recommendations (of 1388; §2, the compiler-world survey, only through its
§2.6 references). Measured tonight from the tree, not recalled: the diff sizes in §2, the
proof-shape counts, the case-site check's rows, the aesop registrations, the codec classifier.
Every design item below is **assumed** until a narrow build tests it; the seats built nothing and
neither did I after the pause. Where a seat's claim was checked against the tree and found off, it
is said in §4.

## 1. The state at this hour, verified

- **Committed on `refactor/phase1-phase3`:** rows 42/43 step 1 (`7db30c8a`), step 2 (`02e7d4f0`),
  L1 of the language push (`61afe78f`).
- **L5 applied, green, uncommitted.** `Ty.unknown` appended last (decisions row 46), the release
  rule as rc.112 (row 47, DI-94), snapshot rules by subsumption. The full chain ran to completion:
  `Effect4`, `Effect4.Laws`, `Test`, `OCaml5`, `Tools` build; `make gen-hermetic` regenerated the
  faces; the OCaml engine compiles under `opam exec --switch=effect4 -- dune build`. Working tree:
  38 files, +213/−57 outside docs (src alone 19 files, +169/−47).
- **One red: the case-site policy.** `make check-cases` refuses with 38 counterexamples and 20
  refused rows, all on `Effect4.Program.Ty`: every decided default arm now also absorbs `refOf`,
  `deferredOf`, `var` (since step 1) and `unknown` (since L5), and eleven new sites exist
  (`Ty.infer` ×11, `Ty.instantiate`, `Ty.closed`, `Checker.exitOf?`, `Checker.listOf?`, two more
  `sub` sites, three more `decEq` sites). The policy is a pin ("SEEDED from a measured scan … every
  later edit is a diff a human signed"); the remedy is a re-seed that keeps the two decision rows'
  notes, and a signed diff. Nothing in the 58 rows is a machine defect; one is a design defect:
- **DI-95, registered tonight.** `Effect4.Schema.Codec.isSupported` ends `| _ => true`, so the four
  constructors that landed today are classified *wire-supported* while `encodeRaw`/`decodeRaw`
  refuse every value at them (`| _, _ => none`). Dormant — its only readers are the `fold_of`
  registration and the `isCodecSupported` abbrev — but re-seeding the policy would pin the wrong
  classification as a fact. The rule it teaches: **a wildcard belongs in a proof and never in a
  classifier**; a classifier lists its positive arms and closes with an explicit negative.
- **The research landed:** four notes, 363 KB, gitignored; the proof-engineering seat finished
  after the hold. Their digests are in §3–§4 and the plan note §2d.
- **L2–L7 wait**, per the hold, for this synthesis and its review.

## 2. The bill, measured: where the time went

| chore | evidence | size |
| --- | --- | --- |
| three `Ty` constructors (step 1) | `git show --stat 7db30c8a` | 43 files, +700/−238 (src 22 files, +571/−197) |
| one `Ty` constructor (L5, tonight) | `git diff --stat HEAD` | 38 files, +213/−57 (src 19, +169/−47); `Typed.lean` +61/−15 with sixteen `first` blocks in `hasTy_sub`; `TypeAlgebra.lean` +5/−1 |
| readers of `Ty` that needed a hand arm | tonight's edit list | `Ty.lean` (nine), `Emit.tyO`, `Metadata`, wire tags, `Codegen/Types`, `Blame`, `Bridge`, `ProfileJson`, `Goldens`, Conform `LcnfMl`/`LcnfSemantics`, `e4_program.ml of_ty`, `Decision.lean`'s positional `rcases` |
| case sites on `Ty` in compiled code | `.lake/conform/cases.json` | 175 subjects, 58 on `Ty` needing a decision |
| aesop in the Laws | grep, tactic positions | ~397 calls; **0** named rule sets; 39 attribute registrations, all into `default`, including the checker's recursive definitions as `norm simp` (`CheckInversion.lean:39-41`) |
| proof shapes in the Laws | grep | `first` 306 occurrences, `try` 251, `simp_all` 96 |
| `fun_induction` | grep | one use in src (`Schema/EffectfulField.lean:58`, a list loop); none over `Ty`, `hasTy`, `normalize`, `infer` |
| atom typing soundness | `Laws/Program/Typed.lean:586-749` | 165 lines by hand, ~8 per atom, one block each; L3 wants 12 more |
| places an atom is known | atoms seat §1.2(d), LCNF seat §4(v) | twelve, one of them a hand-written TS prelude |
| `step_typed` | `Laws/Program/Progress.lean:176-403` | 228 lines, 24 arms, ten byte-identical |
| constructor lists in proofs | `Progress.lean:434-489`, `MeaningSound.lean:642-647` | two that every new row or constructor must edit |
| regeneration rakes tonight | this session | build `Effect4.Program.Ty` before the Driver; `make gen` needs two passes; `dune` only via `opam exec`; the conformance modules are `Ty` readers the chain forgot; the engine mirror pins declaration order (constructors append, never insert) |

The distribution is the argument. `sub_trans_core` absorbed the top rule in two lines because it
dispatches on `isMember` before constructors; `hasTy_sub` paid sixty-one because it is `cases a`
then `cases b` per arm. **The shape of a proof decides the cost of a constructor before anyone
writes the constructor.** The same is true of a table (`spec` versus twelve matches), a generator
(one reader of the environment versus a hand transcription), and a policy (a pin that re-seeds
versus one edited by hand).

## 3. The patterns, and the instrument that retires each

**P1 — appending a constructor to an alphabet.** `Ty` tonight; `NativeAtom` at L3 (twelve);
`NativeOp` at L4 and L7; `Eff` at records/variants. Today's cost is §2's first four rows.
Retired by: the relational view (`Ty.args` with variance, `sameHead`, `litRule`, `topRule`, and
the one law `sub_eq_args`) so the order's proofs never name a constructor; `AdmitsSub` on the
`hasTy` fold so monotonicity is one generated field per constructor and one hand line; the
compiler's own `Ty.sub.induct_unfolding`; `#exhaustive_gate` printing, before you start, every
definition that will break; the closure manifest and the engine's constructor-count pin so the
runtime cannot fall silently behind; a case-site re-seed as a `make` target. What remains is what
should remain: a declared variance line, a wire tag, a `Metadata` sample, and a decision per
classifier.

**P2 — the classifier catch-all.** DI-95 tonight; `renderRaw` and `Val.hasTy` are the two
*decided* ones in the policy. Retired by the rule (wildcards in proofs, explicit negatives in
classifiers), `#exhaustive_gate`'s inventory (a definition without a catch-all is *meant* to
break), and the case-site policy as the ratchet that already exists. Add the rule to
`docs/core/decisions.md` beside the wildcard rule for proofs, which it completes.

**P3 — the same lemma at every row.** `step_typed` (ten identical arms), `nativeAtom_typed`
(twenty blocks), the seven `sub_*_of_ne` scripts, the `syncOpStep_*` arm equations. Retired by
saying the shape once: `refStepOf` + a kernel table + one theorem; `Scheme` + `sound_of_mono`/
`sound_of_shape`/`sound_of_poly`; the decided table fact (`table_fact`, which `Read.lean` already
uses); frame lemmas as generated proof terms. A dispatcher tactic (`row_step`) only for the arms
that are genuinely different, failing loudly when the named equation is absent.

**P4 — one unnamed aesop bank.** ~90 rules in `default`, the checker's definitions among them,
paid by every call. Retired by seven named banks, `Effect4.Checker` moved out first as `norm
unfold`, a red control per bank, `#auto_census` to measure what a bank buys before a proof is
rewritten, and a per-module time pin from `aesop.stats.file` that may only fall.

**P5 — regeneration order and drift.** Roots inside "Do not edit" headers; a two-pass `make gen`;
the engine mirror recording a divergence instead of refusing it; the LCNF outputs re-cut only by
the nightly; a policy and two docs gone stale; the `Ty` olean order. Retired by one ordered
`make gen` that reaches its fixpoint in a pass, `ocaml/gen/roots.json`, a committed closure
manifest in `GENERATED_PATHS`, `frontier` fatal, the mirror raising unless a family is in a signed
allowance, `make gen-lcnf` in the `check-ocaml` job, `make cases-seed`, the proof-shape ratchet,
and the citation gate over the variance table.

**P6 — hand-transcribed faces.** The TS prelude, `Emit.tyO`, `e4_program.ml`, `cas/e4_shape.ml`.
Retired by `Spec.ts` and a prelude generator group; one `Target.Layout` object both OCaml
pipelines project; the runner plan's step 1 (`Api.ofBytes` as an engine root) which deletes the
hand copies rather than generating them.

**P7 — the template calculus, twice.** Rows and atoms share `Ty.var`/`infer`/`matchTemplate`; the
atoms need `inferJoin`; the rows need anchored completeness at L4 (`Ref.setAndGet` repeats a
variable); two side conditions decide over the closed table; the guard should normalise the
instantiated template. One calculus, two consumers, and the laws proved once.

**P8 — totality frames.** `hasTy (.list t)` admits two frames (`Val.list` and the fiber snapshot);
a naive list atom breaks `evalTerm_isSome`. Retired by `Val.asList?` and `Val.hasTy_list_inv`
with the snapshot counterexample as a red control — one deep helper that absorbs the next
`ctor`-framed list for free.

## 4. What the research settles, where the seats disagree, what I checked

**Four points of convergence, independently reached.**
1. The atom table is first-order data and `eval` stays a `match` on the enum (atoms §1.2, LCNF
   §4(v), proof-engineering §3.4): a function field loses the jump table, the exhaustiveness
   error and `DecidableEq`, and reaches `lcnf_unknown` one refactor later.
2. The checker stays out of the runtime closure; `NativeOp.kind` is split off `row` so `Row` and
   `Ty` leave it entirely (LCNF §3(d); atoms §6.2 "the typing half is free of LCNF constraints").
3. Named aesop banks, with `Effect4.Atoms` and `Effect4.TyOrder` the first two consumers (atoms
   recommendation 2, proof-engineering §2).
4. Variance is declared once, as data, and the order's laws are proved once over it (types §2,
   proof-engineering §1.2).

**Two shapes for the same idea, and the reconciliation.** The types seat proposes a *new* `sub`
over a `Head`/`view` with `subArgs` and a `Head.base` table (§2.2); the proof-engineering seat
proposes a *view over the existing* `sub` — `Ty.args`, `sameHead`, and the law `sub_eq_args`
(§1.2). Take the second: `sub`'s equations do not move, the 35 unfold sites and the eleven
`sub_*_of_ne` lemmas are untouched, and the law is checked against the definition rather than
replacing it. Keep the first seat's `Head.base` idea as the home of the exceptional rules if a
numeric tower ever arrives. Both need the same generated variance input; both say generate it.

**One disagreement on timing, resolved by the owner's steer.** The types seat would do the view
*with* records/variants (row 2), not now (§2.6); the proof-engineering seat says now, because L2's
oracle needs the three `hasTy` laws monotone and L6/L7 and row 2 are the next constructors, each
paying the same bill (§0.2, recommendations 4–5). The owner's steer is tooling before building.
**Now.**

**One on sequencing the atoms, compatible.** The atoms seat would write the four L4-blocking atoms
by hand first and build `Spec`/`Scheme` after, so the table refactors a working thing; the
proof-engineering seat would land `#atom_table_check` before L3. Both: the structural check is
cheap and decides only arity/name/coverage; the scheme language lands after the four atoms show
`inferJoin` is right.

**Corrections the seats made to the tree's beliefs, verified.** TypeScript infers `unknown`, not
`never`, for an unconstrained parameter; `never` remains right here because the bottom only makes
the guard harder (types §3.2). `initialize` is not a forbidden token: the binder form is a
bodiless `opaque` (refused, so no environment extensions), the binder-free form is a plain `def`
(allowed, so a deriving handler is possible); R1's `typed_position` command cannot land and the
table-as-data it replaces is better (proof-engineering §6). "Nested loses every induction" is
overstated: structural recursion through a nested `List` works; what is lost is derived equality,
a non-`partial` `Repr`, and the induction tactic's hypotheses (types §0).

**Corrections to the seats, from the tree.** `fun_induction` does appear once in src
(`Schema/EffectfulField.lean:58`), over a byte-array loop; the seat's point stands for every `Ty`
function. The proof-engineering note counts ~210 aesop invocations; a tactic-position grep tonight
finds ~397 across the Laws (docstrings excluded, `<;> aesop` and `· aesop` included) — the cost of
the default bank is larger than the note says. The LCNF seat assumed `make check-cases` red; it is,
with the rows in §1.

**Verified tonight in the tree:** the codec wildcard (DI-95); the checker's definitions in the
default `norm simp` set; zero `declare_aesop_rule_sets`; `Val.hasTy` registered as a fold
(`Folds/Ty.lean:34`), which is what makes `AdmitsSub` possible; the chain green through the engine.

**Still assumed, and to be tested first:** that `sub_eq_args`'s single generated proof closes over
400 constructor pairs (fallback: one lemma per congruence arm plus a dispatcher); that
`fun_induction Ty.sub` with `generalizing c` is workable; that `refStep_eq_refStepOf` closes by
`cases o <;> rfl`; that `declare_aesop_rule_sets`'s module needs one audit entry and not more;
every size in §5.

## 4b. The sources on disk, and the API shapes to take from them

The seats cite their sources; the owner's steer is to go to them. What is **on this machine** and
was opened tonight, with the shape each one gives us:

**rc.112 declares variance at the declaration site, in the source we vendor.** `Fiber<out A, out
E>` (`Fiber.ts:70`), `Ref<in out A>` (`Ref.ts:59`), `Deferred<in out A, in out E>`
(`Deferred.ts:58`), `Cause<out E>` (`Cause.ts:75`), `Effect<out A, out E, out R>`
(`Effect.ts:117`), `Layer<in ROut, out E, out RIn>` (`Layer.ts:54`), `Queue<in out A, in out E>`
(`Queue.ts:303`), `PubSub<in out A>` (`PubSub.ts:64`), `Stream<out A, out E, out R>`
(`Stream.ts:122`), `Context<in Services>` (`Context.ts:617`). That is the variance table, already
written, by the library whose semantics we lower into — measured tonight: 153 of the 373 generic
`export interface`s in rc.112 declare `in`/`out` on at least one parameter, and 26 carry a
`Variance` marker namespace. So `tools/Effect4Gen/variances.json`
(D-C) should not be hand-declared: a small reader over `vendor/effect-4.0.0-rc.112/src/*.ts`
emits it with the `file:line` as the citation, and the proof-engineering seat's fourth risk
("the variance input becomes a second source of truth about rc.112") disappears — the input *is*
rc.112. The service carriers of L7 (`Queue`, `PubSub`) get their variance the same way, before
anyone writes a `sub` arm for them.

**TypeScript 5.9.2's checker is on disk as data** (`ts/eff/node_modules/typescript/lib/typescript.js`):
`getVariances`/`getVariancesWorker` (`:71785-71791`, variance *computed* by probing marker
types where it is not declared, `VarianceFlags` at `:6550`), `isTypeAssignableTo` (`:68403`),
`getTypeListId` (`:64615`, interning by argument list), `removeSubtypes` (`:65855`, optional
subtype reduction with a work cap), `getInferredType` (`:73750`, two candidate sets by variance,
join of the lower bounds), `getDefaultTypeArgumentType` (`:73785`, `unknown` when unconstrained).
Two things to take. (1) *The shapes*: a union as an id-sorted set with reduction as a separate
pass; inference as constraint sets by variance solved by join; a type reference as head plus
argument list — our `Ty.args`/`sameHead` view is exactly TypeScript's `target` + `typeArguments`
read through variance. (2) *The oracle*: the checker itself can decide our order. Print each
`Ty` to its TypeScript spelling (the printer already does, `Codegen/Types.lean`) and ask the
checker whether one is assignable to the other; compare with `Ty.sub`. The vectors exist — the
1,330 unary and 3,249 pair `Ty` vectors of `tools/Conform/Effect4/LcnfSemantics.lean` — and the
truth harness already drives `tsc` on printed programs (`harness/truth`; `tsc` is in
`ts/eff/node_modules/.bin`). That is a
*differential for the type algebra against the target's own semantics*, the same instrument the
corpus lane is for programs, and it makes "typing rock solid" a measured claim: every
disagreement is either our incompleteness (§4, `option (a|b)`), a deliberate cut (`never` for an
unbound parameter), or a defect. Add it as Tier 1.10, with the mutation red control (swap one
`sub` arm; the differential must catch it).

**Lean's own deriving handlers are the template for "a law per constructor".**
`Lean/Elab/Deriving/LawfulBEq.lean` is 58 lines: `mkInductArgNames` (`:26`), per-constructor
alternatives, one macro tactic, `registerDerivingHandler` (`:55`) — and the binder-free
`initialize` it uses is allowed under our gate (proof-engineering §6.1). `DecEq.lean` (295 lines)
and `Repr.lean` (137) show how a handler walks a mutual block and where it gives up (nested →
refuse; nested or mutual → `partial`). The `TyView` generator (1.4) and `AdmitsSub` (1.5) should
copy this structure — header from the inductive, one alternative per constructor, one dispatcher
tactic — whether they live in `tools/Effect4Gen` (emitting text, as the tree does today) or as a
handler. `Lean/Meta/Match/Match.lean:151-180` (the splitter: a catch-all is one case with
negative hypotheses) and `Lean/Meta/Tactic/FunInd.lean` (`induct_unfolding`) are why the order's
proofs can stop naming constructors at all.

**Lean's LCNF mono phase is the fragment**, and the OCaml pipeline already lowers it
(`Lean/Compiler/LCNF/Passes.lean:66-72`, `saveMono`). The TypeScript emitter (Tier 5) lowers the
*same* decls; the accepted-fragment predicate (LCNF §4(i)) is the shared contract. Where the
OCaml side needed `Nat` as a saturating `int` and `Array` as a list, the TS side needs
`bigint`/`number` and a tail-call policy — profile rows, not new machinery.

**Off disk, and worth reading in the order they pay:** GHC's `primops.txt.pp` + `genprimopcode`
(one declarative file → datatype, name table, typing function, manual: the `Spec` row's model);
LLVM `Intrinsics.td` (`LLVMMatchType<0>` is `Ty.var` bound at first occurrence) and TableGen (a
table in the compiler's language projected to every face); Isabelle's BNF package (the relator
`rel_F` and `rel_OO` composition are `Ty.args` and `args_trans` under their proper names);
Pierce–Turner local type inference (the algorithm `rowTy` is an instance of); Dolan's algebraic
subtyping (why polarity, not first occurrence, binds a variable that occurs twice); Emir et al.
on declaration-site variance (the model rc.112 follows); Reynolds' defunctionalization (what the
atom table *is*); Frisch–Castagna semantic subtyping (the only route that closes the
`option (a|b)` gap, and why we decline it).

**What is unique here, so the stealing stays honest.** None of those systems has all four of:
the program as first-order data with a digest; a type algebra that is a Lean inductive whose
every reader is a fold with a proved connector; a fiber machine proved against a reference and
lowered by LCNF to a native engine; and a printer/reader pair proved exact against a TypeScript
image that runs on Effect's own runtime. The API shapes we take must keep those: first-order
carriers (types §6.3), tables as data with decided facts, typing in Lean and out of the engine,
faces generated from one declaration. Every item in §5 was checked against that list.

## 5. The plan: tooling first, in dependency order

Each item names the chore it retires (§3), a size (assumed), and the red control that makes it
trustworthy. Narrow builds throughout; one compiler; commit by explicit paths; no `sorry`,
`partial`, `native_decide`, `implemented_by`, `extern`, `axiom`, bodiless `opaque`.

### Tier 0 — close the night honestly (hours)

| # | do | retires | red control |
| --- | --- | --- | --- |
| 0.1 | DI-95: `isSupported` lists `.refOf _ \| .deferredOf _ _ \| .var _ \| .unknown => false` beside `.handle`/`.fiberOf`/`.int`; narrow build `Effect4.Schema.Codec` and its dependents | P2 | `#guard isSupported .unknown = false`; the policy row then absorbs nothing new |
| 0.2 | `make cases-seed`: the Audit `--seed-policy` run plus tonight's merge (keep `note`s and `unlisted`), moved from the scratchpad into `tools/Conform/`; run it; sign the diff; `make check-cases` green | P5 | a policy with a note must keep it byte-for-byte through a re-seed |
| 0.3 | commit L5 by explicit paths (the owner's call — see D-A) | — | the chain's log |
| 0.4 | the stale documents: `ocaml/gen/NOTES.md:255`, `ocaml/engine/externs.txt:157-162` (division *is* guarded), `docs/core/lcnf-route.md:58-59,111` and `docs/GENERATED.md:48` (what the checks deliver), `Typed/Vocabulary.lean:5-7` (`typed_position` never landed) | P5 | citation gate |
| 0.5 | the two constructor lists: `syncOpOf_validIn` → trailing wildcard; `sound`'s non-straight arm last and `_` | P1 | a new straight constructor fails at the arm, not at a missing case |
| 0.6 | `join_unknown`, `CTy.le_unknown`; the carrier rule (first-order, non-dependent, proof-free, every field a `Shape`) in `Ty.lean`'s header; the wildcard/classifier rule in `docs/core/decisions.md` | P1, P2 | — |
| 0.7 | `e4_program.ml of_ty`: the four missing arms and a generated arity pin, marked as a stopgap the runner plan deletes | P6 | the pin goes red on the next append |

### Tier 1 — typing rock solid: the instruments that change the cost of every later step

| # | do | retires | size | red control |
| --- | --- | --- | --- | --- |
| 1.1 | declare the seven aesop banks (`Effect4.Inversion` default, `TyOrder`, `TypedState`, `Rows`, `Atoms`, `Reader`, `Checker`) in `Laws/Auto/RuleSets.lean`; move nothing; let the gate say whether one audit entry is owed | P4 | an hour | — |
| 1.2 | move the checker's definitions out of `default` into `Effect4.Checker` as `norm unfold`; one commit; narrow build of the Laws; announce to seats | P4 | a day of fallout | one theorem that closes only with the bank; the same statement with `-Effect4.Checker` must fail |
| 1.3 | probe `fun_induction Ty.sub a b` on `sub_trans_core`; read what the splitter gives | P1 | half a day | decides 1.4's shape |
| 1.4 | the `TyView` generator group: `Variance`, `Ty.args`, `sameHead`, `litRule`, `topRule`, `sub_eq_args`, `sameHead_*`, `args_congr`, `sizeOf_args`, `eq_of_sameHead`; variance input `tools/Effect4Gen/variances.json` citing `Ref.ts:59`, `Deferred.ts:58`, `Fiber.ts:70`; the generator *verifies* each `sub` arm is the variance-wise comparison or refuses; rewrite `sub_trans_core`, `sub_antisymm_normal`, `sub_normalize_of_sub` | P1 | ~250 lines emitter, ~80 of proof | a fixture constructor whose arm compares out of order must make the generator refuse |
| 1.5 | `AdmitsSub` (generated, one field per constructor) + `cata_admits_sub` (proved once) + `Val.hasTy_admitsSub` (14 hand lines); `hasTy_sub`, `hasTy_normalize`, `hasTy_mono` as applications; eleven call sites | P1; **L2's oracle monotonicity for free** | ~150 lines | the sixteen `first` blocks of tonight delete |
| 1.6 | `#exhaustive_gate Ty` (and `NativeAtom`, `NativeOp`, `Eff`): definitions without a catch-all as an inventory printed by `make`, a gate on definitions, never on proofs | P1, P2 | ~150 lines meta + fixtures | the three fixtures of proof-engineering §3.1 |
| 1.7 | the proof-shape ratchet: the trust gate's tokenizer counts `first`/`simp_all`/`try` per module into `generated/proof-shape.tsv`, pinned, may only fall | P4 | a day | a planted `first` in a fixture must exceed its pin |
| 1.8 | templates: `templateAdmissible` and `Row.wellScoped` by `decide` beside `row_closed`; `(instantiate σ' template).normalize` in the guard with `sub_normalize_of_sub`; `sub_sound` and `sub_not_complete` as named theorems and a register row | P7 | a day | `matchTemplate_closed` pins today's behaviour on closed rows |
| 1.9 | `make check-aesop`: `aesop.stats.file` → per-module elapsed pin, may only fall; `#auto_census … using aesop (rule_sets := [X])` before any proof is rewritten against a new bank | P4 | a day | the pin, and the census report |
| 1.10 | the assignability differential: print each of the 1,330 unary and 3,249 pair `Ty` vectors to TypeScript, ask the on-disk checker (`isTypeAssignableTo`) and compare with `Ty.sub`; classify every disagreement (incompleteness, cut, defect); run in `check-host` beside the truth harness | typing measured against the target's semantics (§4b) | three days | a swapped `sub` arm in a scratch copy must be caught; the sensitivity count printed |

### Tier 2 — atoms rock solid

| # | do | retires | size | red control |
| --- | --- | --- | --- | --- |
| 2.1 | `#atom_table_check`: `atomWellFormed` decided by `decide +kernel` over `NativeAtom.all`; `all` generated from the constructor list, `all_complete` kept as the acceptance guard | P3 | ~80 lines | an atom whose `arity` and `mono` disagree must fail the decide |
| 2.2 | the `Effect4.Atoms` bank: `Fits.singleton_inv`, `Fits.pair_inv`, `Fits.all_sub_string`, `Val.hasTy_nat_inv`/`_bool_inv`/`_string_inv` | P3, P4 | an hour | the bank's red control |
| 2.3 | `Ty.inferJoin` + its law (the guard is the law, as for `infer`); `Val.asList?` + `Val.hasTy_list_inv`; the `Nat.mul` clamp in `Translate.lean:161` | P7, P8 | two days | `nativeAtom "length" [Val.fibers [0]] = some (.nat 1)`; `Ty.sub (.prod .nat .nat) (.list .nat) = false` |
| 2.4 | the four L4-blocking atoms by hand in the present shape (`ite`, `some`, `none`, `mul`), soundness in the bank | L4 unblocked | a day | the four `#guard`s of atoms §5.1 |
| 2.5 | `AtomRow` (runtime half: name, arity, constGeneric, prelude line) with `ofName?` a `match` on the string; `Spec`/`Scheme` (typing half) with `sound_of_mono`/`sound_of_shape`/`sound_of_poly`; `nativeAtom_typed` as `cases atom <;> first-free dispatch`; the TS prelude atom block as a generator group (D-E) | P3, P6 | a week | `#guard typeOf .pair [.lit "A", .string] = some (.prod (.lit "A") .string)`; the prelude self-test |
| 2.6 | then L3 as rows: `nil`, `cons`, `get`, `length`, `append`, `sub`, `div`, `mod`, `concat` (twelve in all); deferred with reasons: `head`/`tail`/`isEmpty`, `le`/`gt`, `strLength` | — | a day each at first, an hour each after 2.5 | one `ProofWanted` per atom named by 2.1 |

### Tier 3 — the typed state and the rows, before L4

| # | do | retires | size | red control |
| --- | --- | --- | --- | --- |
| 3.1 | `refStepOf` + `SyncOp.refKernel` + `refStepOf_typed` + `refStep_eq_refStepOf`, *added beside* `refStep` (thirteen census receipts stay); `step_typed`'s twelve heap arms become one | P3; **L4's thirteen rows become thirteen kernel lines** | ~120 added, ~130 deleted | a kernel row that disagrees with its `refStep` arm must fail the `rfl` |
| 3.2 | `row_step`/`row_steps` for the twelve different rows, failing loudly without `syncOpStep_<ctor>` | P3 | a day | a row with no arm equation must error by name |
| 3.3 | frame lemmas as generated proof terms (amend R4); a clause reading another field promotes to an obligation | P3 | two days | the two-field fixture |
| 3.4 | the obligation ledger: `ProofWanted` placeholders built from `Expr`, joined by `Census.attempt` (amend R3), found by type head | P3 | three days | the three fixtures of proof-engineering §3.2 |
| 3.5 | `NativeOp.kind` split off `row`; `row`'s `kind` field defined as `kind op` | P1, LCNF (d) | half a day | the closure manifest no longer lists `Ty` |
| 3.6 | `ocaml/gen/roots.json`; header lines rendered from it | P5; **unblocks `FnName`'s retirement** | half an hour | a root removed from the json regenerates cleanly |
| 3.7 | designed into L4's generator change, not after it: `Signature.scopedOp`, the `perform` arm of the scoped algebra, the red control `Eff.scopedAt 1 (.perform (.refUpdate (.var 5)) (.var 0)) = false` | atoms §3.5's silent defect | with L4 | the `#guard` |

### Tier 4 — drift, the engine, the corpus

| # | do | retires | size |
| --- | --- | --- | --- |
| 4.1 | the closure manifest per LCNF output in `GENERATED_PATHS`; `frontier` fatal; cap headroom printed | P5 | a day |
| 4.2 | the mirror raises unless the family is in a signed allowance; `$(GEN)/lcnf` before `$(GEN)/eff` so one `make gen` reaches its fixpoint; `make gen-lcnf` in the `check-ocaml` job | P5 | a day |
| 4.3 | `Ml.checkModule` fatal for the three unseamed outputs; the prelude declares its exports; then fatal for the engine | P5 | two days |
| 4.4 | `Metadata`'s condition inverted: every family the corpus cannot reach must be named by a fixture | P5 | an hour |
| 4.5 | Lean's run answers (outcome, fiber count, exit as canonical bytes) in `generated/corpus-index.tsv`; `cross_face` gated on exit bytes; the mutation-must-fail control with its sensitivity count; the 20,387-vector lane wired into `check-host` | P5 | a week; pin a stated subset if the run is slow |
| 4.6 | the builtin table to a file with fidelity and domain columns, so a row's class is data the conform profile can mutate | P5 | two days |

### Tier 5 — after, in order

The runner plan's step 1 (`Api.ofBytes`/`bytesOf` as engine roots; deletes `e4_program.ml`, the
layout mirror and its script, `e4_shape.ml`'s hand table). One `Target.Layout` object both OCaml
pipelines project, as a strict refactor with no diff on the fourteen generated files. The
TypeScript reader's seam split now (`read-parse.ts`/`read-table.ts` at the `TypeScript.Expr`
boundary), the emitter after `Target.Layout`, with the tail-call policy decided first. Records and
variants as a mutual `Fields` spine (row 2) with the view in place; `Ty.foreign` in place of
`Ty.app`. `collect`/`solve` with anchored completeness at L4. The ruling on `Term.app : NativeAtom`.

### The language ledger, re-cut on top

L2 `hasTyWith` for the proofs, runtime `hasTy` concrete, connected by a lemma; the laws generalise
through `AdmitsSub` (1.5). L3 the twelve atoms (2.4, 2.6). L4 `Row.fn`/`rowTyFn` with the term
typed at `tys ++ [param]`, `printRow` with `n` and `Option Term`, the reader's `binder` refusal,
`FnName` retired after 3.6, thirteen kernel lines after 3.1, the scope fix 3.7, prelude finding F3
closed. L6 faces. L7 service carriers, after 4.4 so the new families are covered by construction.

### 5b. The build must improve: what each tier retires

The owner's rule: a gate is not a virtue; an instrument that does nothing goes, and the build
must get faster as the abstractions get better. So every tier above deletes as it adds, and the
one number that may not rise is the wall time of `make check` and of `lake build Effect4.Laws`.

| added | retired or shrunk, in the same slice |
| --- | --- |
| named aesop banks (1.1, 1.2) | the checker's definitions leave `default`: ~397 calls stop unfolding `check`; measured by `aesop.stats.file`, and the Laws build time is the receipt |
| `TyView` + `sub_eq_args` (1.4) | the eleven `sub_*_of_ne` lemmas, the `first` alternatives in three proofs, and the arm enumerations; the proof-shape counts fall |
| `AdmitsSub` (1.5) | ~150 of `hasTy_sub`'s 214 lines, tonight's sixteen `first` blocks, and the re-proofs L2 would otherwise add (three laws of 200/40/50 lines) |
| `#exhaustive_gate` (1.6) | runs inside the existing traversal-census battery (`Test/Audit/TraversalCensus.lean`), not as a new `make` target; it replaces reading the compiler's errors one at a time |
| the proof-shape ratchet (1.7) | computed by the tokenizer the trust gate already runs; no new build work |
| `make check-aesop` (1.9) | numbers from a build that had to happen (the incremental rule); it exists to let `#auto_census` **delete** proofs the bank closes — measure, then delete |
| the assignability differential (1.10) | lives beside the truth harness in `check-host`; nothing new in `check` |
| `Scheme` + `sound_of_*` (2.5) | `nativeAtom_typed`'s 165 hand lines; `mono`, `constGeneric`, `name`, `arity`, `names` as separate matches; the hand prelude block |
| `refStepOf` (3.1) | ~130 lines of `step_typed`; L4's thirteen proof arms never written |
| the closure manifest (4.1) | `check-gen-full`'s nightly re-cut becomes a hash comparison in `check`; the LCNF outputs regenerate in the job that builds the OCaml, not a second lane |
| the mirror raising (4.2) | *and then* the runner plan's step 1 deletes `e4_program.ml`, `e4_program_layout.{ml,json}`, `scripts/generate-engine-structure.py`, the ordinal pin and the manifest check — a gate, a script and 600 hand lines gone |
| wiring the 20,387 lane (4.5) | or deleting its three drivers: an unwired lane is a dead gate; decide (D-K) |
| `Ml.checkModule` fatal (4.3) | or removed: an informational check nobody reads is a dead gate |
| `Metadata` inverted (4.4) | the nine-name exclusion list stops being maintained by hand |

Two standing instruments for the rule itself. (1) `generated/check-times.tsv`: wall time per
`make check` target and per Lake build of the Laws, written by the runs that already happen,
committed, and read at review — not a gate, a ledger, because a time pin that fails on a slow
laptop is noise; the review reads the trend. (2) The test ledger of 2026-09-13 (memory: verdicts
for every check and test file) is resumed: each Tier 0–4 slice names the batteries it makes
redundant and deletes them in the same commit. The candidates already known: the three unwired
LCNF drivers; the informational `checkModule` print; the engine-mirror script and its check; the
`.ty`-only corpus verdicts once run answers are recorded; any `Test/` battery whose statement a
generated law now proves (found by `#auto_census`).

- **D-K.** The 20,387-vector lane: wire it into `check-host` (one profile entry, one rule) or delete
  `tools/Conform/Cli/{LcnfMl,LcnfSemantics}.lean` and the fidelity driver. *Recommend wire, because
  1.10 reuses its vectors; delete if 1.10 supersedes it.*
- **D-L.** Is the `check-times` ledger enough, or does the owner want a hard budget on `make check`?
  *Recommend the ledger, reviewed each cycle; a budget after the tiers land and the number is known.*

## 6. Decisions for the owner

- **D-A.** Commit L5 now as it stands (builds green, policy red, DI-95 open), or after 0.1 and 0.2
  as one commit whose policy diff is true? *Recommend the latter: two small steps, then the commit.*
- **D-B.** The relational view as a view over the existing `sub` (proof-engineering §1.2), now,
  before any further constructor. *Recommend yes.*
- **D-C.** The variance table lives in `tools/Effect4Gen/variances.json` with rc.112 citations
  under the citation gate. *Recommend yes.*
- **D-D.** The proof-shape ratchet is a gate pinned at tonight's counts, not a report.
  *Recommend gate.*
- **D-E.** The TS prelude's atom block is generated from `Spec.ts`. *Recommend yes; the file's
  own header asks for it.*
- **D-F.** `Term.app` carries `NativeAtom` (wire name mapped at the codec). *After the push, its
  own slice.*
- **D-G.** The typed-state source table's expectation becomes a typed projection (proof-engineering
  D-1). *Recommend yes, while it is 90 rows.*
- **D-H.** Amend the metaprogramming review: R4 frame lemmas as proof terms; R3 the witness join
  by `Census.attempt`; R1's `typed_position` dropped. *Recommend all three.*
- **D-I.** Still owed from the plan: records/variants (now: the `Fields` spine after 1.4),
  `int`/`float`, `Err.value`.
- **D-J.** The deferred atoms (`head`/`tail`/`isEmpty`, `le`/`gt`, `strLength`) stay deferred
  with the seats' reasons. *Agree.*

## 7. Review checklist, for the cycle that follows this note

1. Is each Tier 1–3 item's red control stated, and would it actually fail on the defect it guards?
2. Which claims in §4 are verified and which assumed; is any assumed claim load-bearing for the
   order in §5?
3. Does any item change the wire, a golden, or a census receipt without saying so? (3.1 says no;
   2.5 changes `nativeAtom_typed`'s shape; D-F changes `Term`'s tags.)
4. Are the dependencies right: 1.3 before 1.4; 1.4 before 1.5; 1.5 before L2; 3.1 and 3.6 before
   L4; 2.3 before the list atoms; 4.4 before L7?
5. Is anything here a shortcut? The only one I see is 2.4 (four atoms by hand before the table),
   and both seats argue for it.
6. What in §2 is *not* explained by a pattern in §3 — is there a chore this note missed?

## 8. What I would not build

A bespoke `(Ty, Ty)` eliminator (the compiler derives one). The `sub_*_of_ne` arm lemmas (the law
subsumes them). Anything proof-repair shaped (a new constructor is not an equivalence). An
environment extension, a custom attribute, or `typed_position` (the gate forbids the binder form
and the table is better). A `row_step` tactic as the *primary* answer to `step_typed` (twelve of
twenty-four arms are the same arm). `eval` as a record field. The checker in the OCaml closure.
Widening `Metadata` by hand. A `Row (String × Ty)` inside the carrier. `Ty.app`.

## References

The four research notes above; `docs/research/2026-09-18-rows-42-43-plan.md` §2c–§2d;
`docs/DESIGN-ISSUES.md` DI-94, DI-95; `docs/core/decisions.md` rows 42–47, 55. Verified tonight:
`src/Effect4/Schema/Codec.lean:45-49`, `src/Effect4/Laws/Program/Typing/CheckInversion.lean:39-41`,
`src/Effect4/Program/Folds/Ty.lean:34`, `src/Effect4/Schema/EffectfulField.lean:58`,
`tools/Conform/Effect4/cases-policy.json`, `.lake/conform/cases.json`, the chain log
`l5-build4.log` (scratchpad).
