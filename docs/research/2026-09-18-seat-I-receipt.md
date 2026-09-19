# Seat I receipt — instruments and gate removal (tooling-first wave)

Branch `worktree-agent-a14ec064f4f005f55`, from `4b4e6aa3` on `refactor/phase1-phase3`.
Dispatched items: 1.6, 1.7, 0.10, 0.4, 0.7, 4.8/4.9 and the Q4–Q6 rulings. Stopped by the
owner's wrap-up instruction after 1.6 and 1.7; 0.10 is applied in the working tree but not
committed, and 0.4, 0.7, 4.8/4.9 and Q4–Q6 were not started or not finished. Everything owed is
under **Not done**, with what the next seat needs.

**Setup note, before anything else.** The worktree was created at `9187b9b6`, not at the base
the brief names. The tree was clean, so the branch was moved with
`git switch -C worktree-agent-a14ec064f4f005f55 4b4e6aa3`; nothing was discarded. `.lake` was
seeded by `rsync` from the main checkout, which is at the same commit, so the first build
replayed instead of compiling the closure.

## Commits

### 1. `897e45b1` — `#exhaustive_gate`, the inventory of what a constructor costs (1.6)

New `src/Effect4/Laws/Auto/Exhaustive.lean`; new `Test/Audit/ExhaustiveFixture.lean`;
`Test/Audit/TraversalCensus.lean` runs it; `src/Effect4/Laws.lean` imports it; `Test/All.lean`
imports the fixture; `Test/Audit/AxiomGate.lean` gains two exemption entries.

`#exhaustive_gate <Inductive> [under <Namespace>]` walks the definitions of a scope and reports
`holder, module, matcher, discr, alts, catchAll` for every match that reads the named family. A
row with `catchAll false` is a definition the compiler refuses the day a constructor is
appended. Printed report only: no file is written (decisions row 49), nothing fails (row 34).

The catch-all decision is exact and comes from the matcher's own type, as the plan specified: an
alternative is `∀ fields, notAltHs → ∀ eqs, motive p₁ … pₙ` (`mkMinorType`), so the pattern at
discriminant `d` is the `d`-th argument of `motive`, and the alternative catches every future
constructor exactly when that argument is a bound variable of the fields telescope, after
stripping `mkInaccessible` mdata and a `namedPattern x p h`. `MatcherInfo.altNumParams` gives
the telescope length. `matchMatcherApp? (alsoCasesOn := true)` also reads `casesOn`.

**Two corrections the plan's sketch needed, found by building it.**

* The sketch walks into `.lam`/`.forallE`/`.letE` bodies raw and then calls `inferType` on a
  discriminant, which fails with "unexpected bound variable #0". The walk instantiates each
  binder with a real local (`withLocalDecl` / `withLetDecl`) before descending.
* `Traversals.definitionsUnder` drops internal details by design, and a structural recursion
  keeps nothing in the authored constant: `Ty.closed = fun x => Ty.brecOn x Ty.closed._f`, with
  the twenty-arm match inside `Ty.closed._f`. Measured: with authored definitions only the
  inventory found 24 holders and missed `Ty.closed`, `instantiate`, `normalize`, `members`,
  `renderRaw`, `key`, `Val.hasTy` and `Schema.Bridge.schema` — most of what a constructor costs.
  `bodiesUnder` adds each helper, attributed to the definition a person wrote.

Rows are deduplicated by (holder, matcher, discriminant) and the catch-all question is asked
once per surviving row; that took the `Ty` run from 258 raw hits to 51 rows.

**Red controls, exercised.** `#guard_msgs` over `Test.Audit.ExhaustiveFixture` pins all three:
a twenty-arm `Ty` match with no wildcard is reported `catchAll false`; the same match closed by
`| _ =>` is reported `catchAll true`; a match on `Term` is not reported at all. The pin lives in
`Test/Audit/TraversalCensus.lean` and fails the build if the detection changes.

**Today's `Ty` inventory:** 51 matches read it, 22 with no catch-all — `Ty.closed`,
`instantiate`, `isMember`, `isNever`, `key`, `members`, `normalize`, `renderRaw`, `Val.hasTy`,
`Schema.Bridge.schema`, `findInt`, `rawSupportedErrTy`, `Store.ProgramGen.TyC.toValTy`,
`instReprTy.repr`, the generated folds (`cata_ty`, `foldM_ty`, `foldMapAt_ty`, `foldMap_ty`) and
four `.hom` witnesses. `Ty.sub` and `Schema.Codec.isSupported` are reported `catchAll true`,
which is right: both end in a wildcard, and DI-95's ruling is about which *class* a wildcard
defaults into, not about having one.

**Cost, for the 4.7 ledger.** `Test.Audit.TraversalCensus` 19s → 42s for the three inventories
(`Ty`, `Term`, `Store.Val`). It re-elaborates only when the Laws move.

**Also in this commit, and not this item's work.** `lake build Test` was red at `4b4e6aa3`:
`Effect4.Laws.Auto.RuleSets`'s initializer reaches `Classical.choice` through the aesop
environment extension, which the module's own header predicted. The line belongs to tooling plan
1.1 and landed here only because no seat can be green without it; the coordinator confirms seat
A hit the same red and recommended the same line.

### 2. `6d46565b` — the proof-shape ratchet, and one citation scanner instead of two (1.7)

`Test/Audit/AxiomGate.lean`, new `generated/proof-shape.tsv`, new
`Test/fixtures/trust-gate/proof-shape.lean.txt`, `scripts/test-trust-gate.sh`,
`scripts/test-source-trust-tokenizer.sh`, `scripts/check-source-citations.py`,
`scripts/test-internal-citations-gate.sh`, `scripts/source-citations-allowed.txt`, `Makefile`,
`docs/DESIGN-ISSUES.md`, `docs/core/lcnf-route.md`; **deleted**
`scripts/check-internal-citations.sh`.

**The ratchet.** The tokenizer pass counts `first`, `simp_all` and `try` per library source
under `src/`, in the same pass that looks for a trust token. `generated/proof-shape.tsv` is the
ceiling: **94 sources, 730 counted tactics**, taken from the counter's first run.
`#effect4_print_proof_shape` prints the file so re-pinning is a copy-paste.

**Two measured corrections to the plan.**

* "Count `.atom` tokens only" does not hold at this pin. Probed directly: `try` is a reserved
  keyword and arrives as an atom, while `first` and `simp_all` are identifier-shaped tokens the
  tactic parsers match by name and arrive as idents. The counter reads both shapes by raw text,
  so `Foo.first` is one ident named `Foo.first` and is not counted.
* Reading idents gave 775 `first` against 16 real tactics in `Program/Typed.lean`, because
  `first` is also a binder name in this tree (`intro raw first second` in the optic and
  annotation laws; `Census.attempt`'s own parameter). The tactic's syntax is
  `"first" ("| " tacticSeq)+`, so `first` is counted only when the next token is `|`. That gives
  336, against 337 for a multi-line grep of `first\s*|` — the single difference is a `first` in
  a comment, which the tokenizer skips and grep does not. `simp_all` (120) and `try` (274) agree
  with grep exactly.

**Ratchet policy, as implemented.** A count above its row fails. A count below passes and the
summary says by how much, because blocking a seat for improving a proof is friction with no gate
behind it. Two staleness teeth: a source with a counted tactic and **no row** fails, so a new
module cannot arrive under the radar; a row whose source no longer exists fails.

**Red control, exercised.** `Test/fixtures/trust-gate/proof-shape.lean.txt` holds one
`first | …`; `scripts/test-trust-gate.sh` plants it in a probe copy of
`src/Effect4/Store/Shape.lean`, whose `first` ceiling is zero, and requires the refusal "now
holds 1 `first` … pins 0". Run: 16 planted defects rejected, 5 accepted, all other cases
unchanged. The probe tree now also gets `generated/proof-shape.tsv`, for the same reason it gets
`known-red.txt`: the gate reads the pin from the root it audits and a missing one is a gate that
checks nothing.

**The paired retirement.** `scripts/check-internal-citations.sh` is deleted and its question —
no line-numbered citation into a mutable authored document — is the second half of
`scripts/check-source-citations.py`, asked of the lines that pass already reads.
`make check-citations` runs one program; every text file of the nine trees is read once instead
of twice. Agreement where they overlap, measured before the deletion: **2,682 candidate tokens,
seven protected documents, zero violations, both**. The merged pass reads four files more (the
root `AGENTS.md`, `README.md`, `lakefile.toml` and the coverage skill, which the shell never
scanned), and they hold no `path:line` token. All seventeen cases of
`scripts/test-internal-citations-gate.sh` pass against a new `--internal-only`, and all eight of
`scripts/test-source-citations.py`.

One scoping decision inside that: the "extracted no citation tokens at all" tooth is asked of
this repository and of any tree given to `--internal-only`, and not of a foreign tree scanned in
full mode, which may legitimately hold none — `test_allowance_is_exact`'s three-file tree does.
Both suites pass with the tooth as scoped.

**`make check-citations` was red at `4b4e6aa3`; it is green here.** Checked against the scanner
at HEAD: the same nine unresolved paths and three unmarked research notes fail before and after
the merge, and `generated/citation-baseline.txt` does not exist in the tree at all (so the
baseline was empty and every miss failed). Fixed what this seat owns — the three
`(untracked working note)` markers in `docs/DESIGN-ISSUES.md`, and `docs/core/lcnf-route.md`'s
three short spellings of `tools/Conform/Effect4/Lcnf*.lean` — and named the other six in
`scripts/source-citations-allowed.txt` with a reason each: the emitter named by decisions row 49
that was never written under that name, two planned MCP modules named by
`docs/core/api-surface.md`, the layout specification held outside the tracked tree, the `effect`
package manifest that `bun install` provides, and the timer workshop. Final:
`3726 citation tokens examined; 0 baselined missing targets`. **This is the precondition for
4.8 putting the lane in CI, and it is done.**

### 3. `230c8180`, and this commit — the receipt

Force-added; `docs/research/` is gitignored.

## Not done, and what the next seat needs

### 0.10 — the cite fixes: applied in the working tree, **not committed**

The Lean half is green (`lake build Effect4 Effect4Laws`, exit 0) and correct; what is missing
is the regeneration, which is several long generator runs and one known two-pass fixpoint — not
"within one narrow build", so nothing was committed. The working tree holds, uncommitted:

* `src/Effect4/Program/Native.lean`: `deferredIsDone` `Deferred.ts:1382` → `:1366`;
  `deferredAwait` `Deferred.ts:173-186` → `:223`; both `scopeMake` arms
  `internal/effect.ts:3914-3922` → `Scope.ts:240`; and a doc comment on `def row` naming, for
  each of the three, the unsafe or private form the machine actually models, plus the two
  answer-column exceptions.
* `ocaml/engine/e4_wake.mli`: `is_done`'s comment now cites `Deferred.isDone` (`:1366`) and
  records that the value is the one `isDoneUnsafe` (`:1382`) computes.
* `docs/DESIGN-ISSUES.md`: **DI-96 … DI-100 registered** in DI-95's table shape (the file now
  holds 101 rows). DI-96/99/100 are the cite errors, ruled by plan 0.10; DI-97 (`deferredPoll`
  answers `bool`) and DI-98 (`refSet` answers the cell) are ruled by Q9 as signed exceptions
  with their content stated, DI-98 scheduled with L4's binder-term rows.

**Verified against the vendored source**, so the next seat need not re-read it:
`Deferred.isDone` is `Deferred.ts:1366` and its body is `sync(() => isDoneUnsafe(self))`;
`isDoneUnsafe` is `:1382`; `poll` is `:1414-1416` and answers
`Effect<Option<Effect<A, E>>>`; the private `_await` is `:173-186` and the public name is the
re-export `_await as await` at `:223`; `Ref.set` is `Ref.ts:306-307` and answers
`Effect.Effect<void>`; `Scope.make` is `Scope.ts:240` and is `effect.scopeMake`, while
`internal/effect.ts:3915-3920` is `scopeMakeUnsafe` and `scopeMake` itself is `:3925-3926` —
i.e. the old span named the unsafe function, not the one the row transcribes.

**The plan names three generated files a cite reaches; there are five.** Measured by grep of
the old span `Deferred.ts:1382`, one occurrence in each: `ocaml/eff/eff_native.ml` (the `eff`
group), `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml` (the `lcnf` group),
**`src/Effect4/Program/Authoring/Rows.lean` (the `derived` group)** and
**`ts/eff/profile.gen.ts` (the `ts` group)**. So the regeneration is `make gen-hermetic` (which
covers derived, eff, wire, cas, ts, readme) **and** `make gen-lcnf`, then a second
`make gen-hermetic` because `api_engine.ml` is an `EFF_SOURCE` and the chain is not a fixpoint
in one pass, then `make check-gen`. A `make gen-hermetic` was running when this seat stopped and
may have left the hermetic outputs regenerated; `git status` is the authority. Nothing on the
branch depends on it.

Also uncommitted from **0.4** (started, then stopped by the wrap-up; each edit is one paragraph
and is correct as written, if the next seat wants to lift it):

* `ocaml/gen/NOTES.md` — the `Nat → int` row said division by zero "is still not guarded"; it is
  (`Translate.builtin?` emits `if b = 0 then 0 else a / b` and `if b = 0 then a else a mod b`).
* `ocaml/engine/externs.txt` — the same claim in the Q6 block, with a stale line citation into
  `NOTES.md`; rewritten to say the translator answers it and the two rows stay `fn?`.
* `docs/core/lcnf-route.md` §3 and §6 — the 20,387-vector differential is evidence produced
  once: the three modules are libraries whose `--run` drivers are named by no `make` target, no
  script and no CI job. What runs on every change is the case-site policy, the validity walk and
  the rewrite rules.
* `docs/GENERATED.md` — the lcnf row's check column: `make check-gen` holds that group against a
  *hand edit* only, because lcnf is not in `HERMETIC_GROUPS`, so a stale output is invisible to
  it; the nightly `check-gen-full` is what re-cuts them.

Still owed by 0.4 and untouched: `src/Effect4/Laws/Auto/TypedSources.lean:8-10`, whose docstring
says the trust gate refuses `initialize`. It refuses only the **binder** form, via the
bodiless-`opaque` check; a binder-free `initialize` is a plain `def` and is admitted — which is
exactly why `declare_aesop_rule_sets` compiles.

### 0.7 — `e4_program.ml of_ty`: not started

Read, not edited. `ocaml/engine/e4_program.ml:120-139` has sixteen arms and a named `failwith`
catch-all at `:139` ("Ty constructor beyond the frozen engine's alphabet"), so the four missing
constructors (`refOf`, `deferredOf`, `var`, `unknown`) refuse loudly rather than raising
`Match_failure`. What is owed is the four arms plus the generated arity assertion
(`List.length Eff_types.ctor_names_ty = 20`), marked as a stopgap the runner plan deletes. Build
with `cd ocaml && opam exec --switch=effect4 -- dune build`.

### 4.8 / 4.9 / Q4–Q6 — the removals: not started, with the survey done

Everything below is measured, not assumed; it is the work, not a plan for it.

**The CI line.** `.github/workflows/lean_action_ci.yml:135` is
`run: make build check-truth check-corpus check-target check-schema-codec check-ingest-smoke`.
Append `check-citations check-tsdiag` by name. Never `make check-host` there: it pulls
`check-ocaml`, whose opam switch only the `check-ocaml` job installs. `check-citations` is green
as of commit 2, so the append is safe now. Line 164 of the same file already runs
`python3 scripts/check-conform.py compiler` by hand in the `check-ocaml` job; the Makefile target
owed is one `$(CHK)/compiler` rule plus `compiler` in `CHECKS` (the profile already exists —
`scripts/check-conform.py` `PROFILES["compiler"]`, nine output files), after which `check-full`
reaches it and the CI step can call the target.

**The seven `$(shell find …)`.** In the tree as this seat leaves it they are `Makefile` lines
50 (`LEAN_SOURCES`), 277 (`CONFORM_SOURCES`), 291 (`CITATION_SOURCES`), 360 (`OCAML_SOURCES`),
400 (`SCHEMA_SOURCES`), 413 (the `schema-host` prerequisite) and 444 (the `check-tools`
fixtures). They run on **every** `make` parse, whatever the goal. The replacement that keeps
each trigger exactly: one marker per set, built by a `FORCE` rule that runs the `find` only when
a check that reads it is in the goal's graph, writing the sorted path list and refreshing its
own mtime when the list changed **or** when `find … -newer $@` reports anything — portable, no
`stat`, one `find` per marker. `$(CHK)/inventory` (Makefile 269-271) is the model but is
deliberately *names-only*, because `check-roots` must re-run when a file is added, removed or
renamed and not on every edit; so keep it, and derive it from the new `$(CHK)/inv-lean` with
`cmp -s || cp`, which preserves that semantics exactly. The other six must be mtime-sensitive,
or checks like `check-cases` stop re-running on a content change.

**`check-compat` (Q5, retire).** Everything the lane owns: the `$(CHK)/compat` rule, the four
`COMPAT_*` variables, `compat` in `CHECKS`, `check-compat` on the `check-host` line, the
`$(PY) scripts/test-compatibility.py` row in `$(CHK)/tools`, `scripts/check-compatibility.py`,
`scripts/test-compatibility.py`, and — not named in the brief, but orphaned by the deletion and
built by nothing today — `scripts/lib/compatibility.py` and `tools/Compatibility/Extract.lean`.
The tracked baseline path on this machine is **`Test/`** with a capital T (`git ls-files` says
so), ten files under `Test/fixtures/baseline/`. Two prose references survive the deletion and
need handling: `tools/Effect4Gen/wire-tags.json` names `scripts/lib/compatibility.py` — that
file is a generator input, so editing it re-cuts everything, and the right move is a row in
`scripts/source-citations-allowed.txt`, which is where the estate already records a removed
script; and `AGENTS.md:21` describes `Test/fixtures/baseline/<commit>/` (no extension, so the
citation gate does not see it) and would become a stale row — `AGENTS.md` is outside this seat's
scope. `docs/GENERATED.md` also mentions "the compatibility snapshot" in prose and is in scope.
`docs/DESIGN-ISSUES.md` DI-47 is the ruling the lane implements and should record the
retirement.

**The three `tools/Conform/Cli` drivers (Q4).** `LcnfMl.lean` and `LcnfSemantics.lean` are
four-line `main` wrappers, referenced by nothing in `Makefile`, `scripts/`, `.github/` or
`lakefile.toml` — delete them; `tools/Conform/Effect4/LcnfMl.lean` and `LcnfSemantics.lean` stay.
**`tools/Conform/Cli/BoundaryControls.lean` must not be deleted.** It is not a driver: it has no
`main`, it is a battery of `run_meta` refusals and `#guard`s over `Conform.Core.Proof` and
`Conform.Layout.Reflect` that *executes* inside `lake build Conform`, which `make build-tools`
and the CI build job run — so the plan's condition "named by a target or retired" is already
met — and it is the named falsifier for `E4-CONFORM-CE-002` in
`Test/Counterexamples/Archive/REGISTER.md` ("a theorem-shaped name is evidence of its requested
law"). Deleting it removes a live red control, which the brief's own standing rule forbids. My
recommendation: keep it, and record that `lake build Conform` is the target that names it.

**The five `Test/contracts/*.contract.md` (4.9).** The five that nothing in the tree links —
measured by grepping every packet's name across all file types — are exactly
`machine-scheduling`, `schema-authoring`, `schema-codec`, `schema-recursor` and
`schema-typescript-generation`. The count matching the ledger's "five" is good corroboration
that these are the ones meant. Two caveats the next seat should weigh before deleting rather
than moving to `Test/contracts/archive/`: every one of the five names an implementation and a
battery that still exist (`Machine/Scheduling.lean` + `Test/Machine/Runtime/SchedulingContract.lean`;
`Schema/Authoring.lean` + `Test/Schema/AuthoringContract.lean`; `Schema/Codec.lean` +
`Laws/Schema/Codec.lean`; the generated `Schema/Fold.lean`; `Codegen/Schema.lean` + the live
harness `scripts/check-schema-typescript-generation.sh`), so they are unlinked, not dead; and
`schema-recursor.contract.md` carries an explicit **owner decision owed** in its own 2026-09-17
amendment ("either re-freeze this packet against the generated module or mark it superseded"),
which a deletion answers by fiat. Near misses deliberately excluded:
`machine-completion.contract.md` (linked from `docs/DESIGN-ISSUES.md`),
`schema-effectful-field-typescript.contract.md` (linked from the live
`scripts/check-schema-effectful-field.sh`) and `faces.contract.md` (linked from four documents).

**Q6 and the `generated/axioms.tsv` item.** Not recorded anywhere yet. Q6's ruling (the 178
inline numeric pins stay, and the ledger item closes) and the drop of the `generated/axioms.tsv`
item (the trust gate's environment walk supersedes it) are two lines in `docs/DESIGN-ISSUES.md`
or the 2026-09-13 ledger's follow-up note. Note that the 2026-09-13 research notes do **not**
exist on this machine (`docs/research/` is gitignored and was not synced), so the ledger's own
text could not be consulted; everything above about it is reconstructed from the plan and from
the tree.

**`generated/tsdiag-agreement.tsv` into `GENERATED_PATHS`.** One entry. Per the coordinator, seat
T2 has already edited the first line of `GENERATED_PATHS` (adding `$(VARIANCES)`), so the new
entry belongs on the **last** line of that variable, after the merge.

## Files touched outside the dispatched scope, and why

* `src/Effect4/Laws.lean` — one `import Effect4.Laws.Auto.Exhaustive`. Without it the
  library-root gate refuses the new module as unreachable, so the item cannot land without it.
* `Test/All.lean` — one `import Test.Audit.ExhaustiveFixture`, required by the standing rule
  that every `Test` module is imported by the audit root.
* `scripts/test-trust-gate.sh`, `scripts/test-source-trust-tokenizer.sh` — the trust gate's own
  red-control harnesses. The first gains the ratchet's planted-`first` case and copies the pin
  into its probe tree; the second follows the rename `forbiddenTrustToken?` → `scanSource`. Both
  are the fixtures of `Test/Audit/AxiomGate.lean`, which is in scope, and neither would run
  otherwise.
* `scripts/test-internal-citations-gate.sh` — retargeted from the deleted shell scanner to
  `--internal-only`; without it the seventeen-case reaction suite would exercise nothing.

## Proposed rows for `docs/core/decisions.md` (not edited by this seat)

1. **The exhaustiveness inventory is an inventory.** `#exhaustive_gate` prints; it never writes
   and never fails. The gate over default arms is the compiled-LCNF case-site policy. Read the
   inventory before appending a constructor; the number of `catchAll false` rows is the bill. It
   walks the helper a recursion's body was moved into (`f._f`), attributed to `f`, because a
   structural recursion keeps no match in the authored constant.
2. **The proof-shape ceiling.** `first`, `simp_all` and `try` are counted per library source by
   the trust gate's tokenizer and pinned in `generated/proof-shape.tsv`. A count may only fall.
   A new source holding a counted tactic must take a row before it lands, and a row whose source
   is gone fails. `first` counts only when the next token is `|`, because it is also an ordinary
   binder name in this tree; `try` is a keyword atom and `first`/`simp_all` are idents, which is
   measured at the pin, not assumed.
3. **One citation scanner.** Path existence and the protected-document line-citation ban are two
   questions of one pass over the source trees. A cited path that is not a file of this checkout
   is named in `scripts/source-citations-allowed.txt` with its reason, never baselined silently.
