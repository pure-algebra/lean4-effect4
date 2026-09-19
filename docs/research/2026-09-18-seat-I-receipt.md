# Seat I receipt — instruments and gate removal (tooling-first wave)

Branch `worktree-agent-a14ec064f4f005f55`, from `4b4e6aa3` on `refactor/phase1-phase3`.
Items 1.6, 1.7, 0.10, 0.4, 0.7, 4.8/4.9 and the Q4–Q6 rulings.

**Setup note, before anything else.** The worktree was created at `9187b9b6`, not at the base
the brief names. The tree was clean, so the branch was moved with `git switch -C
worktree-agent-a14ec064f4f005f55 4b4e6aa3`; nothing was discarded. `.lake` was seeded by
`rsync` from the main checkout, which is at the same commit, so the first build replayed
instead of compiling the closure.

## Commits

### 1. `897e45b1` — `#exhaustive_gate`, the inventory of what a constructor costs (1.6)

New `src/Effect4/Laws/Auto/Exhaustive.lean`; `Test/Audit/ExhaustiveFixture.lean`;
`Test/Audit/TraversalCensus.lean` runs it; `src/Effect4/Laws.lean` imports it;
`Test/All.lean` imports the fixture; `Test/Audit/AxiomGate.lean` gains two exemption entries.

`#exhaustive_gate <Inductive> [under <Namespace>]` walks the definitions of a scope and reports
`holder, module, matcher, discr, alts, catchAll` for every match that reads the named family.
A row with `catchAll false` is a definition the compiler refuses the day a constructor is
appended. Printed report only: no file is written (decisions row 49), nothing fails (row 34).

The catch-all decision is exact and comes from the matcher's own type, as the plan specified:
an alternative is `∀ fields, notAltHs → ∀ eqs, motive p₁ … pₙ` (`mkMinorType`), so the pattern
at discriminant `d` is the `d`-th argument of `motive`, and the alternative catches every
future constructor exactly when that argument is a bound variable of the fields telescope,
after stripping `mkInaccessible` mdata and a `namedPattern x p h`. `MatcherInfo.altNumParams`
gives the telescope length. `matchMatcherApp? (alsoCasesOn := true)` also reads `casesOn`.

**Two corrections the plan's sketch needed, found by building it.**

* The sketch walks into `.lam`/`.forallE`/`.letE` bodies raw and then calls `inferType` on a
  discriminant, which fails with "unexpected bound variable #0". The walk instantiates each
  binder with a real local (`withLocalDecl` / `withLetDecl`) before descending.
* `Traversals.definitionsUnder` drops internal details by design, and a structural recursion
  keeps nothing in the authored constant: `Ty.closed = fun x => Ty.brecOn x Ty.closed._f`, with
  the twenty-arm match inside `Ty.closed._f`. Measured: with authored definitions only, the
  inventory found 24 holders and missed `Ty.closed`, `instantiate`, `normalize`, `members`,
  `renderRaw`, `key`, `Val.hasTy` and `Schema.Bridge.schema` — most of what a constructor
  costs. `bodiesUnder` adds each helper, attributed to the definition a person wrote.

Rows are deduplicated by (holder, matcher, discriminant) and the catch-all question is asked
once per surviving row; that took the `Ty` run from 258 raw hits at ~19s to 51 rows at ~10s.

**Red controls, exercised.** `#guard_msgs` over `Test.Audit.ExhaustiveFixture` pins all three:
a twenty-arm `Ty` match with no wildcard is reported `catchAll false`; the same match closed by
`| _ =>` is reported `catchAll true`; a match on `Term` is not reported at all. The pin is in
`Test/Audit/TraversalCensus.lean` and fails the build if the detection changes.

**Today's `Ty` inventory:** 51 matches read it, 22 with no catch-all — `Ty.closed`,
`instantiate`, `isMember`, `isNever`, `key`, `members`, `normalize`, `renderRaw`, `Val.hasTy`,
`Schema.Bridge.schema`, `findInt`, `rawSupportedErrTy`, `Store.ProgramGen.TyC.toValTy`,
`instReprTy.repr`, the five generated folds (`cata_ty`, `foldM_ty`, `foldMapAt_ty`,
`foldMap_ty`, and `Val.hasTy.hom`) and four `.hom` witnesses. `Ty.sub` and
`Schema.Codec.isSupported` are reported with `catchAll true`, which is right: both end in a
wildcard, and DI-95's ruling is about which *class* a wildcard defaults into, not about having
one.

**Cost.** `Test.Audit.TraversalCensus` 19s → 42s for the three inventories (`Ty`, `Term`,
`Store.Val`). It re-elaborates only when the Laws move. First row for the 4.7 ledger.

**Also in this commit, and not this item's work.** `lake build Test` was red at `4b4e6aa3`:
`Effect4.Laws.Auto.RuleSets`'s initializer reaches `Classical.choice` through the aesop
environment extension, which the module's own header predicted ("if the gate reports
`Classical.choice` … this module joins `auditImplementationModules`"). The line is tooling plan
1.1's and landed here only because no seat can be green without it. The coordinator confirms
seat A hit the same red and recommends the same line.

### 2. `6d46565b` — the proof-shape ratchet, and one citation scanner instead of two (1.7)

`Test/Audit/AxiomGate.lean`, new `generated/proof-shape.tsv`, new
`Test/fixtures/trust-gate/proof-shape.lean.txt`, `scripts/test-trust-gate.sh`,
`scripts/test-source-trust-tokenizer.sh`, `scripts/check-source-citations.py`,
`scripts/test-internal-citations-gate.sh`, `scripts/source-citations-allowed.txt`, `Makefile`,
`docs/DESIGN-ISSUES.md`, `docs/core/lcnf-route.md`; **deleted**
`scripts/check-internal-citations.sh`.

**The ratchet.** The tokenizer pass counts `first`, `simp_all` and `try` per library source
under `src/`, in the same pass that looks for a trust token. `generated/proof-shape.tsv` is the
ceiling: 94 sources, 730 counted tactics, taken from the counter's first run.
`#effect4_print_proof_shape` prints the file. A rise fails; a fall passes and the summary says
by how much; a source with a counted tactic and no row fails; a row whose source is gone fails.

**Two measured corrections to the plan.**

* "Count `.atom` tokens only" does not hold at this pin. Probed directly: `try` is a keyword
  and arrives as an atom, while `first` and `simp_all` arrive as idents. The counter reads
  both shapes by raw text, so `Foo.first` is one ident named `Foo.first` and is not counted.
* Reading idents gave 775 `first` against 16 real tactics in `Program/Typed.lean`, because
  `first` is also a binder name (`intro raw first second`; `Census.attempt`'s parameter). The
  tactic's syntax is `"first" ("| " tacticSeq)+`, so `first` is counted only when the next
  token is `|`. That gives 336 against 337 for a multi-line grep of `first\s*|` — the single
  difference is a `first` in a comment, which the tokenizer skips. `simp_all` (120) and `try`
  (274) agree with grep exactly.

**Red control, exercised.** `scripts/test-trust-gate.sh` plants the fixture's one `first | …`
in a probe copy of `src/Effect4/Store/Shape.lean`, whose `first` ceiling is zero, and requires
the refusal "now holds 1 `first` … pins 0". Run: 16 planted defects rejected, 5 accepted. The
probe tree now also gets `generated/proof-shape.tsv`, for the same reason it gets
`known-red.txt`: the gate reads the pin from the root it audits and a missing one is a gate
that checks nothing.

**The retirement.** `check-internal-citations.sh` is deleted and its question is the second
half of `check-source-citations.py`, asked of the lines that pass already reads.
`make check-citations` runs one program; every text file of the nine trees is read once
instead of twice. Agreement where they overlap, measured before the deletion: 2,682 candidate
tokens, seven protected documents, zero violations, both. The merged pass reads four files
more (the root `AGENTS.md`, `README.md`, `lakefile.toml` and the coverage skill), which hold no
`path:line` token. All seventeen cases of `scripts/test-internal-citations-gate.sh` pass
against `--internal-only`, and all eight of `scripts/test-source-citations.py`.

One scoping decision inside that: the "extracted no citation tokens at all" tooth is asked of
this repository and of any tree given to `--internal-only`, and not of a foreign tree scanned
in full mode, which may legitimately hold none — `test_allowance_is_exact`'s three-file tree
does. Both suites pass with the tooth as scoped.

**`make check-citations` was red at `4b4e6aa3`; it is green here.** Checked against the scanner
at HEAD: the same nine unresolved paths and three unmarked research notes fail before and
after the merge, and `generated/citation-baseline.txt` does not exist in the tree at all. Fixed
what this seat owns (three `(untracked working note)` markers in `docs/DESIGN-ISSUES.md`;
`docs/core/lcnf-route.md`'s three short spellings of `tools/Conform/Effect4/Lcnf*.lean`) and
named the other six in `scripts/source-citations-allowed.txt` with a reason each — the emitter
named by decisions row 49 that was never written under that name, two planned MCP modules named
by `docs/core/api-surface.md`, the layout specification held outside the tracked tree, the
`effect` package manifest that `bun install` provides, and the timer workshop. This is the
precondition for 4.8 putting the lane in CI.

## Proposed rows for `docs/core/decisions.md` (not edited by this seat)

1. **The exhaustiveness inventory is an inventory.** `#exhaustive_gate` prints; it never writes
   and never fails. The gate over default arms is the compiled-LCNF case-site policy. Read the
   inventory before appending a constructor; the number of `catchAll false` rows is the bill.
2. **The proof-shape ceiling.** `first`, `simp_all` and `try` are counted per library source by
   the trust gate's tokenizer and pinned in `generated/proof-shape.tsv`. The pin may only fall.
   A new source with a counted tactic must take a row before it lands. `first` counts only when
   followed by `|`, because it is also a binder name in this tree.
3. **One citation scanner.** Path existence and the protected-document line-citation ban are
   two questions of one pass over the source trees. A cited path that is not a file of this
   checkout is named in `scripts/source-citations-allowed.txt` with its reason, never
   baselined silently.
