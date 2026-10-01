# Seat W2: the generator extended once for variable arity and the declared order (commit 2)

Filled at dispatch: base (main after probe Q lands, and P's final cross-head rules), the
`Q/note.md` sections and patches under `Q/patches/`, P's leaf-order table. Rules: `README.md`
here, plan §4, `AGENTS.md`.

**The one thing.** After this commit the next constructor is generated, not hand-written: the
single-motive eliminator and the computational equality for nested families (row 119: generated,
never a third hand copy), `TyView` with list children (`record`, `app`, `tuple`), the variance row
for a head of variable arity, and the generated order laws extended to declared cross-head leaf
edges read from one shared table beside the six fixed exceptional cases (Codex, 19:30): the
different-head theorem restated so its conclusion is false only where no edge is declared, with an
accepted cross-head case and its rejected converse as controls.

## The work

1. Apply Q's patches to `tools/Effect4Gen/` (`View.lean`, `Fold.lean`'s nested block, the
   eliminator and equality emitters, `Variances.lean`/`variances.json`'s shape for variable arity,
   the leaf-order table as data), each with its own test in the generator's fixtures.
2. Regenerate the groups for today's `Ty` in the fixed order and show them byte-identical
   (`make check-gen`): the extension changes no output until a constructor uses it. That is this
   commit's conservativity proof.
3. The monadic-fold decision (no monadic half for nested positions; the consumers Q listed) recorded
   in the generator's header and proposed as a decisions line.
4. The hand tables Q measured as generatable (`cases-policy.json`, the OCaml mirrors' constructor
   tables, the count pins): the emitters, run on today's `Ty`, outputs byte-identical to the hand
   copies, the hand copies deleted (the cut-over).

Receipt `receipt-W2.md`: the patches landed, the byte-identity logs, the tables now generated and
their deleted hand copies, the lines for rows 119 and 162.

## Amendments at dispatch (2026-10-01, probe Q merged at `818c26ff`)

Probe Q landed (`docs/research/2026-10-01-type-language-probe/Q/note.md`; decisions rows 171–174
ruled by the coordinator, row 172's promotion owed to the owner). Its "Brief text for the data
wave", **T's commit 2**, is your step 1, verbatim: apply from `Q/patches/` (each `git apply --check`
clean at `bff50631`; re-check at your base) `Fold-elim.patch`, `View-variable-arity.patch` (it
contains `View-namespace.patch`), `Variances-commit2-mechanism.patch` (the mechanism with today's
head list and an empty rule list; the data rows of `Variances-variable-arity.patch` are commit 4's),
`FoldOf-prod.patch`, then write `fold_of`'s sibling over `List (A × M)` (Q3; assumed 60 to 120
lines), `Translate-array-mk.patch`, `Audit-seed-keeps-notes.patch`, and (row 174)
`LcnfGen-manifest-beside-out.patch` with the wire-tag loaders (Lean and Python) refusing a repeated
key with a fixture. Leave `variances.json` without a `rules` section and `manifest.json` without the
`TyEq` group, so every producer writes today's bytes: `LEAN_NUM_THREADS=1 make gen-variances
gen-derived`, then `git diff --exit-code` over the generated paths and `make check-gen` (Q
reproduced this byte for byte: `Q/logs/gen/today-TyView-patched.log`,
`commit2-variances-today.log`, `commit2-Fold-today.log`, `commit2-ValFold-today.log`). Keep as
fixtures the refusals Q names (the `elim` kind on a family with no nested position and on a
parameterised family; the view on a variable head with no arity word; the producer on an unclosed
edge table; `fold_of` on a pair position before the patch; the LCNF lowering of `List.zipIdx`,
which `dune` refuses unpatched). Row 173's first three items are step 1's last commit: the cases
policy re-seeded with its notes kept (`--seed-policy`), `LcnfMl.tyOcaml` deleted for
`TValue.render ∘ tyT`, the Audit driver change. `Q/check-conservativity.sh` lands as
`scripts/check-conservativity.sh` with its ten controls (row 172) and a `make` target; the policy
promotion of `Ty.refOf`, `Ty.deferredOf`, `Ty.var` and `Ty.unknown` waits for the owner's word
(the coordinator relays it); until then the script is landed and run without `--strict`.

The steps that read probe P's final cross-head rules (the leaf edges as data rows, the accepted
case and its rejected converse) and probe U's measurement (the hand tables generated, row 173's
emitters) arrive as amendments by message when P and U land. If step 1 is done and they have not
arrived, write the receipt for step 1 and hand back; the coordinator resumes you with the
amendments.

## Amendment 2 (2026-10-01, probe P merged at `714d2601`): the leaf-order table

Row 177 is ruled. The table is `leafEdges` (`P/probes/P2Ty.lean:693`) over `LeafHead` (`:666`),
with `leafHead` (`:680`), `leafReach`/`leafLe` (`:700`, `:706`) and `leafRule` (`:710`), in the
core because `sub` consults it (`:739`); the generator reads `Ty.leafEdges` from the environment
and emits its laws (`P3View.lean:666-826`), each by `decide` over `LeafHead.all`, plus
`leafHead_facts` per head; `litRule` and its three lemmas are deleted. `sub_eq_args` and the
different-head theorem take `hleaf : leafRule a b = false` (`P3View.lean:401`, `:472`). Controls:
the accepted cross-head case `sub .nat .number` with its rejected converse (`P2Ty.lean:1281-1283`)
and the cyclic table (`:1285`). Membership's obligation is one lemma per edge (`hasTy_leafEdge`,
W4's). The reconciliation with Q's `rules` section (row 177): the table holds the declared edges
(`lit < string`, `nat < int`, `int < number`, `undefined < unit`; `nat ⊑ number` is derived, never
an entry), the closure is computed as P's `leafLe`, and the producer refuses a cyclic table, not an
unclosed one. In this commit (no `Ty` change) the mechanism lands with today's one edge
(`lit < string`) as the only row, so every producer still writes today's bytes; the wave's edges
are commit 4's data rows. Probe U's amendment (the hand tables generated) is still to come by
message; the Makefile: add `check-conservativity` as its own rule at the end of the checks block
and touch neither `check:`'s prerequisite line, `CHECKS`, nor the help text (seat J2 edits those;
the coordinator wires yours in after both merge).

## Amendment 3 (2026-10-01, Codex 20:46 and 21:16, verified): the checker's revisions

Row 172 is amended (sent to the seat by message): `conservativity.py` resolves each supplied
revision to a commit before reading (`git rev-parse --verify <rev>^{commit}`, a named refusal),
fails on a git execution error, keeps an absent historical file distinct from an unreadable
revision, and its self-test gains invalid-base, invalid-candidate and invalid-both, each also
under `--strict`, all refusing with exit 1, beside the ten controls. Codex's fixture evidence:
`reviews/codex-2046-conservativity/`.

## Amendment 4 (2026-10-01, probe U merged at `b5501b82`): the generated families (sent by message)

Row 182 is ruled (D-U1 (a), D-U2 JSON, D-U3 the clause as written). Step 2, after Q's patches:
(1) the fold generator's `--extras` emission (`U/patches/Fold.lean`, +303/−1; byte-identical
without the flag) merged with Q's `Fold-elim.patch` on the same file, extended to nested blocks
with `ArgF` positions (U §3.5; measure the 150 to 200 lines U assumed), the prisms beside the
view; (2) the table emitter (`U/patches/TableGen.lean`) and the two tables `ty-faces`,
`ty-classes` as JSON (the face table's Schema column as `Representation` values); (3) D-U1 (a)'s
expansion with the `eq_cata` connector per expanded definition on the LCNF cut; (4) U's rule
checker landed as `scripts/check-ty-rule.py` with its two pass-through exemptions and the 78-row
baseline printed, not wired into `check` (the gate is commit 4's); (5) the mirrors `of_ty` and
`rand_ty` emitted if `dune build` and `make check-ocaml` stay green, else left to W4 and said.
Acceptance: the generated modules compile; U's 24 agreement theorems hold against the generated
view on today's `Ty` (a battery at the `Test/All.lean` anchor, `#print axioms`); the two red
tables refused by name; every producer still writes today's bytes. If step 2 cannot finish, land
step 1 and the conservativity script, write the receipt, hand back.
