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
