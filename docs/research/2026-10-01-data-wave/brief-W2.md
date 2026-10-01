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
