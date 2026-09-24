# Brief for Codex: loaded admission of the typed corpus

Repo `lean4-effect4`. Base: the head of `refactor/phase1-phase3` carrying this brief. Branch
`codex/loaded-admission`, its own worktree; nothing pushed. Standing constraints of the slice 5
brief §1 apply (one compiler per checkout, explicit paths, `-DwarningAsError=true`, no `first`,
`simp_all` or `try` by hand under `src/`, narrow builds, `make check` at the end). This can run
beside slice 5's stack proofs: neither changes the other's files.

## Goal

Extend `Test/Program/LoadedAdmission.lean` from five programs to every entry of
`Test/Program/TypedCorpus.lean` outside the context fragment: for each, a theorem that the code
the reference machine loads (`denoteR e e (rootPoint 20)`, or `loadR` as `sleep_admitted` reads
it) is `TypedProg` at the checker's type, at every world. This is the acceptance test of the
protocol repair ([repair note](2026-09-24-typed-state-protocol-repair.md)).

## Scope

- In: all 77 entries. Decision row 90 landed (2026-09-24): services and memoized layers are
  typed (`service_admitted`, `memoAwait_typed` show the moves).

## The pattern

The five landed proofs show the moves: `refine` the judgment's constructor against the
generated code (it reduces), close source admission with `decide +kernel` at the concrete path,
and type each continuation from the row's post. `bind` compiles to an `onSuccess` guard whose
body is the first program and whose success arm is a `construction` followed by the rest at the
extended environment: use `TypedProg.guard` with the first program's type as `mid`, type the
unguard payload, and in `run` invert the value (`Val.hasTy` at the base type gives its
constructor) before the rest's code reduces. A miss is a failure at `mid`, clean or typed.

Prefer a small reusable lemma set in the test file over repeated unfolding: a value inversion
per base type, a guard lemma for `bind`, and one for catches. If a proof needs a fact about the
judgment in general, state it as a lemma and prove it; if it needs world weakening, use the
`M3bWorld` statements as hypotheses and name them in the receipt; do not prove them here.

## Stop conditions

Stop and record the smallest amendment if an entry outside the context fragment cannot be
typed: that is a counterexample to the repair (`E4-SCHED-CE-015` onward).

## Finish

Every in-scope entry proved at `[propext, Quot.sound]`, the out-of-scope list present, the
census and lane unchanged, `make check` green, and a receipt
`docs/research/2026-09-24-loaded-admission-receipt.md` with base and head, the per-entry list,
axioms, commands with exit codes and the unique ledger line.
