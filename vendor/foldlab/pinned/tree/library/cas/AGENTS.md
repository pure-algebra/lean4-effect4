# library/cas — lane laws

Operator-ordered, 2026-08-28.

## The spec corpus for this lane

Indexed with decision record in [docs/SPECS.md](../../docs/SPECS.md).
Binding here: [EFFECTS-BACKEND.md](EFFECTS-BACKEND.md) (R1–R15) and
[SCHEMA-MATERIALIZATION.md](SCHEMA-MATERIALIZATION.md) (S1–S5 + the
ruling queue). Ratified designs:
[REIFICATION-SUBSTRATE](../../.staging/operational-structure/REIFICATION-SUBSTRATE.md)
(P0–P8, G0–G8). Greenlit lanes:
[PLAIN-LANGUAGE](../../.staging/operational-structure/PLAIN-LANGUAGE.md),
[LANGUAGE-POLICE](../../.staging/operational-structure/LANGUAGE-POLICE.md),
[BOOTSTRAP](../../.staging/operational-structure/BOOTSTRAP.md).
Design records for this lane:
[operational-structure/DESIGN](../../.staging/operational-structure/DESIGN.md)
(selective/λ• theory) and the
[schema-materialization set](../../.staging/schema-materialization/)
(ADMISSION-MAP, DERIVING-DESIGN, JIT-SUBSTRATE-SURVEY,
TOOLS-DX-REVIEW, SALVAGE-DOSSIER); the verbal register draft
([REGISTER.md](../../.staging/verbal-register/REGISTER.md)) is
DO-NOT-RATIFY-AS-WRITTEN per PLAIN-LANGUAGE.md.
Check a spec's category and open asks in SPECS.md before building
from it.

The pre-grade [Effect Core v1 packet](../../.staging/effect-core-v1/README.md)
is the indexed successor study for arbitrary effect flow. Before changing a
carrier or theorem for that lane, read its
[existing-type ledger](../../.staging/effect-core-v1/EXISTING-TYPES.md),
[counterexample register](../../.staging/effect-core-v1/COUNTEREXAMPLES.md), and
[per-type closure gate](../../.staging/effect-core-v1/TYPE-CLOSURE.md). It does
not replace current law: block bodies reuse `PProg`; scoped children elaborate
through existing `Handler`/sum/tower machinery into a target that can observe
child failure while retaining the post-body state on that failure. This is the
state-outside-error information contract, not a required transformer spelling:
plain `ReaderT Env (Prog CasSig)` cannot recover, and a state/error layout that
discards state on error cannot implement catch/finalization correctly.
`ensuring` is a reference-machine exit rule, never ordinary `Prog.bind`.
Fixed-fuel `run` has no bind law; CAS refusals keep their existing
classification.

## Portable effect protocol seam

The future `library/effect-protocol/` manifest owns stable cross-language
operation/type IDs, canonical bytes, and profile membership. This lane remains
the semantic authority: Lean admits selected manifest rows into the existing
`Sig.Op`/`OpDesc` families and owns reference meaning and proofs. Do not mint a
second signature, schema universe, `PProg`, refusal family, cause/frontier
family, or CAS spelling in the neutral seam. Proof status and conformance
results are sidecars keyed by the protocol digest, not identity-bearing
manifest fields. Effect TypeScript is one adapter profile, not the protocol's
exclusive consumer.

Effect Core work follows the packet's clean baseline/integration and
per-slice breaker-builder-reviewer worktree protocol. The first implementation
slice is file stubs only; the broad ownership and proof-edge sweep precedes any
deep per-type proof work.

## The two-minute rule

If you cannot make progress on a proof for two minutes, STOP. Do not
grind the same tactic against the compiler. Immediately:

1. look up the standard literature and prior art (mathlib, Batteries,
   core Lean source, the pinned reference clones in `.reference/clones/`);
2. use the skills — `lean` (llm-proof-loop), the `lean4` plugin agents
   (proof-repair, sorry-filler, golf), and their LSP tools
   (`lean_goal`, `lean_diagnostic_messages`, `lean_multi_attempt`,
   loogle/leansearch);
3. anything else that puts an existing determination on the table
   before another blind attempt.

Bit-level and encoding machinery is never hand-derived when a proved
determination exists somewhere citable — import it, credit it, pin it.

## The store language is ratified law

[EFFECTS-BACKEND.md](EFFECTS-BACKEND.md) (R1–R14, operator-ratified
2026-08-28) governs everything in this lane. The load-bearing rules,
so no session re-derives or drifts:

- Meaning lives in the REFERENCE HANDLER only (`Cas/Lang/Handler.lean`);
  every realization — Effect adapter, replay, transports — is claimed
  against it, and the observation is the WORD (byte-decidable).
- The stable effects API is strata 1–2 of `Cas/Lang/Representation.lean`:
  first-order content (decidable, addressable — what metaprogramming
  touches) and `Prog` (lawful monad, initial — what proofs induct on).
  Handler images are equated only by theorem; host IO only by trust
  statement.
- The direction law: HOOVER (parse pinned sources) is ingestion and
  never mints identity; EXECUTE (run the Lean model) is the only way
  fixtures and words are minted; MATERIALIZE flows denotation → code,
  byte-gated, never the reverse.
- Programs are content; hosts are code (R7). Generated code that
  becomes a program's authoritative home is a defect.
- The PURE DISCIPLINE (R14a, `Representation.lean`): effect-free work
  stays OUTSIDE `Prog` as plain definitions on first-order data —
  never lifted; continuations end in `.pure` and programs compose by
  smart constructors + `bind`, so inductions are as short as the
  operation tree and leaves close by `rfl` (`interpret_pure`,
  `interpret_op`); constructor form in theorem statements, typeclass
  form in program text.

## Standing discipline

- Statements are frozen before proof work; a needed statement change
  routes back through the strategy pass, never through a proof edit.
- No `sorry` lands. No `native_decide`. Executable digest checks run
  as build-time `#eval` IO asserts, never kernel `decide`.
- Everything quantifies over the abstract `H`; premises on `H` are
  named at their lattice level (CAS-003), never assumed silently.
