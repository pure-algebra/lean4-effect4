# Codex: a review of the interop plan, for drift

## The one thing to know first

Review the plan in `docs/research/2026-10-15-ocaml-interop-explore/README.md` §6 and §7 against
the tree. The owner's test is reuse: every layer must be an existing representation, or a
function of existing ones. Report where the plan adds a second representation, misreads the
source, or misplaces a law. Write the review only. Change no other file.

## Base

`refactor/phase1-phase3` at the commit that adds this brief. Rows 391, 393 and 394 of
`docs/core/decisions.md` govern it.

## What to read

1. `docs/research/2026-10-15-interop-plan/README.md`: the plan this exploration serves (P0 to P6).
2. `docs/research/2026-10-15-ocaml-interop-explore/README.md`: the probes, §6 (transports and RPC)
   and §7 (the message alphabet).
3. The probes and their logs: `alphabet/Alphabet.lean`, `alphabet/alphabet.log`,
   `alphabet/export.ts`, `rpc/Transport.lean`, `rpc/effect_rpc.ml`, `rpc/client.ts`, `rpc/server.log`.
4. The owners the plan names: `src/Effect4/Schema/Bridge.lean` (`schema`, `ofSchema`,
   `ofSchema_exact`), `src/Effect4/Schema/Codec.lean`, `src/Effect4/Codegen/Classes.lean`,
   `src/Effect4/Codegen/RowServices.lean`, `src/Effect4/Run/Basic.lean`, the `effects` package's
   `Effects/Coalgebra/`.
5. The pin: `vendor/effect-4.0.0-rc.112/src/unstable/rpc/` (`RpcMessage.ts`, `RpcClient.ts`,
   `RpcSerialization.ts`, `Rpc.ts`) and `src/SchemaRepresentation.ts`.

## The questions

1. **A second representation.** Is anything in §7 a new language beside `Ty`, `Row`,
   `Representation` or `Effects.Comodel`? The alphabet must be functions of the rows. The platform
   and serialization tables must be data, not a new type language.
2. **The seams of §7.3.** Check each against the source and the probe log. Is any wrong, and is one
   missing? Pay attention to the option's JSON codec and to the failure form.
3. **The bridge widenings.** Do references, unary and n-ary unions and `~identifier` keep
   `ofSchema_exact` true modulo `normS`? If one cannot, say which and why.
4. **The request id.** Lower `Ty.number`, or restrict ids to integers and strings with a named
   refusal: which keeps DI-56's scalar profile, and which keeps Effect's own client working?
5. **The failure form.** What would unifying `eff_failure X message` onto the tagged record reach,
   in the checker, the faces, the corpus and the batteries? Is a narrower seam available?
6. **The transport law.** `through_serve` (`rpc/Transport.lean`) covers a request/response wire.
   Is the planned correlation law (a host over send and receive simulating that wire) the right
   statement? Which observation must it name, given that HTTP carries no Interrupt?
7. **Placement.** For each planned theorem, name its concept in `docs/core/semantics.md`, its
   requirement and its consumer, as `AGENTS.md` requires. Flag a theorem with no consumer.
8. **Effect as the interface model.** Row 393 (5) takes Effect's services as the interface model.
   Does Effect RPC's split (group, serialization, protocol, socket) carry over cleanly, or does it
   hide a choice the plan should make explicitly?

## The deliverable

Write `docs/research/2026-10-15-ocaml-interop-explore/codex-review.md`. Open with the one finding
the coordinator must act on first. Then rank the findings by what they would force to be
redone. For each, give the file and declaration, the evidence kind (reading, tested or proved) and
a proposed correction. Propose decisions rows in the review; do not edit the register.

## Rules

- Read and run probes only. Install nothing and download nothing.
- Run a Lean probe only through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`.
- Never redirect stderr to `/dev/null`.
- Write in the controlled English of `docs/core/controlled-english.md`.
