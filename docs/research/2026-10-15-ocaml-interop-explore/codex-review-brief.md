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

## The theoretical grounding (the owner's directive)

The owner asks for one framework that fits the tree's literature and serves agents first. The
interop capabilities are many: libraries, transports, platforms, faces. The framework must make
each one a case of a few structures, so an agent reads one description and gets every surface.

Ground each layer in the texts the tree already holds. Read them at these paths:

- `docs/research/2026-10-09-comodel-papers/text/`: Plotkin and Power (2008), Uustalu (2015),
  Ahman and Bauer (2020), Setzer and Hancock (2005), Niu and Spivak (2023);
- `vendor/papers/program-graphs/`: interaction trees, choice trees, Foster et al. on bidirectional
  tree transformations, Huet's zipper, Lamport (1978);
- concept 9 of `docs/core/semantics.md`, with its session-type and I/O-automata literature.

Answer these, each with the declarations it touches:

1. **The interface.** Is a row table a polynomial, with operations as positions and answers as
   directions (Niu and Spivak; Setzer and Hancock's interfaces)? Is a native library's interface
   one too? `Effects.Signature.Hom` (`Effects/Lens.lean`) maps operations forward and answers
   back: is it the polynomial morphism, and is a transport codec that morphism with partiality?
2. **The transport.** State the top abstraction precisely. A candidate: a transport is a pair of
   host maps, read through runners and comodels (Uustalu; Ahman and Bauer). Their composite is
   the identity on a named observation. Does `rpc/Transport.lean`'s `through_serve` instantiate it?
   What do the polynomial operations give for free: the parallel product for several services,
   and composition for layering?
3. **The codecs.** Framing and messages are exact embeddings (the tree's `Image`). Do the lens
   laws of Foster et al. add anything the tree's two laws lack, such as a normaliser?
4. **Correlation.** Is the correlation layer a simulation (concept 9's I/O automata), or an
   interaction tree over the two operations send and receive? Which gives a shorter proof of the planned
   law, and which observation does each name?
5. **Lifecycle.** Setzer and Hancock's state-indexed interfaces are the tree's `ISignature`. Do
   they carry resource handles and their capabilities, for P5 of the interop plan?
6. **Agent utility.** For each choice, say what an agent gains: one place to read an interface,
   generated surfaces, located refusals, replay of a recorded run.

Mark each literature claim as the controlled English requires: "read" only for a text above,
"named" otherwise. Take a locator only from
`docs/research/2026-10-01-semantics/citations-audit.md`. Propose a paper to file; do not download one.

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
