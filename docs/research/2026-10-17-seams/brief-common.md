# Seams design round: the common brief (2026-10-17)

Status: brief (history, not authority). Repository `/Users/pooks/Dev/lean4-effect4`, main checkout at
`9b8f2248a` on `refactor/phase1-phase3`. The authoring branch `gemini/authoring` (`8984bd15e`, with an
uncommitted repair) is in `/Users/pooks/Dev/lean4-effect4-gemini`. Read both freely. Edit nothing,
build nothing, run no `lake`, `lean`, `dune` or `make`. Your answer is your final message.

## The one thing to know first

The owner wants every seam of the authoring tooling and the content-addressed store laid out
before implementation: the interface (types, invariants, ordering, refusals, laws), the data
structures, and worked calculations of the operational semantics. A review pass then walks the
calculations, and one design lands. Incremental is out of scope; the design must leave it a clean
place to plug in later (a derived cache whose answers equal the uncached ones).

## Read first, in this order

1. `docs/research/2026-10-17-authoring-and-store/README.md`: the authoring interface to date, what is
   written twice, the target interface, the store to date and its target, where they meet.
2. `docs/research/2026-10-17-session-composition/plan.md` (version 2) and `codex-review.md` beside it:
   the composition, the document's history invariant, the fill set's witness, the three outcome
   kinds, run origins, the wire, the native boundary, the slices. `ledger.md` gives each control.
3. `docs/research/2026-10-16-tooling-design/README.md` §3.2 to §3.5 and §3.10: the protocol module,
   generation, the lowered closure, the OCaml shell, the interaction kernel.
4. `docs/research/2026-10-17-ocaml-estate-review/cas/README.md` (the store review, items C1 to C8)
   and `docs/research/2026-10-17-ocaml-estate-review/plan.md` §2 (the OCaml estate's target: sealed
   packages, the `Effect4.Run` facade, hosts as module types, Incremental's eight graph rules).
5. The code each design touches, by declaration:
   - edit side: `src/Effect4/Program/Typing/SourceSession.lean` (`SourceSession`, `feed`,
     `feedStep`, `run`, `view`), `src/Effect4/Program/Edit.lean` (`Edit`, `Edit.Delta`, `Edit.Step`,
     `EditSession`), `src/Effect4/Program/Sketch.lean`, `src/Effect4/Program/Typing/Source.lean`
     (`Sketch.sourceCheck`), `src/Effect4/Program/Admission.lean` (`admitProgram`);
   - on the branch: `src/Effect4/Program/Typing/SourceDocument.lean` (`Doc`, `Doc.commit`,
     `EditTarget`, `Policy`, `Doc.Refusal`), `FillSet.lean` (`FillSet`, `add`, `AddOutcome`,
     `materializeDoc`, `MaterializeRefusal`), `CheckCache.lean` (`CheckKey`, `SigData`, `Entry`,
     `lookup`, `suggest`), `src/Effect4/Run/LiveRecord.lean`, `tools/Tools/Session.lean` (the
     string dispatcher being replaced);
   - run side: `src/Effect4/Api/Built.lean`, `src/Effect4/Run/Basic.lean`, `src/Effect4/Run/Live.lean`
     (`Live.opened`), `src/Effect4/Run/Event.lean`, `src/Effect4/Api/Runner.lean` (`Command`,
     `replay`);
   - store: `src/Effect4/Store/Carrier/Val.lean`, `Carrier/Kind.lean`, `Domain/Node.lean`
     (`Content`, `Ref`, `address`), `Domain/Store.lean` (`Store`, `putNode`, `put`, `get`,
     `putRoot`, `Admission`, `Outcome`, `Store.Sound`), `Domain/Word.lean`; OCaml
     `ocaml/engine/cas/*.mli` (`E4_cas`, `E4_control`, `E4_checkpoint`, `E4_wal`); Rocq
     `rocq/StoreLaws.v`;
   - wire: `tools/Effect4Gen/` (generated codecs, `wire-tags.json`), `tools/Tools/JsonBridge.lean`.

## Constraints every design meets

- **Lean idioms.** Inductives with generated folds and codecs; total functions; refusals as
  `Except` values with located reasons; invariants as proof fields (the shape of `Live.opened`), a
  `Subtype`, or an inductive predicate in `Effect4.Laws`. No `partial`, `unsafe`, `axiom`, `sorry`.
  Program content is first-order data; no stored closures.
- **Roots.** Core code lives under the `Effect4` root and never imports `Effect4.Laws`; laws live in
  `src/Effect4/Laws/`. JSON and reflection stay in `tools/`.
- **Lowering to OCaml (LCNF).** No function type whose result depends on its argument (control R9);
  value-indexed families only over finite nullary indexes (F3). Proof fields erase, so the native
  side rebuilds certificates by replay or checked loading. A checked package is abstract in OCaml
  as a whole (the estate plan's rule 1).
- **The store's rules.** Content never changes once published; a second, different result for one
  key is a defect, never an overwrite; a kind enters only with a consumer that references it; the
  kind table (bytes 1 to 23, sentinel 127) is appended, never renumbered. SHA-256 stays, with
  collision resistance as the only assumption.
- **Reuse first.** Name the existing owner of each piece. Add no second program representation, no
  second run language (nest `Api.Runner.Command` and `Run.Event`), no second edit interpreter.
- **Three outcome kinds stay apart:** a refused request (state unchanged), a refused item inside a
  batch, a run command whose recorded phase refuses (journal grows).

## Vocabulary

Architecture words (use exactly): module, interface (everything a caller must know), implementation,
depth (leverage at the interface), seam (where an interface lives), adapter (what fills a seam),
leverage, locality. One adapter is a hypothetical seam; two adapters make a real one. Domain words
come from `docs/core/controlled-english.md` §3: free object, fold, exact embedding, located refusal,
monoid action, simulation, admission, document, snapshot, revision, fill set, live run, journal.

## What to return (your final message, at most 2000 words)

1. **Interface.** Lean declarations (signatures, structures, inductives), with invariants,
   ordering constraints and refusals. OCaml spelling where the seam crosses into OCaml.
2. **A worked calculation.** A concrete trace on small values: the state before, each request or
   call, the answer, the state after, and which law justifies each step. At least one refusal.
3. **What the implementation hides**, and which existing declarations move behind the seam.
4. **Adapters**: what varies across the seam, and the dependency category (in-process,
   local-substitutable, owned remote, true external).
5. **Laws** the seam owes, each one line, and the existing theorem it reuses where one exists.
6. **Trade-offs**: where leverage is high, where thin, and what this design makes hard later.

Cite declarations by name and path, never by line number. Check every name you cite.
