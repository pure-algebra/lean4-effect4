import Cas.Lang.Defun

/-!
# The fragment tower — the interop reference model

**Read this before coding against a CAS program, in Lean or in
TypeScript.** This module carries no definitions. It states the ladder of
program carriers the estate offers, what each rung guarantees, and — the
point of writing it down — **what another effect system may assume when
it consumes one.** Effect-TS is the concrete other system; the answers
below are written so a TypeScript engineer, or an agent driving
`cas_run`, can act on them without reading a proof.

There are two towers in this library and they are orthogonal. Do not
confuse them:

- the **service tower** (`Cas/Lang/Tower.lean`) is VERTICAL: a handler
  may itself be a program over a lower signature (`casOverBytes`,
  `Handler.through`, `interpret_through`). It answers "what implements
  this?".
- the **fragment tower**, this module, is HORIZONTAL: which programs may
  be written at all, ordered by expressive power — applicative-strength,
  selective-strength, monadic. It answers "what can be said about this
  program before running it?".

The horizontal ladder is the one an interop story needs, because the
answer to "what may I assume about a program I was handed?" changes at
every rung, and only at these rungs.

---

## The ladder

`L-A ⊂ L-S ⊂ L-P`. The inclusions are claims to be PROVED, not assumed;
one is proved, one is owed, and the note says which.

### L-A — the table (applicative strength). LANDED.

- **Carrier.** `PProg = List PLine` (`Cas/Lang/Defun.lean`), with
  `PLine = put version tag payload refs | load src` and
  `PIn = lit Addr32 | ans Nat`. Straight line, positional operands, no
  binders, no branch. The designated result is the last answer.
- **Static analysis: YES, and exact up to two named gaps.**
  `PProg.envelope` computes the read set, the put shapes in program
  order, and the answer-index dataflow DAG from the table alone — no
  word, no store, no `H`, no fuel. The sandwich is proved:
  `runPFrom_puts_sound` (every binding a run adds carries a declared put
  shape, in order), `PProg.resolve_sound` and `runPFrom_absent_sound`
  (every address consulted is an enveloped literal or an answer the table
  itself determined), `runPFrom_load_absent`/`runPFrom_load_present` (the
  lower bound: a load line's outcome is a function of the word at exactly
  its address), and `runP_frame_sound` (the frame condition closed for
  every run, refusing ones included — FRAME-1).
- **Why static analysis is possible here, and the reason usually given is
  wrong.** A free applicative is analysable because no later effect may
  depend on an earlier RESULT. `PLine`'s `ans i` IS such a dependence, so
  that is not the reason. The reason is **hash-determined dataflow**: the
  answer to a `put` is the content address of the node it admits
  (`putWord_answer`, Level 0 — no premise on `H`), and a `load` answers
  its source, so given `H` the whole answer environment is a pure
  recursion on the table (`PProg.answersFrom`,
  `runPFrom_done_answers`). The estate's R4/Level-0 addressing discipline
  does the work the applicative restriction does elsewhere. That property
  now has a name and a boundary: `PLine.HashDetermined`, discharged for
  every `CasSig` operation by `PLine.hashDetermined`. An operation
  outside it — `LlmSig.infer` is the estate's live one — keeps none of
  this rung's guarantees and is owed a trace store instead; read that
  definition's docstring before adding an operation to any signature a
  table speaks.
- **Where the over-approximation is, exactly.** Two sources, both
  exhibited by witnesses at the end of `Defun.lean`, and there are no
  others: (1) the SUFFIX AFTER THE FIRST REFUSAL — lines the run never
  reaches are still named by the envelope; (2) `put`'s DUPLICATE outcome
  — a put line that executes adds no binding when the node is already
  stored, so the word projection is a `Sublist` and never a prefix. Note
  that DESIGN.md §3.1's table calls this rung "exact:
  `over = under = actual`"; that is refuted, and the witnesses are the
  refutation.
- **Store encoding: YES.** Wire tags 14 and 15 ARE the `Ty.step` and
  `Ty.cont` sorts — ratified by G3 on 2026-08-29, with forms in
  `Cas.Grammar.manifestV0` witnessed by `encodeLine` and `tableNode`, and
  `Ty.wireTag` the only place either number is written. The reservation
  this line used to describe — bare literals pinned to `REGISTRY.md` by
  `#guard` and deliberately spelled outside `Cas.Grammar.Ty` until the
  grammar grill ratified them — is discharged, and `Defun.lean`'s
  reconciliation note records how.
  `encodeProg` lays a table down children-first; `encodeProg_wf` says it
  admits for EVERY address function (hash-lattice Level 0, no
  injectivity). `decodeProg` reads it back, under two triaged premises —
  `hwf` (line fields fit their wire scalars) and `hsep` (the address
  function separates the table's lines, NECESSARY and strictly weaker
  than `Function.Injective H`).
- **Handler set: all of R10.** `referenceHandler` (the oracle),
  `replayHandler`, `proveHandler`/`verifyHandler` (`Cas/Lang/Auth.lean`),
  the Effect adapter, and any transport — every one of them applies to
  `embed p` with no per-fragment restatement.
- **Agreement theorems, by name.** `runP_embed_agree` (the direct
  interpreter equals the embedded program at fuel exactly
  `p.length + 1`), `runPFrom_embedFrom` (its packaged induction),
  `runP_preserves_wf` (L7 inherited), `runP_halts`,
  `ObsEq_embed_of_runP` (the word gate read as a stratum-3 equality),
  `runP_decodeProg_encodeProg` and `ObsEq_decodeProg_encodeProg` (a table
  stored as content and recovered from it runs identically), and
  `envelope_decodeProg_encodeProg` (so does its envelope).

### L-S — the guarded table (selective strength). PROPOSED, OWED.

- **Carrier (proposed).** `SProg`: L-A plus one branch line whose
  scrutinee is a decidable test on a LOADED node and whose arms are
  closed `SProg`s. Not full `select`: `select`'s second argument is an
  effect answering a FUNCTION, and there is no store node for a function
  (grammar-grill ruling 4). The store-admissible shape is `ifS`-like,
  with first-order decidable scrutinees.
- **The rule that keeps the fragment small (R14a-P1, intact).** A branch
  on a PURE condition is Lean's `if`, outside the program; it earns
  nothing here. A branch is admissible only when its scrutinee is an
  OPERATION'S ANSWER — branch on what a `load` returned.
- **Fragments are carriers, not instances.** Do NOT give `Prog` a
  `Selective` instance. Every monad is selective via `selectM`, and SAF's
  final law forces `select = selectM` when both exist, so the analysis
  becomes exact and useless. The value lives in a separate, smaller
  carrier that EMBEDS into `Prog`, exactly as `PProg` does today through
  `embed` with `runP_embed_agree` as the tie.
- **Why a table is the right shape for it.** Rigid selective functors
  have a normal form and it is a LEFT-ASSOCIATED LINEAR SEQUENCE (SAF
  §5.1) — that is, a table. `PProg` is already a table. Under R4 a
  canonical spelling is the precondition for content addressing, so
  having a normal form is not a nicety here.
- **Static analysis: over ⊋ under, genuinely.** This is the rung where
  the sandwich stops being nearly tight: the arm not taken is possible
  and not necessary. L-A's two gaps remain and a third appears.
- **Store encoding: FORMS on the step and cont sorts, never a third
  tag.** Ruling P6 (`EFFECT-AST-PLACEMENT.md`) supersedes the tag-16
  reservation this line used to carry: a guarded table grows tags 14/15
  by adding forms, so no registry row is reserved and no number is
  minted. Arms are held BY REFERENCE so identical arms deduplicate
  through `put`'s duplicate outcome. The children-first layout and the
  Level-0 admission argument extend unchanged.
- **Handler set: all of R10, unchanged.** Authenticated computation is a
  handler pair defined once at L-P and inherited through the embedding
  (DESIGN.md §3.4); a rung needing its OWN authenticated theorem is a
  tripwire saying the rung does not embed cleanly.
- **Owed theorems, named.** `L-A ↪ L-S` (a table is a branch-free
  guarded table — trivial, stated so the fragment inclusion is law) and
  `L-S ↪ L-P` with its agreement theorem in `runP_embed_agree`'s exact
  style, exact-fuel accounting included. Rigidity is a side condition
  that belongs in the statements, not in a footnote: SAF's free
  construction is free for RIGID selective functors only (`Over` is
  rigid, `Under` is not).
- **The first consumer, NAMED.** L-S is not built until a consumer is
  named, and ruling P7 (`EFFECT-AST-PLACEMENT.md`) named one:
  **`agentStep`** — already a program of the language
  (`examples/CasExamples/AgentStep.lean`), whose `require` on a loaded
  node's tag is exactly an L-S scrutinee: a decidable test on what a
  `load` returned. `cas_run` is the SURFACE that would carry it, not the
  consumer: `RunParams` (`Cas/Backend/Mcp.lean`) today carries a list of
  instructions with index-named references and no conditional, so it
  speaks L-A exactly, and growing it to L-S is an additive params change
  PLUS a `manifestVersion` bump (currently `0`), which is bumped only by
  ruling. What is still open is that bump and the forms on tags 14/15 —
  not a tag reservation, and no longer the consumer.

### L-P — the free monad (monadic strength). LANDED.

- **Carrier.** `Prog CasSig` (`Cas/Lang/Prog.lean`): finite syntax whose
  continuations are HOST FUNCTIONS.
- **Static analysis: NONE, and impossible for this carrier.** Not
  missing — impossible. `Prog.vis` holds `S.Ans op → Prog S A`, so any
  fold over `Prog` must SUPPLY an answer to proceed, while the
  `Const`-shaped carriers that compute an effect summary have no answer
  to give. The estate's own spelling of the same fact: `interpret`
  demands `Monad M`, and `Const` is not a monad. A selective carrier's
  arms are closed programs rather than functions of an answer, which is
  precisely why L-S admits an analysis and L-P cannot.
- **Store encoding: NO — this is R7's boundary.** Programs are content;
  hosts are code. A continuation is a host function and has no canonical
  byte representation, so `Prog` is not content at any effort. That is
  why F3 exists: `PProg` is the fragment that IS content.
- **Handler set: all of R10.** `Prog` is where handlers are defined.
- **Theorems by name.** `LawfulMonad (Prog S)`, `interpret_id`,
  `eq_of_forall_interpret` (initiality — agreement under every
  interpretation IS equality), `interpret_bind` (the monad-morphism law,
  one proof for every semantics), `run_interpretRef_agree` (the fueled
  small-step run and the big-step reference meaning are one semantics),
  and `ObsEq` with its three run corollaries (`Representation.lean`).

---

## What another effect system may assume — the interop contract

Written for a consumer OUTSIDE Lean: an Effect-TS service, a transport,
or an agent driving the MCP tools. Each rung's row is what you may rely
on without reading a proof, and what you may not.

### If you are handed an L-A table (this is what `cas_run` carries today)

**You may assume, before running anything:**

1. **The read set is finite, known, and bounded by the envelope.** Every
   address the run consults is either a literal the table names or an
   address the table itself computed. Concretely: no run of the table
   from any word touches an address outside `reads ∪ answers` — proved
   as `runP_frame_sound`, for EVERY run and not only completing ones,
   out of `runPFrom_append_done` (a run reaches a line at exactly the
   history the table determined for the lines before it) and
   `PProg.answersFrom_prefix` (that history is a prefix of the whole
   table's, early stop included). The refusal half is stated separately
   at the observable, where the run itself names the address:
   `runP_absent_sound`. This is a frame condition, so a scheduler may
   compute read/write sets and a grant may be checked *before*
   execution — a proposed program is refused when its envelope exceeds
   the grant, decided without running.
2. **The write set is bounded by the declared put shapes, in order.** No
   run admits a node whose (version, tag, payload, reference-kind) shape
   is outside the table's declared list, and the order of what is
   actually written is a sublist of the declared order.
3. **The dataflow is a DAG in program order, and closure is decidable.**
   If the envelope reports `dataflowClosed`, the run cannot fail for a
   dangling answer index at any word — one whole refusal clause excluded
   statically.
4. **The program is content.** It has a byte identity, deduplicates,
   travels, and can be recovered from the store and run with the same
   result and the same envelope.
5. **The run halts.** `runP_halts` — it walks a finite table.

**You may NOT assume:**

- that the envelope is TIGHT. It over-approximates in exactly two places
  and you must budget for both: lines after a first refusal never
  execute, and a put of an already-stored node writes nothing. Sizing a
  quota by `putCount` is safe; billing by it is not.
- that the answer addresses are predictable without `H`. They are a
  function of `H` and the table, so a consumer that does not compute the
  same digest cannot predict them.
- that refusal words match across hosts. The estate's observation is the
  word on success and the REFUSAL ALONE on failure; two observationally
  equal programs may leave different partial words when they refuse
  (`ObsEq.run_refused`). Do not gate on a partial word.

### If you are handed an L-S guarded table (not yet available)

Everything above, with one change and one addition. Changed: the write
set becomes a genuine upper bound across branches, so `necessary` and
`possible` diverge and you must decide which one your use needs — SAF's
own split, over-approximation for provisioning, under-approximation for
parallelism. Added: conditional provenance — the branch not taken is
still named, by address.

### If you are handed an L-P `Prog`

**Assume nothing statically.** There is no effect summary, no read set,
no write set, and no way to obtain one; the carrier forbids it. Handle it
or do not accept it. If a producer wants a program you can analyse, it
must hand you a table, not a `Prog` — and that, not aesthetics, is why
the fragment exists.

---

## Which rung do the shipped surfaces speak?

- **`cas_run` speaks L-A.** `RunParams` is a list of instructions with
  index-named references and no conditional (`Cas/Backend/Mcp.lean`),
  and `RunParams.toPProg` maps it onto this module's carrier.
- **`lake exe emitprograms` emits L-A.** `Tree.progK` unfolds to a
  straight line, one put per node, children first, later references
  naming earlier answers. Every emitted program in the estate is L-A, so
  nothing regresses when L-S is added.
- **`deriving Described` / `cas_struct` emit SCHEMA CODES**, which are
  stratum-1 data and not programs at any rung. Do not read a schema code
  as a program.

---

## Citations

- **SAF** — A. Mokhov, G. Lukyanov, S. Marlow, J. Dimino, *Selective
  Applicative Functors*, ICFP 2019, PACMPL 3(ICFP) art. 90,
  doi:10.1145/3341694. Cited here for: the class and Table 1's
  positioning (`<*>` static and parallel; `select` adds conditional
  execution while KEEPING static visibility; `>>=` loses it), §2.2
  `Over`/`Under` and rigidity, §2.3's laws forcing `select = selectM` on
  a monad, §3.2's over/under use-case split, and §5.1's rigid normal form
  and free construction. **CORPUS PIN PENDING** — SAF is not yet
  G0-pinned in `.reference/provenance/papers.lock.json`; the row in
  `.reference/catalog/REFERENCES.md` carries the same status. No claim in
  this library depends on SAF being correct: it is cited as the source of
  the VOCABULARY (over/under approximation, the sandwich, rigidity) and
  as the statement of a gap the estate can close. §"static analysis"
  asserts `necessary ⊆ actual ⊆ possible` and does not prove it; the
  proved instance for L-A is in `Defun.lean`, and the reason the estate
  can state it is that it has a canonical byte-decidable observation of a
  run — the word — where SAF has none.
- **ITrees lineage** — the `Ret`/`Vis` fragment of interaction trees, and
  *HITrees: Higher-Order Interaction Trees* (arXiv:2510.14558), already
  G0-pinned in the paper corpus (`.reference/catalog/PAPERS.md`,
  semantics-carriers cluster) and cited by EFFECTS-BACKEND R1 for
  `Prog`'s carrier choice. Relevant to this page for one reason: ITrees'
  `interp` is defined by `iter` and demands `MonadIter` of the target,
  while `Prog` is finite and interprets into ANY monad by structural
  recursion. That obligation returns exactly when a rung adds loops, and
  no rung above does.
- **Estate.** `library/cas/EFFECTS-BACKEND.md` (R1, R5, R7, R10, R14,
  R14a); `.staging/operational-structure/DESIGN.md` §§2–3 (the ladder,
  hash-determined dataflow, the sandwich, and the terms proposed for
  minting) — staging grade, not ratified.
-/

namespace Cas.Lang

end Cas.Lang
