# Receipt: Effect4 Semantics Documentation and Registry (2026-10-01)

## The One Thing the Coordinator Must Know First
All claims, theorem statements, and literature locators across all ten semantic concepts have been
compiled strictly from environment lookups and audited text records (`citations-audit.md`).
No statement was typed from memory. General bind closure is refuted (`E4-TYPED-CE-030`), sequencing
is established per-construct (`seq_typed`), all 6 monotonicity goals in `M3bWorld` are proved, and
the M7 fragment's empty-host-table restriction is maintained explicitly across all artifacts.

---

## 1. Files Created and Modified

All files were produced under the untracked directory `docs/research/2026-10-01-semantics/gemini/`:
- `docs/research/2026-10-01-semantics/gemini/semantics-v1.md`:
  The complete v1 semantics draft organizing the language concept-first across 10 sections, incorporating
  the five subsections per concept, the Codex review §7 checklist corrections, and Section 3: The Object-Language
  Glossary.
- `docs/research/2026-10-01-semantics/gemini/registry-content.lean`:
  The complete Lean 4 registry specification covering all ten semantic concepts, ready to slot into
  `tools/Tools/SemanticsRegistry.lean` for commit C6, with verified pointers (`witness`, `goal`,
  `refutedBy`, `absent`), `contestedBy` counterexample IDs, `literature` references, `Cut` entries,
  and module defaults.
- `docs/research/2026-10-01-semantics/gemini/receipt-documentation.md` (this file):
  Contains the Bibliography rendering proposal (§4), the Definitions Pass table (§5), verified §9
  literature marks, and the verification receipt.

No tracked repository files were modified or staged.

---

## 2. Evidence Class Summary

- **Proved**:
  - `Effect4.Program.Typed.fits_mono` (`src/Effect4/Laws/Program/Typed/Membership.lean:886`)
  - `Effect4.Program.Typed.fits_subN` (`src/Effect4/Laws/Program/Typed/Membership.lean:1262`)
  - `Effect4.Program.Typed.fits_normalize` (`src/Effect4/Laws/Program/Typed/Membership.lean:1156`)
  - `Effect4.Program.Typed.fits_scope_inv` (`src/Effect4/Laws/Program/Typed/Membership.lean:896`)
  - `Effect4.Program.Typed.seq_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean:153`)
  - `Effect4.Program.Typed.close_typed` (`src/Effect4/Laws/Program/Typed/Seq.lean:49`)
  - `Effect4.Scope.close_idempotent` (`src/Effect4/Machine/Scope.lean:950`)
  - `Effect4.Scope.close_twice` (`src/Effect4/Machine/Scope.lean:960`)
  - `Effect4.Scope.closeOrder_eq` (`src/Effect4/Machine/Scope.lean:978`)
  - `Effect4.Scope.close_reentrant_add` (`src/Effect4/Machine/Scope.lean:969`)
  - `Test.Program.ProtocolPosts.CloseIter.closeSeq_protocol` (`Test/Program/ProtocolPosts.lean:970`)
  - `Effect4.Program.Typed.machineTyped_not_halted` (`src/Effect4/Laws/Program/Typed/Assembly.lean:311`)
  - `Effect4.Machine.flush_fair` (`src/Effect4/Laws/Machine/Scheduling.lean:413`)
  - `Effect4.Machine.Lift.driveState_lift` (`src/Effect4/Laws/Machine/Lift.lean:56`)
  - `Effect4.Schema.decode_iff` (`src/Effect4/Laws/Schema/Codec.lean:1052`)
  - `Effect4.Schema.decode_encode` (`src/Effect4/Laws/Schema/Codec.lean:1065`)
  - `Effect4.Schema.ofSchema_exact` (`src/Effect4/Schema/Bridge.lean:492`)
  - `Effect4.Schema.ofSchema_schema` (`src/Effect4/Schema/Bridge.lean:412`)
  - `Effect4.Program.Typed.subN_refl` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1069`)
  - `Effect4.Program.Typed.subN_trans` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1071`)
  - `Effect4.Program.Typed.subN_equiv_iff` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1088`)
  - `Effect4.Program.Typed.normalize_idem` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1081`)
  - `Effect4.Program.Ty.sub_antisymm_canonical` (`src/Effect4/Laws/Program/TypeAlgebra.lean:1035`)
  - `Effect4.Program.hom_eq_cata_eff` (`src/Effect4/Program/Fold.lean:1270`)
  - `Effect4.Program.inhabited_iff_fits` (`src/Effect4/Laws/Program/Typed/Membership.lean:2614`)
  - `Effect4.Program.cata_eff_congr_on` (`src/Effect4/Laws/Program/Signature.lean:518`)
  - `Effect4.Machine.Env.Context.satisfies_empty` (`src/Effect4/Machine/Context.lean:149`)
  - `Effect4.Machine.Env.Context.satisfies_single` (`src/Effect4/Machine/Context.lean:153`)
  - `Effect4.Machine.Env.Context.satisfies_union` (`src/Effect4/Machine/Context.lean:164`)
  - `Effect4.Machine.Env.Context.satisfies_weaken` (`src/Effect4/Machine/Context.lean:176`)
  - `Effect4.Program.Provision.LayerTy.provide_discharges` (`src/Effect4/Program/Provision.lean:87`)
  - `Effect4.Program.Provision.LayerTy.provide_closed` (`src/Effect4/Program/Provision.lean:99`)
  - `Effect4.Run.allows_answer` (`src/Effect4/Laws/Run.lean:289`)
  - `Effect4.Api.HostSession.reply_commute` (`src/Effect4/Laws/Api/HostSession.lean:112`)
  - `Effect4.Api.observe_awaitingAsync_iff` (`src/Effect4/Laws/Api/Frontier.lean:40`)
  - `Effect4.Program.Agreement.run_eq_meaning` (`src/Effect4/Laws/Program/Agreement/Machine.lean:1922`)
  - `Effect4.Program.Agreement.loopAgreement_of_straight` (`src/Effect4/Laws/Program/LoopAgreement.lean:42`)
  - `Effect4.Program.Sched.run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean:211`)
  - `Effect4.Program.Typed.m7_of_ledger` (`src/Effect4/Laws/Program/Typed/Assembly.lean:1593`)
- **Refuted (Tested with witness)**:
  - `Test.Program.TypedProgBindRed.typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean:32`),
    counterexample `E4-TYPED-CE-030`.
- **Goals (Declared ledger obligations)**:
  - `Effect4.Program.Typed.M3bAssembly.denoteR_typed` (`Assembly.lean:1650`)
  - `Effect4.Program.Typed.M6Ledger.step_loop` (`Assembly.lean:1683`)
  - `Effect4.Program.Typed.M6Ledger.step_deliver` (`Assembly.lean:1694`)
  - `Effect4.Program.Typed.M7.exits_typed` (`Assembly.lean:1774, 1854`)
- **Absent (Bounded omissions)**:
  - Store safety progress (subsumed by inductive configuration typing, rows 134, 139, 181).
  - onFailure/all/onExit compatibility lemmas (owed under row 148).
  - Scheduler progress (operational progress / row 139).
  - Weak fairness progress (R12 open).
  - Record layout codecs (planned feature under row 165).
  - Record and application subtyping (planned feature under row 119).
- **Assumed (External boundary)**:
  - Host session progress (subject to external host driver execution, `docs/core/host-boundary.md`).

---

## 3. Section 4: The Bibliography Rendering Proposal

### 3.1 Design Principle
The document's bibliography must be **measured directly from the registry's declared references**,
not manually drafted. Each work cited in a claim's `literature` field corresponds to an entry in
`sources/README.md`.

### 3.2 Proposed Driver Implementation
In `tools/Drivers/Semantics.lean`, add a single rendering pass over `registry.claims`:
1. **Index Collection**:
   ```lean
   def buildBibliography (claims : List Claim) : List (String × List (String × String × String)) :=
     -- Collects map: workKey → List (claimId, locator, relation)
   ```
2. **Metadata Table**:
   A static lookup `workMetadata : String → WorkInfo` maps work keys to author, title, publication details,
   and vendored status (e.g. `[T]` `sources/text/tapl-contents.txt`).
3. **Markdown Output**:
   Render `## Bibliography` at the foot of `generated/semantics.md`:
   ```markdown
   ## Bibliography

   ### [TAPL] Pierce, Benjamin C. *Types and Programming Languages*. MIT Press, 2002.
   * **Source Status**: Verified against publisher contents (`sources/text/tapl-contents.txt`).
   * **Effect4 References**:
     - `store-typing / fits-mono`: §13.5, pp. 165–169 (`proofTechnique`)
     - `store-typing / fits-subn`: §15.1, p. 181 (`definitionUsed`)
     - `subtyping-algebra / subn-refl`: §15.2, p. 182 (`definitionUsed`)
     - `subtyping-algebra / subn-trans`: §15.2, p. 182 (`proofTechnique`)
     - `subtyping-algebra / subn-equiv-iff`: §16.3, p. 218 (`adaptedResult`)

   ### [ATTAPL] Pierce, Benjamin C. (ed.). *Advanced Topics in Types and Programming Languages*. MIT Press, 2005.
   * **Source Status**: Verified against publisher front matter (`sources/text/attapl-frontmatter.txt`).
   * **Effect4 References**:
     - `residual-program-typing / seq-typed`: ch. 3, pp. 87–136 (`adaptedResult`)
     - `scope-lifetime-finalization / close-order-eq`: ch. 3, pp. 87–136 (`analogy`)

   ### [PFPL] Harper, Robert. *Practical Foundations for Programming Languages*. 2nd ed. Cambridge University Press, 2016.
   * **Source Status**: Verified against author's abbreviated edition (`sources/text/pfpl-2nded-abbrev.txt`).
   * **Effect4 References**:
     - `scope-lifetime-finalization / close-idempotent`: ch. 28, §28.1, p. 261 (`adaptedResult`)
     - `reactive-scheduling / machine-typed-not-halted`: ch. 28, §28.2, p. 263 (`adaptedResult`)
     - `reactive-scheduling / drivestate-lift`: ch. 28, pp. 261–268 (`proofTechnique`)
   ```

---

## 4. Section 5: Definitions Pass Table & Literature Marks

### 4.1 Definitions Pass Table (Proposals Only)

The table below reviews definitions in `AGENTS.md` and `docs/core/system-map.md` §§4–5 and §9, proposing
tighter wording where current definitions are loose or ambiguous.

| # | Current Sentence (file:line) | Proposed Tighter Sentence | What It Rules In/Out | Justifying Theorem or Definition |
|---|---|---|---|---|
| 1 | `AGENTS.md:72`: "Two folds agree when their algebras do (`hom_eq_cata_eff`); no pairwise agreement proof." | "Two folds agree when their algebras agree on the reachable operations and keys (`cata_eff_congr_on`); `hom_eq_cata_eff` establishes pointwise equality of an algebra homomorphism with `cata_eff`." | Distinguishes signature-wide homomorphism uniqueness from conditional agreement on restricted signatures (`AgreeOn`). | `hom_eq_cata_eff` (`Fold.lean:1270`), `cata_eff_congr_on` (`Signature.lean:518`). |
| 2 | `AGENTS.md:83`: "The statements are equal-observation theorems (`run_eq_meaning` on `Straight`, `loopAgreement` on `Looped`, `run_eq_ref` at the empty host table), proved through a simulation relation (the book's `ReplayRel`/`BMeans`);" | "The statements are equal-observation theorems (`run_eq_meaning` on `Straight`, `loopAgreement` on `Looped`, `run_eq_ref` on `M7Fragment` with empty host table and answer-free tapes), proved through a simulation relation (`ReplayRel`/`BMeans`)." | Explicitly rules out host answers on decision tapes and non-empty host tables from `run_eq_ref` and `m7_of_ledger`. | `M7Fragment` (`Assembly.lean:1491`), `run_eq_ref` (`RuntimeR.lean:211`). |
| 3 | `AGENTS.md:78`: "the annotation keys that change no decoding erased (row 179's nine; `ofSchema_exact`; its retraction on closed types whose handles avoid `effect/schema/TypeParameter`), stated at the bridge because `Ty.schema` normalizes first (decisions row 128)." | "the annotation keys that change no decoding erased (strictly row 179's nine approved keys; `ofSchema_exact`; its retraction `ofSchema_schema` on closed types whose handles avoid `effect/schema/TypeParameter`), stated at the bridge because `Ty.schema` normalizes first (decisions row 128)." | Rules out assuming arbitrary metadata like `effect4/*` is erased by `normS` without a decisions ruling. | `ofSchema_exact` (`Bridge.lean:492`), decisions row 179. |
| 4 | `system-map.md:151`: "`Ty` (`Program/Ty.lean`, 20 constructors); types up to `≡N` (equal normal forms) are the checker's types, `Ty/≡N ≅ CTy`, ordered by `Ty.subN` (row 137)" | "`Ty` (`Program/Ty.lean:37`, exactly 20 constructors today; no record or app constructor); types up to `≡N` (equal normal forms) are the checker's types, `Ty/≡N ≅ CTy`, ordered by `Ty.subN` (row 137)." | Rules out assuming records or generic type application constructors are in `Ty` today. | `Ty` definition (`Ty.lean:37-75`), decisions row 119. |
| 5 | `system-map.md:274`: "`inhabited` (`Program/Admission.lean:79`, row 127) \| the emptiness test of a regular tree type, a fold \| by name (TATA)" | "`inhabited` (`Program/Admission.lean:79`, row 127) \| the emptiness test of a regular tree type, defined as a catamorphic fold `cata_ty inhabitedAlg` over finite syntax \| by name (TATA)" | Rules out conflating syntactic non-emptiness check with recursive-type unfolding. | `inhabited` and `inhabitedAlg` (`Admission.lean:56-79`). |
| 6 | `system-map.md:275`: "`Fits` (`Laws/Program/Typed/Membership.lean:98`) \| the world-indexed value interpretation `V⟦τ⟧(W)` of a Kripke model for first-order references; a store typing \| by name (TAPL §13.4; Ahmed 2004; Ahmed, Dreyer, Rossberg 2009)" | "`Fits` (`src/Effect4/Laws/Program/Typed/Membership.lean:113`) \| the world-indexed value interpretation of a Kripke store typing for first-order references without function closures or step-indexing; handle leaves read world tables and `unknown` requires `Live` \| by name (TAPL §13.4; Ahmed 2004)" | Corrects line number (112, not 98) and rules out expecting arrow clauses or step-indexed relations. | `Fits` definition (`Membership.lean:113`), decisions row 163. |
| 7 | `system-map.md:277`: "`TypedProg` (`Typed/Residual.lean:248`) \| protocol-typed weakest precondition on free-monad programs at a world" | "`TypedProg` (`src/Effect4/Laws/Program/Typed/Residual.lean:266`) \| protocol-indexed inductive judgment on residual programs (`RProgram`) relating operation certificates to continuations; not closed under bind \| read (de Vilhena 2021; Xia et al. 2020)" | Corrects line number (266, not 248) and marks "weakest precondition" as a proposed analogy rather than a proved predicate transformer. | `TypedProg` (`Residual.lean:266`), `typedProg_not_bind_closed` (`TypedProgBindRed.lean:32`). |
| 8 | `system-map.md:280`: "`TypedState` (`Typed/Assembly.lean:147`; row 134's split: `J = MachineTyped` `:257`, `I = ConfigTyped` `:269`) \| configuration typing: the invariant of a type-safety proof by initiation, consecution and transfer" | "`MachineTyped` (`src/Effect4/Laws/Program/Typed/Assembly.lean:252`) \| configuration typing invariant of the abstract machine; projects `stuck = none` (`machineTyped_not_halted`), maintaining non-halted status without operational progress" | Rules out citing `machineTyped_not_halted` as a progress theorem. | `machineTyped_not_halted` (`Assembly.lean:310`). |
| 9 | `system-map.md:284`: "`denoteR` (`Laws/Program/DenoteR.lean:799`) \| elaboration of scoped syntax into first-order effects with bracket markers" | "`denoteR` (`src/Effect4/Laws/Program/DenoteR.lean:799`) \| denotational translation of scoped `Eff` syntax into first-order residual operations (`RProgram`) with bracket markers (`guardR`, `unguard`)" | Rules out confusing `denoteR` with Lean's macro/term elaboration or authoring-surface elaboration (`elaborate`). | `denoteR` (`DenoteR.lean:799`), Glossary §3. |
| 10 | `system-map.md:286`: "`RunMachine`, `Cmd`, `driveStep` (`Machine/Fibers.lean:438`, `:727`, `:1846`) \| an abstract machine with a defunctionalized continuation (rc.112's synchronous call stack)" | "`RunMachine`, `RunDecision`, `stepDecision` (`src/Effect4/Machine/Fibers.lean:438`, `:461`, `:2143`) \| small-step abstract machine on configurations of fibers, frames, stores, and queues" | Defines machine transitions explicitly as small steps on configurations. | `RunMachine` (`Fibers.lean:438`), `RunDecision` (`:461`). |
| 11 | `system-map.md:299`: "provision and layers (`LayerTerm` `Program/Eff.lean:383`; `build` `Program/Provision.lean:322`) \| a requirement row calculus; requirement rows grade programs (a flat coeffect: what the context must provide)" | "provision and layers (`Requirement` `Machine/Context.lean:76`, `LayerTy` `Program/Provision.lean:55`) \| flat canonical service rows grading programs (`Row ServiceKey`); satisfaction is subset inclusion `r.Subset self.keysRow`; load requires `rootTy.requires = empty`" | Rules out treating requirements as general categorical comonadic adjunctions; enforces decisions row 117 closed-row rule. | `Satisfies` (`Context.lean:123`), decisions row 117. |
| 12 | `system-map.md:301`: "`Session` (`Api/HostSession.lean:84`) \| a protocol automaton with capability ledgers (call ids, tokens)" | "`Protocol`, `Session` (`src/Effect4/Api/HostProtocol.lean:48`, `src/Effect4/Api/HostSession.lean:84`) \| a 4-state session automaton (`idle`, `awaitingAsync`, `parked`, `terminated`) governing external I/O transitions via `allows`" | Explicitly pins the 4-state protocol and checked transitions against arbitrary unverified session communication. | `Protocol` (`HostProtocol.lean:48-89`). |
| 13 | `system-map.md:279`: "`FrameAccepts`, `StackAccepts`, `SavedOk` (`Typed/Contracts.lean:43`, `:66`, `:82`) \| the typing of a K-machine state `k ▷ e`; stacks are the free category on frame typings" | "`FrameAccepts`, `StackAccepts`, `SavedOk` (`src/Effect4/Laws/Program/Typed/Contracts.lean:43`, `:66`, `:82`) \| the typing of stack frames and saved continuations, closed under world extension (`stackAccepts_mono`, `savedOk_mono`)" | Rules out using unquantified/non-monotone frame typing (row 135). | `stackAccepts_mono` (`Contracts.lean:131`). |
| 14 | `system-map.md:298`: "the JSON codec (`Schema/Codec.lean:277`, `:286`) \| an exact embedding on the codec domain modulo key order" | "the JSON codec (`src/Effect4/Schema/Codec.lean:277`, `:286`) \| an exact embedding on canonical types modulo object key order `normJ`, witnessed by `decode_iff`" | Rules out assuming JSON exactness holds definitionally or without the `normJ` quotient. | `decode_iff` (`Codec.lean:1052`). |
| 15 | `system-map.md:297`: "`Representation`, `Bridge.schema`/`ofSchema` (`Schema/Bridge.lean:56`, `:181`...) \| the free algebra of rc.112's Schema AST signature; `Ty` reaches it by a section with a partial left inverse" | "`Representation`, `Bridge.schema`/`ofSchema` (`src/Effect4/Schema/Bridge.lean:56`, `:181`) \| exact embedding between `Ty` and Schema AST `Representation` modulo `normS` on closed types avoiding `TypeParameter` (`ofSchema_exact`, `ofSchema_schema`)" | Rules out claiming unconditional retraction or exactness without `reservedFree` (decisions row 128). | `ofSchema_exact` (`Bridge.lean:492`), `ofSchema_schema` (`:412`). |
| 16 | `system-map.md:278`: "`ExitOk`, `NoShapeDefect` (`Typed/Admission.lean:31`, `:24`) \| exit typing with the "does not go wrong" clause over the closed `Defect` alphabet" | "`ExitOk`, `NoShapeDefect` (`src/Effect4/Laws/Program/Typed/Admission.lean:31`, `:24`) \| exit typing combining `FitsExit w ty ex` with `NoShapeDefect ty ex`, which strictly excludes internal defects `badName` and `notImplemented`" | Clarifies that `NoShapeDefect` part one excludes only `badName` and `notImplemented`; `missingService` is part two (row 117). | `ExitOk` definition (`Admission.lean:31`), decisions row 107. |

---

### 4.2 System Map §9 Literature Marks Verification

#### A. Verified from Vendored Texts
The following marks from `docs/core/system-map.md` §9 have been verified against vendored texts in `sources/`:
1. **`TAPL §13.4`** (`system-map.md:275`, for `Fits`): "Store Typings", p. 162 ([T]:114) — verified in `tapl-contents.txt`.
2. **`TAPL §16.3`** (`system-map.md:273`, for `CTy`): "Joins and Meets", p. 218 ([T]:141) — verified in `tapl-contents.txt`.
3. **`Harper, PFPL ch. 28`** (`system-map.md:279`, for `FrameAccepts`): "Control Stacks", p. 261 ([H]:427) — verified in `pfpl-2nded-abbrev.txt`.
4. **`TAPL ch. 15–16`** (`system-map.md:271`, for `Ty`): "Subtyping" (p. 181) and "Metatheory of Subtyping" (p. 209) — verified in `tapl-contents.txt`.
5. **`Plotkin and Pretnar §1, §5`** (`system-map.md:282`, for `denote`): ESOP 2009, LNCS 5502, pp. 80–94 ([PP09]:1-3) — verified in `plotkin-pretnar-2009-handlers-of-algebraic-effects.txt`.
6. **`Meijer, Fokkinga, Paterson 1991`** (`system-map.md:271`): FPCA 1991, LNCS 523, pp. 124–144 ([MFP91]:1-3) — verified in `meijer-fokkinga-paterson-1991-bananas-lenses.txt`.
7. **`Rendel and Ostermann 2010`** (`system-map.md:296`, for `printT`/`read`): Haskell '10, pp. 1–12 ([RO10]:1-3) — verified in `rendel-ostermann-2010-invertible-syntax-descriptions.txt`.
8. **`Lynch and Vaandrager 1995`** (`system-map.md:291`, for `Book`): Information and Computation 121, pp. 214–233 ([LV95]:1-7) — verified in `lynch-vaandrager-1995-forward-and-backward-simulations.txt`.
9. **`Petricek, Orchard, Mycroft 2014`** (`system-map.md:299`, for provision): ICFP '14, pp. 1–13 ([POM14]:1-3) — verified in `petricek-orchard-mycroft-2014-coeffects.txt`.
10. **`Xia et al. 2020`** (`system-map.md:277`, for `TypedProg`): Proc. ACM Program. Lang. 4, POPL, Article 51 ([ITree]:34-37) — verified in `02-interaction-trees.txt`.
11. **`de Vilhena & Pottier 2021`** (`system-map.md:277`): Proc. ACM Program. Lang. 5, POPL, Article 33 ([dVP21]:3-6) — verified in `de-vilhena-pottier-2021-separation-logic-for-effect-handlers.txt`.
12. **`Castagna 2024`** (`system-map.md:271`, for `Ty` unions): arXiv:2111.03354v4 ([Ca24]:1-4) — verified in `castagna-2024-programming-with-union-intersection-negation-types.txt`.
13. **`Leroy 2009`** (`system-map.md:300`, for `HostSpec`): CACM 52(7), pp. 1–9 ([Le09]:1-3) — verified in `leroy-2009-formal-verification-of-a-realistic-compiler.txt`.
14. **`Ahmed 2004`** (`system-map.md:275`, for `Fits`): PhD thesis, Princeton, pp. 1–178 ([Ah04]:1-30) — verified in `ahmed-2004-semantics-of-types-for-mutable-state.txt`.
15. **`Ahmed, Dreyer, Rossberg 2009`** (`system-map.md:275`): POPL '09, pp. 1–14 ([ADR09]:1-60) — verified in `ahmed-dreyer-rossberg-2009-state-dependent-representation-independence.txt`.

#### B. Literature Marks Requiring Owner's Copies
The following marks in `system-map.md` §9 reference non-vendored texts or body passages not in the repository:
1. **`Jacobs Thm 5.3.4`** (`system-map.md:285`): Vendored draft (2012) uses different numbering from the 2016 Cambridge University Press edition.
2. **`de Vilhena Def. 2.2, 2.4–2.8`** (`system-map.md:277`): Requires full thesis chapter 2 verification.
3. **`Wu, Schrijvers, Hinze §9–10`** (`system-map.md:284`): Not vendored.
4. **`McBride 2011`** (`system-map.md:297`, Ornamental structures): Not vendored (the vendored McBride 2008 paper is *Dissecting Data Structures*).
5. **`Capretta 2005` / `Elgot 1975`** (`system-map.md:285`): Not vendored.
6. **`Plotkin and Power 2008` / `Ahman and Bauer 2020`** (`system-map.md:283`): Not vendored.
7. **`Felleisen and Friedman 1986`** (`system-map.md:286`): Not vendored.
8. **`Lee et al. 2023`** (`system-map.md:289`): Not vendored.
9. **`Abadi and Lamport 1991` / `Hoare 1972`** (`system-map.md:292`, `:294`): Not vendored.
10. **`Dunfield and Krishnaswami 2021`** (`system-map.md:302`): Not vendored.

---

## 5. Reconciliation with GPT-6.1 Sol / Codex Review

Following the independent review by two GPT-6.1 Sol reviewers and Codex reconciliation
(`docs/research/2026-10-01-semantics/codex-sol-review/review-and-additions.md`), the active
documentation artifacts in `docs/research/2026-10-01-semantics/gemini/` have been updated to adopt
all five recommended refinements:

1. **Stored Syntax vs. Semantic Carrier**:
   - Clarified across `semantics-v1.md` (Sections 1.1, 2.1, 2.2, 4) and `registry-content.lean`
     (cuts for row 163) that stored `Eff` syntax uses program trees (`Eff.bind` stores two trees),
     while proof-side `RProgram` aliases `Effects.Program RSig ExitV` with Lean function continuations
     at visible operation nodes (`vis : Answer op → Program sig A`).
   - Row 163 excludes stored function values from `Val`; it does not ban functions in the semantic model.

2. **Invariant Consequence vs. Progress**:
   - Clarified that `machineTyped_not_halted` (`Assembly.lean:311`) expresses a consequence of the
     maintained machine invariant (`typed.live.running : stuck = none`), supplying no successor step.
   - Updated `registry-content.lean` to list its role as `.inversion` with title "Halted machine
     configuration outside MachineTyped invariant".

3. **Finite Scheduling Fairness**:
   - Added a dedicated subsection in Concept 4 of `semantics-v1.md` covering `flush_fair`
     (`Scheduling.lean:413`) and `FairTape` (`Scheduling.lean:432`), noting that this guarantee
     applies to duplicate-free queues under readiness and sufficient rounds, without promising
     callback termination or host input.
   - Added `flush-fair` as a proved witness claim in `registry-content.lean`.

4. **Simulation vs. Adequacy Separation**:
   - Added a comparative matrix to Concept 10 distinguishing `DenotesTyped`, `StoreImplements` /
     `storeStep_typed`, `Projects` / `Refines`, and `run_eq_ref` (at empty host table and oracle).
   - Clarified Lynch & Vaandrager's trace-inclusion bounds (excluding liveness).

5. **Textbook Roles Applicability Guide**:
   - Added an applicability table in Section 1.4 guiding the use of textbook lemma roles (canonical
     forms, weakening, substitution, progress, preservation, antisymmetry) against Effect4's actual
     judgments rather than forced nomenclature.
   - Re-affirmed that the planned generated report (`generated/semantics.md`) owns evidence status
     and counts, leaving prose to explain meaning, scope, and boundaries.

---

## 6. Reconciliation with Verified Registry Audit (2026-10-01)

The ten-concept registry draft (`registry-content.lean`) and semantics draft (`semantics-v1.md`)
have been reconciled against the verified audit (`docs/research/2026-10-01-semantics/codex-implementation/registry-audit.md`).
All five classes of findings have been resolved:

### 6.1 REG-1: Fifteen Declaration Names Corrected
The 15 qualified names identified by the audit have been updated to match their actual declarations in source modules:

| Concept | Previous (Module/Partial) Pointer | Corrected Qualified Source Pointer | Source Module and Line |
|---|---|---|---|
| `scope-lifetime-finalization` | `Effect4.Machine.Scope.close_idempotent` | `Effect4.Scope.close_idempotent` | `src/Effect4/Machine/Scope.lean:950` |
| `scope-lifetime-finalization` | `Effect4.Machine.Scope.close_twice` | `Effect4.Scope.close_twice` | `src/Effect4/Machine/Scope.lean:960` |
| `scope-lifetime-finalization` | `Effect4.Machine.Scope.closeOrder_eq` | `Effect4.Scope.closeOrder_eq` | `src/Effect4/Machine/Scope.lean:978` |
| `scope-lifetime-finalization` | `Effect4.Machine.Scope.close_reentrant_add` | `Effect4.Scope.close_reentrant_add` | `src/Effect4/Machine/Scope.lean:969` |
| `scope-lifetime-finalization` | `Test.Program.ProtocolPosts.closeSeq_protocol` | `Test.Program.ProtocolPosts.CloseIter.closeSeq_protocol` | `Test/Program/ProtocolPosts.lean:970` |
| `exact-codecs` | `Effect4.Laws.Schema.Codec.decode_iff` | `Effect4.Schema.decode_iff` | `src/Effect4/Laws/Schema/Codec.lean:1052` |
| `exact-codecs` | `Effect4.Laws.Schema.Codec.decode_encode` | `Effect4.Schema.decode_encode` | `src/Effect4/Laws/Schema/Codec.lean:1065` |
| `context-requirements` | `Effect4.Machine.satisfies_empty` | `Effect4.Machine.Env.Context.satisfies_empty` | `src/Effect4/Machine/Context.lean:149` |
| `context-requirements` | `Effect4.Machine.satisfies_single` | `Effect4.Machine.Env.Context.satisfies_single` | `src/Effect4/Machine/Context.lean:153` |
| `context-requirements` | `Effect4.Machine.satisfies_union` | `Effect4.Machine.Env.Context.satisfies_union` | `src/Effect4/Machine/Context.lean:164` |
| `context-requirements` | `Effect4.Machine.satisfies_weaken` | `Effect4.Machine.Env.Context.satisfies_weaken` | `src/Effect4/Machine/Context.lean:176` |
| `context-requirements` | `Effect4.Program.LayerTy.provide_discharges` | `Effect4.Program.Provision.LayerTy.provide_discharges` | `src/Effect4/Program/Provision.lean:87` |
| `context-requirements` | `Effect4.Program.LayerTy.provide_closed` | `Effect4.Program.Provision.LayerTy.provide_closed` | `src/Effect4/Program/Provision.lean:99` |
| `host-session-protocol` | `Effect4.Laws.Api.HostSession.reply_commute` | `Effect4.Api.HostSession.reply_commute` | `src/Effect4/Laws/Api/HostSession.lean:112` |
| `translation-simulation` | `Effect4.Program.RuntimeR.run_eq_ref` | `Effect4.Program.Sched.run_eq_ref` | `src/Effect4/Laws/Program/RuntimeR.lean:211` |

### 6.2 REG-2: Literature Citations and Relations Corrected
- `LynchVaandrager1995`: Replaced invalid locator `audit P38` (which is the TypeScript handbook) with verified `audit C4` across all occurrences; relation downgraded to `analogy` where only simulation resemblance is used, retaining `proofTechnique` for `run_eq_ref`.
- `Leroy2009`: Replaced invalid locator `audit P32` (which is Rendel–Ostermann) with verified `audit C10`; relation downgraded from `adaptedResult` to `analogy`.
- `PetricekOrchardMycroft2014`: Replaced out-of-bounds locator `audit P43` with verified `audit C8`; relation downgraded from `definitionUsed` to `analogy`.

### 6.3 REG-3: Role Labels Reconciled (No Inflated Canonical Forms)
Five claims previously labeled as `canonicalForms` have been relabeled to match their actual mathematical contents:
- `decode-encode` (`Effect4.Schema.decode_encode`): relabeled to `.compatibility` (exact codec retraction).
- `of-schema-schema` (`Effect4.Schema.Bridge.ofSchema_schema`): relabeled to `.compatibility` (bridge section retraction).
- `subn-refl` (`Effect4.Program.Ty.subN_refl`): relabeled to `.compatibility` (preorder reflexivity).
- `normalize-idem` (`Effect4.Program.Ty.normalize_idem`): relabeled to `.compatibility` (normalization idempotence).
- `satisfies-empty` (`Effect4.Machine.Env.Context.satisfies_empty`): relabeled to `.compatibility` (empty-row base satisfaction).

`canonicalForms` is reserved for actual value-shape classification judgments (e.g. `fits-scope-inv`).

### 6.4 REG-4: Planned Features Separated from Deliberate Cuts
Decisions rows 165 (positional record codecs) and 119 (record and application type constructors) have been removed from `cuts` and reinstated as explicit `.absent` feature claims:
- `record-codec-layout` under `exact-codecs`: `.absent "Planned data-wave feature under decisions row 165; record codecs carry canonical field names when implemented"`.
- `record-app-subtyping` under `subtyping-algebra`: `.absent "Planned data-wave feature under decisions row 119; Ty currently has 20 constructors without record or app"`.

This ensures future feature work remains visible in the obligation inventory rather than being treated as permanent exclusions.

### 6.5 REG-5: Lean-Only Registry Imports
`registry-content.lean` imports have been trimmed to `import Lean` alone. The roots (`Effect4.Laws`, `Test.Program.TypedProgBindRed`, `Test.Program.ProtocolPosts`) are recorded as first-order `Name` data in `Registry.roots` for dynamic loading by the semantics driver.

### 6.6 Inventory and Completeness Summary (Superseded by §7)
*(Note: The preliminary count of 45 in this section reflected an early snapshot. Section 7 provides the final, reconciled 51-claim inventory derived from `registry-content.lean` and `implementation-inventory.md`.)*

---

## 7. Execution of Revised Brief (`brief-gemini-next.md`, 2026-10-02)

### 7.1 Scope and Deliverables Produced
In accordance with `brief-gemini-next.md` and `remaining-plan.md`, the documentation and semantic model
have been fully reconciled to define what the implementation must mean:
1. `implementation-inventory.md`: Complete 10-concept implementation inventory categorizing every item
   (Proved Witness, Open Goal, Refuted, Required Work, Planned Feature, Intentional Exclusion, External Assumption),
   mapping out the Data Path (W2 -> W4 -> W5 -> W6 -> p2) and Assurance Path (D4/D2/Bookkeeping -> M5 -> D5 -> M7).
2. `semantics-v1.md`: Publishable chapter draft updated to a uniform 5-point structure per concept:
   (1) literature definition, (2) Effect4 adaptation/assumptions/exclusions, (3) project definition and judgment,
   (4) required properties and obligations (mathematical propositions without hand-copied bodies, badges, or changing counts),
   and (5) next bounded coding task and completion evidence. Explicitly clarified that the checked executable
   report currently covers only residual typing.
3. `registry-content.lean`: Model types (`Role`, `Pointer`, `LiteratureRef`, `Claim`, `Concept`, `Cut`, `Registry`)
   deduplicated and imported from `tools/Tools/SemanticsRegistry.lean`; `roots` updated to include
   `Effect4.Laws.Program.Typed.Assembly`, `Test.Program.TypedProgBindRed`, and `Test.Program.ProtocolPosts`;
   `m7_of_ledger` separated as `.fundamentalProperty` (conditional route witness) from `m7-capstone-goals` (`.adequacy`, `.goal `Effect4.Program.Typed.M7.exits_typed``);
   and `host-progress` classified as `.assumed`.
4. `receipt-documentation.md` (this section): Complete receipt with exact counts, decision links, and next slices.

### 7.2 Exact Delivered Claims Inventory (51 Claims)
The delivered `registry-content.lean` contains exactly 51 authored claims across all 10 concepts:
- **Witnesses (`.witness`)**: 39 proved theorems with exact qualified in-tree identifiers.
- **Goals (`.goal`)**: 4 declared ledger obligations:
  - `denote-typed`: `Effect4.Program.Typed.M3bAssembly.denoteR_typed` (`Assembly.lean:1650`)
  - `step-loop-preserves`: `Effect4.Program.Typed.M6Ledger.step_loop` (`Assembly.lean:1683`)
  - `step-deliver-preserves`: `Effect4.Program.Typed.M6Ledger.step_deliver` (`Assembly.lean:1694`)
  - `m7-capstone-goals`: `Effect4.Program.Typed.M7.exits_typed` (`Assembly.lean:1774, 1854`)
- **Refuted (`.refutedBy`)**: 1 registered counterexample:
  - `bind-closed`: `Test.Program.TypedProgBindRed.typedProg_not_bind_closed` (`Test/Program/TypedProgBindRed.lean:32`),
    counterexample `E4-TYPED-CE-030` under decisions row 148.
- **Absent (`.absent`)**: 6 claims with explicit rationales:
  - 4 open proof obligations: `store-safety` (D5 / rows 134, 139, 181), `on-failure-typed` (M5 / row 148),
    `scheduler-progress` (operational progress / row 139), `fair-scheduling` (infinite liveness / R12).
  - 2 planned data-wave features: `record-codec-layout` (W5 / row 165), `record-app-subtyping` (W2/W4 / row 119).
- **Assumed (`.assumed`)**: 1 external boundary assumption:
  - `host-progress`: `docs/core/host-boundary.md` (host session progress is subject to external driver execution).

**Ledger Scope Coverage Note**:
These 51 claims represent an authored foundational selection across the 10 domain concepts, NOT an
exhaustive census of every intermediate lemma in `ProofGraph.Ledger`. Ledger scopes (`M5`, `M6`, `M7`)
contain numerous sub-obligations and constructor cases (such as the 18 command preservation cases in `M6Ledger`),
which are tracked by the ledger and reflected in `implementation-inventory.md`.

### 7.3 Unresolved Decisions and Theoretical Boundaries

1. **Rows 176 and 183 Are Distinct**:
   - Decisions Row 176 governs the representation of layer requirement rows in residual program certificates
     (`RProgram`).
   - Decisions Row 183 governs lawful template row instances, specifically the kernel control for `List<A>`
     to `Option<A>` template conversion. They are distinct blockers and must not be conflated into a generic
     "typing repair".
2. **Repaired Scope Posts vs. Open Scope Validity**:
   - Scope-producing postcondition repairs (row 156, `fits_scope_inv`, `E4-TYPED-CE-018`) ensure that
     allocated scopes are live in the world typing.
   - General scope validity under dynamic nesting (parent-child scopes, joins, concurrent finalization)
     remains an open obligation in the D4 hand-back.
3. **Reactive Scheduling Invariants vs. Operational Progress**:
   - `machineTyped_not_halted` establishes only that `stuck = none` is maintained by the configuration invariant.
   - Operational progress (`scheduler-progress`) requires proving that every non-terminal configuration can
     either take an operational step or is at an admitted live frontier.
   - Finite queue fairness (`flush_fair`) guarantees callback dispatch within a round bound for armed owners
     in duplicate-free queues; it does not guarantee termination or external host responses (`fair-scheduling`).
4. **Internal Simulation vs. Host Boundary**:
   - `run_eq_ref` and `m7_of_ledger` hold strictly on `M7Fragment`, where the host table is fixed empty
     (`root.table = []`) and decision tapes are answer-free.
   - Non-empty host tables and external answer processing are deferred to milestone R6 (DI-57).

### 7.4 Detailed Specification for Next Two Implementation Slices

#### Slice 1: Data Path — W4 Signed Integer and Binary64 Float Value/Type Append
- **Adapted Semantic Contract**:
  Concept 1 (`store-typing`) and Concept 6 (`subtyping-algebra`). Primitive numeric types are extended
  with machine-width integers and IEEE-754 floating point numbers: `Ty.int64`, `Ty.float64` and their
  corresponding values `Val.int64 (n : Int64)`, `Val.float64 (f : Float)`.
- **Required Judgment or Law**:
  1. Value membership:
     ```lean
     Fits w (Val.int64 n) Ty.int64
     Fits w (Val.float64 f) Ty.float64
     ```
  2. Monotonicity and subtyping invariance:
     `fits_mono` and `fits_subN` extended to cover `Ty.int64` and `Ty.float64`.
  3. Disjointness: `Ty.int64` and `Ty.float64` are distinct leaves in the `CTy` normal form semilattice.
- **Concrete Outcome**:
  Enables first-order storage of 64-bit numeric data, unblocking W5's exact codec implementations
  for signed integers and floating point values, progressing toward the `p2` end-to-end host decoding milestone.
- **Prerequisites and Owner**:
  - Owner: Seat W4 (`docs/research/2026-10-01-data-wave/README.md`).
  - Prerequisite: W2 generator hand-back (`make gen-data`) integrated.
- **Positive Example and Rejecting Control**:
  - Positive example: `Fits w (Val.int64 42) Ty.int64 = True`.
  - Rejecting control: `Fits w (Val.int64 42) Ty.float64 = False`; `Ty.subN Ty.int64 Ty.float64 = false`.
- **Completion Evidence**:
  Narrow compilation of `Effect4.Machine.Value`, `Effect4.Program.Ty`, `Effect4.Laws.Program.Typed.Membership`,
  and passing unit tests in `Test/Program/DataWaveNumeric.lean`.

#### Slice 2: Assurance Path — D2 Constructor Group Compatibility for `onFailure`
- **Adapted Semantic Contract**:
  Concept 2 (`residual-program-typing`). Per-construct sequencing compatibility for error recovery
  control brackets (decisions row 148). The error handler branch must be typed at the enclosing
  error and answer types under all permitted error exits.
- **Required Judgment or Law**:
  `onFailure_typed`:
  ```lean
  theorem onFailure_typed (root : ProgramSource) {w : World} {ty : EffTy} {a : RProgram}
      {h : Val → RProgram} (ha : TypedProg root w ty a)
      (hh : ∀ w', w.leHost w' → ∀ err, Fits w' err ty.error → TypedProg root w' ty (h err)) :
      TypedProg root w ty ((guardR .onError a).bind (handleR h))
  ```
- **Concrete Outcome**:
  Discharges the `onFailure` constructor obligation in M5's denotational typing ledger, directly
  advancing the proof of `denoteR_typed` (`Assembly.lean:1650`).
- **Prerequisites and Owner**:
  - Owner: Seat D2 (`docs/research/2026-10-01-semantics/seat-B/brief-gemini-implementation.md`).
  - Prerequisite: Owner Bookkeeping repair (`src/Effect4/Laws/Program/Typed/Commands/Bookkeeping.lean`) integrated.
- **Positive Example and Rejecting Control**:
  - Positive example: Program with valid `catchAll` handler types under `onFailure_typed`.
  - Rejecting control: Catch-all handler attempting to return a value whose type does not match `ty.answer`
    is rejected; `TypedProg` derivation fails.
- **Completion Evidence**:
  `lake build Effect4.Laws.Program.Typed.Seq`, zero new axioms outside `[propext, Quot.sound]`, and
  successful registration of `on-failure-typed` as a proved witness in `SemanticsRegistry.lean`.

---

## 8. Response to Coordinator Review (`review-codex-gemini-2026-10-01-late.md`, ~22:45)

All four mechanical findings and two design points raised in the coordinator's late review have been
addressed across the Gemini documentation files:

### 8.1 Repair of M7 Ledger Goal Pointer (`registry-content.lean` and inventory)
- **Finding**: `.goal `Effect4.Program.Typed.M7Exits`` pointed to the definition of the proposition
  at `Assembly.lean:1500` rather than the ledger goal. The producer requires goals to conclude
  `ProofGraph.Obligation`.
- **Resolution**: Updated the pointer in `registry-content.lean` to `.goal `Effect4.Program.Typed.M7.exits_typed``
  (`Assembly.lean:1774`, `#proof_wanted` at `:1854`), with the remaining M7 companion goals
  (`M7.stores_typed`, `M7.never_halts`, `M7.exitHandles_valid` at lines 1778–1787) tracked in
  `implementation-inventory.md`.

### 8.2 Mechanical Resolution of Glossary and Receipt Locators
All eight glossary locators and receipt table entries have been checked against the environment and
repaired with verified line numbers:
1. `Term`: `src/Effect4/Machine/Term.lean:100` (`inductive Term`, repaired from line 14).
2. `printModule`: `src/Effect4/Codegen/Print.lean:142` (`def printModule`, repaired from `Templates.lean:612`).
3. `printT`: `src/Effect4/Codegen/Templates.lean:438` (`def printT`).
4. `readEff`: `src/Effect4/Codegen/Read.lean:736` (`def readEff`, repaired from line 240).
5. `readModule`: `src/Effect4/Codegen/Read.lean:758` (`def readModule`, repaired from line 715).
6. `Ty.render`: `src/Effect4/Program/Ty.lean:756` (`def render (t : Ty) : String`, repaired from line 124).
7. `Atom.render` / `renderAll`: `tools/Effect4Gen/Atoms.lean:64` (`def renderAll`, repaired from line 45).
8. `AxiomGate`: `Test/Audit/AxiomGate.lean:376` (`elab "#effect4_axiom_gate"`, repaired from line 55).
9. `MachineTyped`: `src/Effect4/Laws/Program/Typed/Assembly.lean:251` (repaired from line 257 in `semantics-v1.md` and receipt §5).
10. `HostProtocol`: Named `structure Protocol` at `src/Effect4/Api/HostProtocol.lean:48` (repaired in receipt §5).

### 8.3 Correction of Decisions Rows for Integer and Float Work
- **Finding**: `implementation-inventory.md` incorrectly cited decisions row 180 for signed integer and
  binary64 float value appends. Row 180 is "Registered handle bytes (seat D3, M7)" and does not govern numbers.
- **Resolution**: Updated `implementation-inventory.md` to cite the true governing rows:
  - **Decisions Row 109** (FloatLib: binary64 IEEE-754 representation).
  - **Decisions Row 121** (`int` and numbers: signed integer profile and `number` leaf).
  - `store-safety` citations updated to rows 134, 139, and 181 (field census).

### 8.4 Paper Key Scheme Design for `sources/README.md` (Pre-C6 Proposal)
- **Problem**: `registry-content.lean` uses 14 author-year paper keys (`Ahmed2004`, `LynchVaandrager1995`,
  `Leroy2009`, `PetricekOrchardMycroft2014`, `WrightFelleisen1994`, etc.), while `sources/README.md`
  currently lists files and works without a standardized key column.
- **Proposed Key Column**: Add a `Key` column to `sources/README.md` matching the author-year tokens
  used in `citations-audit.md` and `registry-content.lean`:
  - `Ahmed2004` $\leftrightarrow$ `ahmed-2004-semantics-of-types-for-mutable-state.pdf` (P1)
  - `AhmedDreyerRossberg2009` $\leftrightarrow$ `ahmed-dreyer-rossberg-2009-state-dependent-representation-independence.pdf` (P2)
  - `Castagna2024` $\leftrightarrow$ `castagna-2024-programming-with-union-intersection-negation-types.pdf` (P6)
  - `deVilhenaPottier2021` $\leftrightarrow$ `de-vilhena-pottier-2021-separation-logic-for-effect-handlers.pdf` (P8)
  - `FosterEtAl2007` $\leftrightarrow$ `S05-tree-lenses.pdf` (P11)
  - `Gibbons2002` $\leftrightarrow$ `gibbons-2002-calculating-functional-programs.pdf` (P12)
  - `Leroy2009` $\leftrightarrow$ `leroy-2009-formal-verification-of-a-realistic-compiler.pdf` (C10)
  - `LynchVaandrager1995` $\leftrightarrow$ `lynch-vaandrager-1995-forward-and-backward-simulations.pdf` (C4)
  - `MeijerFokkingaPaterson1991` $\leftrightarrow$ `meijer-fokkinga-paterson-1991-bananas-lenses.pdf` (P24)
  - `PetricekOrchardMycroft2014` $\leftrightarrow$ `petricek-orchard-mycroft-2014-coeffects.pdf` (C8)
  - `PlotkinPretnar2009` $\leftrightarrow$ `plotkin-pretnar-2009-handlers-of-algebraic-effects.pdf` (P29)
  - `RendelOstermann2010` $\leftrightarrow$ `rendel-ostermann-2010-invertible-syntax-descriptions.pdf` (P32)
  - `Wadler2012` $\leftrightarrow$ `wadler-2012-propositions-as-sessions-icfp.pdf` (P35)
  - `WrightFelleisen1994` $\leftrightarrow$ `citations-audit.md` (P36 / C24)
  The semantics generator/producer can then validate each `Claim.literature.work` against this key column.

### 8.5 Promotion Boundaries
The coordinator's two design points for eventual promotion are acknowledged and accepted:
1. **Ownership of "Next"**: `docs/STATE.md` and the decision/proof registers remain the sole owners
   of scheduling and product priorities. In the promoted `docs/core/semantics.md`, Part 5 ("Next Bounded
   Coding Task") will be dropped, retaining Parts 1–4 as the enduring semantic contract.
2. **Worksheet Status of Implementation Inventory**: The categories in `implementation-inventory.md`
   serve as a design and planning worksheet. Upon landing C6, the generated report (`generated/semantics.md`)
   becomes the single verified authority for claim statuses and evidence states.
