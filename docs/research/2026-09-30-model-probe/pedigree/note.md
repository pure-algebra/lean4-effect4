The one thing: R2 ("extension is additive") is not true by construction. It is proved at the free monad (in the pinned package) and, by this seat, for the generic protocol judgment in both directions, but only under three conditions: a monotone world projection with the back condition, protocols that refine the old ones, and fresh, append-only names. Widening the world order, weakening an old promise, overriding a service type or inserting a host row each breaks it (proved or tested here), and the concrete `TypedProg` owes the same lemmas. The basis should state R2 as those obligations, cite DI-69 and DI-47, which already rule parts of it, and drop `interpret_pinned` and `Ψ_S ⊕ Ψ_F` as its support.

# Pedigree seat: the design basis of the full-program model, with its sources

Status: research note, 2026-09-30. Read and probed at HEAD `7cae243a` on `refactor/phase1-phase3`.
The note under review was committed there; its stated base is `74b526d4`. Nothing tracked was
edited. The probes are in this folder, with their logs.

Evidence words: **proved** means a kernel theorem this seat ran, with its axioms printed.
**Tested** means a finite check this seat ran. **Reading** means read in code or notes, not run.
**Assumed** means not checked. For literature: **read** means the cited section was read, by this
seat or by the note that cites it (named). **By name** means cited without a section and not read in
the tree.

Short paths: `Laws/…`, `Program/…`, `Machine/…` and `Codegen/…` are under `src/Effect4/`. Research
notes are under `docs/research/` and are named by date and title.

## 0. The answer in brief

- **The model's pedigree is real, but it is scattered, and much of it is untracked.** The
  algebraic basis comes from the end-state note §8 (2026-09-16). The four levels come from the
  M1 kickoff §3 (2026-09-20). The literature maps are in the core-math note (2026-09-05), the
  papers review (2026-09-05), the lit-papers note (2026-09-07) and the coherence principle
  (2026-09-17). Seven of the notes the model rests on are untracked, among them the end-state
  note, the core-math note, the papers review, the lit-papers note and the provision algebra. A
  clone loses them (§4.4).
- **Several claims of the note under review are superseded or wrong at HEAD.** The world now has
  Θ. The concrete typing judgment is no longer `Typed (Ψ_S ⊕ Ψ_F)`. The fiber half has a
  placeholder, not a handler. `build_total` was landed and then cut. `interpret_pinned` is not
  the additivity theorem. See §1.3.
- **The DI register already rules part of R1 and R2.** DI-69 (2026-09-11) gives the row table
  its meaning as a signature summand, `Sum StoreSig (RowSig table)`, built from the package's
  `Family`. It is unimplemented. DI-47 rules what compatibility of an extended description
  means: appends only. DI-89 (2026-09-16) rules the three routes by which a module enters.
  The note cites none of them.
- **`docs/DESIGN-BASIS.md` has absorbed nothing since 2026-09-10 except the clock.** Several of
  its rows and sections are stale or conflict with newer authorities. It lacks the model's main
  decisions: the open signature, protocols over a world, the budgeted meaning, the row calculus,
  and coarse values with a typed world (§2).
- **R2, stated precisely, is seven obligations (C1–C7, §3.1).** The tree proves C1 and C2 for
  binary sums. This seat proves C4 for both coproduct injections and in general, and shows by red
  controls that each premise is needed. C3 and C7 hold for appends and fail for insertions and
  overrides (tested).
- **The basis should own the pedigree** (§4): one row per settled decision, carrying its
  witnesses, its sources and its literature with evidence words. The system map keeps status;
  the decisions register keeps open questions.

## 1. Pedigree (item 1)

### 1.1 The components of the model (the note's §1)

"At HEAD" marks each link with one of three words, by this seat's reading of the cited code at
`7cae243a`: **holds**; **superseded** (a later ruling or landing replaced it); **unsupported**
(no source supports it, or a register row or the code contradicts it).

| Component | Established or decided in | Literature, as the notes give it | At HEAD |
| --- | --- | --- | --- |
| **Level 0: the free monad, typed by a protocol** | Composed graph (2026-09-18) §4, layer L0, probe Q1. M1 kickoff §3. Theoretical review (2026-09-21) §4.3. | Xia et al., *Interaction Trees*, POPL 2020: §3.2 and §7 read (lit-papers Q7, Q10). de Vilhena, thesis 2022: Def. 2.2, 2.6 and 2.7 read (papers review §1.3). Def. 2.4, 2.5 and 2.8 and rule Monotonicity (Fig. 2.4) read by this seat in the text copy (`2026-09-05-effects-papers/text/verification_with_effects.md`, lines 586–760). | **Holds for the generic judgment.** `Typed` (`Laws/Effects/Protocol.lean:45`), with `mono` (`:57`), `bind` (`:66`), `widen` (`:75`), `Protocol.sum` (`:83`), `Typed.inl` (`:97`) and the two inversions (`:108`, `:119`). **Superseded for the concrete judgment.** Since the slice-5 contract ruling (2026-09-23) §3, `TypedProg` is its own inductive (`Laws/Program/Typed/Residual.lean:186`). It is not an instance of `Typed (Ψ_S.sum Ψ_F)`, so `Typed.inl` does not apply to it. |
| **Level 1: the world and its order** | M1 kickoff §2.2 and §3: `⟨Γ, Π, Ρ, s⟩`, ordered by extension, `Stores.le` and cell compatibility. Compatibility was forced by `heapNotMonotone`, a refutation, not a ruling. Slice 2 added Θ (theoretical review §1). Post-phase-C F3 asked for allocation `Extends`. | de Vilhena §4.3: the promise map only grows, so `isPromise` is persistent (papers review §1.3, A3). MCA §4.1.1 and Example 21; Jacobs Prop. 6.2.4 (papers review A3). Ahmed 2006 and "the Iris split": by name (theoretical review §4.1). | **Holds, with Θ.** `World` is `⟨ids, state, Γ, Π, Ρ, Θ⟩` (`Laws/Program/Typed/World.lean:52-57`). `World.le` (`:131-135`) includes `CellCompatible`. `TypedProg` uses `World.leHost`, which is `le` plus `Extends` on external allocations (`Laws/Program/Typed/Validity.lean:38-39`). So the theoretical review's §2.4 worry (strict equality on externals) is already repaired. |
| **Level 2: the typed stack, one delivery lemma** | Composed graph §4, L2. Decisions row 48 (existential middle types, ruled 2026-09-20). Slice-5 landing (2026-09-24): `popR_typed`, `deliver_active`, `deliver_stale` (decisions row 86). | Danvy and Nielsen, *Defunctionalization at Work*, 2001: §1 and §3 read (lit-papers Q12). Reynolds; Van Horn and Might: by name (M1 kickoff §3). Typed frames as a free category (theoretical review §4.2). | **Holds** (reading of decisions row 86's landing record). |
| **Level 3: the invariant, the store as comodel, the machine as runner** | Core-math note §7. M1 kickoff §3. Decisions row 41 (the milestone). | Plotkin and Power, MFPS 2008 (comodels); Ahman and Bauer, ESOP 2020 (runners). Both by name: the core-math note pins no section. | **Holds as a reading.** `storeHandler : Handler StoreSig (StateT Stores Id)` (`Laws/Program/Denote.lean:124`). `TypedState` is assembled (slice 5). M5 and M6 are refuted as stated; the bounded repairs are rows 95–96 and 104–107. |
| **Operations are algebraic; meaning is initial** | End-state §8, "the proved part". | Plotkin and Power 2002/2003; Plotkin and Pretnar, *Handling Algebraic Effects* (local paper 05; §1 and §5 read in lit-papers Q11); Goguen, Thatcher, Wagner and Wright 1977 (coherence principle, "Literature"). | **Holds.** `program_is_free` (`.lake/packages/effects/Effects/Algebra/Universal.lean:98`), `program_is_initial_in_models` (`:119`), `interpret_pinned` (`:243`). This seat reran `interpret_pinned`: `[propext, Quot.sound]`. |
| **Control is scoped syntax, elaborated into the algebra** | End-state §8, "the elaborated part". Core-math §5–§6. DB-05. Decisions row 12; DI-12. | Wu, Schrijvers and Hinze 2014 (local paper 10: §9–§10 read). Piróg et al. 2018 (paper 11: §1.2–§1.3 read). Bach Poulsen and van der Rest 2023 (paper 14: §1.2–§1.4, §2.5–§2.6, §3.1, §3.4–§3.5 and §5.2–§5.4 read). van den Berg et al. 2021 (paper 13: §2.2 read). All read in lit-papers Q2. | **Holds for "elaborated into `denoteR`".** **Unsupported (contradicted) for "plus a handler for fiber control".** The right half is `fiberRefusal` (`Laws/Program/Sched.lean:216-218`), "Not a semantics (`SCHED-FB-FIBER-HANDLER`)", and register row `E4-SCHED-CE-001` refutes that reading. Fiber meaning is the reference machine, related by `run_eq_ref` at the empty table. Choice Trees §7.1 says such a scheduler "cannot be implemented as a simple fold" (lit-papers §0, Q5, Q8). |
| **Behavior is a function of the tape** | Core-math §2. DB-03. Lit-papers Q7 (INV-TAPE-1, INV-TAPE-2). | Jacobs, Ch. 2, Moore coalgebras: read (papers review §1.4, §7). Interaction Trees §7, Def. 1–2: trace equivalence coincides with weak bisimulation (lit-papers Q7, read). Choice Trees §2.2 (read). | **Holds.** `Beh` (`Laws/Machine/Behaviour.lean:74`); `Beh_fuel_irrelevant` (`:92`); `replay_unique` and `journal_replays` (system map §5). |
| **Partiality is a budget** | Core-math §3. End-state §2.2 and §8. Decisions row 41 ("loop soundness"). | Capretta 2005; Chapman, Uustalu and Veltri 2015/2019; Hasuo, Jacobs and Sokolova 2007: by name (core-math §§2–3). Jacobs Thm. 5.3.4 and Prop. 5.3.3: read (papers review §1.4). Elgot 1975; Adámek, Milius and Velebil 2006: by name (coherence principle). | **Holds, by a different construction than the end-state note proposed.** `iter`, "Elgot iteration cut at a budget, generic over the signature" (`Laws/Program/Iter.lean:30`), with `iter_uniform` (`:40`). `denoteB` (`Laws/Program/DenoteB.lean:208`) sits beside `denote`, joined by `denoteB_straight` (`:285`), with `denoteB_mono` (`:386`) and `meaningB_unique` (`:496`). Also `soundB` (`Laws/Program/LoopSound.lean:306`) and `loopAgreement` (`Laws/Program/Agreement/Loop.lean:839`). End-state §4.2's "budget as a parameter of the one `denote`, changed in place" is superseded: the budget lives in a second function with a connector. |
| **Protocols compose by coproduct** | Composed graph §4: `TypedProg w ty p := Typed o (Ψ_S.sum Ψ_F) w (ExitOk ty) p`. Theoretical review §4.3. | The theoretical review cites "Plotkin & Pretnar 2009; Bauer & Pretnar 2015" for "the coproduct of algebraic theories", which those papers are not the source for. The sum of theories is Hyland, Plotkin and Power, *Combining Effects: Sum and Tensor*, TCS 2006, listed "primary not read" in the algebra-package review (2026-09-02). Coproducts of signatures with injections are Swierstra, *Data Types à la Carte*, JFP 2008: §2 and §6 read by this seat in the local paper 06. Hazel's sum (Def. 2.4) is a disjunction on one alphabet, not a coproduct of signatures. | **Superseded for the concrete judgment** (slice-5 ruling, 2026-09-23, §3). The store and fiber arms still read `Ψ_S` and `Ψ_F` separately (`Residual.lean:189-199`), so the two halves stay separate by the construction of the arms. The coproduct lemmas no longer carry that separation. |
| **Services and layers are one row calculus** | Provision algebra (2026-09-04) §§1–2, landed as `f182d2b3`. Papers review A1: rows as free-variable sets, `provide` as the substitution lemma. DB-12. DI-20 and DI-28. Decisions rows 51, 90, 104, 105. | Provision §7, as that note gives them: Kuessner et al. (CALM); Burckhardt et al. (Durable Functions, Thm. 5.3 and 6.4); Lamport and Merz (refinement mappings). de Vilhena, Tes §7.3.1 (papers review §1.3, read). Leijen (local paper 17) §3.2, read: row polymorphism exists to type arrow types, which `Eff` does not have (lit-papers Q4). Wand, Rémy, Gaster and Jones, Leijen 2005, Morris and McKinna 2019: "assumed; not read here" (type algebra §8). | **Holds for the row laws**: `provide_closed` (`Program/Provision.lean:98`), `merge_rows_comm` (`:138`), and the rest. **Unsupported: the note's "build totality was proved in the 2026-09-04 workshop spike only".** `build_total` landed in the tree with `f182d2b3` (2026-09-04) and was cut by `b08f3b58` (2026-09-18). The module docstring still advertises it (`Program/Provision.lean:37-41`), which is stale. |
| **Faces: exact embeddings and simulations on named observations** | Coherence principle (scout F, 2026-09-17) §§1–4. System map §5 (K1–K5). The `AGENTS.md` vocabulary (decisions row 36). Lcnf-route §8 (stages as named connections). | Goguen et al. 1977; Rendel and Ostermann 2010; Matsuda and Wang 2013; Foster et al. 2007; Pickering, Gibbons and Wu 2017; Rutten 2000; Lynch and Vaandrager 1995; Leroy 2009. Each is cited by name, with the use it is put to (coherence principle, "Literature"). | **Holds.** `read_print`, `read_exact`, `ofVal_toVal`, `ofVal_exact` (system map §5). |
| **A run is data (K5)** | Coherence principle §2, rows 27–28. M1 kickoff §4 (event sourcing). | The free monoid action is standard. CompCert labels and the CakeML FFI oracle: by name (M1 kickoff §4). | **Holds** (`replay_unique`, `journal_replays`). |

### 1.2 The requirements R1–R9

| Req. | Established or decided in | Literature | At HEAD |
| --- | --- | --- | --- |
| **R1** the signature is a parameter | Author receipt (2026-09-17) C2. Findings ledger 4B and D-I3. Decisions row 21: keep "until an application needs a seventh carrier" (owner, open). Rows 42–43 plan §2c, L7: "the six type codes … become a service table beside the program, as the row table is". DI-69 (the row table as a summand; ruled, unimplemented). DI-54 (`Signature.dom`). DI-61 (`admitProgram`). | Signature as data, a universe of descriptions: Benke, Dybjer and Jansson 2003; Chapman et al. 2010, by name (coherence principle §1). | **Holds, with corrections.** The counts are right (tested by grep: 188 `(sig : Signature` binders; 89 `nativeSignature` uses in 15 `Laws` files). `check_sound` and `check_complete` hold over any `Op` and any `sig` (`Laws/Program/Typing/CheckSound.lean:37`, `:361`). **Correction 1:** `MeaningSound.sound` and `LoopSound.soundB` lose nothing by their pin. Their fragments exclude every host row (`.external` has kind `.program`; `Program/Fragment.lean:28-31`) and every service and layer form (`Fragment.lean:46-48`; `DenoteB.lean:150-152`). **Correction 2:** the pins that matter are elsewhere: `AdmittedProgram` (`Program/Admission.lean:89-90`); `PointTyped` at `src.table` with native services (`Laws/Program/Typed/Admission.lean:92-96`); `ServicesOk`, which reads `nativeServiceTy` directly, so the `nativeSignature` count misses it (`Typed/Admission.lean:32-33`); `memoGet`'s `checkLayer` (`Residual.lean:53`); and the fork bridge at the **empty row table** (`Laws/Program/Typed/ForkSource.lean:32`, `:47`, `:53`, `:68`). So a forked body that calls a host row is outside the fork bridge. |
| **R2** extension is additive | End-state §10, the charter's "Extensible", and §8 ("a new **operation** … or a new **equation**, never a new evaluator"). Theoretical review §4.3. REIFICATION-STRATEGY RS-4 (untracked): "Adding a standard adds a summand and a handler; it does not reopen the ones below it." The layers steer of 2026-09-17 is recorded only in the session memory, in no research note. DI-47 (compatibility of an extended description: appends only). DI-22 and DI-64 (the link table; row identity). DI-69. | Swierstra 2008, §2 (verified here: the injections "may no longer be the right injection into the coproduct") and §6. de Vilhena Def. 2.4 and 2.8 and rule Monotonicity (verified here). Tes §7.3: row extension is a subsumption, and labels must be distinct (thesis text, lines 2828 and 3235; papers review G5). Hyland, Plotkin and Power 2006: not read. | **Holds in part; the cited support is unsupported (the wrong theorems).** C1 and C2 are proved in the package for binary sums: `interpret_inl` (`Effects/Algebra/Sum.lean:48`), `Program.inl_injective` (`:92`), `Program.inl_bind` (`:72`). The tree uses them once, in `interpret_inl_store` and `meaning_via_rsig` (`Laws/Program/Sched.lean:230`, `:237`). `interpret_pinned` gives uniqueness, not additivity. "Rows: additive by construction" holds for host rows **appended** to the link table and fails for insertion (tested, §3.4). It does not hold for built-in constructors (`NativeOp`, `SyncOp`, `FiberOp`, `NativeAtom`, `Ty`, `Eff`). Those are closed inductives; growing them is additive only by discipline: decisions row 56 (wildcards in proofs, not in classifiers) and row 61 (the exhaustiveness inventory). |
| **R3** data | Decisions row 2 (open: "(c) now, (b) before the first foreign consumer"). Row 3: `Ty.app`, to be replaced by `Ty.foreign`, per type algebra §1.3 and §7.2. Type algebra §1.3: the `Ty`/`Fields` mutual spine; "B lands with row 2 and not before". Language cut §§2–3. DI-15, DI-62, DI-67. | Lean 4.33.1's deriving facts F1–F6, read at the toolchain lines (type algebra §0). The record and row literature: "assumed; not read here" (type algebra §8). | **Unsupported as a decision, and in conflict with the basis.** DB-15 refuses "A record type in `Ty`: columns are pairs" (`docs/DESIGN-BASIS.md:665`) and `Err.value` (`:655`). R3 needs DB-15 amended by a ruling on row 2. "The design is ready" is a recommendation, not a decision. No register row covers recursive types (tested by grep), as the note says. |
| **R4** state | Decisions rows 42–45 (ruled) and 55 (variance). Rows 42–43 plan §§1, 2a, 2b, 2e. Catalogue (2026-09-19) §3, items 1, 2 and 4. M1 kickoff §2.1–§2.4. Row 96 D2. | Cell types invariant under writes: Hoare Type Theory, Nanevski et al. 2006/2008, by name (theoretical review §2.1). Declaration-site variance: Emir et al. 2006, assumed (type algebra §8); rc.112's own declarations are the data (decisions row 60). | **Holds.** `refTy := .handle refTarget` (`Program/Native.lean:91`); `FnName` (`Machine/Stores.lean:61`); `Ρ` and `Π` per cell (`Typed/World.lean:54-55`). |
| **R5** services | Rows 21, 51, 90, 104 and 105. The provision algebra. DB-12. Author receipt D4: the build refuses a disagreeing carrier. | As R1 and the row-calculus line above. | **Holds.** Tested here: the service table of `nativeSignatureWith` is a **right-biased override**, not an extension (`Program/Authoring/Services.lean:42-45`). A fresh key is conservative; a key the built-in signature already types is retyped (§3.4). |
| **R6** host | `docs/core/host-boundary.md` §§1–6, the authority. Rows 95–101. DI-57 (`session_eq_ref`, amended 2026-09-11). DI-58. DI-65 (host transitions are relational; DB-09's Wave 2 amendment). DB-03. | Loring, Marron and Leijen, *Semantics of Asynchronous JavaScript* §2.4 (`E-Oracle`); Interaction Trees §7. Both read in lit-papers Q6–Q7. | **Holds, with a condition** on "parking is sound if the premise is stated now". It is sound only if the host lane extends the world by a monotone projection with the back condition and its protocols refine the old ones (§3.5). The order already admits allocation growth (`leHost`), which was the main hazard the theoretical review named. |
| **R7** retained behavior | Decisions row 82 (open). Catalogue §0 and §3 item 5. Machine-state §5. Language cut §1 ("functions as values" is a profile decision). | Danvy and Nielsen §1: a `Capture` is closure conversion over a first-order code pointer (lit-papers Q12, read). Latent effects (paper 13 §2.2) and hefty algebras §2.6.4: deferred bodies are latent, not scoped (lit-papers Q2, read). | **Holds** (open, as the note says). |
| **R8** runs, composition, faces | Row 98. The K5 laws. System map §6 (`composeAt`). The critique response §2 witnesses, by citation. Lcnf-route §8. DI-56 and row 108. | Graded Freyd category: Power and Robinson 1997; Levy, Power and Thielecke 2003; Katsumata 2014; Orchard et al. 2014, all by name (coherence principle §4b). | **Holds.** |
| **R9** never goes wrong | Row 107 (ruled). Pass synthesis §2.4 part 6 and §5.2 item 4. Side audit §2: the clause must live in the exit judgment that code, saved stacks, queued results and stored completions read. Addendum 3, H2. Row 52. | — | **Holds as ruled.** For an open Σ, the refused defects (`badName`, `notImplemented`, `missingService`) belong to the core machine. An extension's own failure alphabet would have to be part of its lawfulness (C6). |

### 1.3 Corrections to the note under review, in one list

1. §1's table gives the world as `⟨Γ, Π, Ρ, Θ, s⟩` and cites the M1 kickoff §3, which has
   `⟨Γ, Π, Ρ, s⟩`. Θ came with slice 2 (theoretical review §1), and `ids` is also a field
   (`Typed/World.lean:52-57`). The tuple is nearly right; the citation is incomplete.
2. "typed by `Typed o Ψ w Q p`" and "Protocols compose by coproduct … `Ψ_S ⊕ Ψ_F`" are superseded
   for the concrete judgment by the slice-5 contract ruling (2026-09-23) §3.
3. "plus a handler for fiber control" is contradicted by `E4-SCHED-CE-001` and
   `SCHED-FB-FIBER-HANDLER` (`Sched.lean:216-218`).
4. "Build totality was proved in the 2026-09-04 workshop spike only": it was in the tree from
   `f182d2b3` to `b08f3b58`.
5. R2's "`interpret_pinned` and `Protocol.sum` are per operation": the additivity theorems are
   `interpret_inl`, `inl_injective` and `inl_bind` (package), and `Typed.inl`, which now has a
   proved converse (§3.4).
6. §5 item 1's restatement of `MeaningSound` and `LoopSound` buys nothing: their fragments contain
   no host row and no service form. The pins that bite are admission, `PointTyped`, `ServicesOk`,
   `memoGet` and the fork bridge at the empty table (R1 row above).
7. §4's "typed state: rows yes" is false for the fork bridge, which is pinned to the empty row
   table.
8. Sources the note should cite and does not:
   - DI-69, DI-47, DI-89, DI-22 and DI-64;
   - the composed graph §4 and the slice-5 contract ruling §3;
   - the coherence principle's reading list (Swierstra; Elgot);
   - `interpret_inl_store` and `meaning_via_rsig`.

## 2. Audit of `docs/DESIGN-BASIS.md` (item 2)

The basis was last changed on 2026-09-20 (`8b64039f`, the clock amendment to DB-14). Its proof
graph was re-cut on 2026-09-10 (`59482298`). Nothing from the charter (2026-09-16), rows 41–110,
the typed state, the protocols, the budgeted meaning, row 96's `Fits` or the 2026-09-30 system
map has reached it.

Verdicts:
- **stands**;
- **stands, stale wording**;
- **stale**;
- **conflicts**: another authority says otherwise, so two files own one fact.

### 2.1 Row by row

| Row | Verdict | Evidence |
| --- | --- | --- |
| DB-01 `Program` is the proof carrier | stands, stale wording | The pin is `v0.8.0` (`a4ee7a14`, `lakefile.toml:126-131`), not `v0.1.0` (`5611c3a`, `DESIGN-BASIS.md:72`). DI-90 (ruled 2026-09-16) moves the consumed core in-tree; delivery is pending (design-issue map). `Handler.sum` and `Handler.through` exist (`Effects/Algebra/Handler.lean:51`; `Effects/Algebra/Handler/Composition.lean:27`). The core root still imports the package, in `Schema/EffectfulField.lean` and `Machine/Context.lean`; row 39 removes the first. |
| DB-02 `Flow` is the representation | superseded, as marked | The rule it carried ("pure code is closed at this boundary"; a host function becomes "a named and registered foreign boundary") lives on in `AGENTS.md`'s representation rules. It is R7's pedigree. |
| DB-03 meaning is relational | stands, stale wording | "Meaning remains in judgments over `Flow`" (`:159-160`). On `Eff` the carriers are `Beh` and the tape (§1.1). It should also carry DI-65's relational host, which is now only in DB-09's amendment, and row 95's rule that host answers are decisions. |
| DB-04 fuel is an approximation | stands; its receipts are archived | Its theorems are at `git:c407ab7`. On the `Eff` route, partiality is the budgeted Elgot iteration (`Iter.lean`, `DenoteB.lean`) and `drive_add` with `Beh_fuel_irrelevant`. The row mentions neither. Missing: the budgeted meaning as a decision (§2.3, item 5). |
| DB-05 no `HHandler` for first-order children | stands, stale wording | "Block" and `BlockId` are archived terms. On `Eff` the children are subterms addressed by `Point` and path. The honest boundary belongs here: the end-state note §8 calls the fiber layer "algebraic in representation … operational in meaning", and `E4-SCHED-CE-001` records it. |
| DB-06 EffHOL is the logic layer | stands as a constraint; its "discharged" sentence is archived | The basis's own proof-graph row calls the logic edge "Pending, and empty" (`:733`). |
| DB-07 state survives failure | stands, stale wording | No `EStateM` under `src/` (tested by grep). Failure is a value (`ExitV`) and state is threaded by `StateT` (`Denote.lean:124`, `:130`): "an equivalent result type". |
| DB-08 `Expr` is a metaprogramming input | stands | Restated in `AGENTS.md`. |
| DB-09 Effect TypeScript is a profile | **conflicts** | "OCaml native is a **test bed**, not a claimed target" (`:381`), against the system map §1 (owner, 2026-09-30): "The model runs natively. The same Lean machine is compiled through LCNF into OCaml today. WASM is next". The numbers profile (DI-56) is now row 108 and lcnf-route §8. One owner is needed: the system map owns the route, and DB-09 keeps the evidence classes. |
| DB-10 PolyFun is prior art | stands, stale wording | "It cannot replace first-order checked `Flow`": read `Eff`. |
| DB-11 one value carrier; admission as a premise | stale | "the executable admission is owed to X2" (`:420`, `:437`). It exists: `admitProgram` (DI-61, landed at S1a) and reply admission (`Program/Admit.lean`). Row 44 (coarse values, a typed world), row 96 (`Fits`) and the system map §4 ("Value fits type") now own the value-typing fact. |
| DB-12 one context, layers by path | stands; amendment pending | Row 104 (ruled 2026-09-30) builds every layer at a closed point, so the row's "builds a layer at its point" changes when addendum 2 item F lands. Row 105 adds the key-type check to `LayerHasTy.succeed`. |
| DB-13 one wake protocol | stands, stale wording | "Latch, Queue, Semaphore, Pool, PubSub … as they land" (`:494-495`) reads as one store family each. DI-11 (ruled 2026-09-10) makes Queue, Mailbox and PubSub composite programs, "never new machine stores". Latch is row 81 (open). |
| DB-14 one logical clock | stands | Amended 2026-09-20; matches machine-state §2. |
| DB-15 strings and host records | stands; **blocks R3** | Its refusals ("A record type in `Ty`"; `Err.value`) are the settled side of row 2 and R3. Lifting them needs a ruling and an amendment here. |

### 2.2 The other sections

| Section | Verdict | Evidence |
| --- | --- | --- |
| Re-review ruling | stands, stale wording | Four refinements; "logic … rather than in `Program` or `Flow`". |
| Semantic decomposition | superseded | A Flow-era table of faces. The system map §2 (layers) and §5 (arrows) own the faces now. |
| Native library boundaries | **conflicts** | "Streams, channels, schedules, and transactions retain their own state machines" (`:705-708`). DI-11 makes streams a pull kernel and queues composites; DI-89 gives three routes (core constructors, generated rows, `Forms` templates with behavior laws). Machine-state §5 restates DI-89. |
| Required proof graph | **stale, and a second owner of status** | The `run_eq_ref` cell (`:731`) omits "empty table only", which the theorem's docstring states (`Laws/Program/RuntimeR.lean:197-210`). It calls finite adequacy "single-fiber straight-line only" (`:732`), but `loopAgreement` covers `Looped`. The typed-state graph (slices 1–5, M5–M7) is absent. Status is owned by the system map §2 and §5 and by the post-phase-C synthesis; `docs/DESIGN-MAP.md` grades it a third time. |
| Source and evidence rules | stands | Agrees with the system map §7 and `AGENTS.md`'s evidence words. |
| Designs excluded | stands | DI-20 and DI-28 (no polymorphism in a stored program) bound R1. R1's "every lawful Σ" quantifies **theorems**, not stored programs: each admitted program stays closed over one Σ. |
| Primary sources | stale | Nine entries. The model now also rests on de Vilhena; Xia et al. and Chappe et al. as used in §1.1; Plotkin and Power on comodels; Ahman and Bauer; Capretta; Hasuo, Jacobs and Sokolova; Jacobs; Goguen et al.; Swierstra; Hyland, Plotkin and Power; Danvy and Nielsen; Lynch and Vaandrager; Leroy; Wu, Schrijvers and Hinze; Piróg et al.; Bach Poulsen and van der Rest. None of these is listed. |

### 2.3 What the model needs and the basis lacks

Each needs a row with its statement, its witnesses and its sources.

1. **The open signature, with additive extension.** DI-69, DI-89, DI-22, DI-64, DI-47 and row 21
   are its pieces, scattered across two registers. §3 gives the statement.
2. **Typing as a protocol per operation over a world.** The pieces:
   - the composed graph §4;
   - the slice-5 ruling §3 (one inductive, shared certificates);
   - row 87 (certificates) and rows 44–45 (coarse values, tables per cell);
   - the world order (`World.le`, `leHost`);
   - row 96 (`Fits`).
3. **The host as a relation.** DB-03 and DB-09's DI-65 amendment carry it in pieces;
   `host-boundary.md` owns the contract. The basis needs a pointer, not a copy.
4. **The provision row calculus.** The pieces:
   - the provision algebra (landed `f182d2b3`) and papers review A1;
   - DI-20 (rows stay monomorphic; subeffecting is owed);
   - rows 51, 90, 104 and 105;
   - `build_total`'s cut, recorded.
5. **The budgeted meaning.** `iter`, `denoteB`, monotonicity and uniqueness of the limit, and the
   connector to `denote`, with the Elgot, Capretta and Jacobs §5.3 pedigree. DB-04 should point to
   it.
6. **The faces as exact embeddings and simulations.** Owned by the vocabulary and the system map
   §5. The basis should cite them, not restate them.
7. **Elaboration of control, and the honest boundary.** The fiber layer is operational in meaning,
   with `run_eq_ref` as its only connection. DB-05 is the natural home.

## 3. "Extension is additive", stated precisely (item 3)

### 3.1 The statement

Split the signature into its two kinds of entries.

- **Σ_core: closed inductives the language owns.** These are the `Eff` and `Ty` constructors,
  the built-in `NativeOp` rows, `SyncOp`, `FiberOp` and `NativeAtom`. Growing them is a
  constructor append. Each new arm is a local proof obligation, enforced by the exhaustiveness
  inventory and the wildcard rule (rows 56 and 61). That is a discipline, not a theorem.
- **Σ_app: data.** Today that is the row table and the service table; later it would include
  named data declarations and code references. R1 should quantify over this part. R2 is a theorem
  obligation for it.

Two kinds of growth need no extension of Σ once their design lands:
- Structural records (the `Fields` spine of type algebra §1.3) are types, not signature entries.
- Cells at any type are typed by the world's `Ρ` at allocation, not declared.

Only nominal entries extend Σ_app: host rows, services, recursive or named data, and retained code.

An **extension** ε of a lawful Σ has four parts:
- an append-only, fresh injection of names `ι` (positions never move; no old name is reused);
- a projection of worlds `π : W' → W`;
- a certificate map for the old operations;
- the new entries' own data.

R2 for ε is seven statements:

| | Statement | Literature | In the tree | This seat |
| --- | --- | --- | --- | --- |
| **C1** syntax | `ι*` is an injective monad morphism of free monads | Swierstra §2 and §6 (read) | `Program.inl_bind` and `Program.inl_injective` (`Effects/Algebra/Sum.lean:72`, `:92`); rerun here at `[Quot.sound]` and `[propext, Quot.sound]` | `along_bind` for any signature morphism (proved) |
| **C2** meaning | `interpret h' (ι* p) = interpret (h' restricted along ι) p` | Plotkin and Pretnar (handlers as homomorphisms); Interaction Trees `InterpTrigger` and `IgnoreTrigger` (lit-papers Q10, read) | `interpret_inl` (`Sum.lean:48`, rerun at `[propext, Quot.sound]`); used once, in `meaning_via_rsig` (`Sched.lean:237`) | `interpret_along` for any morphism, at a lawful monad (proved) |
| **C3** checker | For every Σ-program `p`, `check Σ' p = check Σ p`; and `check Σ p = ok t → check Σ' p = ok t` | — | No signature-weakening lemma exists. `check_weaken` and `hasTy_weaken` weaken the **context**, not the signature (`Program/Typing.lean:88`; `Laws/Program/Typing/Sound.lean:156`) | Holds for an appended row and a fresh service key; fails for an inserted row and an overriding service (tested, with red controls) |
| **C4** protocol typing | `Typed_Σ' w' Q' (ι* p) ↔ Typed_Σ (π w') Q p` | de Vilhena Def. 2.8 and rule Monotonicity (read): a stronger protocol may be used where a weaker one is required | `Typed.inl` (lift, left only); `inl_inv` and `inr_inv` (inversion only) | `inl_iff` and `inr_iff` (both directions, both injections); `typed_along` (preservation along a morphism under refinement); `typed_pull_of_typed` and `typed_of_typed_pull` (along a world projection). All proved, with no axioms |
| **C5** world | `π` is monotone and has the **back condition**: every old later world of `π w'` is `π` of a richer later world of `w'`. Old protocols read only `π w'` (the frame). The new protocol refines the old on old operations (demand forward, promise backward). Old steps commute with `π` and keep the new components. | That p-morphisms preserve and reflect modal formulas is standard modal logic; assumed, no note cites it. Iris's extensible ghost state: by name only, through de Vilhena. | `leHost` already admits allocation growth (`Validity.lean:38-39`) | Red controls, proved: reflection fails without back (`reflection_needs_back`); widening the order loses typing (`order_widening_loses_typing`); a weaker promise loses typing (`post_refinement_needed`). Narrowing the order keeps typing (`typed_antitone`). |
| **C6** lawfulness is local | `Lawful Σ' ↔ Lawful Σ ∧ Fresh(ε) ∧ LocalLawful(new entries)` | Tes §7.3: distinct labels (thesis text, read) | `LawfulTable` has exactly this shape: unique keys plus per-row clauses (`Codegen/Read.lean:1943`) | Shape only |
| **C7** representation | The exact embeddings of Σ' restrict to Σ's on Σ-programs; old bytes read back unchanged | Swierstra §2's warning (read); Unison's split of hash and name, by name (DI-01) | DI-47 (ruled): "Reject reorder/removal/reframing/tag reuse; declared appends are allowed"; `Test/fixtures/baseline/66ee4657/` | The link-table instance of C3 is the same fact one level down |

With R1 (every theorem stated for every lawful Σ), C1–C7 make the charter's "adding one changes no
theorem's statement about the others" exact. The Σ'-instance of a theorem then says of every
Σ-program exactly what the Σ-instance said. The two parts buy different things:

- **R1 alone saves re-proving.** A generic proof is reused.
- **C1–C7 make the statement stable.** Without them the Σ'-instance may say something different
  about an old program, as the override and insertion controls show.

**Two caveats with pedigree.**

- **C1 and C2 are free today only because `Eff` and the algebra carry no equations.** The
  coherence principle §1 says so, citing the Plotkin–Power distinction between a free algebra
  and a theory with equations. If the fiber layer gets its deferred equational theory (end-state
  §8), whether the sum of theories is conservative becomes a real question. Hyland, Plotkin and
  Power 2006 is the reference. It is unread in the tree (algebra-package review, "Next internal
  reading", item 2), so this caveat is assumed.
- **Meaning is not automatically additive across summands that share state.**
  REIFICATION-STRATEGY RS-4 records the sum-versus-tensor rule: every pair of signatures that
  meet gets a ruled answer before their handlers are composed. Here all state is one comodel
  (`Stores`), so that question lives in the frame part of C5: old steps keep the new components.

### 3.2 What the tree already gives

- **Free monad (C1, C2), binary sums:** proved in the pinned package (rerun here).
- **Generic protocol, left lift only (C4, in part):** `Typed.inl`. The theoretical review §4.3
  claims more: "`Typed.inl` and `Typed.inr_inv` guarantee that adding new store operations or
  modifying fiber scheduler mechanics never invalidates the complementary half of the proof
  graph". An inversion is not a lift, and since 2026-09-23 neither lemma applies to `TypedProg`.
- **Weakening lemmas** (`Typed.mono`, `Typed.widen`, `check_weaken`, `hasTy_weaken`) weaken along
  the world, the result predicate and the context. None weakens along the signature.
- **`interpret_pinned`** fixes an interpreter once each operation's meaning is fixed. It is the
  uniqueness half of initiality, as the dogfood conclusions review §6.1 says ("fixes an
  interpreter once all primitive meanings are fixed"). It is not an extension theorem.

### 3.3 What this means for `TypedProg` and M6

`TypedProg` is a dedicated inductive with four control arms, so C4 must be proved for it directly.
The probe's proofs are one induction each, so the cost is low. Proposed statements:

- `TypedProg.pull`: preservation along a monotone projection.
- `TypedProg.reflect`: reflection under the back condition.
- `TypedProg.along`: transport along a refining protocol.

The four marker arms keep their payload clauses unchanged.

For the M6 statement, the useful consequence is about the order. Typing is antitone in the world
order (proved):
- Adding conjuncts for new components keeps every derivation.
- **Widening** the order loses derivations.

So a later lane may add components with their own order, but must not add later worlds to the old
components. R6's "parking is sound" holds exactly under that rule.

### 3.4 The probes

`Conservativity.lean` imports only `Effect4.Laws.Effects.Protocol` and `Effects.Algebra.Universal`.
It exits 0; the axioms are in `conservativity.log`.

| Theorem | What it says | Axioms |
| --- | --- | --- |
| `inl_reflect`, `inl_iff` | A sum-typed `p.inl` is a left-typed `p`; with `Typed.inl`, an iff | none |
| `inr_lift`, `inr_reflect`, `inr_iff` | The same at the right injection, which the tree does not state | none |
| `typed_pull_of_typed` | Preservation along a monotone world projection | none |
| `typed_of_typed_pull` | Reflection, with the back condition | none |
| `reflection_needs_back` (red control) | The identity from `(ℕ, =)` to `(ℕ, ≤)` is monotone; a program typed under the first is untyped under the second | none |
| `typed_antitone`, `order_widening_loses_typing` (red control) | A finer order keeps typing; a wider one loses it | none |
| `along_bind`, `interpret_along`, `along_inl` | A signature morphism (operations forward, answers backward) gives a monad morphism that meets interpretation by restriction; the left injection is one | `[Quot.sound]`; `[propext, Quot.sound]`; `[Quot.sound]` |
| `typed_along` | Transport under a refining protocol | none |
| `post_refinement_needed` (red control) | A richer protocol whose promise about an old operation is weaker loses an old program's typing | none |

`ServiceExtension.lean` imports `Effect4.Program.Authoring.Services`. It exits 0, with twelve
`#guard`s.

- **Service table.** Two keys: `natKey` (`⟨⟨10⟩, ⟨4⟩⟩`, typed `nat` by the built-in signature) and
  `freshKey` (`⟨⟨11⟩, ⟨20⟩⟩`, typed by nothing).
  - Adding `freshKey` leaves `service natKey` at `nat` and types the new read at `string`.
  - The override `[(natKey, .string)]` retypes the old read to `string`.
- **Row table.**
  - Appending a row leaves `perform (external 0)` at `nat` and types `external 1`.
  - Inserting the same row in front retypes `external 0` to `bool`.
- **Red controls.** `ServiceExtensionRed.lean` and `RowExtensionRed.lean` each assert
  conservativity for the bad extension. Each exits 1, reporting "did not evaluate to `true`" at
  its one guard.

### 3.5 Consequences for R1, R2 and R6

- **R1** should name its parameter as Σ_app, the tables, with Σ_core fixed. That matches the
  note's own §5 item 1, and it is realistic: the machine is concrete over `NativeOp`.
- **R2** should replace "Status, per extension point" with C1–C7 and this status:
  - **rows:** append-only extensions are conservative (tested); the theorem is owed.
  - **services:** conservative for fresh keys only (tested). The build-time agreement check
    (`BuildRefusal.serviceCarrier`) is today's freshness guard, and must stay when the table is
    threaded.
  - **built-in constructors and atoms:** core; additive by discipline.
  - **structural records and polymorphic cells:** not extensions, once row 2 and rows 42–43 land.
  - **recursive or named data, and retained code:** nominal, so C1–C7 apply when they are
    designed.
- **R6:** the host lane must extend the world by a projection with the back condition, refine the
  old protocols, and add no later worlds to the old components. Then M6, proved now with no host,
  transfers.

## 4. A refreshed design basis: proposal (item 4)

### 4.1 One owner per fact: the duplicates found

| Fact | Owners today | Proposed single owner |
| --- | --- | --- |
| Status of each proof edge | DESIGN-BASIS "Required proof graph"; system map §2 and §5; DESIGN-MAP; post-phase-C §11 | The system map. The basis cites the witness theorem for each decision, never progress. |
| The execution route and targets | DB-09 ("OCaml is a test bed"); system map §1 and §3 | The system map (owner, 2026-09-30). DB-09 keeps the profile parts: ProfileData, HostSpec, Binding and the evidence classes. |
| How modules enter | DESIGN-BASIS "Native library boundaries"; DI-11; DI-89; machine-state §5 | DI-89, until it becomes a DB row. Retire the basis paragraph to history. |
| Value typing | DB-11; system map §4; host-boundary §4.4; rows 44 and 96 | The system map §4 for the frame; a new DB row for the settled decision (coarse values, a typed world). |
| The algebra's version | DB-01; `lakefile.toml`; DI-90 | `lakefile.toml` and `docs/GENERATED.md` for pins. DB-01 states the decision only. |
| The charter (seven properties) | End-state §10 (untracked); the note under review §2 | The system map §1, as the goal's acceptance. Extensibility becomes a DB row with C1–C7. |
| Literature | Spread over seven notes, two of them tracked | The basis, per row (§4.2), plus one bibliography section. |

### 4.2 What a basis row should hold

Today a DB row mixes a decision, an implementation record and dated amendments. Proposed shape, the
same for every row:

- **Decision**, one paragraph: what is settled, stated in the current tree's names.
- **Witnesses**: theorem names with `file:line`, at a stated commit. Tests are named as tests.
- **Refusals**: what the decision excludes, with register ids.
- **Sources**: the research notes that established it, by path and section, each marked tracked or
  untracked.
- **Literature**: author, title, and section or theorem as read, marked **read**, **by name** or
  **assumed**.
- **Status line**: adopted; amended (date, ruling); or superseded (by what).
- **Checked at**: the commit at which a coordinator last re-read the witnesses.

### 4.3 Rows to propose (to the coordinator; not written here)

1. **DB-16, the open signature and additive extension.** R1 over Σ_app; C1–C7; DI-69's `RowSig`
   route; DI-47's compatibility; Σ_core growth by discipline. Pedigree: §1.2 and §3.
2. **DB-17, typing as a protocol per operation over a world.** `Typed` is the generic judgment and
   `TypedProg` the concrete one, with shared certificates. It covers the world, its order and
   antitone typing, and coarse values with `Fits`. Pedigree: §1.1, levels 0–2.
3. **DB-18, the requirement row calculus.** The provision laws; DI-20 and DI-28; rows 51, 90, 104
   and 105; `build_total` landed and cut.
4. **Amendments.**
   - DB-04 gains the budgeted meaning.
   - DB-05 gains the operational fiber layer (`E4-SCHED-CE-001`).
   - DB-03 gains the host relation (row 95; a pointer to `host-boundary.md`).
   - DB-11 gains rows 44 and 96 and the landed admission.
   - DB-13 gains DI-11.
   - DB-12 changes when row 104 lands.
   - DB-15's record refusal is marked as the decision that row 2 must amend.
5. **Retire** "Semantic decomposition", "Native library boundaries" and "Required proof graph" to a
   dated history appendix or to `docs/research/`, with pointers to their owners.

### 4.4 Research notes: which become cited history, and the tracking problem

**Cited history.** These would be cited by section from the basis rows, not copied:
- the end-state note §§8 and 10;
- the composed graph §4;
- the M1 kickoff §§2–4;
- the theoretical review §4, with the corrections of §1.1 and §3.2;
- the core-math note, the papers review and the lit-papers note;
- the provision algebra §§1–3 and §7;
- the type algebra §§0–1 and §8;
- the catalogue §§0 and 3;
- the coherence principle's reading list;
- the slice-5 contract ruling §3.

**The tracking problem.** Seven of these are untracked:
- `2026-09-16-core-goals-and-end-state.md`
- `2026-09-05-runtime-semantics-core-math.md`
- `2026-09-05-effects-papers-review.md`
- `2026-09-07-lit-papers.md`
- `2026-09-04-provision-algebra.md`
- `2026-09-16-dogfood-conclusions-review.md` and `2026-09-16-dogfood-findings-applied.md`

So are `2026-09-08-effectful-repository-notes.md`, `2026-09-09-scout-proof-statements.md` and
`REIFICATION-STRATEGY.md` (tested with `git ls-files`). DESIGN-ISSUES' own rule is that "A ruling
is not made until it is written into a tracked file". The tracked note under review cites five of
them as sources: the end-state note, the core-math note, the provision algebra and the two dogfood
notes.

The coordinator's options:
- **Force-add them**, as was done for the 2026-09-19 design push.
- **Carry each cited claim into its basis row**, with its literature line, so the basis stands
  without them.

I recommend the second for the literature lines and section citations, and force-adding the
end-state note, which holds the charter.

## 5. Open obligations and owner boundaries

**Owner decisions surfaced, not taken.**
- Whether R1's parameter is Σ_app only (recommended) or the whole alphabet.
- Whether DB-15's record refusal is lifted (row 2).
- Whether the untracked pedigree is force-added or carried into the basis.

**Theorems owed if R2 is adopted.**
- C3, checker conservativity along table appends: a mutual induction over the `Eff` families.
- `TypedProg.pull`, `TypedProg.reflect` and `TypedProg.along`.
- C6 for `LawfulTable` appends.
- The C5 frame lemma for old steps.

**Not checked.**
- The C3 theorem itself: only twelve finite instances.
- Hyland, Plotkin and Power, and any p-morphism literature.
- The PDFs beyond the thesis text and the à la carte paper.
- Other seats' notes in `2026-09-30-model-probe/`.

## 6. Receipt

- **Base and head.** `7cae243a` throughout. No file outside this folder was written.
- **Files written.**
  - `note.md` (this file)
  - `Conservativity.lean` (SHA-256 `0b36d34f…5e579`)
  - `ServiceExtension.lean` (`8be60c27…ae21f`)
  - `ServiceExtensionRed.lean` (`29dc0491…02ebc`)
  - `RowExtensionRed.lean` (`053863c4…a009`)
  - the logs: `conservativity.log`, `service-extension.log`, `service-extension-red.log`,
    `row-extension-red.log`
- **Commands.** Each probe ran through `serial.sh` as
  `lake env lean -M6144 -DwarningAsError=true <file>`:
  - `Conservativity.lean`: exit 0. 21 new theorems, each with no axioms or within
    `[propext, Quot.sound]`. Reruns: `Typed.inl`, `inl_inv`, `inr_inv` and `mono` with no axioms;
    `interpret_inl`, `interpret_inr`, `inl_injective` and `interpret_pinned` at
    `[propext, Quot.sound]`; `inl_bind` at `[Quot.sound]`.
  - `ServiceExtension.lean`: exit 0, twelve guards.
  - `ServiceExtensionRed.lean`: exit 1, as expected.
  - `RowExtensionRed.lean`: exit 1, as expected.
- **Otherwise, reads only:** `grep`, `sed`, `git log`, `git show --stat`, `git ls-files`, and
  `pdftotext` of local paper 06 into the session scratchpad.
- **Bounded evidence.** C3 rests on twelve finite instances. Everything in §1 and §2 is reading.
