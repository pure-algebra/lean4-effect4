The one thing: the seat's core result holds (every probe reruns identically, and its C4 pieces compose into one iff, proved here), but "fresh, append-only names" is not enough at HEAD: a fresh service key changes an old program's printed TypeScript, and the old text stops reading back until row 105 lands; the build guard the seat calls a freshness guard refuses every fresh key; `Package.install` itself puts new rows in front; and `TypedProg.along` for the row table needs C3, so P17's order (the `TypedProg` lemmas now, C3 later) does not work.

# Verifier for seat PEDIGREE: verdicts on P1–P17, and what the seat missed

Status: research note, 2026-09-30. Verified at HEAD `7cae243a` on `refactor/phase1-phase3`.
Nothing tracked was edited. The seat's files are untouched: its four probes still have the SHA-256
values its receipt gives. My probes and logs are in this folder, all named `Verify*` or
`verify-*`.

Evidence words, as in the brief. **Proved**: a kernel theorem I ran, with its axioms printed.
**Tested**: a finite check I ran. **Reading**: read in code or notes, not run. **Assumed**: not
checked. Short paths: `Laws/…`, `Program/…`, `Machine/…`, `Codegen/…`, `Api/…` are under
`src/Effect4/`. Research notes are under `docs/research/`.

## 0. In brief

- **Reruns.** All four of the seat's probes reproduce through the lock (§4).
  - `Conservativity.lean` exits 0, and its axioms match `conservativity.log` line for line.
  - `ServiceExtension.lean` exits 0 with its twelve guards.
  - `ServiceExtensionRed.lean` and `RowExtensionRed.lean` each exit 1, with the same message.
  - The counts reproduce: 188 `(sig : Signature` binders and 89 `nativeSignature` lines in 15
    `Laws` files (tested by grep).
- **Verdicts.** Nine findings confirmed, eight partly, none refuted (§1).
  - The partly verdicts come from errors in the seat's evidence or its statements, not in its
    direction.
  - The largest gaps are in P8 and P17, and in the conditions P2 states.
- **What the seat missed** (§2). Each item below is tested or proved here, with a red control.
  - C7 fails for a fresh service key until row 105 lands.
  - Today's build guard admits no fresh key, so it is not a freshness guard.
  - The authoring surface inserts rows in front: `Package.install` prepends.
  - Admission along an append needs more than `LawfulTable`.
  - For host rows, C2 has no instance at the free monad. The only meaning is the machine's run,
    which is conservative along an append and not along an insertion.
- **Pedigree errors the seat did not catch** (reading).
  - The M1 kickoff maps `Typed.mono` to de Vilhena's rule Monotonicity, which is a different law.
  - DB-01 already rules that a signature map owes "its own contract and coherence laws". That is
    where R2's C1–C2 belong.
  - DI-47 governs core alphabet appends, including typing and admission, not only the link table.

## 1. Verdicts

| Id | Verdict | Reason, in one line |
| --- | --- | --- |
| P1 | partly | `interpret_pinned` is uniqueness, not additivity (confirmed). But the tree uses the sum lemmas more than once: `Program.inl_bind` six times in `denoteR_straight`. And only R2, not the charter, cites `Protocol.sum`. |
| P2 | partly | The proofs reproduce and compose into one iff (`c4_iff`, proved here). But the statement is not yet exact: "Σ-program" is undefined for service keys; C6 omits admission's own table checks; C7 fails for services before row 105. Red controls were missing for two of the premises; both are added here. |
| P3 | confirmed | `TypedProg` is its own inductive with seven arms (`Typed/Residual.lean:186-215`). The theoretical review's §4.3 overclaims. Its §7.2 item 5 has the same superseded form, which the seat did not flag. |
| P4 | partly | The facts hold. But the note's phrase paraphrases end-state §8 ("a handler for the control signature (the scheduler)"), so "unsupported" misplaces the error. The tracked statement is the header of `Laws/Program/Sched.lean:33-39`. |
| P5 | confirmed | `f182d2b3` added `build_total`; `b08f3b58` removed it. The docstring at `Program/Provision.lean:35-41` is stale. The cut is already recorded in `docs/core/traversal-census.md:433-435`. |
| P6 | confirmed (reading) | The fragments exclude host rows and service forms. Three things are missing from the list: the face theorems are pinned to native services too; row 21's own text overstates the cost of threading; and `origin_eq_ref` will add another empty-table pin. |
| P7 | confirmed | DI-69, DI-47, DI-89, DI-22 and DI-64 are ruled, and the note cites none of them. DI-47's scope is wider than the seat says (§2, item 9). |
| P8 | partly | The C3 results reproduce, and `nativeServiceTyWith` is an override. But C7 fails for a fresh key (tested), and `BuildRefusal.serviceCarrier` refuses every fresh key (tested), so it is an agreement guard, not a freshness guard. |
| P9 | confirmed (open) | Two corrections. `leHost` had `Extends` from its first commit, so nothing was repaired. And "M6 transfers" covers today's steps only; host-answer steps still need host-boundary §4.5's application theorem. |
| P10 | partly | Most row verdicts hold. "None of these is listed" is wrong for Xia et al. and Chappe et al. (`DESIGN-BASIS.md:808-811`). The DB-13 conflict is weaker than stated. |
| P11 | partly | The budgeted meaning, protocols over a world and the row calculus have no basis row (confirmed). The open signature is partly ruled already, in DB-01, DB-05 and DB-10. |
| P12 | confirmed | DB-15 refuses records and `Err.value`. No register row covers recursive types. The note under review already concedes the `Err.value` half, and post-phase-C §11.2 (W1) already says the basis must be amended. |
| P13 | partly | The untracked list is right (tested). "The layers steer exists only in session memory" is wrong: the coherence principle (tracked) states its shape. The seat's own source for HPP, the algebra-package review, is untracked and missing from the list. |
| P14 | confirmed | The theoretical review's §4.3 header misattributes the sum of theories. HPP 2006 is cited by name in the tree and never read. de Vilhena's Def. 2.4 is a disjunction. |
| P15 | confirmed | The links hold at the cited lines, with one small slip: the quoted `Iter.lean` sentence is at lines 8–9, not line 30. |
| P16 | confirmed (owner) | The recommendation is sound. Add DI-47 as the existing compatibility ruling for the core alphabet's growth. |
| P17 | partly | The generic lemmas are cheap (proved). `TypedProg` is fixed to one `World`, and its protocols call the checker at `root.table`. So `TypedProg.along` for an appended row needs C3 in both directions. "The lemmas now, C3 later" does not hold. |

## 1.1 The evidence, finding by finding

**P1 (partly).**
- **Confirmed: `interpret_pinned` is uniqueness, not additivity.**
  - At `.lake/packages/effects/Effects/Algebra/Universal.lean:243`, any candidate that is a monad
    morphism and agrees on `perform` equals `interpret` (reading; rerun at `[propext, Quot.sound]`).
  - The additivity lemmas are where the seat says: `Sum.lean:48`, `:72`, `:92` (reading).
- **Wrong: "the tree uses them once".**
  - `Effects.Program.inl_bind` is used six times inside `denoteR_straight`
    (`Laws/Program/DenoteR.lean:1422`, `:1465`, `:1482`, `:1502`, `:1527`, `:1534`). That theorem
    states `eraseControl (denoteR root e p) = Effects.Program.inl (denote e p.env)` (`:1379-1381`).
  - `meaning_denoteR_straight` (`:1545-1550`) composes it with `meaning_via_rsig`.
  - So the tree's one real summand extension, the store signature inside `RSig`, carries C1 and C2
    through the connector between the full reference meaning and the straight meaning. That is
    R2's best in-tree witness, and the seat undercounts it.
  - `inl_injective` has no use in `src/` or `Test/` (tested by grep).
- **Imprecise: the charter.** The charter's *Extensible* row cites `interpret_pinned` only (end-state
  §10). `Protocol.sum` landed on 2026-09-18 (`c297c4c7`), after the charter. Only the note under
  review cites both.

**P2 (partly).**
- **Proved here.** The seat's pieces compose into its C4 as one statement: `c4_iff` in
  `VerifyConservativity.lean`, with no axioms. For an extension that adds a summand with its own
  protocol, and reads the old protocol through a projection `π` that is monotone and has the back
  condition:
  `Typed o' ((pull Ψ π).sum Ψn) w (Q ∘ π) (inl p) ↔ Typed o Ψ (π w) Q p`.
- **Gaps in the statement.**
  1. **"Σ-program" is undefined, and C3's first clause depends on it.** Service keys are data. A
     `Signature` has `dom` for operations (`Program/Typing/Rules.lean:62`) but nothing for keys.
     The seat's own guards show the trouble: `readFresh` fails to type before the extension and types
     at `string` after it (`ServiceExtension.lean`). The definition must be: every operation in
     `dom Σ`, and every key at a position the checker looks up typed by Σ. Item 2 shows that is still
     not enough for the faces.
  2. **C7 for services fails before row 105.** See §2, item 1 (tested).
  3. **C6 cites `LawfulTable` only, but admission also checks the table.** It asks for registrability
     (`checkTable`) and for no integer type (`findIntInTable`) (`Program/Admission.lean:89-95`).
     An append that `LawfulTable` accepts can still make an old program inadmissible. See §2, item 4
     (tested).
  4. **C2 for host rows has no free-monad instance yet.** See §2, item 5.
- **Red controls.** The seat's controls cover the back condition, the promise refinement and
  widening of the order. They do not cover monotonicity of `π` or the demand refinement, though the
  seat's note §0 says "each premise is needed". Both are added here, with no axioms:
  - `mono_needed`: the projection `flip : ℕ → Bool` is not monotone; the old program is typed and
    its pull-back is not;
  - `pre_refinement_needed`: a richer protocol that demands more of an old operation loses the old
    typing.

**P3 (confirmed).**
- **The inductive.** `TypedProg`'s arms are `pure`, `store`, `fiber`, `guard`, `unguard`,
  `finishFinalizer` and `scopeExit` (`Typed/Residual.lean:186-215`).
- **The ruling.** The slice-5 ruling's item 3 says "`Typed` stays the Effects library's judgment".
  It is item 3 of the section "The ruling"; the note has no numbered §3.
- **The superseded form.** The composed graph §4 has `TypedProg w ty p := Typed o (Ψ_S.sum Ψ_F) w
  (ExitOk ty) p`.
- **Uses of `Protocol.sum`.** In `src/`, it appears only in the obligation ledger
  (`Typed/ProtocolObligations.lean:30-50`). In `Test/`, it appears in `ProtocolCertificates.lean`
  and in the retained refutation `ReviewedTypedProg`
  (`Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean:146-149`).
- **Not flagged by the seat.** The theoretical review's §7.2 item 5 states
  `TypedProg … ⟺ Typed (World.le) (Ψ_S + Ψ_F) …`. That is superseded twice: by `leHost`, and by the
  inductive.

**P4 (partly).**
- **The facts hold.**
  - `fiberRefusal` is "Not a semantics" (`Laws/Program/Sched.lean:216-218`).
  - `E4-SCHED-CE-001` refutes reading it as one (`Test/Counterexamples/REGISTER.md:157`).
  - The register's repair column says the fiber operations are "interpreted by
    `Program/RuntimeR.lean`" (`Test/contracts/program-sched.contract.md:109`).
- **The error is older than the note.** End-state §8 itself says "an elaboration into an algebraic
  tree (`denoteR`), and a handler for the control signature (the scheduler)". The note under review
  paraphrased that.
- **The tracked statement to cite.** `Sched.lean`'s header (`:33-39`): the fiber operations "have no
  handler here on purpose … not as a `Handler`".
- **The seat's restatement is right.** It is end-state §8's own "honest boundary".

**P5 (confirmed).**
- `git log -S build_total` gives `f182d2b3` (2026-09-04, the theorem added at its line 1724) and
  `b08f3b58` (2026-09-18, "Cut: … Provision's build_total/buildAll_total").
- The cut is already recorded in a tracked authority: `docs/core/traversal-census.md:433-435`
  ("no consumer, 175 lines").
- The provision note itself says the spike landed as `f182d2b` and was deleted
  (`2026-09-04-provision-algebra.md:391`).
- The landed `build_total` was stated over any `(sig : Signature Op)`.

**P6 (confirmed, reading).**
- **The counts.** 188 explicit `(sig : Signature` binders; 219 if the implicit `{sig : Signature`
  binders are counted. 89 `nativeSignature` lines in 15 files (tested by grep).
- **The fragments.** `Straight` admits only `.sync` performs (`Program/Fragment.lean:28-31`).
  `NativeOp.kind (.external _) = .program` (`Program/Native.lean:127`). `service`, `provideService`
  and `provideLayer` are false in both fragments (`Fragment.lean:46-48`;
  `Laws/Program/DenoteB.lean:150-152`).
- **The same holds for `TypedProgram.run_sound*`** (`Laws/Program/TypedRun.lean:83-120`). They are
  pinned to the empty table and restricted to `Straight` and `Looped`.
- **The pins the seat lists are right.**
  - `AdmittedProgram`: `Program/Admission.lean:89-90`.
  - `PointTyped`: `Typed/Admission.lean:92-96`.
  - `ServicesOk`, which reads `nativeServiceTy` directly: `Typed/Admission.lean:32-34`.
  - `memoGet`: `Residual.lean:53`.
  - `ForkSource`: `:32`, `:47`, `:53`, `:68`. It has no consumer outside its file (tested by grep).
- **Missed 1: the faces.** The face theorems are pinned to native services:
  `Laws/Codegen/Admit.lean:229-289`, `Laws/Codegen/Checked.lean:22-84` and
  `Laws/Api/ModuleReadable.lean:139-178` all take `nativeSignature table`. The printer and the reader
  read `sig.serviceTy` at every key (`Codegen/PrintLeaf.lean:300-306`; `Codegen/Read.lean:346-361`).
  So threading the service table also restates the K2 laws.
- **Missed 2: row 21.** Its own recommendation says threading "changes `Built`, `HostSession.start`,
  `Run.open` and both soundness statements". The seat's reading shows the soundness statements lose
  nothing, so row 21's cost is overstated too.
- **Missed 3: the next slice adds a pin.** The design pass synthesis (§2.1, line 43) states the fork
  ledger's `origin_eq_ref` "at the empty table". The next slice therefore adds another empty-table
  pin of the same kind as `ForkSource`.

**P7 (confirmed).**
- **The rows exist and are ruled** (`docs/DESIGN-ISSUES.md`):
  - DI-69 (`:141`): `RowFamily`, `RowSig`, `Sum StoreSig (RowSig table)`;
  - DI-47 (`:119`);
  - DI-89 (`:161`);
  - DI-22 (`:94`);
  - DI-64 (`:136`).
- **DI-69 is unimplemented.** Its names appear only in `Test/contracts/foundation-wave2.contract.md`
  and the register (tested by grep). The design-issue map marks it "ruled delivery pending".
- **The note cites none of them** (reading).
- **DI-47's scope is wider than the seat says.** See §2, item 9.

**P8 (partly).**
- **What reproduces.** The four C3 checks reproduce, and so do the two red controls. The override
  reading is right (`Program/Authoring/Services.lean:42-51`).
- **Refuted (tested): the description of the guard.**
  - The seat says `BuildRefusal.serviceCarrier` "acts as the freshness-or-agreement guard".
  - `Api.Author.disagreeingService` (`Api/Author.lean:45-50`) refuses any declaration whose carrier
    differs from what the built-in signature types the key at.
  - So a fresh key is refused with `signature := none`, exactly as an override is
    (`VerifyGuards.lean` §1; red control `VerifyGuardsRed.lean`).
  - It is an agreement-only guard. That is what row 21 and the note under review say: "no seventh
    carrier".
  - Threading the table therefore needs a new guard, "fresh for the built-in table, or agreeing",
    not "keep" this one.
- **Refuted (tested): C7 for a fresh key.** See §2, item 1.
- **Untested, but likely by reading: C7 for an appended host row.** `nativeSpell` returns the first
  matching index (`Codegen/Read.lean:1948-1952`), so reading is stable under appends.

**P9 (confirmed as an open question).**
- **Proved (seat, rerun).** `typed_antitone` and `order_widening_loses_typing`.
- **Correction 1: nothing was repaired.** `World.leHost` was defined with `Extends` in its first
  commit, `cd769650` (2026-09-21 01:23), and has not changed since (tested with `git log -L`). The
  theoretical review's §2.4 quotes a strict-equality version found only in a plan
  (`2026-09-20-m1-evidence/phase-b/proof-plan/PhaseCWorldPlan.md:74`, `:82`). So "repairs the §2.4
  risk" should read "the §2.4 risk was never in the tree".
- **Correction 2: the transfer claim is too strong.** The seat's note §3.5 says "M6, proved now with
  no host, transfers". That covers the steps that exist today. A host answer is a new step, and it
  needs host-boundary §4.5's application theorem ("preparation yields a valid state and world
  extension …") however the world is extended.
- **The seat's order rule fits the host contract.** New components get their own order, and old
  components keep theirs. host-boundary §4.3 already asks for a host key kept separate from the
  machine index, and §4.5 says "Unrelated allocation alone cannot invalidate a claim". That is C5's
  frame clause.

**P10 (partly).**
- **These verdicts hold (reading at the cited lines):**
  - DB-01: `v0.1.0` at `:72`, while the pin is `a4ee7a1…` (`lakefile.toml:126-130`);
  - DB-09: `:381`, against system map §1;
  - DB-11: `:418-420`;
  - "Native library boundaries": `:705-708`, against DI-11 and DI-89;
  - the "Required proof graph" rows: `:731` has no empty-table qualifier; `:732` says finite adequacy
    holds on the single-fiber straight-line fragment only, but `loopAgreement` covers `Looped`;
  - DB-07: there is no `EStateM` under `src/` (tested by grep; 0 hits).
- **Wrong.** The seat's §2.2 says of the basis's "Primary sources": "None of these is listed".
  The basis lists Xia et al. and Chappe et al. (`DESIGN-BASIS.md:808-811`).
- **Weaker than stated.** DB-13 says every waiting family parks on one `WakeList`. DI-11's composite
  route uses `WakeList` too ("over Ref + Deferred + WakeList"). The tension is in DB-13's wording,
  "Queue … as they land", with rows that register on "the family's list". It does not amount to "a
  store per family". machine-state §6 ("correcting a contradictory summary does not require ruling
  it again") supports the seat that some summary contradicted DI-11.

**P11 (partly).**
- **Confirmed: these have no basis row.**
  - The budgeted meaning: no register row owns `denoteB` either (tested by grep of
    `decisions.md`, `DESIGN-ISSUES.md`, `system-map.md`, `STATE.md` and `DESIGN-MAP.md`).
  - Typing as a protocol over a world.
  - The row calculus.
- **Not missing: the open signature is partly ruled already.**
  - DB-01's last paragraph: "`Handler.sum` is the operation for disjoint signatures … Any explicit
    signature map or universe lift requires its own contract and coherence laws." The seat's
    `along_bind` and `interpret_along` are those coherence laws for a signature map.
  - DB-05: "`Scope` remains a separate signature summand".
  - DB-10 names "signature maps and lenses, first-class monad morphisms" as shapes Effect4 may adapt.
- **So** DB-16 should amend DB-01, which is the row that rules signature sums and maps, rather than
  stand beside it as a second owner.

**P12 (confirmed).**
- `DESIGN-BASIS.md:665` refuses records ("A record type in `Ty`: columns are pairs").
- `:655` refuses `Err.value`.
- Decisions row 2 is open (`decisions.md:23`).
- No register row mentions recursive types (tested by grep).
- **Two qualifications.**
  - The note under review already says "The basis refuses `Err.value` … an owner ruling is needed".
    Only the record half is new.
  - Post-phase-C §11.2 W1 already states the rule: "Arbitrary error payloads need the existing basis
    ruling amended, not silently enabled".

**P13 (partly).**
- **Confirmed (tested).** `git ls-files --error-unmatch` confirms that all ten notes the seat names
  are untracked, and that the note under review cites five of them.
- **Wrong: the layers steer.** The seat says the "layers steer … exists only in session memory".
  - `docs/core/coherence-principle.md:552-553` (tracked) cites Swierstra and Cartwright–Felleisen for
    "rows as extension points: a signature coproduct with per-row algebras, the shape the layers steer
    wants".
  - Scout B (`2026-09-17-language-constructs-api-scout-B.md` §1.4, tracked) records "the extension
    point the owner names".
  - Only the steer's own words are in memory, including that composition "needs a lawful
    `Signature.append`". That is the earliest statement of R2 as an obligation, and no note has it.
- **Missing from the list.** `2026-09-02-algebra-package-review.md` is untracked too. It is the
  seat's own source for "HPP 2006 … primary not read".

**P14 (confirmed).**
- The theoretical review's §4.3 header cites "Plotkin & Pretnar 2009; Bauer & Pretnar 2015", and the
  text says "mirrors Plotkin & Pretnar's coproduct of algebraic theories".
- HPP 2006 appears in the tree by name only:
  - `coherence-principle.md:547`, for free algebra against a theory with equations;
  - `REIFICATION-STRATEGY.md:120`, `:225`;
  - the algebra-package review, `:410`, "primary not read".
- de Vilhena's Def. 2.4 is `Ψ1 + Ψ2 ≜ λu Φ. Ψ1 u Φ ∨ Ψ2 u Φ`
  (`2026-09-05-effects-papers/text/verification_with_effects.md:590`, reading). That is a disjunction
  on one payload domain, not a coproduct of signatures.
- The Swierstra quotation is in §2 of local paper 06, just before §3 "Evaluation" (reading in the
  session's `alacarte.txt`, lines 89–92).

**P15 (confirmed).** Reading at every cited line:
- `World.lean:52-57`, `Behaviour.lean:74` and `:92`;
- `Iter.lean:30` and `:40`, but the quoted sentence ("Elgot iteration cut at a budget, generic over
  the signature") is the module docstring at `:8-9`;
- `DenoteB.lean:208`, `:285`, `:386` and `:496`; `LoopSound.lean:306`; `Agreement/Loop.lean:839`;
- `Provision.lean:98` and `:138`.

End-state §4.2's "a parameter of the one `denote`, changed in place, not a second denotation beside
it" is indeed superseded. The tree followed AGENTS.md's build-in-parallel rule instead, with
`denoteB_straight` as the connector.

**P16 (confirmed; owner decision).**
- `check_sound` and `check_complete` hold over any `Op` and `sig`
  (`Laws/Program/Typing/CheckSound.lean:37`, `:361`).
- The machine is concrete over `NativeOp`, `SyncOp` and `FiberOp`.
- **Missed: DI-47.** "Σ_core growth is additive only by discipline (rows 56, 61)" leaves out that
  DI-47 rules a compatibility relation for exactly those alphabets. It is a finite gate, not a
  theorem. See §2, item 9.

**P17 (partly).**
- **Confirmed.** The generic lemmas closed in a few lines each (proved, the seat's and mine).
- **The cost of the `TypedProg` lemmas is understated.** `TypedProg` is declared over the fixed
  structure `World` (`Residual.lean:186`). Its marker arms read `fiberPost` and `StrongExit` directly
  (`:200-215`). So `TypedProg.pull` and `TypedProg.reflect` along a world projection first need a
  `TypedProg` generic in its world and protocols. That is a refactor, not one induction.
- **The order does not work for rows.** The one extension point the tree has today is the row table,
  read through `root.table`.
  - `fiberPre` calls `PointTyped`, hence `Checker.check (nativeSignature src.table)`, for `raceAll`,
    `scoped`, `forkScoped`, `forkIn`, `gen` and `loop`, and `BodyTyped` for `mask` and `fork`
    (`Residual.lean:132-146`).
  - `asyncPre` reads `rowOf` (`:111-112`). `storePre`'s `memoGet` calls `checkLayer` (`:52-53`).
  - So `TypedProg.along` for an appended row needs C3 in both directions: monotone, to lift, and the
    first clause, to reflect.
  - "Schedule the `TypedProg` lemmas with M6 … Defer C3" therefore cannot be followed for the row
    table.
  - Recommended order: C3 for table appends first, or with the lemmas, as one induction over the
    checker's families. The world-projection lemmas wait until the host lane actually adds a world
    component.

## 2. What the seat missed

Items 1–6 are tested or proved here, and each has a red control that fails as expected. The rest
are reading.

1. **C7 fails for a fresh service key until row 105 lands** (tested: `VerifyServiceFace.lean`,
   10 guards; red control `VerifyServiceFaceRed.lean`).
   - **Why a typed program can hold such a key.** The checker does not look up a layer leaf's key
     today: the `.succeed` arm of `checkLayer` reads only the literal
     (`Program/Checker.lean:228-230`). Row 105 rules the lookup, and it has not landed.
   - **The program.** An old program `provideLayer (.succeed k (.nat 1)) false (succeed 0)`, with
     `k := ⟨⟨11⟩, ⟨20⟩⟩`, types under the built-in signature.
   - **C3 holds:** the program has the same type under `nativeSignatureWith [] [(k, .nat)]`.
   - **C7 fails:**
     - the key prints as `Context.Service("k11_20")` before the extension and as
       `Context.Service<number>("k11_20")` after it;
     - the old printed module does not read back under the extension, because `readKey` admits a
       bare key only when the signature does not type it (`Codegen/Read.lean:346-361`).
   - **Consequence.** R2 for services needs row 105 as a precondition: every key position is looked
     up. The alternative is to state C7 only over key positions the checker reads. The seat's P8 and
     its one-thing line claim C7 for fresh keys without a test.
2. **The build guard is agreement-only** (tested: `VerifyGuards.lean` §1, 6 guards; red control
   `VerifyGuardsRed.lean`).
   - `disagreeingService` refuses a fresh key with `signature := none`, refuses an override with
     `some .nat`, and accepts only an agreeing declaration.
   - It is the guard that keeps out the seventh carrier, not a freshness guard.
   - Threading (R5) must replace it with "fresh for the built-in table, or agreeing", as the seat
     intends. The seat's description of today's guard is wrong.
3. **The authoring surface inserts rows in front** (tested: `VerifyGuards.lean` §2, 8 guards; red
   control `VerifyGuardsRed.lean`).
   - **Why.** `Package.install ps m` sets `rows := rowsOf ps ++ m.rows`
     (`Program/Authoring/Services.lean:186-187`). `Module.table` is the module's rows, then each
     service's operations (`Program/Authoring.lean:322-326`).
   - **What happens.** Installing the SQLite package into a module that already has the key-value
     package:
     - moves `get` from position 1 to position `sqliteBun.length + 1`;
     - elaborates the same source to a different `Eff`;
     - retypes the earlier `Eff` against the new table.
   - **The append case.** Installing both packages in one call, old one first, is an append, and the
     `Eff` is unchanged.
   - **What protects programs today.** The source survives, because rows are called by spelling.
     The stored tree survives only if it travels with its own link table (DI-22, DI-05).
   - **Consequence.** DI-47's "appends only" is not enforced where modules are assembled. The basis
     row must say which of two rules holds: installation appends, or a stored program is never
     re-linked.
4. **Admission along an append needs more than `LawfulTable`** (tested: `VerifyAdmission.lean`, 8
   guards; red control `VerifyAdmissionRed.lean`).
   - Appending a row with `registration := .deferred`, or a row whose answer is `.int`, keeps the
     table lawful by `LawfulTable`, and the checker's type for the old program is unchanged.
   - `admitProgram` nonetheless refuses the old program: `.table (.notExternal 1)` in the first case,
     `.uninhabited` in the second. The old program never calls the new row.
   - So C6's "local lawfulness" for a row must include `checkTable` and the integer scan
     (`Program/Admission.lean:89-95`; `Program/Native.lean:347-354`), not only `LawfulTable`
     (`Codegen/Read.lean:1943`).
5. **For host rows, C2 has no instance at the free monad; the conservativity owed is operational**
   (tested: `VerifyRun.lean`, 8 guards; red control `VerifyRunRed.lean`).
   - **No free-monad meaning yet.** DI-69 (the row table's meaning as `Sum StoreSig (RowSig table)`)
     is unimplemented, so `interpret_inl` has nothing to say about a host row. Today the only meaning
     of a host call is the native run against the supplied table (`Api.lean:285-293`).
   - **Along an append, the run is conservative.** The checked replay of the old journal is accepted
     and the raw run exits with 7, as before.
   - **Along an insertion, it is not.** The call is retyped to `bool`. The checked replay refuses the
     old journal with `.answerType root 0 .bool`. The raw run with the old preloaded answer stops at
     a live frontier waiting for the host (`awaitHost`), with no exit.
   - **Consequence.** R2 for rows needs an operational clause beside C2, "the run of an old program
     against an appended table is the run against its own table". That clause is owed. The
     reference relation is empty-table only (`run_eq_ref`, `Laws/Program/RuntimeR.lean:197-210`), so
     no current theorem covers it.
6. **Two of the seat's premises had no red control** (proved: `VerifyConservativity.lean`, no
   axioms).
   - `mono_needed`: preservation fails for a projection that is not monotone.
   - `pre_refinement_needed`: transport fails when the richer protocol demands more.
   - With the seat's controls, every premise of `typed_pull_of_typed`, `typed_of_typed_pull` and
     `typed_along` now has one, except the result-predicate premise `hQ`, which is trivially needed.
   - `c4_iff` shows the pieces compose.
7. **The M1 kickoff maps `Typed.mono` to the wrong Hazel rule** (reading).
   - **The claim.** The kickoff's §3 (tracked, lines 249–251) says "`Typed.mono` is his
     Monotonicity rule, which is why the demand and the result predicate must be upward closed
     (Definitions 2.6, 2.7)".
   - **What Hazel says.** de Vilhena's Def. 2.6 and 2.7 close a protocol upward in the continuation's
     postcondition, `Φ ≤ Φ'` (`verification_with_effects.md:606-641`). Rule Monotonicity weakens the
     protocol by Def. 2.8 and the postcondition (`:664-668`, `:752`, `:782`).
   - **What the tree has.** `Typed.mono` (`Laws/Effects/Protocol.lean:57-63`) weakens along the
     *world order*, which needs `Mono` in the world.
   - **The right mapping.**
     - Hazel's Monotonicity is `Typed.widen` plus protocol refinement, the seat's `typed_along`.
     - Def. 2.6 holds by the shape of `Typed.vis`'s continuation clause.
     - World-order weakening is the Kripke and Iris upward closure in resources. That is by name
       only (the theoretical review's §4.1 cites Ahmed 2006 and Iris by name).
   - **Consequence.** The seat's proposed DB-17 cites level 0's pedigree from these notes, so it would
     inherit the conflation. The seat's own C4 citation (Def. 2.8 with rule Monotonicity) is the
     right one.
8. **The basis already rules pieces of R2** (reading).
   - DB-01 (`DESIGN-BASIS.md:101-105`): `Handler.sum` for disjoint signatures, and "Any explicit
     signature map or universe lift requires its own contract and coherence laws".
   - DB-05 (`:224`): `Scope` as a separate summand.
   - DB-10 (`:409`): signature maps and monad morphisms as adaptable shapes.
   - The seat's C1–C2 (`along_bind`, `interpret_along`) are DB-01's owed coherence laws.
   - Recommendation: write C1–C7 as an amendment to DB-01, with DB-05's summand rule cited, rather
     than a parallel DB-16.
9. **DI-47 covers the core alphabets, not only the link table** (reading).
   - **What it freezes.** DI-47 replaces DI-02 and DI-03. DI-02 lists what is frozen: "`Eff` 0–26,
     `NativeOp` 0–22, `Store.Tag` 1–12, `HandleKind` 0–7, `Kind` 1–15, service codes 4–9, package row
     positions" (`docs/DESIGN-ISSUES.md:74`).
   - **What it compares.** DI-47 compares "structural/wire compatibility, old-value exact decoding,
     typing/admission, and execution permission separately" against the retained baseline
     `Test/fixtures/baseline/66ee4657/`, whose README lists what the gate must refuse. The Conform
     mirrors read that baseline (`tools/Conform/Effect4/mirrors.json`).
   - **So core growth is not "by discipline" alone.** C3 and C7 for appends to the core alphabets
     are ruled, as a finite gate, not a theorem ("Current snapshot equality is not a universal
     compatibility theorem"; the contract: "A finite fixture gate is not a universal theorem").
   - This bears on P7 and P16.
10. **More pins than P6 lists** (reading).
    - The face laws at `nativeSignature table` (`Laws/Codegen/Admit.lean:229-289`;
      `Laws/Codegen/Checked.lean:22-84`; `Laws/Api/ModuleReadable.lean:139-178`).
    - The printer and reader reading `serviceTy` (item 1).
    - The fork ledger's coming `origin_eq_ref`, "at the empty table" (design pass synthesis §2.1).
    - Row 21's text claims threading changes "both soundness statements". By P6's own reading they
      lose nothing.
    - The note under review's §4 counts only the `Typed/` folder. `Laws/Program/Typed.lean` and
      `TypedRun.lean` have 7 `nativeSignature` lines each, all at the empty table on `Straight` or
      `Looped`, so they lose nothing either. The codegen faces have 14 more.
11. **`TypedProg.along` for the row table depends on C3** (reading; see P17). The seat's cost and
    order for the `TypedProg` lemmas do not survive this.
12. **The theoretical review misquotes the tree twice** (reading).
    - §2.4 quotes a strict-equality `leHost` that only a plan had (`PhaseCWorldPlan.md:74`). The tree
      has had `Extends` since `cd769650`.
    - §7.2 item 5 states `TypedProg` as `Typed (World.le) (Ψ_S + Ψ_F)`.
    - Both should be marked superseded wherever the basis cites the review, beside the §4.3
      correction the seat makes.
13. **The layers steer stated R2 as an obligation first** (reading, session memory
    `layers-composability-steer-2026-09-17.md`).
    - Its words: composition "needs a lawful `Signature.append`". It is the earliest form of R2 as an
      obligation. Only the steer's shape reached a tracked file (`coherence-principle.md:552-553`).
    - If the basis cites the steer, it should cite that sentence, with its date, from a tracked note.

## 3. R2's conditions, as amended by this verification (proposal)

The seat's C1–C7 stand, with these changes. Each change cites the item above that forces it.

| | Change | Forced by |
| --- | --- | --- |
| C2 | Add an operational clause: an old program's run against an appended table is its run against its own table. It holds on the probe (tested). It is owed in general, and for host rows it is the only form until DI-69 lands. | §2 item 5 |
| C3 | Define "Σ-program": every operation in `dom Σ`, and every key at a looked-up position typed by Σ. State C3 for table appends first, because `TypedProg.along` needs it. | P2; §2 item 11 |
| C6 | Local lawfulness of a new row is `LawfulTable` and `checkTable` and the integer scan. For a new service, the guard is "fresh for the built-in table, or agreeing", replacing today's agreement-only guard. | §2 items 2, 4 |
| C7 | For services, it holds only once every key position is looked up (row 105). For rows, only if module assembly appends (`Package.install` prepends today), or a stored program is never re-linked. | §2 items 1, 3 |
| C5 | As the seat states. "M6 transfers" covers today's steps; host-answer steps need host-boundary §4.5's application theorem. | P9 |
| Home | An amendment to DB-01, citing DB-05, DI-47, DI-69, DI-22 and DI-64, rather than a parallel row. | §2 items 8, 9 |

## 4. Probes

Every probe ran through the one-compiler lock as
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <file>`. Each log ends with
its exit code.

**The seat's probes, rerun.** All are unchanged; their SHA-256 values match the seat's receipt.

| File | Exit | Log | Result |
| --- | --- | --- | --- |
| `Conservativity.lean` | 0 | `verify-rerun-conservativity.log` | 30 `#print axioms` lines, identical to `conservativity.log`. The new theorems need no axioms, except `along_bind` and `along_inl` (`[Quot.sound]`) and `interpret_along` (`[propext, Quot.sound]`). |
| `ServiceExtension.lean` | 0 | `verify-rerun-ServiceExtension.log` | 12 guards pass |
| `ServiceExtensionRed.lean` | 1 | `verify-rerun-ServiceExtensionRed.log` | the expected guard fails |
| `RowExtensionRed.lean` | 1 | `verify-rerun-RowExtensionRed.log` | the expected guard fails |

**My probes.** The red controls are kept as fixtures beside the green probes.

| File | Exit | Log | What it shows |
| --- | --- | --- | --- |
| `VerifyConservativity.lean` | 0 | `verify-conservativity.log` | Proved, all 11 theorems with no axioms: `pull_of`, `of_pull`, `inl_reflect'`, `c4_iff`; the red controls `mono_needed` (with `flip_not_mono`, `old_typed_at_false`, `pulled_untyped`) and `pre_refinement_needed` (with `free_typed`, `never_untyped`). |
| `VerifyGuards.lean` | 0 | `verify-guards.log` | 18 guards: the agreement-only build guard (§2 item 2); `Package.install` prepending, and appending in one call (§2 item 3); `LawfulTable` of two disjoint tables appended (C6's shape). |
| `VerifyGuardsRed.lean` | 1 | `verify-guards-red.log` | Two red controls fail as expected: "the guard admits a fresh key"; "a later install keeps the tree". |
| `VerifyServiceFace.lean` | 0 | `verify-service-face.log` | 10 guards: a fresh key keeps C3 and breaks C7 (§2 item 1). |
| `VerifyServiceFaceRed.lean` | 1 | `verify-service-face-red.log` | Red control fails as expected: "the old text reads back under the extension". |
| `VerifyAdmission.lean` | 0 | `verify-admission.log` | 8 guards: a lawful append can make an old program inadmissible (§2 item 4). |
| `VerifyAdmissionRed.lean` | 1 | `verify-admission-red.log` | Red control fails as expected: "`LawfulTable` append implies admission". |
| `VerifyRun.lean` | 0 | `verify-run.log` | 8 guards: the run is conservative along an append and not along an insertion (§2 item 5). |
| `VerifyRunRed.lean` | 1 | `verify-run-red.log` | Two red controls fail as expected: "the checked replay and the raw run survive an insertion". |

`VerifyRunScratch.lean` was a scratch `#eval` file that found the frontier outcome. It was moved to
the session scratchpad and is not evidence.

## 5. Receipt

- **Base and head.** `7cae243a` throughout. The note under review states base `74b526d4` and was
  committed at `7cae243a`. No `lake build`, `make`, generator, `git add`, commit or checkout was
  run. `/Users/pooks/Dev/lean4-effect4-slice6` was not read.
- **Files written.** All are under this folder; none of the seat's files was touched.
  - `verify.md` (this note).
  - The probes: `VerifyConservativity.lean`, `VerifyGuards.lean`, `VerifyGuardsRed.lean`,
    `VerifyServiceFace.lean`, `VerifyServiceFaceRed.lean`, `VerifyAdmission.lean`,
    `VerifyAdmissionRed.lean`, `VerifyRun.lean`, `VerifyRunRed.lean`.
  - The logs: `verify-*.log`.
- **SHA-256 of my probes:**
  - `VerifyConservativity.lean` `85a43515…3e64`
  - `VerifyGuards.lean` `c8645822…f07a`
  - `VerifyGuardsRed.lean` `ffa18023…8b56`
  - `VerifyServiceFace.lean` `06417c9a…6011`
  - `VerifyServiceFaceRed.lean` `6b3869ea…9816`
  - `VerifyAdmission.lean` `af9a3309…8497`
  - `VerifyAdmissionRed.lean` `0e2f87c5…b01b`
  - `VerifyRun.lean` `fc6d851f…e1f7`
  - `VerifyRunRed.lean` `915ec43b…3076`
- **Axioms.** Every theorem I stated prints "does not depend on any axioms". The seat's reruns stay
  within `[propext, Quot.sound]`. There is no `sorry`, `native_decide`, `axiom`, `partial` or
  `unsafe`.
- **Reads.** Otherwise the work was reads only: `grep`, `sed`, `awk`, `git log` (`-S`, `-L`,
  `--diff-filter`), `git show`, `git ls-files --error-unmatch`, and the session scratchpad's
  `alacarte.txt` (local paper 06, produced by the seat).
- **Bounded evidence.**
  - Every tested item is a handful of finite instances: one fresh key, one row, two packages.
  - C3, C7 and the operational C2 are not proved for appends in general; each is owed (§3).
  - The literature mappings in §2 item 7 are reading of the thesis text, and the Iris side is by name.
- **Open obligations, for the coordinator.**
  - Rule where C1–C7 live (an amendment to DB-01, recommended).
  - Decide whether `Package.install` must append, or whether stored programs are never re-linked.
  - Order C3 before or with any `TypedProg` transport lemma.
  - Name row 105 as a precondition of service-table threading (R5).
  - Correct the M1 kickoff's `Typed.mono` mapping before a basis row cites it.
