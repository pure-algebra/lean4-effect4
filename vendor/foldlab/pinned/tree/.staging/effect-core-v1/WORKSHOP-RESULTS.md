# Effect Core v1 — workshop results: probes, anchors, and adjudication

Status: **PRE-GRADE**, 2026-08-31. Written by **Opus** (coordinator, Mac) and
reconciled into the packet after the breaker and local-anchor proofs landed.

Lane roster, stage routing, and the classified finding list live in
[`.staging/agent-reports/2026-08-31-effect-core-coordination.md`](../agent-reports/2026-08-31-effect-core-coordination.md).
Read that first if you are picking this up cold or standing up the
counterexample space.

**Every Lean task on this packet routes through a `lean` skill stage**
(`.claude/skills/lean/`). This document's own work sat in
`lean-assurance-review` — "try to refute each link" — and its findings are
classified in that stage's verdict vocabulary in the coordination note. A lane
that does not name the stage it used has not reported completely.

This is the `WORKSHOP-RESULTS.md` slot named in this directory's `AGENTS.md`
ownership table: it owns *exact local probe commands and observations*, and it
owns no frozen declaration and no promoted claim. Where a probe implies a change
to a row, the change is stated here as an **ask against the file that owns that
row** — `PROOF-DAG.md` for theorem signatures and proof routes, `ALGEBRA.md` for
carriers and semantic faces, `PLAN.md` for construction decisions. Nothing here
is copied into those files by this document.

Companion file: [`workshop/exhibits.lean`](workshop/exhibits.lean) — 17 theorems that COMPILE.
Check them with

```
cd library/cas && lake env lean ../../.staging/effect-core-v1/workshop/exhibits.lean
```

Every one reports standard axioms only — `propext`, plus `Quot.sound` wherever
list reasoning enters. No `sorryAx`, no `Classical.choice`; the `#print axioms`
block at the foot of the file is the receipt.

## 0. Packet reconciliation

This section is the controlling reading of the workshop. Later passages retain
the alternatives that were investigated, but they are evidence history rather
than open design choices.

1. A graph block body is the existing `PProg`. The ANF-only scratch carrier is
   a useful checker probe, not a proposed second sequential representation.
2. Finite block unfoldings land in existing `Prog`; full-core meaning remains a
   relation over typed decisions, including external answers and scheduler
   selections. Scheduler policy/state belongs to the initial configuration;
   supplying one complete compatible decision tape selects a deterministic
   replay path but does not collapse the public semantics to a function.
3. `Handler`, `Handler.sum`, `Handler.through`, `interpret_bind`, and
   `interpret_through` remain the handler basis. No `HHandler` is introduced.
   `Handler.sum` combines handlers with one target; `Handler.through` applies
   only to an upper `Handler S (Prog T)` and lower `Handler T M`. A scoped
   handler already targeting the state/error machine is interpreted directly.
   The breaker proves, however, that `ReaderT Env (Prog CasSig)` is too weak to
   implement recovery: the same existing `Handler` must target a machine that
   can observe child success/failure and state.
4. `Prog.bind` is failure-strict, so the scratch `ensuring` clause does not run
   a finalizer after refusal.
5. EffHOL's modality is existing `wlp`. Its elimination/composition rule is the
   new pending `EC1-T130`, to be derived from shipped `wpAux_append` with a
   nonempty prefix and the prefix-produced answer history threaded into the
   suffix. No `wlp_append` is inherited. The unconditional table-only reading
   has two kernel-checked counterexamples.
6. `toPProg` is a sound recognizer for one literal normal form, not a semantic
   projection from arbitrary CAS-only graphs.

All counterexamples now have stable IDs and evidence states in
[`COUNTEREXAMPLES.md`](COUNTEREXAMPLES.md). That register, the operator-set
representation decisions in [`README.md`](README.md), and the declaration
owners outrank stale recommendation language in an incoming lane report.

## 0a. Standing beside the packet's other work

Two things in this directory were written concurrently with this one. Neither
is superseded as evidence; they no longer represent competing decisions.

**[`EXISTING-TYPES.md`](EXISTING-TYPES.md) is complementary, not overlapping.**
It annotates existing *declarations* (`EC1-XT001`…`EC1-XT024`) with a
disposition — reuse / restrict / bridge / embed / separateCalculus. This
document annotates existing *theorems*, and maps them onto the DAG's PENDING
rows. A declaration ledger says what may be reused; a theorem ledger says what
need not be re-proved. `EC1-XT017` already cites
`Universal.run_has_no_composition_law` as a boundary; §1.5 below draws the
consequence that citation implies for `ALGEBRA.md` §10's triangle, which the
row does not.

**[`workshop/EffectCoreProbe.lean`](workshop/EffectCoreProbe.lean) tests the
rejected ANF-only contrast, and that is useful.** It imports `Std` and nothing
else: fresh `ValueTy`, `RawProgram`, a decidable `ProgramWF` with diagnostics,
`check_sound`, a may/must `FlowSummary` algebra, and a total surface
disposition. `workshop/exhibits.lean` imports `Cas.Lang.*` and builds the graph on the
existing carriers. Both compile. They are not rivals — they are different
slices, and together they price the representation choice:

| | `workshop/EffectCoreProbe.lean` | `workshop/exhibits.lean` |
|---|---|---|
| imports | `Std` | `Cas.Lang.Wp`, `Cas.Lang.Tower` |
| slice | `EC1-S1`/`EC1-S2` — raw carrier, checker, diagnostics | `EC1-S3`/`EC1-S5` — CAS seam, cycles, coherence |
| block shape | `RawBlock = ⟨id, RawTerm⟩` — one terminator, **no straight-line body** (ANF) | `GBlock = ⟨PProg, GTerm⟩` — basic block |
| proves | `check_sound`, footprint assoc/union-intersection, total disposition | modality identification, `EC1-T101`/`T102`, coherence, colimit determinism, one counterexample |
| CAS seam | owed in full | two of four boundary laws proved |
| monad laws | owed | inherited (`interpret_bind`, `LawfulMonad (Prog S)`) |

The probes did not settle the block shape by themselves; the packet has now
settled it to basic blocks with `PProg` bodies under `EC1-R15`. ANF — one
operation per block — remains the documented counterdesign: it maximises
sharing and gives every operation an address, but loses direct transfer of the
existing L-A theorem set because there is no `PProg` inside the block.

**Tracking note.** `.gitignore:11` (`.staging/*/*/*`) ignores everything at depth
3 except `.md`, so both files under `workshop/` need `git add -f` to be
committed. That is the precedent
`.staging/algebraic-review/handlers-semantics-exhibits.lean` and
`word-store-exhibits.lean` already run; both are tracked.

---

## Why this document exists

`PROOF-DAG.md` states ~120 PENDING theorem rows in schematic notation. Not one
of them cites a declaration that already exists in `library/cas`. That is
correct for a Pass A architecture and wrong to carry into Pass B, because the
corpus already proves — or already refutes — a substantial fraction of the DAG.
This document supplies three things the packet does not yet have:

1. **kernel-checked evidence** for five design questions the packet leaves open
   (§1), including one counterexample;
2. **the local anchor spine** — which existing theorem each layer of the DAG
   inherits, specialises, or is contradicted by, at `file:line` (§2);
3. **the three representation questions** that changed the DAG's shape, the
   evidence used to resolve them (§3), and the challenges that survive (§4).

---

## 1. What the exhibits establish

| § of `workshop/exhibits.lean` | Bears on | Finding |
|---|---|---|
| §1 | `EC1-PV01` | EffHOL's `⟨x ← p⟩ φ` is **`wlp`**, not `wp` — but only PARTIALLY: `wlp` fails EffHOL's unconditional (Mod-E). |
| §2 | `EC1-R05`, `EC1-K15` | The fuel-indexed shape is **forced**, not chosen. |
| §3 | `EC1-R02`, `EC1-R04` | Each approximant is an ordinary `Prog`; every R10 handler applies unchanged. |
| §4 | `EC1-T101`, `EC1-T102`, `EC1-S3` | `runCore_runP` proved by a monad law and survives attack; `toPProg` is **not** `projectCas`. |
| §5 | `EC1-A30`, `EC1-T039` | Coherence is **derived**, and only at the big-step face. |
| §6 | `EC1-R06`, `EC1-K16` | Scoped bodies need no `HHandler`; the scratch target is not adequate for recovery. |
| §7 | `EC1-A29` | **Counterexample**: out-of-fuel must not be spelled as a refusal — a witness, not a schema. |

### 1.1 EffHOL's modality is `wlp` (`EC1-PV01`)

`PLAN.md` §5 admits EffHOL as advisory only, pending a lock. The advice can be
made precise now, because the paper carries its own discriminator: Fig. 5 gives
the modality exactly (Mod-I), (Mod-E), (Mon), and §III-C records *"while `⊥` is
underivable, `⟨x ← p⟩ ⊥` may be derivable for some `p`"*.

The estate has both transformers already ([`Cas/Lang/Wp.lean:150,154`](../../library/cas/Cas/Lang/Wp.lean)).
`workshop/exhibits.lean` §1 settles which one the modality is:

- `wlp_bot_derivable` — `⟨x ← p⟩ ⊥` **is** derivable for `wlp`, witnessed by
  `Falsifier.absentLoad`;
- `wp_bot_never` — `wp` refutes it universally, via the estate's own
  `wp_bot` ([`Wp.lean:364`](../../library/cas/Cas/Lang/Wp.lean));
- `wp_is_modality_and_total` — and the decomposition
  `wp Q ↔ wlp Q ∧ wp ⊤` is already proved (`wp_iff_wlp_and_total`,
  [`Wp.lean:380`](../../library/cas/Cas/Lang/Wp.lean)).

So the specification logic inherits its modality rather than deriving one, and
the split between partial and total correctness is `PartialTriple` vs `Triple`
([`Wp.lean:552,557`](../../library/cas/Cas/Lang/Wp.lean)), both already anchored
at `interpretRef` by `Triple_iff_interpretRef` ([`Wp.lean:652`](../../library/cas/Cas/Lang/Wp.lean)).

One caveat is live and dispatched to the breaker: `wp_append`
([`Wp.lean:528`](../../library/cas/Cas/Lang/Wp.lean)) carries a `pre ≠ []` side
condition, and `falsifier_empty_prefix` ([`Wp.lean:815`](../../library/cas/Cas/Lang/Wp.lean))
proves it necessary. EffHOL's (Mod-E) is unconditional. Whether `wlp`'s
sequencing law needs the same premise decides whether the identification is
total or partial.

### 1.2 The fuel-indexed shape is forced (`EC1-R05`)

`PLAN.md` lists `EC1-R05` as a construction *decision*. It is not a decision.
`workshop/exhibits.lean` §2 exhibits the cyclic unfolding as commented-out source and
records Lean's refusal:

```
fail to show termination for EffectCoreV1.unfoldBad
  ... Could not find a decreasing measure.
```

`Prog` is inductive by ratified ruling — R1, [`EFFECTS-BACKEND.md:32`](../../library/cas/EFFECTS-BACKEND.md),
carried by [`Cas/Lang/Prog.lean:25`](../../library/cas/Cas/Lang/Prog.lean) — so a
cyclic graph has **no** structural denotation and any denotation must be
fuel-indexed. `EC1-R05` is therefore a consequence of law, which is a stronger
footing than the packet currently claims for it, and `EC1-K15`'s divergence
discipline inherits that footing.

### 1.3 Each approximant is an ordinary `Prog` (`EC1-R02`, `EC1-R04`)

The design choice under test is what the unfolding lands in. `workshop/exhibits.lean` §3
lands it in `Prog CasSig`, and the entire argument for that choice is four
`example`s that typecheck: `interpretRef`, `run`, `ObsEq`, and `replayHandler`
all consume a graph approximant with no restatement. R10's stratification
([`EFFECTS-BACKEND.md:150`](../../library/cas/EFFECTS-BACKEND.md)) survives the
new rung for free rather than being re-established for it.

`out_of_fuel_refuses` is `rfl`: the exhausted leaf is expressible in the
existing `Refusal` family — though §7 shows it must not *stay* there.

### 1.4 CAS is a protected sublanguage — two of four laws, proved (`EC1-T101`, `EC1-T102`)

`ALGEBRA.md` §12 lists four boundary laws, all PENDING, and `PROOF-DAG.md` §12
puts them at `EC1-S3` so later power cannot obscure a CAS regression. Two of
them are proved in `workshop/exhibits.lean` §4, on one design choice: **a block's body is
a `PProg`**, the L-A table reused whole rather than a new straight-line form
beside it.

- `project_inject` (`EC1-T101`) — `rfl`.
- `inject_embed` — the injection is **syntactic**, not merely observational:
  `denoteG (ofPProg p) (fuel+1) = embed p`, by `Prog.bind_pure_right`
  ([`Representation.lean:39`](../../library/cas/Cas/Lang/Representation.lean)).
  A monad law, not an induction.
- `runCore_runP` (`EC1-T102`) — follows immediately, at the exact fuel bound
  `Defun.lean` already proved: `runP_embed_agree`
  ([`Defun.lean:362`](../../library/cas/Cas/Lang/Defun.lean), fuel `p.length + 1`).
  No new fuel accounting.
- `inject_obsEq` — and the CAS observation mask needs no new definition, since
  `ObsEq.of_eq` ([`Representation.lean:137`](../../library/cas/Cas/Lang/Representation.lean))
  carries it.

The consequence beyond the two rows: because the injection is an equality of
`Prog`s, **every** theorem `Defun.lean` proves about `embed p` transfers to the
graph rung unrestated — the envelope, the frame condition, hash-determination,
the codec round trip. `Fragments.lean`'s owed `L-A ↪ L-S` row
([`Fragments.lean:143`](../../library/cas/Cas/Lang/Fragments.lean)) collapses to
one line under this choice, and to an induction under any other.

### 1.5 Coherence is derived, and only at the big-step face (`EC1-A30`, `EC1-T039`)

An earlier draft made coherence a field of a `Denotation` family. The repaired
packet instead keeps `Runs`/`Denotes` as relations, derives `FinApprox`, and
owes `approx_coherent` as a theorem. `workshop/exhibits.lean` §5 supplies the
deterministic CAS/block specialization over carriers the estate already has:

- `blockBody_mono` — one step is monotone in its recursive tail. The whole
  content of coherence, and the proof contains **no fuel reasoning at all**;
- `coherent`, `coherent_le` — the family is a chain;
- `denotes_unique` — **stable successful outcomes in this fragment form a
  partial function**. Two witnessing fuels agree, so adequacy is a corollary
  rather than a separate obligation, and R5's
  byte-decidable word gate ([`EFFECTS-BACKEND.md:83`](../../library/cas/EFFECTS-BACKEND.md))
  survives the admission of cycles.

The proof factors through `interpret_bind`
([`Handler.lean:53`](../../library/cas/Cas/Lang/Handler.lean)) — proved once, for
every handler into every lawful target. **That law holds at the big-step
judgment and provably does not hold at the fueled `run`.**
`run_has_no_composition_law` ([`Universal.lean:894`](../../library/cas/Cas/Backend/Universal.lean))
proves no binary operation whatsoever reproduces `bind` at fixed fuel, for any
monad structure on the codomain, and the obstruction is well-definedness rather
than the choice of `bind`.

So the coherence arrow of `ALGEBRA.md` §10's triangle must be drawn at the
big-step face. This is the sharpest constraint the exhibits found, and it is not
a preference: it is the estate's own boundary theorem applied to the packet's
diagram.

### 1.6 Scoped bodies need no `HHandler`; recovery needs an adequate target (`EC1-R06`, `EC1-K16`)

The literature shape for scoped effects is a higher-order signature functor
`(Type → Type) → (Type → Type)` and a handler that receives its children already
interpreted. `workshop/exhibits.lean` §6 shows the estate does not need it, and every
line of the section typechecks:

- `ScopeE` carries `catchE`/`ensuring`/`scoped`/`provide`/`raise` with children
  as `BlockId` — first-order data, the same defunctionalization `PIn.ans`
  already runs ([`Defun.lean:167`](../../library/cas/Cas/Lang/Defun.lean)). So
  `ScopeSig : Sig` is an ordinary `Sig`;
- `raise` answers `Empty`, so a raised program has no continuation **by type** —
  exactly the discipline `CasE.fail` already runs
  ([`Ops.lean:24`](../../library/cas/Cas/Lang/Ops.lean)). `EC1-R09`'s typed-error
  channel needs no carrier change;
- `scopeHandler : Handler ScopeSig (ReaderT Env (Prog CasSig))` is a **value of
  the existing type**;
- `scopedCasHandler := storeInScope.sum scopeHandler` — and this is
  `Handler.sum`'s **first call site**. `THE-ALGEBRA.md` §1.3 records it with zero
  uses and §3.2 makes the missing injection laws debt rank 2; the scoped layer
  is the consumer that answers ruling question Q5 in the keeping direction;
- `EC1-K16`'s monad-morphism law is free (`interpret_bind`), and the two-level
  collapse is the existing tower theorem `interpret_through`
  ([`Tower.lean:71`](../../library/cas/Cas/Lang/Tower.lean), R12).

The breaker settles the caveat. `no_scoped_catch_clause` and
`no_handler_into_ScopeM_catches` prove that no clause into
`ReaderT Env (Prog CasSig)` satisfies the exhibited recovery law. This does not
justify a new handler type: `scopeHandlerR` remains an ordinary `Handler` and
recovers once its target includes the state/error face needed to observe a
child outcome. The same strictness refutes the scratch `ensuring` clause on a
refusing body. See `EC1-CE041` and `EC1-CE045`.

### 1.7 Counterexample — out-of-fuel must not be a refusal (`EC1-A29`)

`ALGEBRA.md` §10.3 gives `FinApprox` a `live` leaf distinct from `halt`.
`workshop/exhibits.lean` §7 proves that distinction is **forced**, and that the obvious
economy — reusing `Refusal.failed` for "out of fuel" — breaks coherence in the
error direction:

```lean
theorem exhausted_is_not_a_refusal :
    run H 2 (denoteG onePutGraph 0) []
        = (.refused (.failed "graph: fuel exhausted"), [])
      ∧ (run H 2 (denoteG onePutGraph 1) []).1
        ≠ .refused (.failed "graph: fuel exhausted")
```

The witness is the smallest completing graph — one block, one operand-free put,
`ret` — and it needs no computed address, because `putWord_ne_failed`
([`Defun.lean:1694`](../../library/cas/Cas/Lang/Defun.lean)) proves a put's
refusal is never `.failed`, for **every** address function. So the statement
holds at every `H`.

The estate already has the right arm on the small-step side: `Status.running`,
whose docstring calls it *"the only status a fuelled run reports that says
nothing about the program"* ([`Interp.lean:55`](../../library/cas/Cas/Lang/Interp.lean)).
The big-step face is the one missing it, because `interpretRef` lands in
`Except Refusal (A × Word)` and that type has nowhere to hold "still live".

**Ask.** Either `EC1-A29`'s `live` leaf stays genuinely distinct from every
`halt` in the mask algebra, or the big-step face grows a distinguished exhausted
arm. Silence produces a coherence statement that is false in the error
direction, and `EC1-T039` as currently worded (`truncate h (approx n c) =
approx m c`, an unrestricted equality) is the row that would carry the defect.

---

## 2. The local anchor spine

What follows is the DAG re-drawn by **what already exists**. Layers are ordered
by dependency; each row names the existing declaration and its relation to the
packet's PENDING rows. A full row-by-row sweep of all ~120 `EC1-T*` ids is
dispatched (see §5); this is the spine.

```text
                    THE ANCHORED SPINE
        (existing declarations on the left, EC1 rows they
         discharge on the right; ═══ is INHERITS, ─── is
         SIMULATES, ✗ is CONTRADICTS)

  L0  LawfulMonad (Prog S)  ═══════════════════▶ T021 T022 T023 T024
      interpret_bind        ═══════════════════▶ T055
      prog_is_free                                   │
      existsUnique_handler  ═══════════════════▶ T050│
      eq_of_forall_interpret ══════════════════▶ T042 T043
             │                                        │
             │        ◆ RESOLVED A: finite unfoldings embed in Prog
             │           inherited laws apply on that specialization
             ▼           the full relational machine keeps bridge rows
  L1  Handler.sum_unique    ═══════════════════▶ T050
      interpret_inl/inr     ───────────────────▶ alphabet composition
      doubleInl_not_interpret_inl ─────────────▶ the F-battery style
             │                                   (and C6: the word gate
             ▼                                    cannot see this class)
  L2  Handler.through
      interpret_through     ═══════════════════▶ T057T, handler-clauses-
      through_monoid                                as-graphs (ALGEBRA §6)
             │
             ▼
  L3  step_handle           ───────────────────▶ T033
      run_interpretRef_agree ══════════════════▶ T036 + T037 (for CAS)
      run_preserves_wf      ═══════════════════▶ T031
      run_has_no_composition_law ─────── ✗ ────▶ ANY fixed-fuel bind law
             │                                   ⇒ the coherence arrow of
             │                                     ALGEBRA §10 must be
             ▼                                     drawn at interpretRef
  L4  runP_embed_agree      ═══════════════════▶ T102   ← exhibits §4
      (exact fuel p.length+1)                          runCore_runP
      decodeProg_encodeProg ═══════════════════▶ T104
      PProg.envelope + the sandwich ───────────▶ T105, CLASSIFICATION D1–D4
      runPFrom_puts_sound (Sublist, NOT prefix) ── ✗ ──▶ any "exact" mark
      putWord_ne_failed     ═══════════════════▶ exhibits §7 counterexample
             │
             │        ◆ RESOLVED B: block body = PProg
             │           T101/T102 proved, T104 trivial, L4 transfers
             ▼           a second straight-line carrier is refused by R15
  L5  wp / wlp             ═══════════════════▶ the modality (= wlp)
      wp_iff_wlp_and_total ═══════════════════▶ total vs partial split
      wpB_iff_wp           ───────────────────▶ the shape EVERY classifier
                                                 dimension should copy
      wp_append (pre ≠ [])  ──── side cond ────▶ EffHOL (Mod-E), partial?
             │
             ▼
  L6  whole_run_security                        ORPHANED — no EC1-T row
      whole_run_correctness ───────────────────▶ SHOULD anchor K20 /
      interpret_agree_or_collision                 ALGEBRA §11 receipts
             │
             ▼
  L7  table_eq_treeProg, embed_treeProg ───────▶ T100 upstream
      since_compose        ───────────────────▶ mask composition (A31)
      stepRooted_cas_agrees ──────────────────▶ alphabet: roots, words

             ◆ RESOLVED C: relation quantifies over choices/schedules;
               a fixed typed tape selects deterministic replay
               existing summed signatures/handlers remain reusable
               Q4 stays a separate replayHandler contract obligation
```

### L0 — the carrier is already free, initial, and lawful

| Existing | Site | Bears on |
|---|---|---|
| `LawfulMonad (Prog S)` | [`Representation.lean:54`](../../library/cas/Cas/Lang/Representation.lean) | `EC1-T021`, `EC1-T022`, `EC1-T023` |
| `Prog.bind_pure_right`, `Prog.bind_assoc'` | `Representation.lean:39,46` | same |
| `interpret_bind` | [`Handler.lean:53`](../../library/cas/Cas/Lang/Handler.lean) | `EC1-T055`, and §1.5's coherence |
| `interpret_id`, `eq_of_forall_interpret` | `Representation.lean:68,80` | `EC1-T042`, `EC1-T043` |
| `prog_is_free`, `existsUnique_handler` | [`Universal.lean:502,519`](../../library/cas/Cas/Backend/Universal.lean) | `EC1-T050` |
| `prog_is_initial_in_S_models` | `Universal.lean:566` | `EC1-T043` |
| `Handler.ext`, `handler_eq_of_interpret_eq` | `Universal.lean:128,345` | `EC1-T050`, `EC1-T051` |

**Resolved use of this layer (§3.1).** Finite block unfoldings embedded into
`Prog` inherit the relevant laws. The full transition relation keeps its own
agreement obligations, and `run_has_no_composition_law` remains the boundary
against inventing a fixed-fuel bind law.

### L1 — signature sums, with their adversaries already built

| Existing | Site | Bears on |
|---|---|---|
| `Handler.sum_handle_inl/inr`, `Handler.sum_unique` | [`SumAlgebra.lean:196,202,212`](../../library/cas/Cas/Backend/SumAlgebra.lean) | `EC1-T050` |
| `interpret_inl`, `interpret_inr` | `SumAlgebra.lean:231,239` | alphabet composition |
| `Prog.inl_bind`, `Prog.inl_injective` | `SumAlgebra.lean:256,284` | `EC1-T027` |
| `swapSum_not_sum_handle_inl` | `SumAlgebra.lean:685` | falsifier model |
| `badAgentSum_not_interpret_inr` | `SumAlgebra.lean:753` | falsifier model |
| `doubleInl_not_interpret_inl` | `SumAlgebra.lean:790` | falsifier model |
| `narrowing_to_Id_fails` | `SumAlgebra.lean:966` | quantifier-narrowing falsifier |

These four adversaries are the house pattern for the packet's `EC1-F*`
batteries, and they are already kernel-checked. A breaker writing new batteries
should read them before inventing a style.

### L2 — the tower is the mechanism `ALGEBRA.md` §6 asks for

| Existing | Site | Bears on |
|---|---|---|
| `Handler.through`, `interpret_through` | [`Tower.lean:65,71`](../../library/cas/Cas/Lang/Tower.lean) | `EC1-T057T`, handler-clauses-as-graphs |
| `through_assoc`, `through_id_left/right`, `through_monoid` | [`Universal.lean:739,757,765,785`](../../library/cas/Cas/Backend/Universal.lean) | handler-tower composition |

`ALGEBRA.md` §6 wants "handlers whose clauses are themselves checked core
graphs". That is `Handler S (Prog T)` composed by `Handler.through`, and R12
already rules it ([`EFFECTS-BACKEND.md:204`](../../library/cas/EFFECTS-BACKEND.md)).
`workshop/exhibits.lean` §6 is the instance.

### L3 — the two faces and the bridge between them

| Existing | Site | Bears on |
|---|---|---|
| `step_handle` — `step` IS the handler clause | [`Handler.lean:131`](../../library/cas/Cas/Lang/Handler.lean) | `EC1-T033` |
| `interpretRef_vis` | `Handler.lean:149` | `EC1-T033`, `EC1-T036` |
| `interpretRef_of_run_done` / `_refused` | `Handler.lean:165,189` | `EC1-T036` |
| `run_of_interpretRef` | `Handler.lean:214` | `EC1-T037` |
| `run_interpretRef_agree` | `Handler.lean:255` | **`EC1-T036` + `EC1-T037` together** |
| `step_preserves_wf`, `run_preserves_wf` | [`Interp.lean:119,163`](../../library/cas/Cas/Lang/Interp.lean) | `EC1-T031` |
| `run_has_no_composition_law` | [`Universal.lean:894`](../../library/cas/Cas/Backend/Universal.lean) | **CONTRADICTS any fixed-fuel bind law** |

`run_interpretRef_agree` is the packet's executable/relational agreement pair
already discharged for the CAS sublanguage, and its docstring states the two
shape facts `EC1-T036`/`T037` will hit. Both are reproduced as challenges in §4.

### L4 — the defunctionalized plane, where the analysis lives

| Existing | Site | Bears on |
|---|---|---|
| `runP_embed_agree` (exact fuel `p.length + 1`) | [`Defun.lean:362`](../../library/cas/Cas/Lang/Defun.lean) | `EC1-T102` |
| `runP_halts`, `runP_preserves_wf` | `Defun.lean:403,368` | `EC1-T032` |
| `ObsEq_embed_of_runP` | `Defun.lean:419` | `EC1-T106` |
| `decodeLine_encodeLine`, `readLine_exact`, `decodeLine_exact` | `Defun.lean:635,764,826` | `EC1-T116`, `EC1-T117` |
| `encodeProg_wf`, `decodeProg_encodeProg` | `Defun.lean:871,998` | `EC1-T104` |
| `runP_decodeProg_encodeProg`, `ObsEq_decodeProg_encodeProg` | `Defun.lean:1051,1062` | `EC1-T104` |
| `PProg.envelope`, `dataflowClosed_eq` | `Defun.lean:1205,1225` | `EC1-T105`, `CLASSIFICATION.md` D1–D4 |
| `runPFrom_puts_sound`, `runP_puts_sound` | `Defun.lean:1618,1672` | classifier soundness (**`Sublist`, not prefix**) |
| `PProg.resolve_sound`, `runP_absent_sound` | `Defun.lean:1332,1839` | frame condition |
| `PLine.HashDetermined`, `PLine.hashDetermined` | `Defun.lean:1480,1496` | `CLASSIFICATION.md` D4 |
| `putWord_answer`, `putWord_ne_failed` | `Defun.lean:1401,1694` | §1.7's counterexample |

### L5 — the logic

| Existing | Site | Bears on |
|---|---|---|
| `wp`, `wlp` | [`Wp.lean:150,154`](../../library/cas/Cas/Lang/Wp.lean) | the modality |
| `wp_mono`, `wlp_mono` | `Wp.lean:308,316` | EffHOL (Mon) |
| `wp_append`, `wp_append_le_total` | `Wp.lean:528,538` | EffHOL (Mod-E), **with a side condition** |
| `wp_bot`, `wlp_top`, `wp_iff_wlp_and_total` | `Wp.lean:364,373,380` | §1.1 |
| `Triple`, `PartialTriple`, `Triple_iff_wp`, `PartialTriple_iff_wlp` | `Wp.lean:552,557,566,573` | the Hoare form |
| `wp_iff_interpretRef`, `Triple_iff_interpretRef` | `Wp.lean:629,652` | the logic anchored at the big-step face |
| `wpB`, `wpB_iff_wp` | `Wp.lean:669,726` | **the executable transformer** — a decidable verdict, already proved to characterise `wp` |
| six falsifiers, incl. `falsifier_wlp_ne_wp`, `falsifier_partial_is_not_total`, `falsifier_fuel_bound_is_tight` | `Wp.lean:773–858` | the battery model |

`wpB_iff_wp` deserves particular notice: the estate already has a **computed**
transformer proved equal to the logical one. That is the shape every classifier
dimension in `CLASSIFICATION.md` should copy — a decidable fold plus a theorem
tying it to the semantic object — rather than the abstract-interpretation
framing invented fresh.

### L6 — authenticated computation, and the packet's largest missed reuse

| Existing | Site |
|---|---|
| `proveHandler`, `verifyHandler` | [`Auth.lean:117,173`](../../library/cas/Cas/Lang/Auth.lean) |
| `verify_load_or_collision` | `Auth.lean:245` |
| `interpret_agree_or_collision` | `Auth.lean:608` |
| `whole_run_security`, `whole_run_correctness`, `interpret_prove_verify` | `Auth.lean:678,757,702` |

**No `EC1-T*` row routes through any of these.** Yet `ALGEBRA.md` §11's foreign
atoms with *receipts*, and `EC1-K20`'s foreign-atom laws, are structurally the
same object: an untrusted party supplies a claimed answer plus a claimed stream
for content held only by digest, and the theorem is *agree, or exhibit a
collision*. `Auth.lean` has that theorem, in the corrected shape the mechanized
literature forced (`.staging/operational-structure/DESIGN.md` §1.1 records why
the published form would import a known-false statement).

Two further consequences worth recording: `DESIGN.md` §1.2 still lists mode V as
**absent** and §1.5 lists the security theorem as missing. Both are stale —
`Auth.lean` landed them. That is a third drift item beyond the two the
originating brief named, and `STATE-OF-MECHANIZATION.md` already grades them
L3 (proved, unwired).

### L7 — grammar, trees, roots, words

| Existing | Site | Bears on |
|---|---|---|
| `table_eq_treeProg`, `embed_treeProg` | [`TreeProgCorrect.lean:456,679`](../../library/cas/Cas/Backend/TreeProgCorrect.lean) | `EC1-T100` |
| `treeProg_run`, `treeProg_Triple`, `treeProg_two_state` | `TreeProgCorrect.lean:706,751,764` | `EC1-T102` upstream |
| `stepRooted_cas_agrees`, `publish_mem` | [`Roots.lean:85,111`](../../library/cas/Cas/Lang/Roots.lean) | alphabet package: roots |
| `since_suffix`, `since_zero`, `since_cas_agrees`, `since_next`, `since_compose` | [`Worded.lean:110,119,134,163,176`](../../library/cas/Cas/Lang/Worded.lean) | alphabet package: words; observation composition |

`RootSig` and `WordSig` are two signature packages **already landed and proved**
that the closed alphabet must absorb rather than re-derive. `since_compose` is
the model for mask composition in `EC1-A31`.

---

## 3. Evidence behind the resolved representation choices

Each question changes the DAG's shape. The alternatives remain recorded so a
future session can see the cost of the rejected branch.

### 3.1 Approximants — reuse `Prog`; keep the full relational machine explicit

| | embedding into `Prog` | own evaluator |
|---|---|---|
| `EC1-T021`–`T024`, `T055` | INHERITED (monad laws + `interpret_bind`) | owed from scratch |
| `EC1-T033`–`T037` | the approximants reuse `run_interpretRef_agree`'s pattern | new bridge per constructor |
| bind law at fixed fuel | not needed | **provably absent** (`run_has_no_composition_law`) |
| cost | every `Flow` constructor needs a `Prog`-valued unfolding | none |

**Resolution:** finite block unfoldings reuse `Prog`, supported by
`workshop/exhibits.lean` §3 (four examples typecheck), §4 (`inject_embed` is a
monad law), and §5 (`blockBody_mono` needs only `interpret_bind`). This does not
replace the full transition relation or its typed decision interface.

### 3.2 Block body — existing `PProg`

| | body is `PProg` | new form |
|---|---|---|
| `EC1-T101`, `EC1-T102` | PROVED (`workshop/exhibits.lean` §4) | owed |
| `EC1-T104` (the canon stop theorem) | trivial — there is no second encoding | a second canonical CAS spelling, which `EC1-R15` forbids |
| L-A theorem set (envelope, frame, codec, hash-determination) | transfers unrestated | re-derived per theorem |
| `Fragments.lean`'s owed `L-A ↪ L-S` | one line | an induction |

**Resolution: `PProg`.** `EC1-R15` already says the seam must not mint a
second canonical identity; making the body *be* the existing carrier is the only
shape in which that is true by construction rather than by a theorem.

### 3.3 Nondeterminism — relational meaning plus deterministic replay inputs

`PLAN.md`'s `EC1-R11` and `ALGEBRA.md` make typed decisions, external answers,
and schedules explicit. The relational semantics quantifies over all admitted
choices; `execN n tape c` supplies one fixed stream and therefore selects one
replay path. Where a source is naturally an algebraic operation, its executable
implementation may still use the existing `Sig`/`Handler`/`Handler.sum` route.
That implementation fact does not turn the full denotation into a function or
make every schedule item stored program content.

R5's byte-decidable equality remains the gate for fixed generated artifacts and
the deterministic CAS/block specialization. Full-core semantic comparison uses
the declared relational/refinement judgments. The existing `replayHandler`
question remains an independent reuse obligation; no proof row assumes its
unstated contract.

---

## 4. Challenges — the hard parts, each with its local evidence

**C1 — the fuel is existential, not a size.** `run_of_interpretRef`'s docstring
([`Handler.lean:214`](../../library/cas/Cas/Lang/Handler.lean)) states it: `Prog`'s
continuations are host functions, so `Prog.vis` branches over an answer type
that is `Addr32`, not a finite index, and there is no structural measure to
quantify over. Only the defunctionalized fragment has an exact bound
(`runP_embed_agree`, `p.length + 1`). At the graph rung the number of block
transitions is not bounded by the graph, so the exact-fuel style does **not**
extend. `PROOF-DAG.md` should say, per row, which bounds are exact and which are
existential; today it does not distinguish them.

**C2 — the refusal word is not relatable, and it is a type fact.** `run` reports
`(.refused r, w)` — the partial word — while `interpretRef` lands in
`Except Refusal (A × Word)`, whose error branch has no word slot at all
([`Handler.lean:105`](../../library/cas/Cas/Lang/Handler.lean) records the triage).
`ObsEq.run_refused` ([`Representation.lean:198`](../../library/cas/Cas/Lang/Representation.lean))
propagates the asymmetry, and `Fragments.lean`'s interop contract tells consumers
outright not to gate on a partial word. **Constraint on `EC1-A31 ObservationMask`:
it cannot include the partial word on the refusing branch without changing the
reference target monad.** `EC1-K05` should record this.

**C3 — the executable face has no bind law.** `run_has_no_composition_law`
([`Universal.lean:894`](../../library/cas/Cas/Backend/Universal.lean)) kills every
candidate composition law at fixed fuel simultaneously, for any monad structure,
because the obstruction is well-definedness. Every compositional statement in the
triangle must therefore be made at the big-step face or at the colimit.
`workshop/exhibits.lean` §5's `blockBody_mono` is the shape that works.

**C4 — live and refused must not share a leaf.** §1.7, proved.

**C5 — the L-A envelope over-approximates in exactly two places, permanently.**
`Fragments.lean` names them: the suffix after the first refusal, and `put`'s
duplicate outcome — which makes the word projection a `Sublist` and never a
prefix (`runPFrom_puts_sound`). It also records that
`.staging/operational-structure/DESIGN.md` §3.1's "exact: over = under = actual"
is **refuted**, with the witnesses at the end of `Defun.lean`. Consequence for
`CLASSIFICATION.md`: no dimension whose transfer function is "the puts, in
order" can be marked exact at the straight-line rung, and any that is marked
exact today is wrong before the graph rung is even reached.

**C6 — the sum laws' falsifier is invisible to the word gate by construction.**
`THE-ALGEBRA.md` §3.2: an `inl` that performs every operation twice is
`ObsEq`-equal to the real one for every `CasSig` program. The statement is the
whole of the protection; `doubleInl_not_interpret_inl`
([`SumAlgebra.lean:790`](../../library/cas/Cas/Backend/SumAlgebra.lean)) is the
theorem that catches it. **A byte gate will not catch an alphabet-injection
violation**, so `EC1-T050`'s family must be stated, not gated.

**C7 — `Handler.sum` had zero call sites until now.** `THE-ALGEBRA.md` §1.3.
`workshop/exhibits.lean` §6 is its first consumer. Ruling question Q5 ("law it or lose
it") is answered in the keeping direction by this packet; that answer is a
ruling ask, not a fait accompli.

**C8 — universes.** `Prog` is `Type u`-polymorphic
([`Prog.lean:25`](../../library/cas/Cas/Lang/Prog.lean)); `Handler` targets
`Type → Type v` ([`Handler.lean:42`](../../library/cas/Cas/Lang/Handler.lean)).
Every law in the estate is at answer-universe 0, and `Prog CasSig Type` is
well-typed syntax that `interpret` cannot consume (`THE-ALGEBRA.md` §3.20,
ruling question Q9). `EC1-D001`/`EC1-D002` are consistent with the narrowing;
`PROOF-DAG.md` §17 should list it, since it is a breaking signature edit if
taken.

**C9 — `PureAtom`'s conformance obligation inherits an unconfronted pattern.**
`ALGEBRA.md` §3 requires each `PureAtom` to carry a total Lean meaning, a
separate TypeScript implementation, and a conformance obligation between them.
The estate's nearest existing instance is `Cas/Schema/Foreign.lean`'s
`RepresentedIn` type-expression strings, and R8's own ingestion note records
that they are *"rfl-proved against hand-written strings and confronted by
nothing on the TypeScript side"*
([`EFFECTS-BACKEND.md:241`](../../library/cas/EFFECTS-BACKEND.md)). So
`PureAtom` clause 5 is not merely PENDING; it is PENDING against a pattern the
ratified law already flags as unconfronted. The fix is to name the confronting
instrument in the row rather than to discover the gap at `EC1-S11`.

**C10 — the three drift items.** `.staging/operational-structure/DESIGN.md` §1.2
and §1.5 say the λ• verifier mode and its security theorem are absent;
`Auth.lean` has both. `STATE-OF-MECHANIZATION.md:47` says there is no Effect
host runner; `library/effects/src/cas/Programs.ts` has one.
`DESIGN.md` §3.1 calls the linear analysis exact; `Fragments.lean` refutes it.
A packet that cites these documents as authority inherits all three.

---

## 5. Completed incoming lanes

Four incoming lanes reported against this contribution. Their reports are
evidence inputs; packet ownership and counterexample IDs are assigned during
reconciliation.

| Lane | Question | Report |
|---|---|---|
| Local anchors | every `EC1-T*` row classified INHERITS / SPECIALIZES / SIMULATES / **CONTRADICTED** / NO ANCHOR, plus the existing theorems no row routes through | `2026-08-31-effect-core-local-anchors.md` |
| Breaker | adversarial batteries against the exhibit findings, in compiling Lean | `effect-core-v1/breaker-exhibits.lean`, summarized by the coordination report and central register |
| Classification anchors | `CLASSIFICATION.md` D0–D14 against what `PProg.envelope` and the sandwich already compute, with the exactness verdict per dimension | `2026-08-31-effect-core-classification-anchors.md` |
| Provenance | `EC1-PV01`/`EC1-PV02` lock rows, the originating brief's unpinned citations, and the maintenance checklist | `2026-08-31-effect-core-provenance.md` |

The predicted handler hit was confirmed and sharpened: no handler clause into
`ReaderT Env (Prog CasSig)` can satisfy the exhibited catch law. The obstruction
is the target, not the existing `Handler` type. The breaker also narrowed
projection, frontier, coherence, and `wlp`-composition claims. Exact statements
are `EC1-CE040`–`EC1-CE048` in the central register.

---

## 5b. Lane results, verified

All four lanes have reported. The classification anchors, local anchors,
breaker, and packet workshops were rerun before reconciliation; provenance rows
remain explicitly pending where the estate has no admitted lock/gate.

### Classification anchors — six divergences, proved

Report: [`2026-08-31-effect-core-classification-anchors.md`](../agent-reports/2026-08-31-effect-core-classification-anchors.md),
with a companion `.lean` whose 11 theorems compile (`propext` or no axioms;
re-run independently for this document).

Four of `CLASSIFICATION.md`'s fifteen dimensions are **already landed under
other names**: D1 is `PProg.puts` + `PProg.reads`; D2 is `runP_frame_sound` with
the whole FRAME-1 chain; D4 is `PProg.dataflow` + `PLine.hashDetermined`; D5 is
`runP_halts` with `wp`/`wlp` as its bounds. Three have **no anchor at all** —
D7 scope topology, D8 resource protocol, D11 cancellation — which is the honest
measure of how much of the packet is genuinely new. D5 is the only dimension
that is **exact**, and it is exact because `PProg` is a list.

The six proved divergences sharpen §4's C5 considerably, because they are
failures of the *composition rules*, not of precision:

- **DIV-1** — D4's `seq` is neither union nor append.
  `dataflow (p ++ q) = [(1,0)]` while `dataflow p ++ dataflow q = [(0,0)]`: the
  naive rule names an edge the composite lacks and misses the one it has. The
  corollary is worse — closure is not `seq`-homomorphic, so a joining transfer
  would refuse a program `runP_no_dangling` proves safe.
- **DIV-2** — D2's "sequential composition unions frames" is unsound *as a
  commutative operation*: permutation-equal put lists leave different words.
  This is exactly why `runPFrom_puts_sound` concludes `List.Sublist` and not `⊆`.
- **DIV-3** — §5's single must-footprint column cannot carry D1 and D2 at once.
  A run that reports `done` with every line executed performs **2 put
  operations** and writes **1 binding**, because of `put`'s duplicate outcome.
- **DIV-4** — an empty read set with closed dataflow still refuses (`collision`).
  The envelope's two decidable outputs do not bound the error row at all, which
  matters directly for D0's `E` component.
- **DIV-5** — write *addresses* are not in the envelope: `PutShape` carries no
  address and `PProg.envelope` takes no `H`. §5's `CAS injection` row is true
  only in the shape register.
- **DIV-6** — two tables, same refusal, different partial words. Independent
  confirmation of C2 from the classifier side.

**D13 — the operator's dimension — has a clean answer.** `PLine.HashDetermined`
([`Defun.lean:1480`](../../library/cas/Cas/Lang/Defun.lean)) quantifies over runs
and therefore can never be decidable; it is the *spec*, not the grade. The model
to copy is the pair the estate already runs: `Envelope.dataflowClosed : Envelope
→ Bool` ([`Defun.lean:1221`](../../library/cas/Cas/Lang/Defun.lean)) plus
`runP_no_dangling` — a Bool on stratum-1 data, and a theorem that `= true`
implies a property of every run. `Sig`
([`Sig.lean:12`](../../library/cas/Cas/Lang/Sig.lean)) intentionally owns only
operations and answer families. The packet therefore keeps finite grade data in
the authored alphabet metadata indexed by `Sig.Op`, with a separate discharge
theorem; it does not alter `Sig` merely to attach classifier data.

The lane also read `ALGEBRA.md` §3 against the corpus and found the estate
already has `PureExpr` at degenerate size: `PIn = lit | ans` with `PIn.resolve`
as its total denotation, and `ArgMap` as `PLine.operands` plus the payload field.
Two review concerns were raised there. `PureAtom` clause 4 — "an explicit
statement that it reads and writes no effect world" — would create tension with
§3's "no trust-me pure escape" rule if treated as self-authenticating evidence.
The packet resolves this as an independently checked carrier/property fact,
not an unverified declaration; no counterexample claim is made here. Holing off already has its mechanism in
`Prog.handleLlm` / `Handler.sum`; only the decidable label is missing.

### Local anchors — four rows contradicted, three vacuous, five orphan clusters

Report: [`2026-08-31-effect-core-local-anchors.md`](../agent-reports/2026-08-31-effect-core-local-anchors.md),
596 lines, 125 distinct `path:line` citations.

Coverage, recorded against a stated revision because the DAG moved twice during
the session: §1–§7 classify `PROOF-DAG.md` at **27,395 B / 97 rows**, §8 at
**36,326 B / 110 rows**, identical before and after that pass. Thirteen rows are
genuinely new; seven of the twenty I flagged were already covered as ranges and
are re-spelled individually.

**Final counts over all 110 rows: INHERITS 36 · SPECIALIZES 22 · SIMULATES 18 ·
CONTRADICTED 4 · NO ANCHOR 30.** Sixteen of the no-anchor rows are the two
concurrency bundles —
the corpus has zero occurrences of *finalizer*, *fairness* or *supervisor*, and
every *fiber*/*race* hit is `trace` or `brace`. That is the honest measure of
how much of the packet is new construction.

Two of the new rows are this document's §1.1 arriving in the DAG independently.
`EC1-T124` is `wp_iff_wlp_and_total` character-for-character. `EC1-T123` is
*not* verbatim — it needs one lemma the corpus lacks, and finding that gap is
the lane's most useful by-product: `Wp.lean` anchors `wp` at the big-step
judgment (`wp_iff_interpretRef`, `:629`) and anchors `wlp` only at the run
(`wlp_iff_forall`, `:287`). The pair is asymmetric. §9 of
`workshop/exhibits.lean` supplies the missing half — `wlp_iff_interpretRef` and
`PartialTriple_iff_interpretRef`, both `[propext]` — and they are candidates for
the library on their own merits, independent of this packet.

The first-pass anchor classification called four rows discharged. The breaker
supersedes that classification. Its `denotes_unique` is executable function
determinism, so it cannot discharge the now-relational `EC1-T045`; the
ask-free witness supports only the narrower `EC1-T045A` premises. The scoped
handler construction into `ReaderT Env (Prog CasSig)` is well typed but cannot
recover, so it does not discharge direct scoped-target adequacy. `Handler.sum`
supports `EC1-T057`; `Handler.through` supports only the separate, correctly
typed `EC1-T057T` tower. `EC1-T046` retains only its CAS specialization anchor.

One first-pass revision folded in, and it sharpens §1.5 rather than confirming
it: **`EC1-T039` moves NO ANCHOR → SIMULATES, not INHERITS.** What §5 proves is a
coherence *chain* as a `Refines` relation; what `EC1-A30` declares is a
`truncate` *equality* — and §7 proves that equality false unless the `live` leaf
stays distinct from every `halt`. The two statements are not the same theorem,
and the difference is exactly the leaf question.

**The four CONTRADICTED rows.** `EC1-T088` was re-verified here from scratch
(`classifier_finer_than_semantics`, `[propext, Quot.sound]`); the other three are
taken on the report's exhibited proofs.

- **`EC1-T015 diagnostic_local`** — the estate's checker reports one clause, not
  a set. `checkRefs` ([`Admission.lean:49`](../../library/cas/Cas/Core/Admission.lean))
  returns `Except AdmissionError Unit` and stops at the first failure, and
  `checkRefs_complete:137` says so in its own docstring: *"with the first failing
  clause found, not necessarily the condemning one"*. The witness is a store
  where a dangling ref and a wrong-kind ref both condemn and only the first
  surfaces. The cost is precise: `EC1-D024`'s `Except (NonEmpty Diagnostic)`
  signature quietly commits D3 to an **accumulating** checker with a per-clause
  locality proof — a strictly harder object than anything in the corpus, and one
  that cannot reuse `Cas/Core/Admission.lean`.
- **`EC1-T088 classifier_semEq`** — *the classifier is strictly finer than the
  ratified semantic equality, and that is not a defect.* `[load a]` and
  `[load a, load (ans 0)]` have identical `runP` at every word — the second load
  resolves to the address the first already found — and different
  `PProg.dataflow`. So `classify` is a function of the **syntax**, not of the
  denotation, which is exactly what R4 requires (identity hashes presentations)
  and exactly what `EC1-T088` denies. The row must be restated as
  `classify p = classify q → SemEq p q`, or dropped.
- **`EC1-T100 injectCas_checked` / `EC1-D080`** — `injectCas : PProg →
  CheckedProgram` **cannot be total**. The empty table and a dangling `ans` index
  are both representable in `PProg` and both refuse by name
  (`"defun: empty program"`, `"defun: dangling answer index"`,
  [`Defun.lean:215`](../../library/cas/Cas/Lang/Defun.lean)). This sharpens §1.4:
  the graph constructor `ofPProg` is total, but the *checked* injection is not,
  and the fix is already in-repo — `Mcp.lean:436/446/458` runs exactly this
  pattern, where `ofPProg_isSome` carries the encodability side condition rather
  than pretending totality.
- **`EC1-T002 normalizeRow_canonical`** — the forward direction is refuted by the
  estate's own live witness `canonServices_perm_premise_is_necessary`
  ([`Canon.lean:376`](../../library/cas/Cas/Backend/Canon.lean)). It needs a
  duplicate-free premise, which is the same `Nodup` hazard
  `CORE-ABSTRACTIONS-PLAN.md` HARD PART 5 already records for CANON-1.

**Three rows are true but vacuous** — `EC1-T003`, `EC1-T035`, `EC1-T115`. Any
Lean function satisfies them, so they cost a line in the DAG and buy nothing. The
report also notes that four `EC1-T*` **names promise more than their statements
deliver**, which is the defect the estate has twice fixed by renaming a theorem
(`run_composite_outruns_its_parts` is the standing example).

**Five orphan clusters** — proved results no row routes through. §2's L6 predicted
the first; the fourth is new here and matters more than it looks:

1. `Auth.lean:678/757` — W-SEC/W-COR, the λ• prover–verifier pair at hash-lattice
   Level 0 with the mechanized correction. No row mentions authenticated
   computation at all.
2. `Universal.lean:502/566/598/785/894` — freeness, initiality in `S`-models, the
   adequacy pin, the tower monoid, and the non-composition boundary.
3. The whole `Wp.lean` transformer layer — now partly absorbed as `T123`/`T124`.
4. **The CAS-003 hash-hypothesis lattice** ([`Address.lean:56/69`](../../library/cas/Cas/Core/Address.lean),
   `Canonicalize.lean:200-219`). Every CAS row and every render row depends on
   `H`, and **not one names its level**. Every theorem in
   `workshop/exhibits.lean` is at Level 0 — no premise on `H` at all, including
   §7's counterexample, which is why it holds at every address function. A DAG
   that does not carry the level cannot tell a Level-0 result from one that
   silently assumes injectivity.
5. `SumAlgebra.lean` language composition with its five kept adversaries, plus
   `Roots.lean:85` and `Worded.lean:134` proving that signature extensions leave
   the core undisturbed.

### Provenance — a twelfth cluster, and two citation defects

Report: [`2026-08-31-effect-core-provenance.md`](../agent-reports/2026-08-31-effect-core-provenance.md).

`EC1-PV01`'s digest is `a493e698895878136a71e9ffdaaf9ece786cdd30864f853149cd69cec774ad0c`,
777,345 bytes — recomputed here. Two structural findings:

- **None of the eleven clusters fits.** `semantics-carriers` admits ITrees-lineage
  *carriers*; EffHOL is a logic. `type-effect-lineage`'s "Does not support" line
  is written for its two members. `build_ledger.py` hard-errors on a paper with
  no cluster, so a twelfth cluster is required, not optional. The proposed
  **Does not support** line must exclude any total-correctness reading — which is
  §1.1 of this document arriving at the same place from the Lean side.
- **The root PDF can never acquire a row** where it sits: the generator globs
  `.reference/papers/` only. It stays gitignored either way, so the commit
  carries the lock row and the catalog row, never the bytes.

Of the ten sources the originating brief cited, **three are pinned** (HITrees,
Interaction Trees ×2 rows, Choice Trees) and **seven are absent**, each now with
a deterministic identifier. Two citation defects, one of them mine: the brief's
scoped-effects row **fuses two different papers with different author lists** —
*Effect Handlers in Scope* (doi:10.1145/2633357.2633358) and the LICS 2018
scoped-operations paper (doi:10.1145/3209108.3209166), whose authors are not the
same people. `workshop/exhibits.lean` §6 carried the fused attribution and has
been corrected to name neither. CompCert exists in the tree as three unpinned
artifacts. `Fragments.lean`'s "CORPUS PIN PENDING" note on SAF is still true.

`EC1-PV02` is the one place the packet's numbers hold exactly: `typescript@7.0.2`
and `@effect/tsgo@0.38.0` agree across `TOOLS.md`, `package.json`, `bun.lock`,
and installed `node_modules`, and the patch is provable by digest. The defects
were precision ones in the incoming draft: it named
`Effect-TS/language-service`, while `@effect/tsgo@0.38.0` publishes from
`Effect-TS/tsgo` and no standalone `@effect/language-service` package is
installed. `PLAN.md` now names `Effect-TS/tsgo` as the pending source pin and
keeps `@effect/language-service` only as the configured plugin identity.

**The finding that outranks all of the above**: `.reference/manifest.json` has no
row for `papers.lock.json`, `PAPERS.md`, `README-papers.md`, `fips202.lock.json`
or `receipts/`, so `MANIFEST.md`'s "update manifest.json in the same change"
contract is currently undischargeable for the entire paper corpus. And `mise.toml`
contains **zero** occurrences of `.reference` — verified by grep for this
document — so no gate in `check` or `check:ci` touches any of it. Every pin this
packet adds is ungated by construction until that changes.

---

## 6. Resolution record and remaining asks

1. **Approximants** — finite block unfoldings reuse `Prog`; the general machine
   still has an explicit relational semantics.
2. **Block body** — a block body **is** a `PProg`, making `EC1-R15` true by
   construction and `EC1-T101`/`EC1-T102` proved rather than pending.
3. **Nondeterminism** — full meaning is relational over typed decisions,
   external answers, and schedules; a fixed input stream yields deterministic
   replay. Existing summed signatures/handlers are reused where they express a
   source, without assuming that every schedule is stored program content.
4. **`EC1-A29`** — live and halt keep distinct leaves, or the big-step face
   grows a distinguished exhausted arm. §1.7 is the falsifier either way.
5. **`EC1-K05`** — record that the observation mask cannot carry the partial
   word on the refusing branch (C2).
6. **`EC1-T050` family** — stated, not gated; the word gate is blind to its
   falsifier by construction (C6).
7. **`Auth.lean`'s security pair** — routed into the foreign-atom bundle
   (`EC1-K20`) rather than re-derived (L6).
8. **The three drift items (C10)** — corrected in their owning documents before
   this packet cites them as authority.

From the lanes (§5b), each carrying a compiling witness or a recomputed digest:

9. **`CLASSIFICATION.md` §2's composition rules** — three are refuted as stated.
   D4's `seq` is neither union nor append (DIV-1); D2's frame `seq` is not
   commutative (DIV-2); and the single must-footprint column cannot carry D1 and
   D2 at once, so it splits into an operation column and a world column (DIV-3).
10. **D13 becomes decidable through finite alphabet metadata plus a discharge
    theorem**, modelled on `Envelope.dataflowClosed` + `runP_no_dangling`.
    Existing `Sig` is not changed merely to carry the grade; the metadata is
    indexed by the existing `Sig.Op` family.
11. **`ALGEBRA.md` §3's `PureAtom` clause 4** is recorded as an independently
    discharged carrier/property fact, not a self-authenticating declaration.
    This resolves a review concern; it is not registered as a contradiction.
12. **A provenance cluster/lock for `EC1-PV01` remains owed.** The current root
    PDF cannot acquire a row because the generator globs `.reference/papers/`.
    This packet records the gap but does not move or admit the source.
13. **`EC1-T088` is restated or dropped.** The classifier is finer than the
    semantics by construction under R4; the row asserts the converse.
14. **`EC1-T100` loses its totality claim** and adopts the in-repo
    `ofPProg_isSome` pattern — an encodability side condition, not a total
    injection.
15. **`EC1-D024`'s diagnostic signature is ruled.** `Except (NonEmpty Diagnostic)`
    commits D3 to an accumulating checker that cannot reuse
    `Cas/Core/Admission.lean`; either restate `EC1-T015` existentially to match
    `checkRefs_complete`, or state that D3's checker is new construction.
16. **`wlp_iff_interpretRef` and `PartialTriple_iff_interpretRef` are verified
    promotion candidates**, proved in `workshop/exhibits.lean` §9. They are not
    silently copied into `Cas/Lang/Wp.lean` by this pre-grade packet.
17. **Every `H`-dependent row names its hash-hypothesis level.** The lattice
    exists (`Address.lean:56/69`); no DAG row cites it, so a Level-0 result and
    one assuming injectivity are currently indistinguishable in the ledger.
18. **`.reference/` acquires manifest rows and a gate.** `manifest.json` has no
    row for the paper corpus, and `mise.toml` contains zero occurrences of
    `.reference`. Until both change, every pin this packet adds is ungated by
    construction — which makes `EC1-K06`'s "external tooling identity" a promise
    nothing enforces.
