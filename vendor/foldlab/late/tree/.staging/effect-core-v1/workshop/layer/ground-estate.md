# Layer — the ground estate

Scout report. Every `file:line` below was read at `feb29321`. Line numbers were
re-derived from the files, not copied from the brief; three of the brief's were
wrong and are corrected in §0.

Probe files compiled against the warm cache with
`cd library/cas && lake env lean <path>`. Their receipts are in §7.

---

## 0. Citation corrections before anything else

| Brief said | Actual |
| --- | --- |
| `Handler.through` at `Tower.lean:65` | correct |
| `interpret_through` at `Tower.lean:71` | correct, and PROVED — induction on `Prog`, no `sorry` |
| `casOverBytes` at `Tower.lean:111` | correct |
| `prog_is_free :502`, `existsUnique_handler :519`, `prog_is_initial_in_S_models :566`, `through_monoid :785` | all correct |
| `interpretRef_bind` in `Cas/Lang/Handler.lean` | **does not exist.** `grep -rn interpretRef_bind library/cas` returns nothing. The theorem lives in staging at `.staging/effect-core-v1/workshop/counterexamples/EnsuringRepair.lean:151`. `library/cas/Cas/Lang/Handler.lean` has `interpretRef` (`:96`) and `interpretRef_vis` (`:149`), and neither is a bind law. |
| `interpretRef` at `Cas/Lang/Handler.lean` | correct, `:96` |

One more, load-bearing for §4: **`through_monoid` is not the theorem the brief
wants.** It is stated only on `Handler S (Prog S)`. See §4.

---

## 1. What a Layer already is in this estate

**`Handler ROut (Prog RIn)`.**

Read off the three ratified facts in order:

- a service IS a handler — `Handler` is `structure Handler (S : Sig) (M : Type → Type v) where handle : (op : S.Op) → M (S.Ans op)` (`library/cas/Cas/Lang/Handler.lean:42`);
- a handler CAN BE a program — its target monad may be `Prog T`;
- therefore "a thing that builds the services `ROut` given the services `RIn`" is
  `Handler ROut (Prog RIn)`.

That is, verbatim, the type of `Handler.through`'s FIRST argument
(`library/cas/Cas/Lang/Tower.lean:65`):

```lean
def Handler.through [Monad M] (t : Handler S (Prog T)) (h : Handler T M) :
    Handler S M where
  handle op := interpret h (t.handle op)
```

### Say it loudly: `Handler.through` IS layer composition

Instantiate `M := Prog RIn`. Then

```
t : Handler ROut (Prog RMid)     -- the outer layer
h : Handler RMid (Prog RIn)      -- the inner layer
t.through h : Handler ROut (Prog RIn)
```

`ROut` provided, `RIn` still demanded, `RMid` discharged. That is
`Layer.provide(outer, inner)` and nothing else. The argument order even matches
the estate's own emitter: `exprOf` at `library/cas/Cas/Backend/EmitLayer.lean:282`
emits `.call (.ident "Layer.provide") [o, i]`, and `residualOf` at `:251-254`
computes `provides := ro.provides` (the outer's) — the same handedness.

And the second argument is polymorphic in `M`, so **one operation serves both
`provide` and `launch`**: at `M := Prog RIn` it composes two layers; at
`M := RefM` (or `Effect<_,_,_>`) it launches a layer into a runtime.
`interpret_through` (`Tower.lean:71`) is then the statement that building and
then running equals running against the composite — which is `Layer.provide`'s
soundness theorem, already proved.

### The estate already ships a worked Layer

`llmOracleHandler oracle : Handler LlmSig (Prog CasSig)`
(`library/cas/Cas/Backend/SumAlgebra.lean:479`) is a layer providing the LLM
service over the store. `idHandler.sum (llmOracleHandler oracle) :
Handler AgentSig (Prog CasSig)` is that layer `provideMerge`d with the ambient
store context, and `handleLlm_eq_interpret` (`SumAlgebra.lean:485`) proves the
hand-rolled `Prog.handleLlm` (`Cas/Lang/Interp.lean:184`) IS that layer applied.
`runAgent` (`Interp.lean:190`) is the launch.

I compiled the factorization (probe `LayerAgent.agent_launch_factors`, §7):

```lean
interpret (referenceHandler H) (p.handleLlm oracle)
  = interpret ((idHandler.sum (llmOracleHandler oracle)).through (referenceHandler H)) p
```

Build-then-launch = launch-against-the-composite, on the estate's own layer, with
no new machinery.

### And exactly what is missing

`Handler.through` is layer composition **with the build erased.** Five gaps, in
descending order of how much they cost:

**(a) There is no build step, and this is not a proof gap — it is a concept gap.**

Kernel-checked falsifier, mine, no axioms
(`LayerNoBuild.through_has_no_build`, §7). A layer whose service implementation
acquires before answering:

```lean
def acquiringLayer : Handler HighSig (Prog LowSig) where
  handle _ := (Prog.op .acquire).bind fun _ => Prog.op .useLow

theorem through_has_no_build :
    (interpret (acquiringLayer.through countAcquires) twoUses 0).2 = 2 := rfl
```

Two uses of one service pay TWO acquisitions. `through` INLINES the service
implementation at every call site; there is no moment at which the service is
constructed. Everything Effect's Layer does that depends on "built once" —
memoization, connection pooling, `Scope`, `fresh` — is invisible to this carrier.
`SystemNode.fresh` (§2) has literally no image here: on a function carrier
`fresh l` can only be `l`.

**(b) There is no error index.** `Layer.Layer<ROut, E, RIn>` carries three;
`Handler ROut (Prog RIn)` carries two. Build failure has to be an operation of
`RIn` (`CasE.fail`, `ByteE.fail` at `Tower.lean:40`). Under R10 that is arguably
*correct* — `Handler.lean:17-19` states that the error channel is the target
monad's contribution, never the language's — but E is then not independently
tracked, and the estate's emitter already hardcodes it: `layerTypeOf`
(`EmitLayer.lean:306`) always writes `E := never`, and `EmitLayer.lean:80-83`
says so out loud.

**(c) There is no scope, and the fix is a target change, not a carrier change.**
See §5 and §6.

**(d) Merge has no monoid laws.** See §3.

**(e) A `Handler` is CODE, not content.** `handle` is a dependent function. A
Layer that must be hashed, stored, or shipped cannot be a `Handler`. The estate
already knows this and already built the other half — §2.

**R1 does not block any of this.** A layer's build is a finite program; nothing
here reaches for coinduction. A long-lived service is not a `Prog` at all — it is
the target monad's business under R10/R14a. A design that reaches for a
coinductive carrier "because a service stays up" has misread which side of the
seam the service lives on.

---

## 2. The estate has a SECOND Layer object, on the other side of R7

This is the largest thing the packet is not currently looking at.

`Cas.Schema.SystemNode` (`library/cas/Cas/Schema/System.lean:208`) is a
`cas_union` — first-order, canonically encodable, store-resident content:

```lean
cas_union SystemNode where
  | backing (ctor : CodeRef) (provides : List ServiceRef) (requires : List ServiceRef)
  | fresh (inner : StoreRef systemKindTag)
  | merge (parts : List (StoreRef systemKindTag))
  | «opaque» (ctor : CodeRef) (note : String) (provides : List ServiceRef) (requires : List ServiceRef)
  | provide (inner : StoreRef systemKindTag) (outer : StoreRef systemKindTag)
  | provideMerge (inner : StoreRef systemKindTag) (outer : StoreRef systemKindTag)
  | service (ctor : CodeRef) (provides : ServiceRef) (requires : List ServiceRef)
```

Children are `StoreRef`, so a topology is a Merkle DAG and its root address is
the certificate (`System.lean:75-87`). `residualOf`
(`Cas/Backend/EmitLayer.lean:243`) computes provides/requires in Effect's own
algebra; `exprOf` (`:269`) emits `Layer.provide` / `Layer.provideMerge` /
`Layer.mergeAll` / `Layer.fresh`; `layerTypeOf` (`:306`) renders
`Layer.Layer<ROut, E, RIn>` through the pinned target row
(`Cas/Backend/Target.lean:43`, `rfl`-pinned at `:108-118`).

So the estate holds:

| | carrier | R7 side | laws | build step | scope | `fresh` |
| --- | --- | --- | --- | --- | --- | --- |
| **handler layer** | `Handler ROut (Prog RIn)` | CODE | assoc + 2 units + merge's universal property | none | none | inexpressible |
| **system layer** | `SystemNode` | CONTENT | **zero** | delegated to TS | none | expressible |

`grep -c theorem library/cas/Cas/Backend/EmitLayer.lean` → **0**. `residualOf`
and `exprOf` are unverified functions.

**No theorem connects the two carriers.** That is the design's central hole, and
it already has a named shape in this repository twice over:

- `Tower.lean:26-29` names the refinement obligation for `casOverBytes` —
  "over a faithful byte-plane handler, `casOverBytes` agrees with
  `referenceHandler` word for word" — and does not claim it;
- `Cas/Lang/Defun.lean` is the *worked* instance of exactly this pattern on the
  PROGRAM side: `PProg` (`:187`) is the R7-storable table, `embed` (`:231`) is
  the `Prog` it denotes, and `runP_embed_agree` (`:362`) is the bridge.

`SystemNode` is to `Handler` what `PProg` is to `Prog` — **minus `embed` and
minus the agreement theorem.** Supplying those two is the single highest-value
consolidation available on this lane, and it mints nothing.

The estate has also already ruled on why the bridge is hard, and the ruling is
not naive: Effect memoizes a layer by object identity, a description shares by
digest, so the two disagree on how many instances exist
(`System.lean:36-68`, `EmitLayer.lean:74-83`, `tools/EmitLayers.lean:12-17`).
Generation is one-way **by ruling**. `System.lean:59-68` reads the v4 source and
records that `Layer.fresh` is a property of the MemoMap not of the layer value,
and that `Layer.build` forks and reads through to a parent — so the gap narrowed
in v4 and did not close.

---

## 3. Merge — what `Sig.sum` + `Handler.sum` already give, and what they don't

`Sig.sum` (`Cas/Lang/Sig.lean:20`, notation `⊕ₛ` at `:25`, `infixl:65`) and
`Handler.sum` (`Cas/Lang/Handler.lean:63`) at `M := Prog RIn` are merge.

### Given

| Law | Site | Strength |
| --- | --- | --- |
| `Handler.sum_handle_inl` | `SumAlgebra.lean:196` | `rfl` |
| `Handler.sum_handle_inr` | `SumAlgebra.lean:202` | `rfl` |
| **`Handler.sum_unique`** | `SumAlgebra.lean:212` | **the universal property** — any handler on the sum agreeing with the two sides on their own operations IS `h.sum g`. This is what "merge has laws" should mean, and it is discharged. |
| `interpret_inl` / `interpret_inr` | `:231` / `:239` | a program using only one summand interprets through the merge exactly as through that side's layer. Merge does not disturb a one-sided client. No lawfulness needed on the target. |
| `Prog.inl_pure` / `inl_bind` / `inr_pure` / `inr_bind` | `:249` / `:256` / `:265` / `:269` | the injections are monad morphisms — requirement-weakening is a monad morphism |
| `Prog.inl_injective` / `inr_injective` | `:284` / `:307` | weakening is faithful |
| `inlHandler` / `inrHandler` + `interpret_inlHandler` / `interpret_inrHandler` | `:341` / `:345` / `:349` / `:359` | weakening is itself an INTERPRETATION — so `l.through (inlHandler R1 R2)` is requirement-weakening with no new construct |
| `sum_inlHandler_inrHandler` | `:371` | the two injection handlers sum to `idHandler` |
| `Prog.inl_unique` / `Prog.inr_unique` | `:427` / `:460` | the injections are forced |

I compiled the derived combinators (§7):

- `mergeL l r := l.sum r`
- `weakenLeft l := l.through (inlHandler R1 R2)`
- `mergeIndependent l r := mergeL (weakenLeft l) (weakenRight r)` — merging layers
  with *different* requirements, from existing parts only
- `provideMergeL outer inner := (outer.through inner).sum inner`, with both
  projections by `rfl` and uniqueness from `Handler.sum_unique`.
  **`provideMerge` is derived, not primitive.**

### Not given — four, and they are real

1. **No associativity.** `(R1 ⊕ₛ R2) ⊕ₛ R3` and `R1 ⊕ₛ (R2 ⊕ₛ R3)` are different
   TYPES. Verified: `example : ((R1 ⊕ₛ R2) ⊕ₛ R3) = (R1 ⊕ₛ (R2 ⊕ₛ R3)) := rfl`
   fails with *type mismatch*. `grep -rE "sum_assoc|sum_comm" library/cas/Cas`
   returns nothing.
2. **No unit.** No empty signature anywhere. Verified: `#check @Sig.empty` →
   *Unknown constant*. `Sig.sum` therefore has no `Layer.empty`.
   (`idHandler` is the unit of `through`, not of `sum`.)
3. **`Sig.sum` is DISJOINT, and Effect's merge is not.** Two layers providing the
   same service key cannot even be stated here — there is no overlap to resolve,
   so "later wins" has no image. `swapSum` (`SumAlgebra.lean:671`) and
   `swapSum_not_sum_handle_inl` (`:685`) already sit in the estate as the
   falsifier showing arm order is observable.
4. **`Handler.sum` forces both sides into the SAME target.** Effect merges layers
   with different `RIn`. The repair exists and I compiled it
   (`mergeIndependent`), but no estate theorem says that weakening is the right
   one, and it changes the requirement type from `RIn` to `A ⊕ₛ B` — so a merge
   chain of *n* layers accumulates an *n*-deep right-nested sum with no
   normalization.

Merge's laws are therefore **half present**: the universal property is the
strong half and it is discharged; the monoid structure is absent and its absence
is structural (types, not missing proofs).

---

## 4. `through_monoid` — refuted as stated, confirmed as needed

This was flagged as the single highest-value thing to confirm or refute. Both.

**Refuted as the theorem to cite.** `through_monoid`
(`Cas/Backend/Universal.lean:785`) quantifies over `t u v : Handler S (Prog S)` —
the ENDOMORPHISMS at one signature. A Layer changes signature: `ROut ≠ RIn` is
the whole point. `through_monoid` never applies to a layer that provides
something it does not already require. The estate says this itself at
`Universal.lean:776-784`: *"Across signatures the same three facts are a
CATEGORY, not a monoid."*

**Confirmed as the three theorems it bundles.** Those DO reach layer composition,
and at `M := Prog U` they cost nothing:

| | site | hypothesis | at `M := Prog U` |
| --- | --- | --- | --- |
| `through_assoc` | `Universal.lean:739` | `LeftUnit M`, `BindAssoc M` | free — `Prog S` is a `LawfulMonad` (`Representation.lean:54-58`) |
| `through_id_right` | `:757` | none at all | free |
| `through_id_left` | `:765` | `RightUnit M` | free |

Compiled (`LayerProbe`, §7):

```lean
theorem provideL_assoc (a : LayerH S T) (b : LayerH T U) (c : LayerH U V) :
    provideL (provideL a b) c = provideL a (provideL b c) :=
  through_assoc leftUnit_of_lawful bindAssoc_of_lawful a b c

theorem provideL_id_right (a : LayerH ROut RIn) : provideL a emptyL = a := through_id_right a
theorem provideL_id_left  (a : LayerH ROut RIn) : provideL emptyL a = a :=
  through_id_left rightUnit_of_lawful a
```

with `emptyL := idHandler` (`Cas/Lang/Representation.lean:63`).

**So: layer composition has its identity and associativity for free, from
theorems already on main.** `idHandler` is `Layer.empty`. The correction is that
the citation is `through_assoc` + `through_id_left` + `through_id_right`, not
`through_monoid`.

**One boundary that does bite.** `through_assoc` is FALSE at unlawful final
targets, with two kernel-checked witnesses in the estate:
`through_assoc_fails_over_shift` (`contracts/attacks/PDD-8/AttackAmended.lean:185`,
`BindAssoc` without `LeftUnit`, `2 ≠ 3`) and `through_assoc_fails_over_skew`
(`:237`, both units without `BindAssoc`, `15 ≠ 9`), bundled as
`through_assoc_two_equations_are_minimal` (`:249`). This does not touch
layer-to-layer composition — the intermediate targets are always `Prog`, which is
lawful — but it constrains LAUNCH: **the runtime a layer stack is launched into
must satisfy `LeftUnit` and `BindAssoc`, or the stack's bracketing is
observable.** Any `Effect` adapter this design writes owes those two equations.

---

## 5. The handler algebra — the laws actually available

| Law | Site | Notes |
| --- | --- | --- |
| `interpret` | `Handler.lean:47` | structural recursion; lands in ANY monad because `Prog` is finite (R1) |
| `interpret_bind` | `Handler.lean:53` | the monad-morphism law, at `[LawfulMonad M]` |
| `interpret_bind_of_equations` | `Universal.lean:195` | the same, at the two equations it actually spends |
| `interpret_through_of_equations` | `Universal.lean:211` | `interpret_through` re-proved without `[LawfulMonad M]` — this is the version `through_assoc` uses |
| `interpret_id` | `Representation.lean:68` | |
| `eq_of_forall_interpret` | `Representation.lean:80` | programs agreeing under every lawful interpretation are equal |
| `Handler.ext` | `Universal.lean:128` | |
| `prog_is_free` | `Universal.lean:502` | every monad morphism out of `Prog S` comes from exactly one handler. Note the amendment at `:496-501`: the first draft called this *initiality* and it is not — `Prog S` admits two distinct morphisms into `StateT Nat Id`. |
| `existsUnique_handler` | `Universal.lean:519` | alias of the above |
| `prog_is_initial_in_S_models` | `Universal.lean:566` | the other quantifier order, in the category of `S`-models: for every handler, exactly one morphism, and it is `interpret h` |
| `interpret_pinned` | `Universal.lean:598` | adequacy — with the honest emptiness caveat at `:588-597` |
| `referenceHandler` / `interpretRef` | `Handler.lean:78` / `:96` | |
| `run_interpretRef_agree` | `Handler.lean:255` | big-step = fueled small-step, with the refusal word EXISTENTIAL — `Except Refusal (A × Word)` has nowhere to hold it (`:100-124`). This is the same information loss R18 rules on. |
| `replayHandler` | `Handler.lean:279` | in the algebra, and still the wrong semantics — `Universal.lean:825-828` |

Together: `prog_is_free` + `prog_is_initial_in_S_models` say a Layer's *meaning*
is completely determined by its per-operation clauses and nothing else. That is
why `Handler.sum_unique` and `Handler.ext` are enough to pin merge, and why
adding a new carrier for Layer would have to argue against two universal
properties, not one.

**What the algebra does NOT reach**, enumerated by the estate itself at
`Universal.lean:792-842`: `Prog.handleLlm` (conditionally, now discharged by
`handleLlm_eq_interpret`), `step`/`run` (no composition law at fixed fuel),
`replayHandler` (in the algebra, wrong content), `runP` (domain is `PProg`), and
`wp`/`wlp` (contravariant). None of these is a Layer, but the last two say where
a Layer's *verification* story cannot live.

---

## 6. Absence — scope, resource, ownership, memo

Counts are over `library/cas/{Cas,tools,contracts}` (the Lean estate), case-
insensitive, word-boundary-prefixed. Every nonzero bucket was read.

| Term | Estate | Verdict |
| --- | --- | --- |
| `finaliz*` | **0** | anchor lane confirmed |
| `fairness` | **0** | confirmed |
| `mask*` | **0** | confirmed |
| `supervisor` | **0** | confirmed |
| `\brace\b` | **0** | confirmed — the 39 substring hits are `trace` / `brace` |
| `ownership` | **0** | (1 in `AGENTS.md`, meaning task ownership) |
| `lifetime`, `dispose`, `cleanup` | **0** | |
| `scope*` | 178 | **ZERO are resource scope.** All are: English "claim scope" / "honest scope" (`Universal.lean:594,840`, `Wp.lean:8,352`, `SumAlgebra.lean:818`, `Canon.lean:522`), Lean's binder scope (`Notation.lean:39`, `Annotation.lean:284`), Lean's `scoped` attribute, or the `Rule.scope : String` field (`Cas/Lift/Manifest.lean:29`) — a *syntactic recognition rule's* scope, valued `"declaration"` / `"statement"` / `"expression"`. There is no `Scope` type and no scope-extending operator. |
| `resource*` | 37 | **ZERO are acquired resources.** All are HTTP REST resources: `structure Resource` at `Cas/Backend/HttpProfile.lean:327`, `resources` at `:340`, and the theorems over them at `:374-412`. |
| `acquire*` | 11 | prose only — `Canonicalize.lean:41` ("acquire → ingest → NORMALIZE → gate → admit"), `TreeProgCorrect.lean:58` ("`runP` acquires an executed…"), `Ast.lean:137`, and `Strata.lean`'s `requireSource`. No acquisition semantics. |
| `release` | 7 | **all seven are software releases** ("that field stays for one release"). Zero resource release. |
| `region` | 1 | `Cas/Llm/Judge.lean:82`, "the accepted region" of a grammar. |
| `bracket*` | 10 | JSON delimiters and proof-term parenthesization. |
| `memo*` | 14 | **the interesting bucket.** `EmitLayer.lean:76`, `System.lean:39`, `tools/EmitLayers.lean:16,100` are all about **Effect's Layer memoization as a hazard**, already ruled on (§2). The rest (`Reach.lean:99`, `Ingest.lean:907`, `Guarded.lean:446,637`, `Manifest.lean:855`) are ordinary computation caching. |
| `interrupt` / `cancel` | 1 / 1 | both `Handler.lean:18,24`, prose naming what the TARGET monad contributes. |

### One correction to the anchor lane

**"Every *fiber* hit is a false positive (`trace`, `brace`)" is wrong as stated.**
`fiber` has three genuine word occurrences: `Cas/Lang/Handler.lean:17`,
`Cas/Schema/System.lean:46`, and `EFFECTS-BACKEND.md:164`. They are not
`trace`/`brace` artifacts. The `trace`/`brace` diagnosis is correct for `race`
(confirmed: `\brace\b` → 0) and does not extend to `fiber`.

The accurate claim is: **no `fiber` is an estate construct.** All three
occurrences are prose describing what the *target* monad supplies — and
`Handler.lean:17-19` is the ruling that makes that the right place for it:
"fibers, interruption, and the error channel are the target monad's
contribution, never the language's."

### What this means for the design

The vocabulary is not merely absent — **it is absent by a ruling that is already
written down.** R10 puts fibers, interruption, and errors in the target monad.
A Layer design that introduces `Scope` as a signature, a carrier, or a `Prog`
constructor is arguing against `Handler.lean:17-19`, not filling a gap.

And R18 already fixed where scope's *state* has to go. `EC1-CE045`
(`COUNTEREXAMPLES.md:115`) is `VERIFIED-KERNEL`, 44 receipts:
`reraise_is_finalizer_blind`
(`workshop/counterexamples/EnsuringRepair.lean:309`) proves **no** clause into
`ReaderT EnvR (StateT Word (Except Refusal))` can finalize correctly, because
`Except.error r` has no word slot, so any clause preserving the refusal is
determined by `r` alone and identifies two finalizers leaving observably
different words (`reraise_blindness_is_not_vacuous`, `:319`). The forced target
is `RefW := ExceptT Refusal (StateM Word)` — **state outside error**
(`EnsuringRepair.lean:361`), with `ensuringT` at `:547` and all four laws at
`:600`, `:620`, `:640`, `:726`.

Consequence for Layer, stated plainly: **a Layer whose `build`/`launch` releases
on failure must launch into an `ExceptT _ (StateT _ _)`-ordered target.** This
does not touch the layer carrier — R18 ruling 1 keeps `Handler` and refuses
`HHandler` — it touches the launch target only, which is exactly where §4's
lawfulness obligation also lands. The two constraints compose: the launch target
owes `LeftUnit` + `BindAssoc` (§4) *and* state-outside-error (R18). `RefW` is a
lawful stdlib stack and satisfies both.

---

## 7. Probes — what I compiled

All under `library/cas` with `lake env lean`. Sources at
`/private/tmp/claude-501/-Users-pooks-Dev-foldlab/a31288e1-481d-4d48-bbf7-34e199015bcd/scratchpad/`.

**`LayerProbe.lean` — exit 0.** Ten claims: `LayerH ROut RIn := Handler ROut (Prog RIn)`;
`provideL := through`; `emptyL := idHandler`; `provideL_assoc`;
`provideL_id_left` / `_id_right`; `mergeL := Handler.sum`; `weakenLeft` /
`weakenRight` / `mergeIndependent` via `inlHandler`/`inrHandler` + `through`;
`launch_through := interpret_through`; `merge_left_transparent := interpret_inl`;
`merge_unique := Handler.sum_unique`.
Receipts: `provideL_assoc`, `provideL_id_left`, `launch_through`,
`merge_left_transparent` → `[propext, Quot.sound]`; `merge_unique` →
`[Quot.sound]`.

**`LayerNoBuild.lean` — exit 0.** The build-step falsifier.
`through_has_no_build` and `build_once_is_refuted` → **no axioms**.

**`LayerAgent.lean` — exit 0.** `agent_launch_factors` → `[propext, Quot.sound]`.

**`LayerDerived.lean` — exit 0.** `provideMergeL` with both projections by `rfl`
and `provideMergeL_unique` → `[Quot.sound]`.

**Negative probes, both fail as predicted.**
`example : ((R1 ⊕ₛ R2) ⊕ₛ R3) = (R1 ⊕ₛ (R2 ⊕ₛ R3)) := rfl` → *Type mismatch*.
`#check @Sig.empty` → *Unknown constant `Cas.Lang.Sig.empty`*.

---

## 8. The shortest statement of the finding

1. A Layer is `Handler ROut (Prog RIn)`. Nothing needs minting.
2. `Handler.through` (`Tower.lean:65`) IS `Layer.provide`, and one operation
   serves both provide and launch because its target is polymorphic.
3. `idHandler` is `Layer.empty`. Associativity and both units come free from
   `through_assoc` / `through_id_left` / `through_id_right` — **not** from
   `through_monoid`, which is quantified at one signature and never applies.
4. `Handler.sum` is `merge`, `Handler.sum_unique` is its universal property, and
   `provideMerge` is derived from `through` + `sum`. Merge's *monoid* laws are
   absent for a structural reason: `Sig.sum` has no unit and is not associative
   on the nose, and it is disjoint where Effect's merge overlaps.
5. `Handler.through` has **no build step** — proved, no axioms — so memoization,
   `fresh`, and `Scope` have no image on this carrier.
6. The estate already has the R7-side Layer: `SystemNode`
   (`Cas/Schema/System.lean:208`), with zero theorems. The missing piece is the
   `embed` + agreement bridge that `Cas/Lang/Defun.lean` already worked out for
   programs.
7. Scope/resource/finalizer/ownership vocabulary is genuinely absent, and absent
   *by ruling* (`Handler.lean:17-19`), not by oversight. Where scope's state must
   live is already settled by R18 / `EC1-CE045`: outside the error.

---

## 9. What I did NOT check

- **The papers.** *HITrees: Higher-Order Interaction Trees* (arXiv:2510.14558,
  pinned `86389e25…`) and *Modular Denotational Semantics for Effects with
  Guarded Interaction Trees* (arXiv:2307.08514, pinned `40d999b3…`) are pinned at
  `.reference/catalog/PAPERS.md:194-195`. I did not open either PDF. The catalog
  carries titles and content hashes, not summaries. **No conclusion in this
  report rests on either paper**, and I make no claim about their contents.
- **`library/effects` (TypeScript).** I confirmed `layerMemory` /
  `layerMemoryBackend` exist and that the replay-plane uses are archived; I did
  not read the Layer or Scope implementations, so my account of Effect's Layer
  semantics is second-hand from `System.lean:36-68` and `EmitLayer.lean:74-83`,
  which read the v4 source and cite it.
- **`library/effect-protocol` and `library/machine`** — not searched.
- **`EnsuringRepair.lean` end-to-end.** I read its declarations and the S17
  ruling's receipt claim (44 receipts, exit 0). I did not re-run the file.
- **`Cas/Lang/Wp.lean`, `Cas/Lang/Worded.lean`, `Cas/Lang/Roots.lean`** beyond
  their declaration lists. `StoreSig := CasSig ⊕ₛ RootSig` (`Roots.lean:42`) and
  `WordedSig := StoreSig ⊕ₛ WordSig` (`Worded.lean:77`) are two more merge sites
  whose handlers I did not trace — they may already contain a layer stack in
  disguise, and are worth a follow-up.
- **`Cas/Lang/Defun.lean`'s suitability as a defunctionalized HANDLER carrier.**
  I confirmed `PProg`/`embed`/`runP_embed_agree` exist and that no handler
  analogue does. Whether `PLine` can be extended to code points that *are*
  handler clauses is the obvious next question and I did not investigate it.
- **Slices S1 and S2** — untouched, per instruction.
