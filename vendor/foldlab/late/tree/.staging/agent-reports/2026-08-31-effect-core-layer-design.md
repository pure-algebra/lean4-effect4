# Effect Core v1 — Layer, dependencies, runtimes and Scope: the design

**Author:** architect, closing the S-layer design pass
**Date:** 2026-08-31
**Status:** PLAN. Sections marked KERNEL rest on files that compile; sections marked ARGUMENT do not.
**Write fence:** this file only. Nothing in `library/`, `formal/`, or the packet `.md` files was modified. No git operation.

---

## 0. One-paragraph summary

A Layer is **a program whose value is a handler**: `Layer := Prog LayerSig (Handler SvcSig (Prog LayerSig))`. Both names are `abbrev`s over carriers already in `library/cas`; every combinator — `provideMerge`, `run`, `merge`, `build`, `launch`, `unwrap`, `shared` — is `bind`, `interpret`, `Handler.through` or `Handler.sum`, and the three composition laws are discharged by the estate's own `through_monoid` (`Cas/Backend/Universal.lean:785`) through a two-line embedding. Scope is a **signature summand**, not a carrier and not a per-layer target choice: `acquire` and `scoped` are operations of `LayerSig` whose children are `CodeRef`s, and the tower leaves `Prog` exactly once, at one floor handler into R18's ruled `ExceptT Refusal (StateM (Word × FinStack))`. The shipped Layer is `Cas.Schema.SystemNode`, unchanged except for one arm.

**The team converged 5/5 on a common core and then split, in the minimizer/modeler round, on exactly one question.** It is stated in §6 as a decidable experiment.

---

## 1. The recommendation

### 1.1 Signatures — keys at the value level, scope as a second summand

```lean
abbrev SvcKey := String

/-- The service language. ONE operation, because under R7 the service SET is
    content, not a type index: a `Sig` computed from stored content forces a
    signature-normalization apparatus the estate does not have (§2, position B). -/
inductive SvcE where | ask (key : SvcKey)
abbrev SvcSig : Sig := ⟨SvcE, fun _ => Addr32⟩

/-- The scope language. Children are `CodeRef`s — first-order, R18 clause 1,
    no `HHandler`. `acquire` runs its acquisition and REGISTERS its release;
    `scoped` is the DELIMITER that drains what was registered inside it. -/
inductive ScopeE where
  | acquire (acq release : CodeRef)
  | scoped  (body : CodeRef)
abbrev ScopeSig : Sig := ⟨ScopeE, fun _ => Addr32⟩

abbrev LayerSig : Sig := SvcSig ⊕ₛ ScopeSig        -- `Sig.sum`, existing
```

Two summands rather than one flat signature is the one place I overrule the minimizer, and the reason is a type-level guarantee: a `Svc` has only `ask` clauses, so **a service context structurally cannot intercept another layer's acquisition**. On one flat signature the scope passthrough must be hand-written in every leaf handler and nothing enforces it. (ARGUMENT, not kernel-checked — but see §7 on `PROOF-DAG.md` §7, which already rules that scoped interpretation is direct and separate from the `Handler.through` tower.)

### 1.2 The two names — both `abbrev`, zero new types

```lean
abbrev Svc   : Type := Handler SvcSig (Prog LayerSig)   -- Effect's `Context<R>`
abbrev Layer : Type := Prog LayerSig Svc                -- the BUILD PREFIX, then the context
```

No inductive, no eliminator, no new equality; `LawfulMonad` is inherited from `Prog` (`Cas/Lang/Representation.lean:54`). Erasing both names changes nothing.

The `Prog LayerSig (·)` prefix is **not** decoration. Four independent lanes proved, axiom-free, that `Handler ROut (Prog RIn)` alone is layer composition *with the build erased* — it pays one acquisition per USE where a layer pays one per BUILD. That is the single settled result of the whole pass (§5.2).

### 1.3 Every operation, derived

```lean
def injSvc    : Svc := ⟨fun | .ask q => Prog.op (Sum.inl (SvcE.ask q))⟩
def scopePass : Handler ScopeSig (Prog LayerSig) := ⟨fun op => Prog.op (Sum.inr op)⟩

/-- The embedding that makes the estate's ENDOMORPHISM monoid reachable. -/
def lift (h : Svc) : Handler LayerSig (Prog LayerSig) := Handler.sum h scopePass

def Svc.andThen (outer inner : Svc) : Svc := outer.through (lift inner)

def Layer.empty : Layer := pure injSvc

def Layer.provideMerge (inner outer : Layer) : Layer :=
  inner >>= fun hi => interpret (lift hi) outer >>= fun ho => pure (ho.andThen hi)

def Layer.run (l : Layer) (p : Prog LayerSig A) : Prog LayerSig A :=
  l >>= fun h => interpret (lift h) p

def Layer.unwrap (m : Prog LayerSig Layer) : Layer := m >>= id      -- `join`,  by `rfl`
def Layer.shared (c : Layer) (k : Svc → Layer) : Layer := c >>= k   -- `bind`,  by `rfl`
```

`build` is `interpret` at the floor. `runtime` is the bound `h` in `l >>= fun h => …` — running many programs against one runtime is one `bind`. `launch` is `Layer.run` inside a region. `memoize` does not exist (§1.6). **`merge` does not exist as an operation**: a context ANSWERS the keys it provides and FORWARDS everything else, so `andThen` of two independent leaves answers both key sets — merge is composition, proved by `interpret_op` and nothing else. `Handler.sum_unique` was never merge's anchor; it is the anchor for composing *languages*, which is what `lift` and the floor do with it.

### 1.4 Scope — concrete

```lean
abbrev FinStack   := List CodeRef                     -- pending releases, innermost first
abbrev ScopeState := Word × FinStack                  -- R18's word, widened
abbrev ScopeM     := ExceptT Refusal (StateM ScopeState)   -- state OUTSIDE error

/-- `EnsuringRepair.ensuringT` with the finalizer split by exit — requirements-lane C9. -/
def ensuringExitT (body onOk onErr : ScopeM α) : ScopeM α

def acquireT (run : CodeRef → ScopeM Addr32) (acq rel : CodeRef) : ScopeM Addr32
  -- run `acq`; on success push `rel`. On failure register NOTHING.
def drainT (run) : FinStack → ScopeM Addr32           -- head-first, i.e. LIFO
def scopedT (run) (body : ScopeM Addr32) : ScopeM Addr32
  -- fresh stack; drain on BOTH exits; restore the enclosing stack

def floorH (run) : Handler LayerSig ScopeM :=
  Handler.sum svcFloor (scopeFloor run)               -- ONE floor, not one per layer
def launch (run) (l : Layer) (p) := scopedT run (interpret (floorH run) (Layer.run l p))
```

Three things kept separate, deliberately: **acquisition**, **registration**, **release**. `ensuring` alone is a bracket that releases when its own body returns — but a layer's resource must outlive the build step that acquired it, so the delimiter is a different operation from the acquisition and the pending-finalizer list is *state*. Without a delimiter the build's resource is never released at all (`unscoped_launch_leaks`, KERNEL). LIFO is then a property of the stack, not of nested `ensuring` — which matters, because `EnsuringRepair.lean` §3's nested-LIFO law is unreachable at a floor whose blocks carry no scope operation, and one proposal was killed for citing it as if it transferred.

### 1.5 The content plane — `SystemNode`, plus one arm

The shipped Layer is `Cas.Schema.SystemNode` (`Cas/Schema/System.lean:208`): seven arms, addressed children, an emitter (`Cas/Backend/EmitLayer.lean`), and a residual calculus (`residualOf`, `:243`) that is already pure and first-order (R14a). Six of the seven things `REIFICATION-CHECKLIST.md:885` names as `LayerCore` exist today. The delta is one arm:

```lean
| scoped (acquire release : CodeRef) (provides : ServiceRef) (requires : List ServiceRef)
```

`System.lean:105-107` names an added arm as the sanctioned growth path, verbatim: *"By an ARM, on the Exchange precedent — never by a sibling carrier."* Everything else stays: **no nonce on `fresh`**, **no `let`/`shared` binder arm**, **`opaque` kept** (it is the only home for the dynamic fragment). Measured migration cost: `library/cas/tools/EmitLayers.lean` authors 18 nodes (3 `service`, 4 `backing`, 2 `fresh`, 3 `merge`, 3 `provide`, 3 `provideMerge`, 0 `opaque`), **none of which acquires today**.

Whether the arm is paid at all is the crux (§6).

### 1.6 Sharing — no memo map, no memo key, no binder

The question every one of the five designers named as their crux — is sharing a **binder** on the content plane or an **address-keyed memo** in the build fold? — has a third answer, and it is the right one: **neither. Sharing is the elaboration ORDER.**

`EmitLayer.Resolved` (`:236`) is built children-first — the file says so at `:68` and `:235` (*"Built children-first, so a lookup never recurses"*). Elaborating a topology as a fold over that order visits each address **once**; the Lean-level `>>=` between visits is the binder, and it lives at elaboration time, in the host, never in the stored node. So:

* `SystemNode` needs no `shared`/`let` arm — no variable references, no de Bruijn indices, no alpha-equivalence inside a Merkle DAG (this is what killed position A);
* the build needs no `MemoMap`, no memo key, no content-address lookup, and no fuel (this is what killed positions B and C from opposite sides);
* `fresh` needs no nonce — it is the traversal elaborating that child off the order instead of reading the environment.

KERNEL: `topological_order_shares = [7,1,2]` against `tree_elaboration_does_not = [7,1,7,2]`, separated axiom-free (`minimal.lean`).

### 1.7 Does Layer dissolve?

**Half of it does, and the halves must be named separately.** The SEMANTIC Layer dissolves completely into `Prog`, `Handler`, `Handler.through` and `Handler.sum` — two `abbrev`s and no new law about layers as such. The CONTENT Layer does not dissolve and does not need to be invented: it is `SystemNode`, already shipped, and what it lacks is not a carrier but a *denotation* and an *agreement theorem*. That is the `Defun.lean` pattern (`PProg` / `embed` / `runP_embed_agree`) at the layer plane, and it is where the remaining work is.

---

## 2. Why this and not the other four

**A — layer-is-a-program.** Got the carrier exactly right, and it is kept verbatim: `Prog T (Handler S (Prog T))`. `unwrap_is_join` and `shared_is_bind` are kept (both `rfl`, axiom-free), and A's demonstration that REIFICATION C6's node/edge refutation does not reach a free monad is kept. A died on its own headline: "sharing is `bind`" makes sharing a *binder*, and A's own consequence — *"what `SystemNode` actually needs is a `shared`/`let` arm it does not have"* — is a variable-binding construct inside a content-addressed DAG, a strictly larger mint than the one it was avoiding, and absent from A's mint list. §1.6 keeps A's `bind` and pays no binder, by putting it in the elaboration rather than the node. A's `through_monoid`-is-the-wrong-anchor correction is **reversed** in §3.

**B — layer-is-a-dag.** Got R7 right, and it wins the content plane outright: the deliverable is `SystemNode`, already first-order, addressed, emittable to a non-Lean consumer, and — B's own correction, which four of five lanes needed — **not lawless**. `Cas/Backend/Canon.lean` carries 31 theorem declarations, 18 of them public (I counted declarations, not occurrences of the word — the raw `grep -c theorem` gives 38 and two of those lines are wrapped prose), including `canonServices_last_wins` (:278), `canonServices_perm` (:313) with exactly the `Nodup` premise the requirements lane says the law needs, `canonServices_perm_premise_is_necessary` (:376), `canonServices_idem` (:297), `systemNode_authored_stable` (:508), `systemAddressOf_authored_stable` (:531). The "SystemNode has zero theorems" headline came from grepping `EmitLayer.lean` (which is genuinely 0) and is wrong; any document still repeating it is repeating a grep. B also settled `fresh` (no nonce — freshness is the traversal) and owns the only lifetime pair in the field. B died on a bridge it could not state: `sigOf (canonServices (px ++ py)) = sigOf px ⊕ₛ sigOf py` is an equation between TYPES with three independent obstructions. §1.1 dissolves it by never computing a `Sig` from content.

**C — layer-is-a-handler-transformer.** Got the build step and the FORK-A lift, and both are kept — though by a cheaper route. C is also the source of the correct framing of memoization: what "built once" decides is **which scope owns the resource and when it releases**, not a cost model. C died because its own headline buy was refuted at its own carrier (`Addr32 → Layer` caches the *function*; the build happens at application, so the table cannot reach it) and because `Ctx In M → M (Ctx Out M)` pays target-monomorphism, universe-monomorphism and R7 for a distinction A's carrier already makes for free. C's self-critique is the most accurate document in the packet and its cost column can be trusted.

**D — dissolve-the-layer.** Contributed the one result in the field that nobody else has, and it is kept verbatim: the **two-sided** characterization of sharing — `sharing_is_not_free_in_general` paired with `sharing_is_free_under_idempotent_acquisition`. Everyone else proved only that sharing is observable; D alone proved the converse, which turns the memo row from an unproved obligation into a characterization and explains (rather than contradicts) the requirements lane's "the memo law is vacuous at `ObsEq`" finding — that is a fact about *acquisition*, not about memoization. D's `injHandler` + `interpret_injHandler` is kept as `scopePass`/`injSvc`, and its `scope_is_not_bind` is the cleanest statement of why a finalizer must be a handler clause. D died as A-with-less: byte-identical carrier, strictly fewer theorems, and a flagship scope lemma that holds with arithmetic in the scope slot.

**E — the two halves.** Contributed the keystone, and it is the single move the whole recommendation is built on: **R7 forces the service set to the value level**, so there is ONE service signature and no `sigOf`. That dissolves B's fatal flaw and C's `DecidableEq Sig` block at once. E also closed requirements-lane C9 — exit-indexed finalization, first-order (two block ids, not a closure over an `Exit`), with `ensuringExitT_diagonal := rfl` proving it conservative over R18's ruled repair. Every other lane left C9 open. E's `liftL`/`liftL_through` survive as `lift`/`lift_hom`, and E's late finding that `provide` is not associative is confirmed and strengthened in §3. E died for having no build step: its `.acquires` leaf compiles to a handler *clause*, re-entered per ask, so two sibling uses of one service open two brackets.

---

## 3. The law ledger

Every `file:line` below was opened and read **this session**. The distinction between DISCHARGED and NEW WORK is drawn at whether a theorem exists in `library/` — not staging, not a workshop probe.

### 3.1 Discharged by existing `library/` theorems

| Law the design owes | Discharged by | Verified |
| --- | --- | --- |
| `andThen` associativity | `through_monoid`, first conjunct | `Cas/Backend/Universal.lean:785` |
| `andThen` right unit (`injSvc`) | `through_monoid`, second conjunct | `Universal.lean:785` |
| `andThen` left unit | `through_monoid`, third conjunct | `Universal.lean:785` |
| …and their cross-signature forms | `through_assoc` / `through_id_right` / `through_id_left` | `Universal.lean:739` / `:757` / `:765` |
| `run (provideMerge i o) p = run i (run o p)` (R12's collapse at the layer plane) | `interpret_through` + `interpret_bind` | `Cas/Lang/Tower.lean:71`, `Cas/Lang/Handler.lean:53` |
| `run empty p = p` | `interpret_id` (with `lift_injSvc`) | `Cas/Lang/Representation.lean:68` |
| forwarding: `interpret (lift h) (fwd q) = h.handle (.ask q)` | `interpret_op` | `Representation.lean:115` |
| every handler-equality / uniqueness argument | `Handler.ext` | `Universal.lean:128` |
| `Layer` inherits the monad laws (so `shared` = `bind`, `unwrap` = `join`) | `instance : LawfulMonad (Prog S)` | `Representation.lean:54` |
| composing LANGUAGES at one target (`lift`, `floorH`) | `Handler.sum`, `Handler.sum_unique` | `Handler.lean:63`, `Cas/Backend/SumAlgebra.lean:212` |
| requirement weakening as interpretation | `interpret_inl` / `interpret_inr` | `SumAlgebra.lean:231` / `:239` |
| shadowing on the residual row is last-wins | `canonServices_last_wins` | `Canon.lean:278` — **but see §3.4** |
| unrelated-service commutation, with its necessary premise | `canonServices_perm` + `canonServices_perm_premise_is_necessary` | `Canon.lean:313`, `:376` |
| context-combination idempotence | `canonServices_idem` | `Canon.lean:297` |
| a layer's identity is stable under authored reordering | `systemNode_authored_stable`, `systemAddressOf_authored_stable` | `Canon.lean:508`, `:531` |

**Explicitly NOT an anchor, and this is a packet-wide correction in the other direction.** Four of five lanes wrote `through_monoid` off because `Svc = Handler SvcSig (Prog LayerSig)` is not an endomorphism. That is true of `Svc` and beside the point: `lift : Svc → Handler LayerSig (Prog LayerSig)` **is** an endomorphism handler, and it is an injective monoid homomorphism (`lift_injSvc`, `lift_hom`, `lift_inj` — KERNEL). So the estate's own monoid theorem discharges all three layer laws with three one-line lemmas and no new algebra. The one lane that claimed `through_monoid` was recovered instantiated it at two different signatures, where it does not typecheck, and was correctly refuted for that — but its instinct was right. **Withdraw the "`through_monoid` is refuted as the theorem to cite" ruling.**

### 3.2 Proved in the workshop model, NOT in `library/` — promotion is NEW WORK

These have kernel receipts (§5) but live in `.staging`. Nothing may cite them as estate law until promoted.

* The four R18 `ensuring` laws at the ruled target, plus `ensuringExitT_diagonal := rfl` making the exit-indexed form conservative. Estimate: **small** — the file compiles; promotion is a module placement and a naming pass.
* The region laws: `acquireT_registers`, `acquireT_registers_nothing_on_failure`, `drainT_cons`, `registration_is_LIFO`, `scopedT_releases_on_success`, `scopedT_releases_on_failure`, `scopedT_never_replaces`, `scopedT_state_is_the_drains`, `scopedT_restores_the_stack`. Estimate: **small**.
* The residual-row laws: `provide_requires_mem` and its four corollaries (removes exactly what it supplies — no more, no less), `provideMerge_provides_assoc`, `provideMerge_requires_assoc`, `provide_requires_not_assoc`. Estimate: **small**, but see §3.3 item 2.
* The bridge, sound direction: `build_forwards_of_not_provides` — unconditional. Estimate: **small**.
* `provides_can_overclaim` — a **result, not a gap**: two layers implementing each other's service compose into a context that advertises a key it forwards, and no check on the description can catch it because the bodies are opaque `CodeRef`s. A shipped `provides` row is an advertisement, not a guarantee. This belongs in `COUNTEREXAMPLES.md`.
* `lift_injSvc`, `lift_hom`, `lift_inj`, `interpret_ask`, `mergeOn_unique` — five short lemmas.

### 3.3 Genuinely owed — nobody has attempted these

1. **`requires`-soundness against the builder.** The design has the `provides` half unconditionally. The dual — `q ∉ d.requires` implies the built context never asks `q` of the floor — is *not* a type equation (that obstruction died with value-level keys) but an induction over what an arbitrary block body may emit. It needs an `AsksOnly : List SvcKey → Prog LayerSig A → Prop` and a leaf well-formedness hypothesis. **Estimate: medium.** The induction shape is the mirror of `build_forwards_of_not_provides`, which is done. Until it lands, the emitted `RIn` rests on the row alone in that direction. *This is the single largest owed item in the design.*
2. **The row laws under `canonServices`.** Every row theorem in the model is at plain `++`/`filter`. The shipped `residual` (`EmitLayer.lean:231`) wraps `canonServices`, which ends in `List.mergeSort` and does not reduce in the kernel. Restating them turns list equalities into permutation-and-dedup statements. **Estimate: medium**; `canonServices_perm` (:313) and `canonServices_idem` (:297) exist to build on.
3. **The stratified floor.** `scopeFloor` takes already-interpreted blocks, so an acquisition block cannot itself ask for a service — and most real acquiring layers depend on a config or a client. The repair makes the floor self-referential and therefore fuel-bounded (`EnsuringRepair.runBlocks`'s shape). **Estimate: medium-large**, and it carries an uncosted consequence nobody in the field noticed until the minimizer/modeler round: **a fuel refusal is indistinguishable from a genuine refusal at the finalizer**, so exhaustion fires the release path.
4. **Elaboration over `Resolved`'s order without fuel.** The order exists and is children-first; the well-founded fold and its termination argument are not written. **Estimate: small-medium.**
5. **n-ary `SystemNode.merge` at the residual.** The model is binary. **Estimate: small.**
6. **Finalizers that can fail.** Every `ensuring` receipt in this packet — mine, the modeler's, the minimizer's, and both convergence probes' — is taken against a total drain or carries a premise on it. The non-trivial half of "runs on refusal of ANY finalizer" is exercised only at the combinator, never at a witness. **Estimate: small**, and it is the packet's most-repeated blind spot.
7. **`#guard SystemNode.schemaCode.discriminated` after the arm** (`Cas/Schema/System.lean:225`). Mechanical, minutes — but requires editing `library/`, which no agent in this pass was permitted to do, so **nobody has tested it**.
8. **The shadowing reconciliation** — §3.4, new, and owed by nobody.
9. Concurrency, fibers, interruption, parallel scope: out of v1 **by ruling**, not oversight. `Handler.lean:16-19` puts fibers, interruption and the error channel in the target monad; every ordering theorem here is about a sequential fold.

### 3.4 NEW FINDING — the row and the meaning shadow in opposite directions

`residualOf`'s `.provideMerge` arm (`Cas/Backend/EmitLayer.lean:255-259`) builds its provides row as

```lean
    pure (residual (ro.provides ++ ri.provides) …)      -- outer FIRST, inner LAST
```

`residual` (`:231`) applies `canonServices`, whose `dedup` (`:202-206`) drops the *earlier* occurrence of a repeated key, and `canonServices_last_wins` (`Canon.lean:278`) certifies exactly that. So **on a key both children provide, the row keeps the INNER's `ServiceRef`.**

The meaning does the opposite. `Layer.provideMerge inner outer` composes as `outer.through (lift inner)`, and at a key the outer answers, the outer's clause runs and wins.

KERNEL (mine, this session): `earlier_is_shadowed (a b : ServiceRef) (hk : a.key = b.key) (hne : a ≠ b) : a ∉ canonServices [a, b]`, derived from `canonServices_last_wins`. Ceiling `[propext, Classical.choice, Quot.sound]` — `Classical.choice` is **inherited** from `canonServices_last_wins` itself, which carries the same ceiling; the probe adds no axiom of its own.

This is observable only when two nodes provide the same key with *different* `ServiceRef` values — different `name`/`path`, i.e. different declared TypeScript types — so it never arises within one authored node under the estate's own distinct-keys door (which is where `canonServices_perm_of_nodup_keys`, `Canon.lean:288`, is stated). Across a `provideMerge` of two separately-authored children it can. The repair is one token: swap `:258` to `ri.provides ++ ro.provides`. **I do not recommend making that change on my evidence alone** — the direction must first be settled against rc.112's `Layer.provideMerge`, which nobody in this pass read. Note also that one proposal cited `canonServices_last_wins` *in support of* "the outer wins"; the theorem is real, and given `residualOf`'s actual argument order it certifies the opposite. That is precisely the `wlp_append` failure mode in a subtler form: right theorem, wrong direction.

### 3.5 Laws that are FALSE, or true only under a stated premise

* **`provide` is not associative — at both planes.** `provideMerge` is (`provideMerge_requires_assoc`, `provideMerge_provides_assoc`, as *literal list equalities*). Effect's `provide` is `provideMerge` followed by a mask to the outer's services, and the mask breaks it on the row (`provide_requires_not_assoc`: `["A"]` vs `[]`) **and in the meaning** (`provide_is_not_associative_in_the_meaning`: the same witness forwards under one bracketing and answers under the other). The row is not over-approximating — it reports a real semantic difference. This is why rc.112 ships both operations, and it dissolves the packet's four-to-one split: the lanes claiming `provide_assoc` were right about `provideMerge` and wrong about `provide`.
* **`EC1-T064` (`release_lifo`) needs a premise.** LIFO holds for the sequential strategy. `Layer.mergeAll` opens a parallel scope (Layer.ts:1596, as reported by the requirements lane — I did not read it). v1 admits only the sequential strategy; the divergence is **declared, not discovered**, and the row must carry it. `EC1-T066` inherits the same correction.
* **`Handler.sum_unique` is not merge's universal property.** `Sig.sum` is disjoint where service merge overlaps. It remains the universal property of *language* composition, which is what `lift` and `floorH` use it for.
* **`ensuring_LIFO` does not transfer to a floor whose blocks carry no scope operation.** It quantifies over a nested `ensuringT`; if the block table is `Prog CasSig`-valued the nested form is unreachable, and `EnsuringRepair.lean` §3's own preamble says so. In this design LIFO comes from the finalizer *stack*, which makes that trap structurally unavailable.

---

## 4. The minting ledger

Standing order: consolidate, never mint. Each row argues why an existing carrier cannot do the job.

### 4.1 Genuinely new in `library/`

| Minted | What it is | Why nothing existing carries it |
| --- | --- | --- |
| `SvcE` | one-constructor inductive, the op type of `SvcSig` | `Sig` is R10's declared extension point and every `Sig` value in the estate (`CasSig`, `ByteSig`, `RootSig`, `WordSig`, `LlmSig`) has its own op inductive. There is no generic "one operation carrying a string" signature to reuse. Cost: one constructor. |
| `ScopeE` | two-constructor inductive, the op type of `ScopeSig` | Nothing in `library/` carries scope operations at all — the estate lane's absence audit found `finaliz*`, `mask`, `ownership`, `fairness` at zero, and `Handler.lean:16-19` places fibers/interruption/errors in the *target monad by ruling*. Scope's TARGET machinery does belong there; its OPERATIONS must be in a signature, or `Handler.through` stops composing a layer that acquires and R18's "FORK A must be restated per-layer" becomes real. Today `ScopeE` exists only in unpromoted staging (`EnsuringRepair.lean:168`); **promotion is a mint and is counted.** |
| `SystemNode.scoped` arm | one arm on an existing `cas_union` | The sanctioned growth path, named verbatim at `System.lean:105-107`. `opaque` cannot substitute: it *"contributes IDENTITY, never structure"* and its children are not addressed, so a release under `opaque` cannot be named — which is exactly what a first-order finalizer stack requires. **This is an address-moving event** (18 authored nodes; `System.lean` paid one before and argued *"it will never be cheaper"*), and whether it is paid at all is §6's crux. |

### 4.2 Abbrevs and definitions over existing carriers — not carriers

`SvcKey`, `SvcSig`, `ScopeSig`, `LayerSig`, `Svc`, `Layer`, `FinStack`, `ScopeState`, `ScopeM`, `injSvc`, `scopePass`, `lift`, `Svc.andThen`, `Layer.empty/provideMerge/run/unwrap/shared`, `mergeOn`, `restrictTo`, `without`, `acquireT`, `drainT`, `scopedT`, `ensuringExitT`, `svcFloor`, `scopeFloor`, `floorH`, `launch`, `LDesc.provides/requires/acquiring/build`. Plus five lemmas: `lift_injSvc`, `lift_hom`, `lift_inj`, `interpret_ask`, `mergeOn_unique`.

**One of these carries a real cost that is not visible in its shape.** `ScopeState := Word × FinStack` widens R18's ruled state from `Word`. That is a product of existing types and mints nothing — but it re-opens the *statements* (not the proofs) of the four `ensuring` laws, and it breaks any word-exact equation between the scoped run and the estate's `run`/`interpretRefW`. Position D identified this obstruction and did not connect it to the arm question; §6 does.

### 4.3 Explicitly NOT minted

No `Layer` inductive or structure. No `Scope` type. No `MemoMap`, `MemoTable`, or memo key. No `Runtime` or `ManagedRuntime`. No `HHandler` or higher-order handler carrier (R18 clause 1). No `Sig.empty`, no `sigOf`, no `SigEnv`, no signature-subsumption or normalization apparatus. No binder/`let`/`shared` arm on `SystemNode`. No nonce on `fresh`. No first-order block table (`Defun.lean:186`'s `PProg = List PLine` is straight-line `put | load` and cannot carry a block — it is not needed, because the block children are `CodeRef`s and the floor resolves them, exactly as `Defun.embedFrom` takes its environment). No coinduction anywhere (R1). No change to `Handler`, `Sig`, or `Prog`.

---

## 5. Kernel evidence

### 5.1 What compiles

I re-ran every workshop file myself. All commands are `cd /Users/pooks/Dev/foldlab/library/cas && lake env lean <path>`.

| File | Exit | Receipts | Axiom-free | Errors | Warnings |
| --- | --- | --- | --- | --- | --- |
| `workshop/layer/ScopeLayer.lean` (modeler) | 0 | 67 | 11 | 0 | 0 |
| `workshop/layer/minimal.lean` (minimizer) | 0 | 38 | 21 | 0 | 0 |
| `workshop/layer/converge-A.lean` | 0 | 17 | 7 | 0 | 0 |
| `workshop/layer/converge-position-B.lean` | 0 | 19 | 15 | 0 | 0 |
| `workshop/layer/converge-D.lean` | 0 | 13 | 7 | 0 | 0 |
| `workshop/layer/converge-E.lean` | 0 | 24 | 2 | 0 | 0 |

`ScopeLayer.lean`: 1280 lines, 67 `theorem` declarations, 67 `#print axioms` receipts, **zero** `sorryAx`, **zero** `Classical.choice`, zero `native_decide`, zero `axiom`, zero `sorry` (the two source hits for those words are in the header prose). Ceiling `[propext, Quot.sound]`. The modeler's reported counts are accurate.

### 5.2 The receipts that carry the design

Verbatim from the run, namespace stripped for width:

```
'Tgt_is_exceptT_over_state'            does not depend on any axioms
'ensuringExitT_diagonal'               does not depend on any axioms
'ensuringExitT_runs_on_failure'        depends on axioms: [propext]
'ensuringExitT_never_replaces'         depends on axioms: [propext]
'ensuringExitT_reads_the_exit'         depends on axioms: [propext]
'acquireT_registers'                   depends on axioms: [propext]
'acquireT_registers_nothing_on_failure' depends on axioms: [propext]
'registration_is_LIFO'                 depends on axioms: [propext]
'scopedT_releases_on_failure'          depends on axioms: [propext]
'scopedT_state_is_the_drains'          depends on axioms: [propext]
'scopedT_restores_the_stack'           depends on axioms: [propext]
'demo_success_releases_LIFO'           depends on axioms: [propext]
'demo_failure_releases_LIFO'           depends on axioms: [propext]
'lift_injSvc'                          depends on axioms: [Quot.sound]
'lift_hom'                             depends on axioms: [propext, Quot.sound]
'lift_inj'                             depends on axioms: [Quot.sound]
'andThen_assoc'                        depends on axioms: [propext, Quot.sound]
'layer_monoid_is_through_monoid'       depends on axioms: [propext, Quot.sound]
'Layer.provideMerge_assoc'             depends on axioms: [propext, Quot.sound]
'Layer.run_provideMerge'               depends on axioms: [propext, Quot.sound]
'unwrap_is_join'                       does not depend on any axioms
'shared_is_bind'                       does not depend on any axioms
'provide_requires_mem'                 depends on axioms: [propext, Quot.sound]
'provide_removes_supplied'             depends on axioms: [propext, Quot.sound]
'provide_keeps_unsupplied'             depends on axioms: [propext, Quot.sound]
'provideMerge_requires_assoc'          depends on axioms: [propext]
'provide_requires_not_assoc'           does not depend on any axioms
'mergeOn_unique'                       depends on axioms: [propext, Quot.sound]
'build_forwards_of_not_provides'       depends on axioms: [propext, Quot.sound]
'provideMerge_discharges'              depends on axioms: [propext, Quot.sound]
'provides_can_overclaim'               depends on axioms: [propext]
'provide_is_not_associative_in_the_meaning' depends on axioms: [propext]
'ScopeM_is_Tgt'                        does not depend on any axioms
'sys_row'                              does not depend on any axioms
'launch_acquires_and_releases_LIFO'    depends on axioms: [propext]
'launch_releases_on_failure'           depends on axioms: [propext]
'unscoped_launch_leaks'                depends on axioms: [propext]
'build_registers_one_finalizer'        depends on axioms: [propext]
'inlined_registers_two_finalizers'     depends on axioms: [propext]
'build_step_is_observable'             depends on axioms: [propext]
'the_word_alone_is_vacuous'            depends on axioms: [propext]
```

From `minimal.lean`, the sharing result: `topological_order_shares = [7,1,2]`, `tree_elaboration_does_not = [7,1,7,2]`, `sharing_is_the_order`, all axiom-free.

Mine, this session: `earlier_is_shadowed` — `[propext, Classical.choice, Quot.sound]`, the `Classical.choice` inherited from `canonServices_last_wins` (checked: that theorem carries the same three).

**Two results are worth naming because they are non-obvious.**

*The build step's honest observable is the finalizer stack, not the word.* `build_registers_one_finalizer = [1]` against `inlined_registers_two_finalizers = [1,1]`, separated by `build_step_is_observable` — and then `the_word_alone_is_vacuous`: both designs leave the *same word*. `put` is word-idempotent, so a sharing law stated over the word is a vacuity. The requirements lane's "the memoization law is vacuous at `ObsEq`" is therefore a fact about acquisition, not about sharing, and any future row stating a sharing law over the word alone states nothing.

*Non-vacuity against the estate's own store.* The scope demo's blocks are real `Prog CasSig` programs run through a handler built from `referenceHandler` (`Cas/Lang/Handler.lean:78`) with the estate's `Falsifier.lenAddr` as the address function, so nothing digests in the kernel and the release order is *read off the word*: `[0, 2, 3, 1]` — acquire-outer, acquire-inner, release-inner, release-outer — identical on the success and the refusal paths.

### 5.3 What the model could not do

1. **`requires`-soundness** — the dual of the bridge. Not proved. §3.3 item 1.
2. **The bridge's converse is FALSE**, exhibited (`provides_can_overclaim`). A result, not a gap.
3. **The floor is not stratified** — an acquisition block cannot ask for a service.
4. **No concurrency, fibers, interruption, or parallel scope.**
5. **`Layer.merge` with a build prefix is not lifted** — `mergeOn`/`mergeOn_unique` are at the value plane only.
6. **The rows are pre-canonicalization** — plain `++`/`filter`, not `canonServices`.
7. **Nothing in `library/` was touched**, so the `#guard` after the arm is untested.
8. **Finalizers are total** in every witness.
9. **The dynamic fragment** (`unwrap`/`flatMap`/`suspend`/`catchCause`) has no content-plane description; it goes to `SystemNode.opaque`, and sharing does not cross an `opaque` boundary where rc.112's memo map does. Declared divergence.
10. **`launch` claims no law** beyond the region laws it inherits; its real laws are blocked on the interruption bundle.

### 5.4 What I did not check, stated plainly

* **No rc.112 source was read this session.** Every claim about `Layer.ts`, `Context.ts`, `Scope.ts`, `internal/effect.ts` — the single `build` member, `in ROut`'s contravariance, `MemoMapImpl`'s reference-keyed map, `Layer.fresh`'s empty memo map, `mergeAll`'s parallel scope, `Context.add`'s last-wins, the absence of a `memoize` export — is taken from the ground and convergence reports as reported. §3.4's reconciliation depends on rc.112's `provideMerge` and I could not settle it.
* **No pinned PDF was read.** The interaction-trees cluster (HITrees, arXiv:2510.14558; Guarded Interaction Trees, arXiv:2307.08514) is named in `ground-literature.md`; I did not open either and **no conclusion in this plan rests on any paper**.
* I did not re-run `propose-*.lean` or `judge-*.lean`, nor `EnsuringRepair.lean`; I read the latter's declarations at the cited lines.
* I did not read `workshop/s1/` or `workshop/s2/` and did not touch them.
* The claim that a *service context must not be able to intercept a scope operation* (§1.1) is **ARGUMENT**. So is §6's decisive consideration.

---

## 6. The residual disagreement, located exactly

The five designers converged. The minimizer and the modeler did not, and their split is one question with a clean statement.

> **CRUX. Is a layer's RELEASE separately addressed on the content plane?**
>
> Does `SystemNode` grow `| scoped (acquire release : CodeRef) (provides : ServiceRef) (requires : List ServiceRef)` — or does acquisition stay inside a single `CodeRef` whose host meaning is `Effect.acquireRelease(acq, rel)`, leaving `SystemNode` untouched?

**Who holds which side.** The **minimizer** holds NO: acquisition lives inside the constructor, exactly where rc.112 puts it; `SystemNode` is unchanged; **zero address-moving events**; the `#guard` is never at risk; and it deletes the largest item any lane put on the ledger. The **modeler**, and positions A, B, D and E, hold YES: the arm is the sanctioned growth path, and it buys a content-decidable `acquiring` classifier where rc.112's `Exclude<R, Scope>` hides the fact.

**What settles it — and it is a two-line experiment nobody ran.** Ask whether the floor's finalizer stack can stay first-order under NO.

If the release is reachable only inside the acquire's host closure, then the value the floor pushes onto `FinStack` is a host function. `ScopeState`'s second component leaves the content plane; R18's ruled state stops being `Word`-shaped; and any word-exact equation between the scoped run and the estate's `run`/`interpretRefW` breaks. Position D named that obstruction and did not connect it to the arm; the minimizer's probe hides it behind `(c + 100)`, deriving a release id from an acquire id — which is available for `Nat` and is not available for `CodeRef`. If, on the other hand, a first-order stand-in exists — the acquire's own `CodeRef` serving as the release *key*, with the host holding the acquire→release table — then the stack stays `List CodeRef`, the arm is unnecessary, and the minimizer is right.

**The experiment:** define `FinStack := List CodeRef` with the floor's resolver mapping an ACQUIRE `CodeRef` to a release action, and check whether the resulting run still satisfies the word-exact equation with the estate's `run`. An afternoon. It is decidable, it is cheap, and it decides an address-moving event.

**My recommendation, held with medium confidence and marked ARGUMENT:** pay the arm. The reasoning above is not kernel-checked, and I would not spend the address-moving event before someone runs the experiment. Two facts bound the cost either way: `library/cas/tools/EmitLayers.lean` authors 18 nodes and **none of them acquires today**, so the migration is one file; and `System.lean` already paid this once and argued *"it will never be cheaper."*

**Secondary, mechanically decidable, and untested by anyone:** does an eighth arm keep `#guard SystemNode.schemaCode.discriminated` (`Cas/Schema/System.lean:225`) passing? No agent in this pass was permitted to edit `library/`. Whoever owns the file should check this **before** the crux is argued further, because a negative answer settles it.

**Third, and I rule on it rather than leaving it open:** one flat signature (minimizer) versus two summands plus `lift` (modeler). I rule for two summands, for the reason in §1.1, and I note that `PROOF-DAG.md` §7's closing paragraph already rules the adjacent point — *"Scoped children are `BlockId`s interpreted by the same existing `Handler` carrier … That scoped interpretation is direct; it is not an application of `Handler.through`. `Handler.sum` handles same-target signature composition, while `Handler.through` discharges only the separately typed `Prog T` tower case."* The recommended design is that paragraph, made concrete. The cost of my ruling is three one-line lemmas; the cost of the alternative is a hand-written passthrough in every leaf that nothing checks.

---

## 7. What this changes in the packet

I own none of these files. Everything below is **proposed**.

### 7.1 `EC1-XT104` — `effect/Layer::Layer<ROut,E,RIn>`, `separateCalculus`

**CONFIRMED in substance; the annotation understates and mis-locates the separation.** Layer does remain a dependency/resource-building calculus with a typed lowering, and it is not flattened into a single service operation. But the separation is **entirely on the content plane**: `SystemNode`/`LDesc` is the separate calculus, and its denotation is the *existing* `Handler` algebra with no new carrier — `provideMerge` is `Handler.through`, `empty` is `idHandler`, and the composition laws are `through_monoid`. Proposed annotation amendment:

> Layer remains a dependency/resource-building calculus **on the content plane** (`Cas.Schema.SystemNode`), with a total lowering into scoped Core. It is not flattened into a single service operation. **The lowering mints no semantic carrier: a built Layer is `Handler SvcSig (Prog LayerSig)` and layer composition is `Handler.through`, with associativity and both units discharged by `through_monoid` (`Cas/Backend/Universal.lean:785`).** The reification obligation is that rc.112's `Layer` has one non-phantom member and it is a closure, so v1 supplies the first-order object the pin never had.

### 7.2 `EC1-XT106` — `effect/Scope::Scope` and resource APIs, `bridge`

**CONFIRMED exactly, and the design is a concrete realization of it.** Explicit regions (`scoped`), registrations (`acquire` pushing onto `FinStack`), ownership (the region that registered owns the release), finalization (`drainT` / `ensuringExitT`); and no host scope object enters content — `FinStack` is `List CodeRef`. Proposed addition, because four of five designers spent effort deciding something this row is silent on:

> **Scope is a signature summand of the layer language, not a carrier and not a per-layer target.** Its operations' children are `CodeRef`s (R18 clause 1; no `HHandler`). The region combinators live at the target monad and appear **once**, at the floor — so `Handler.through` composes an acquiring layer like any other and FORK A is a single global choice, not a per-layer restatement.

### 7.3 `REIFICATION-CHECKLIST.md:885` — the `LayerCore` row

Two proposed amendments, both kernel-backed.

* Strike **"memo key"** from the component list. Sharing is the elaboration ORDER over `EmitLayer.Resolved`'s children-first table (`:236`), not a keyed lookup; there is no memo map, no memo key, and no fuel. Replace with *"elaboration in the resolved children-first order, one visit per address."*
* Split **"identity/associativity for typed composition."** Associativity holds for `provideMerge` — as a literal list equality on the row, and in the meaning — and **fails for `provide`**, at both planes, because `provide` masks to the outer's services. Both are kernel-checked. A single row claiming associativity for "typed composition" is false as written.

### 7.4 `PROOF-DAG.md` §8 — the scope/resource bundle

`EC1-T061` (`register_atomic`), `EC1-T063` (`release_zero_unregistered`), `EC1-T064` (`release_lifo`) and `EC1-T065` (`scope_waits_cleanup`) now have model-level witnesses (`acquireT_registers`, `acquireT_registers_nothing_on_failure`, `registration_is_LIFO`, `scopedT_state_is_the_drains`), as does `EC1-T059` (`ensure_runs_after_failure`, via `scopedT_releases_on_failure`). None is promoted; they are staging. Two row corrections proposed:

* `EC1-T064` must carry the **sequential-strategy premise** explicitly, and `EC1-T066` inherits it.
* The §7 note that `EC1-T057T` is the only `Handler.through` case should be extended: `Handler.through` *also* carries the whole of layer composition, via `through_monoid` at the lifted endomorphism setting.

### 7.5 New rows owed

* **`COUNTEREXAMPLES.md`** — the residual row can **over-claim**: two mutually-implementing layers compose into a context that advertises a key it forwards, and no check on the description catches it because bodies are opaque `CodeRef`s. `provides_can_overclaim`, `[propext]`.
* **A reconciliation row** for §3.4 — the shipped `residualOf` and any `Handler.through` denotation shadow a duplicate key in opposite directions.
* **Withdraw** the packet-wide finding that `through_monoid` (`Universal.lean:785`) is refuted as the composition anchor. It is the anchor, reached through `lift`. Four of five lanes adopted the refutation and it should not propagate further.
* **Retire** the "`SystemNode` has zero theorems" claim wherever it appears. `Cas/Backend/Canon.lean` carries 31 theorem declarations (18 public), four of them about `SystemNode` term and address identity: `systemNode_authored_stable` (:508), `systemAddressOf_authored_stable` (:531), `systemNode_canon_stable` (:545), `systemAddressOf_canon_stable` (:556). `grep -c theorem Cas/Backend/EmitLayer.lean` → 0 is a fact about that one file.

---

## 8. Confidence

**KERNEL — rests on files that compile and that I ran myself:** the carrier and both `abbrev`s; every composition law and its estate anchor; the build step's necessity and its observable; the R18 region laws and exit-indexing's conservativity; the residual-row laws including `provide`'s non-associativity at both planes; the bridge's sound direction and its false converse; sharing-by-elaboration-order; the shadowing direction on the row; and every `file:line` citation in §3, each of which I opened this session.

**ARGUMENT — reasoned, not checked:** the two-summand ruling (§1.1); the finalizer-stack-must-be-first-order consideration that decides the crux (§6); the practical reach of §3.4; the effort estimates in §3.3.

**TAKEN AS REPORTED — not verified by me:** everything about rc.112. I read no Effect source this session.

**UNTESTED BY ANYONE:** whether an eighth `SystemNode` arm keeps `#guard SystemNode.schemaCode.discriminated` passing.
