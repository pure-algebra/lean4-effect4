# Design C2: the verdict seam, flexible

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# Seam: checking and verdicts. One key, one verdict type, one law

The main idea: every checking question becomes one constructor of a first-order `CheckInput`. One total function, `eval : CheckInput → Verdict`, answers it by calling the existing owners. Each question also has a static decomposition into sub-questions, `deps` and `combine`. Each backing (memory, the store, later Incremental) only has to show that its answers to the sub-questions equal `eval`. The profiles are data inside the key, so they share part entries automatically.

## 1. Interface

**Placement.** The seam goes in `src/Effect4/Program/Check/`, below `Api`. `Api/Built.lean` imports `Effect4.Api`, and `Run/Basic.lean` imports `Api.Built`, so the seam cannot import `Run`. The pure folds it needs move down into it and are re-exported from their old namespaces:
- `Run.Tree.armOf` and `outsideAt`;
- from `Run.Preview`: `rowIsGeneric`, `hasHandle`, `rowFaultAt` and `outsideProfileAt`.

The store adapter sits above the codecs, in `src/Effect4/Api/CheckStore.lean`.

```lean
namespace Effect4.Program.Check
inductive RefMode | asWritten | throughRefs        -- Sketch.check | Sketch.sourceCheck
structure Gates where                              -- flags in admission's fixed order: one spelling per profile
  signature formation columns tree rows : Bool := false
structure Profile where refs : RefMode; gates : Gates
inductive ProfileName | raw | source | kit | admission | preview
-- raw ⟨asWritten,{}⟩; source ⟨throughRefs,{}⟩; kit ⟨throughRefs,{signature,columns}⟩ (R13: no formation);
-- admission adds formation; preview adds tree and rows

inductive CheckInput where                         -- the complete key
  | part      (sig : SigData) (env : TyEnv) (program : NativeEff)   -- today's CheckKey: the unit of sharing
  | signature (app : SigApp)                                         -- admitSig: shared by every program
  | entry     (refs : RefMode) (app : SigApp) (sketch : Sketch) (path : List Nat)
  | fit       (refs : RefMode) (app : SigApp) (base : Sketch) (path : List Nat) (candidate : NativeEff)
  | whole     (profile : Profile) (app : SigApp) (sketch : Sketch)
  -- appended, never renumbered: partSparse (Incremental), …

inductive Fit | exact (ty : EffTy) | mismatch (expected actual : EffTy) | refused (why : TypeRefusal) | noFocus
inductive Refusal                                  -- AdmitRefusal ∪ Preview.Refusal, with typing located
  | signature (why : SigRefusal) | formation (why : Formation.Refusal) | typing (why : TypeRefusal)
  | columns («at» : Path) | tree (path : List Nat)
  | genericRow (path : List Nat) (row : Nat) | handleAnswer (path : List Nat) (row : Nat)
inductive Verdict
  | part (answer : Except TypeRefusal EffTy) | signature (answer : Except SigRefusal Unit)
  | entry (entry : Table.Entry) | fit (fit : Fit) | whole (answer : Except Refusal EffTy)

def eval : CheckInput → Verdict                    -- the uncached meaning
def CheckInput.rank : CheckInput → Nat             -- part, signature 0; entry, fit 1; whole 2
inductive KeyPolicy | dense                        -- sparse appended later
def CheckInput.deps    (pol : KeyPolicy) : CheckInput → List CheckInput
def CheckInput.combine : CheckInput → List Verdict → Verdict
def CheckInput.blamed  : CheckInput → List Verdict → Option (Nat × List Nat)   -- which dep refused, at what base
```

**What `eval` calls.**
- `part`: `Checker.check sig.signature env [] q`.
- `signature`: `admitSig`.
- `entry`: `Sketch.tableEntry` or `Sketch.sourceEntry`.
- `whole`: the gates run in a fixed order, the first refusal wins:
  1. signature (`admitSig`)
  2. formation (`Formation.checkInput`)
  3. references (`Eff.firstRefFault`)
  4. typing (`Checker.checkModule` on the expansion or the program as written)
  5. columns (`findEmptyColumnInEffTy`)
  6. tree (`outsideAt`)
  7. rows (`outsideProfileAt`)

Each gate reads what its owner reads: formation, tree and rows read the program as written, typing reads the expansion. All of them read `app.withHoles sketch.holes`.

**What `deps` reads.** The decomposition is static (applicative).
- A `whole` reads `signature` if that gate is on, then the module's parts as `Eff.partAt` carves them:
  - each body at `.body decls params`, with its declared request as environment;
  - the main program and `Part.layersProgram` at `.block decls`, with environment `[]`;
  - all of them at path `[]`.
- An `entry` or a `fit` reads the parts at its address. Its environment comes from `Node.envAt`, which is a traversal, not a cached check.
- `combine` keeps `checkModule`'s order: block length, then each body (`formed`, its part, `admits`), then main, then the layers.

**The memory cache**:

```lean
structure Entry where input : CheckInput; verdict : Verdict
inductive Provenance | computed | memory | extended | store      -- never inside a Verdict
structure Answered where verdict : Verdict; provenance : Provenance; hits computed : Nat
structure CheckCache where
  private mk ::
  entries : List Entry
  built   : ∃ asked : List CheckInput, replay asked = entries      -- erases; FillSet's witness pattern
def CheckCache.find    (c : CheckCache) (i : CheckInput) : Option Verdict
def CheckCache.answer  (c : CheckCache) (pol : KeyPolicy) (i : CheckInput) : CheckCache × Answered
def CheckCache.explain (c : CheckCache) (i : CheckInput) : CheckCache × Option Explanation
```

- `answer` is total. On a hit it returns the verdict. On a miss it answers each dependency in order, runs `combine`, and inserts the result. So there is at most one entry per input.
- A positive `part` verdict also answers at a prefix extension of the rows (`SigData.extendsB`, provenance `extended`). This works in memory only.

**Explanations**:

```lean
inductive Site | address (path : List Nat) | inCopy (site path : List Nat) | column («at» : Path) | application
structure Explanation where
  refusal : Refusal; site : Site            -- whole-program address; where to draw it in the sketch as written
  part : Option CheckInput; base : List Nat; «local» : Option TypeRefusal   -- replayable evidence
def Explanation.blame : Explanation → Option (List Nat)
def Api.explain (p : Program) (app : SigApp) := …  -- projection of whole source at holes []
```

When `Table.belowSite (Sketch.sites s) path` holds, the site is `inCopy`: the refusal stands inside a reference's copy, so the document marks the reference.

**Suggestions.** `suggest c (d : Doc) path cursor limit supplied : CheckCache × Except SuggestRefusal SuggestAnswer`.
- Candidates come from `CheckCache.localCandidates`, and each one is one `fit .throughRefs` query.
- The answer lists each candidate's `Fit` and its `part` input, whose digest is its action key. The answer holds no cache.
- `noProgram` or `noFocus` refuses the whole request and leaves the cache unchanged. A refused candidate is an item inside a successful answer.

**The store tier.** Kinds 8 and 9 are already in the table, and this is their consumer.

```lean
structure Query where engine : Digest; input : CheckInput       -- Content, kind query (8)
structure Recorded where query : Ref Query; verdict : Verdict   -- Content, kind result (9)
inductive ActionOutcome | fresh | duplicate | poisoned (resident : Verdict)
def ActionCache.find   (s : Store) (q : Query) : Option Verdict
def ActionCache.record (s : Store) (q : Query) (v : Verdict) : Except Admission (ActionOutcome × Store)
```

- `engine` is C7's key of the lowered checker, so a stored verdict answers only the engine that computed it.
- `record` puts the query node, then the result node. Admission refuses a result whose query is absent (`dangling`).
- If a different verdict is already resident, `record` answers `poisoned` and writes nothing.
- The action index is the set of result-kind dependents of a query address (`E4_deps.dependents_of`). It is a derived index (E4_deps rule DP1: rebuild equals incremental).
- Gaps to fill:
  - a new `Check` group for the generated codecs, with `--kind query` and `--kind result`;
  - a codec for `SigApp`, which the manifest does not have yet.

**OCaml spelling**:

```ocaml
module Effect4.Program.Check : sig
  module Input : sig type t = … end   module Verdict : sig type t = … end      (* generated, concrete *)
  val eval : Input.t -> Verdict.t
  val deps : Key_policy.t -> Input.t -> Input.t list
  val combine : Input.t -> Verdict.t list -> Verdict.t
  module Cache : sig type t (* abstract: rule 1 *) val empty : t
    val answer : t -> Key_policy.t -> Input.t -> t * Answered.t end
end
module type VERDICT_STORE = sig type t
  val find : t -> Query.t -> (Verdict.t, Verdict.t list) result option     (* Error: poisoned *)
  val record : t -> Query.t -> Verdict.t -> Action_outcome.t end
module Tiered (S : VERDICT_STORE) : sig
  val answer : S.t -> Cache.t -> ?verify:bool -> Input.t -> Cache.t * Answered.t end
```

`?verify` is C6's determinism mode: it recomputes a store hit and compares.

## 2. Worked calculation

**Values:**
- `app = {rows := [log]}`, where `log : Text → Unit`.
- `greet`: request `Text`, answer `Unit`, no parameters. `T = ⟨Unit, never, ∅⟩`.
- `B = .perform (.external 0) (.var 0)` and `L0 = .succeed K v`.
- `M = .provideLayer (.ref [2,0]) false (.perform (.call 0) (.lit "hi"))`. `M'` is `M` with `L0` in place of the reference.
- `s = {program := .defs [greet] (.cons B .nil) M (.cons L0 .nil)}`, so `Sketch.sites s = [[1,0]]`.
- `σb = ⟨app,[],.body [greet] []⟩` and `σk = ⟨app,[],.block [greet]⟩`.
- The part keys:
  - `q1 = part σb [Text] B`
  - `q2 = part σk [] M`
  - `q2' = part σk [] M'`
  - `q3 = part σk [] (Part.layersProgram (.cons L0 .nil))`

| # | Call | Work | Answer | State | Law |
|---|---|---|---|---|---|
| 0 | | | | `c0 = empty` | |
| 1 | `answer c0 dense (whole raw app s)` | deps `[q1,q2,q3]`, all misses: `q1 ↦ ok T`; `q2 ↦ error ⟨[0], layerReference [2,0]⟩` (`checkLayer`'s `ref` arm); `q3 ↦ ok` | `greet` admits `T`; main's refusal moves below `[1]`: `whole (error (typing ⟨[1,0], layerReference [2,0]⟩))`. 0 hits, 4 computed | `c1 = {q1,q2,q3,w_raw}` | `eval_unfold` (`check_rebase`); `eval_raw` |
| 2 | `explain c1 w_raw` | all hits | site `address [1,0]` (the reference site itself), part `q2`, base `[1]`, local `⟨[0],…⟩`; blame `[1,0]` | `c1` | `explain_replays` |
| 3 | `answer c1 dense (whole source app s)` | `firstRefFault = none` (a module layer: before the site, in scope); deps `[q1,q2',q3]`: **q1 and q3 hit**; `q2' ↦ ok T` | `whole (ok T)`. 2 hits, 2 computed | `c2 = c1 + {q2', w_src}` | `find_sound`; `eval_source` |
| 4 | `answer c2 dense (whole admission app s)` | deps `[signature app, q1, q2', q3]`: parts hit, signature computed; `combine` runs formation and columns | `whole (ok T)`. 3 hits, 2 computed | `c3 = c2 + {sig, w_adm}` | `eval_admission` |
| 5 | `answer c3 dense (fit throughRefs app s [0,0] B)` | the focus at `[0,0]` is `q1` (`Part.bodyAt`, `sketchSigData`); the candidate's key is `q1` too | `fit (exact T)`. 2 hits, 1 computed | `c4` | `fit_certified` |
| 6 | `s₂ := s` with `L0✗ = .effect K e✗`, where `e✗` is refused for reason `r`; `answer c4 (whole source app s₂)` | `q1` hit; `q2'₂ ↦ error ⟨[0,0], r⟩`, inside the copy; `q3₂ ↦ error` | `whole (error (typing ⟨[1,0,0], r⟩))`; its explanation has site `inCopy [1,0] [1,0,0]`. Under raw, `s₂` still hits `q2`, because `M` is unchanged | `c5` | `explain_replays`; `Table.belowSite` |
| 7 | `record S ⟨e, w_src⟩ (whole (ok T))`, then the same key with a different verdict | first call puts the query node, then the result node | `fresh`, then `poisoned (whole (ok T))`; the store is unchanged | `S'` | `record_poisoned` |

## 3. What the implementation hides

It hides the decomposition, the order of the sequence, the provenance counters, and the address relocation: bodies and main move by rebase, and the layers map `0::0::r ↦ 2::r`.

What moves behind the seam:
- callers of `Sketch.check` and `Sketch.sourceCheck`;
- `Api.explain` and `Api.blame`, which become projections;
- the gates of `Run.Kit.check` and `Run.Kit.admit`;
- the `check` arm of `Tools.Query`;
- the refusals of `Run.Preview.admit` (its certificate stays with the owner);
- the tool state's `cache` field.

From `CheckCache.lean`:
- `CheckKey` becomes `part`, and `Entry` moves into the seam;
- `lookup` and `insert` become `find` and `answer`;
- `evaluateCandidate` and `evaluateCandidates` become `fit` queries;
- `Evidence.fromCache` goes, because provenance is not part of the meaning, and `SuggestResult.cache` goes too.

`certifiedB` (in `FillSet.lean`) becomes a `fit` query. That makes a mismatch visible: by reading, `certifiedB` uses the raw profile (`Sketch.focusAt`, `Sketch.sigAt`), while `materialize` uses `sourceCheck`. So a fill whose environment reads past a layer reference has no raw focus. This is untested.

These stay as owners: `Checker`, `SigData`, `partSigAt`, `sketchSigData`, `Table`, `admitProgram`, and `Preview.admit` for its certificate.

## 4. Adapters

| Seam | Adapters | Category |
|---|---|---|
| backing | memory list (now); store action cache over `E4_cas` (C6); Incremental graph (later); shared cache (hypothetical) | in-process; local-substitutable; in-process; owned remote |
| key policy | `dense` now; `sparse` later | in-process |
| profile | five named profiles, or any `Gates` value | data |
| candidates | the local harvest and supplied programs; a scope-shifted source later (slice F) | in-process |
| face | Lean; lowered OCaml | in-process |

The memory and store backings exist now, so the backing seam is real.

## 5. Laws

- `find_sound`: a memory hit is `eval`. Generalizes `CheckCache.lookup_sound`; `Valid` comes from `built`, as `FillSet.add_wf` does.
- `eval_unfold`: `eval i = combine i ((deps pol i).map eval)`. Reuses `check_rebase` and the definitions. The layers step is a new lemma built on `checkLayers_rebase`.
- `deps_rank`: every dependency has a lower rank.
- `oracle_sound`: any `ask` that agrees with `eval` on `deps i` gives `combine i (map ask) = eval i`. This is the one law every backing instantiates.
- `answer_eq_eval`: `Valid c → (c.answer pol i).2.verdict = eval i`, and `answer` keeps `Valid`. This is the Incremental pass's acceptance stated in Lean.
- `eval_raw`, `eval_source`, `eval_kit`, `eval_admission`, `eval_preview`: each forgetful map equals its owner. They reuse `Sketch.check_program`, `Sketch.sourceCheck_toOption`, `Sketch.sourceCheck_of_admitted` (branch) and `admitProgram_signature`.
- `entry_table`: `entry` equals `sourceEntry`. Reuses `Sketch.sourceAnnotate_eq_sourceTable`.
- `fit_certified`: `fit` equals `certifiedB` with its exact type. Reuses `CheckCache.evaluateCandidate_valid_and_sound` and `sketchSigData_signature`.
- `explain_none_iff`: generalizes `Api.explain_none_iff`.
- `explain_replays`: `eval part = .part (.error local)`, and `refusal = local.rebase base`. Reuses `check_rebase`.
- `deps_shared_of_refSites_nil`: with no reference sites, the raw and source profiles have the same dependencies. Reuses `expandRefs_eq_self_of_refSites_nil`.
- `record_sound` and `record_poisoned`: a recorded verdict is `eval`, and a poisoned put changes nothing. Reuses `putNode_ok` and, in Rocq, `put_conflict_collision`.
- Two keys share an address only with an exhibited collision: `address_eq_or_collision`.

## 6. Trade-offs

**Where leverage is high:**
- One key and one law serve every backing.
- The kit, preview and admission profiles become named restrictions of admission (slice S4's goal), and they share all their part entries.
- An explanation is replayable evidence: a single part query a receiver can recompute.
- Later, the key is the dependency set. Incremental keys `Incr_map` by part digest, uses `map` for `combine`, and cuts off when a key's digest is unchanged (rule 5). `E4_deps` gives the reverse edges on disk.

**Where it is thin:**
- Dense keys contain the whole `SigApp` and every declaration, so they break rule 4 (exact dependencies). After an omission adds a hole row, only positive part verdicts survive (through `extendsB`). The fix is the later `partSparse` constructor: the rows the part performs by position, and the declarations it invokes by index. `check_restrict` proves it equal to the dense key, refusals included, given `SigProgram`.
- A `whole` key hashes the entire sketch on every lookup.
- Query nodes inline the program's bytes.
- The cache returns verdicts, not `AdmittedProgram`. `start` still reruns `admitProgram`: a refusal may come from the cache, a certificate cannot, because the core cannot cite `check_rebase`.

**What this makes hard later:**
- Each new question costs a constructor, an `eval` arm, the `deps` and `combine` arms, an unfolding law and a codec.
- Any change to the checker changes `engine` and invalidates the store, by design.
- Constructors must stay append-only under the wire-tag ledger.

### Critical Files for Implementation
- /Users/pooks/Dev/lean4-effect4-gemini/src/Effect4/Program/Typing/CheckCache.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/Source.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Definitions.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Admission.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Store.lean

