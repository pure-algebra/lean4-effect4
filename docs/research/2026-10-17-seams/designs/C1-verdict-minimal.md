# Design C1: the verdict seam, minimal

Status: design (history, not authority), one of nine in the seams round; see `../brief-common.md`.

# Checking and verdicts: one key, one function, three entry points

Note: main moved during this round. `refactor/phase1-phase3` is now at `774ddc3d7`, which merges the authoring branch. `CheckCache.lean`, `FillSet.lean` and `SourceDocument.lean` are on main with the same contents as the branch's repaired worktree. Paths below are main's.

## 1. Interface

There is one new core module, `src/Effect4/Program/Typing/Check.lean` (namespace `Effect4.Program.Check`).

```lean
/-- Everything one check reads; `run` takes nothing else, so `toVal` of it is a complete key. -/
inductive CheckInput where
  | module (app : SigApp) (holes : RowTable) (program : NativeEff) -- a sketch, through its references
  | part (sig : SigData) (env : TyEnv) (program : NativeEff)      -- a program in a context
deriving DecidableEq

/-- The answer at the empty base path. -/
structure Verdict where
  result : Except TypeRefusal EffTy
  table  : List Table.Entry
deriving DecidableEq

def run : CheckInput → Verdict
  | .module app holes p => ⟨Sketch.sourceCheck ⟨p, holes⟩ app, Sketch.sourceAnnotate ⟨p, holes⟩ app⟩
  | .part d env q => let o := Annotate.check d.signature env [] q; ⟨o.2, o.1⟩

/-- The expansion's parts, each at its base: the declared bodies, then main. `[]` for a part. -/
def deps : CheckInput → List (List Nat × CheckInput)
/-- The module from its parts' verdicts, in `deps` order. It runs the length, `formed` and `admits`
checks, `checkLayers`, and `Table.atSource`. A missing verdict is computed by `run`. -/
def combine : CheckInput → List Verdict → Verdict
```

Readings are accessors, not entry points:

```lean
def Verdict.focus (v : Verdict) (a : List Nat) : Option (TyEnv × EffTy) := Table.typedAt v.table a
def Verdict.placed (a : List Nat) (v : Verdict) : Verdict   -- refusal and entries moved below `a`
def CheckInput.fill (app : SigApp) (s : Sketch) (whole : Verdict) (a : List Nat) (q : NativeEff) :
    Option CheckInput :=                                    -- none: the root, or no typed focus
  if a = [] then none else (whole.focus a).map fun (env, _) => .part (sketchSigData s app a) env q
def certifies (whole loc : Verdict) (a : List Nat) : Bool :=
  (whole.focus a).any fun (_, ty) => decide (loc.result = .ok ty)
```

| Question | Call |
| --- | --- |
| whole-sketch verdict | `(run (.module app s.holes s.program)).result` |
| verdict at an address | the entry at `a` in that verdict's `table` |
| the type a hole expects | `(run (.module …)).focus a` |
| fill certification (`certifiedB`) | `CheckInput.fill … a q`, then `certifies whole (run it) a` |

**Invariants and ordering:**
- `run` is total, and a type refusal is a verdict, not a seam refusal.
- Verdicts are computed at base `[]`. A caller places one with `placed a`.
- `combine` reads its list in `deps` order.
- The seam's only refusal is `CheckInput.fill`'s `none`.

| Checker today | After |
| --- | --- |
| `Sketch.sourceCheck` | the module arm's result; it stays as the specification |
| `Tools.Query` `check`, `table`, `refusals`, `focus` (today `Sketch.check`, as written) | calls of `run (.module app holes p)`; answers change only for layer references, where they now agree with admission |
| `certifiedB`, `Tools.Query.fillPremises` (`effTy`), `CheckCache.evaluateCandidate`, the splice check in `EditSession.feed` | calls of the part arm |
| `Api.check` | named restriction: holes `[]`; its refusal is `run`'s, and it rebuilds its certificate by `checkTypedProgram` |
| `Run.Kit.check` (the kit profile) | named restriction: `(run (.module app [] p)).result`, a monomorphic LCNF root |
| `Run.Preview.admit` (the preview profile), `admitProgram` | admission, not checking; they rebuild their certificates and read no cache |
| `Sketch.check` | used inside laws only; no tool calls it |

The store side is a new module, `src/Effect4/Store/Domain/Answer.lean`:

```lean
structure Query where          -- Content at kind `query` (8); its address is the action key
  engine : Digest              -- the checker's own code (C7): the one input no Lean value holds
  input  : Check.CheckInput
structure Answered where       -- Content at kind `result` (9)
  query   : Ref Query          -- an edge: admission refuses it `dangling` or `wrongKind`
  verdict : Check.Verdict
inductive Recall where | miss | hit (v : Check.Verdict) | poisoned (vs : List Check.Verdict)
def Store.recall (s : Store) (k : Ref Query) : Recall   -- the result nodes that name `k`
```

- **The action cache is the object store plus its dependents index.** It needs no new table and no new kind.
- **Writes go through `Store.putNode`, query first.**
- **A second, different `Answered` for one key is never an overwrite.** It is a fresh node beside the first, and `recall` reports `poisoned`.

The OCaml spelling:

```ocaml
module Effect4.Check : sig          (* generated; concrete types (estate rule 4) *)
  val run : Input.t -> Verdict.t
  val deps : Input.t -> (int list * Input.t) list
  val combine : Input.t -> Verdict.t list -> Verdict.t
end
(* boundary code in effect4_tool: the one memo loop, which decides nothing *)
val ask : E4_cas.t -> engine:E4_addr.Addr.t -> mode:[`Trust | `Verify] ->
          Effect4.Check.Input.t -> Effect4.Check.Verdict.t
```

## 2. A worked calculation

The abbreviations are `toVal` trees, with wire tags from `tools/Effect4Gen/wire-tags.json`. A structure is `ctor 0`.

- **Types and records:**
  - u = `ctor 1[]` (unit), n = `ctor 2[]` (nat), s = `ctor 4[]` (string), ⊥ = `ctor 0[]` (never).
  - A = `ctor 0[list[],list[],list[]]` (the empty `SigApp`).
  - h = `Row.hole "h" .nat` = `ctor 0[str"h",str"h",ctor 0[],list[],ctor 1[],u,n,⊥,list[],str"",list[],ctor 1[]]`.
  - d0 = `ctor 0[str"greet",u,s,⊥,list[],ctor 0[],list[]]`; d1 is the same with `str"count"` and n.
  - Db = `ctor 0[A,list[h],ctor 2[list[d0,d1],list[]]]` (PartSig.body); Dm = `ctor 0[A,list[h],ctor 1[list[d0,d1]]]` (PartSig.block).
- **Programs:**
  - `succeed t` = `ctor 0[t]`; `lit` = `ctor 1`; `nat i` = `ctor 1[nat i]`; `str x` = `ctor 3[str x]`; `var 3` = `ctor 0[nat 3]`.
  - `perform` = `ctor 6`; `bind` = `ctor 7`; `call 0` = `ctor 32[nat 0]`; `hole` = `ctor 6[ctor 22[nat 0], lit unit]`.
  - m = `bind (perform (call 0) (lit unit)) hole`.
  - P(b, main) = `ctor 30[list[d0,d1], ctor 1[succeed (lit (str "hi")), ctor 1[b, ctor 0[]]], main, ctor 0[]]`.
- **Keys:** `.module` = `ctor 0`, `.part` = `ctor 1`. Each key's bytes are `Node.encode ⟨0, .query, specOf Query, ctor 0[bytes E, input]⟩`, under one engine E.
- **Types:** T = ⟨nat, never, ∅⟩; S = ⟨string, never, ∅⟩.

| Key | Input contents |
| --- | --- |
| Kb0 | `ctor 1[Db, list[u], succeed (lit (str "hi"))]` |
| Kb1 | `ctor 1[Db, list[u], succeed (lit (nat 1))]` |
| Kb2 | `ctor 1[Db, list[u], succeed (lit (nat 2))]` |
| Km | `ctor 1[Dm, list[], m]` |
| Kx | `ctor 1[Dm, list[s], succeed (var 3)]` |
| Km′ | `ctor 1[Dm, list[], bind (perform (call 0) (lit unit)) (succeed (var 3))]` |
| Kc | `ctor 1[Dm, list[s], succeed (lit (nat 7))]` |
| K0 | `ctor 0[A, list[h], P(succeed (lit (nat 1)), m)]` |
| K1 | `ctor 0[A, list[h], P(succeed (lit (nat 2)), m)]` |
| K2 | `ctor 0[A, list[h], P(succeed (lit (nat 2)), main of Km′)]` |

The trace starts with an empty memo M and document D.

| # | Request | Lookups | Answer | State after | Law |
| --- | --- | --- | --- | --- | --- |
| 0 | open ⟨P(…1, m), [h]⟩ | K0 misses; deps `[([0,0],Kb0), ([0,1,0],Kb1), ([1],Km)]` all miss | Vb0 = ok S, one entry; Vb1 = ok T; Vm = ok T with entries `[]` ok T, `[0]` ok S, `[1]` (env `[s]`) ok T; V0 = `combine` = ok T | M = {Kb0, Kb1, Km, K0}; D at revision 0 | L1, L4 |
| 1 | commit fill `[0,1,0]` ← succeed 2, `keepExactType` | splice: Kb2 misses, ok T, the old type, so the table splices; K1 misses; Kb0 hits, Kb2 hits (the splice's own entry), Km hits | ok T | M gains Kb2, K1; D at revision 1 | L3, L6 |
| 2 | `fills.add [([1,1], succeed 7)]` | K1 hits; focus `[1,1]` = (`[s]`, T); Kc misses → ok T | applied | M gains Kc | L7 |
| 3 | commit fill `[1,1]` ← succeed (var 3) | splice: Kx misses → error ⟨[], term (var 3)⟩, so the session reopens; K2 misses; Kb0 and Kb2 hit; Km′ misses → error ⟨[1], term (var 3)⟩ | V2.result = error ⟨[1,1], term (var 3)⟩, placed by `[1]`; **`Doc.commit` refuses** with `.refused [⟨[1,1], term (var 3)⟩]` | D unchanged at revision 1; the fill set is kept; M gains Kx, Km′, K2 | the proposed `serve`'s refusal law; L6 |
| 4 | commit fill `[1,1]` ← succeed 7 | splice: Kc hits (the entry from step 2's certification) → ok T, so the table splices | ok T | D at revision 2 | L6: the refused revision is followed by a valid one |

M grew during step 3's refused request. The growth cannot be observed (L6), because the memo lives outside `State`. Also, `CheckInput.fill` at `[]` answers `none`.

## 3. What the implementation hides

- **Assembling the module** from its part verdicts: `annotateModule`, `Checker.checkModule`/`checkBodies`, `checkLayers`, `Table.atSource`, `Eff.firstRefFault`, `expandRefs`.
- **The signature data:** `partSigAt` and `bodyIndex`.
- **Placement:** `TypeRefusal.rebase` and `Table.Entry.rebase` move from `Laws/Program/Typing/Rebase.lean` into the core, because the core imports no law.
- **`CheckCache`'s pieces move behind the seam:** `CheckKey` becomes the `.part` constructor, and `Entry`, `lookup` and `insert` become the in-process adapter. The `cache` field leaves the state of `tools/Tools/Session.lean`; the host holds the memo.
- **Codecs:** a generated group covers `SigApp`, `PartSig`, `SigData`, `NodeEnv`, `Table.Entry`, `CheckInput`, `Verdict`, `Query` and `Answered`. A generic `Canonical (Except ε α)` joins Option and Prod in `Store/Domain/Canonical.lean`; it lowers to OCaml's `result`.

## 4. Adapters

What varies across adapters is the hit set and the cost, never the answer.

| Adapter | Category |
| --- | --- |
| pure `run` (Lean `serve`, replay, proofs) | in-process |
| `Check.Memo`, a list of `(CheckInput × Verdict)` (today's `CheckCache` list), in the Lean driver | in-process |
| the store: `Store.recall` and `putNode`; natively `E4_cas`, `E4_deps` (the dependents index) and `E4_cache.Decoded` with `V.kind = Result` | local-substitutable |
| Incremental (later): one node per `deps` entry keyed by its base (`Incr_map`), `map` to `run`, cutoff by verdict equality, and a module node that is `combine`; misses fall back to `recall` | in-process |

The first two exist now, so the seam is real.

## 5. Laws

- **L1 `run_module`:** the module arm is (`sourceCheck`, `sourceAnnotate`), by `rfl`. It reuses `Sketch.sourceAnnotate_eq_sourceTable` and `Sketch.sourceCheck_toOption`.
- **L2 `run_part`:** the part arm is the checker and its table at `[]`. It reuses `Annotate.check_eq`.
- **L3 `run_placed`:** `Annotate.check d.signature env a q` is `run`'s verdict placed at `a`. It reuses `Checker.check_rebase` and `tableAt_rebase`.
- **L4 `combine_deps`** (the differential of graph rule 7): `combine i ((deps i).map (run ·.2)) = run i`. This is new, proved from the definitions of `checkModule` and `annotateModule` together with L3.
- **L5 `deps_parts`:** every dependency is a `.part` with no dependencies of its own, so the depth is one.
- **L6 transparency:** `Memo.Valid m → (m.ask i).2 = run i ∧ (m.ask i).1.Valid`. It follows the pattern of `CheckCache.lookup_sound` and `insert_valid`.
- **L6s `recall_sound`:** if the store's answers are valid, a hit is `run` of its query's input, and `recall` never reports `poisoned`. A `putNode` of a computed `Answered` keeps the answers valid. It reuses `putNode_find` and `get_put`.
- **L7 `certifiedB_eq`:** on reference-free sketches, `certifiedB` equals the `fill`/`certifies` reading. It reuses `sketchSigData_signature`, `Checker.check_rebase` and `open_shown_of_refSites_nil`.
- **L8 key completeness:** equal query addresses give equal verdicts, or exhibit a collision. It reuses `address_eq_or_collision`.
- **L9:** `Memo.Valid m → (serveCached m s r).2 = serve s r`.
- **Restrictions:** `Run.Kit.check app p = (run (.module app [] p)).result`, and `Api.check`'s refusal agrees with it. They reuse `SigApp.withHoles_nil` and `Api.explain_none_iff`.

## 6. Trade-offs

**Where leverage is high:**
- One key shape serves the splice, certification, suggest and the module's parts. In the trace, the hits in steps 1, 3 and 4 come from different callers reading one entry.
- `deps` and `combine` replace a fetch callback, so generated code never calls boundary code. The native host and Incremental hold no semantics.
- Correction to the brief: a complete key must also name the checker's own code, hence `engine`.

**Where it is thin:**
- **Granularity is per part.** A program with no definition block is one part. Inside it, only the session's splice is incremental, and a stateless host rechecks the whole part. Graph rule 1 accepts this.
- **Complete keys hold the whole `SigData`.** An omission grows the hole table and misses every part key. `CheckCache.lookup`'s extension read is dropped because a digest cannot address it.
  - The later remedy is `CheckInput.narrow`: the holes the program performs, and the declarations it calls (incremental.md, proposal I2). Its law would come from `sketch_reads_its_holes` and `check_restrict`. I2's premise is unchecked.
- **Storage cost:**
  - Verdicts carry tables, and a candidate's stored table goes unread.
  - Inline keys repeat `SigData` in every part key.
  - Outlining `SigData` into its own node needs a kind and a consumer.
- **The `Trust` mode waits on C7.** Until engine digests are deterministic, the store adapter runs `Verify` only.
- **The `.part` arm checks a filling as given.** A filling that holds a layer reference refuses, as it does today.
- **Behaviour changes:** `Tools.Query` and `certifiedB` now read through layer references. A control is needed: a filling beside a layer reference.

**What this makes hard later:** inference across parts would break L5's depth of one.

### Critical files for implementation
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/Source.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/CheckCache.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Program/Typing/PartsTable.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Laws/Program/Typing/Rebase.lean
- /Users/pooks/Dev/lean4-effect4/src/Effect4/Store/Domain/Store.lean
