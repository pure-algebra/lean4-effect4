# Lane S2 — the node, the store, the word, the traits

Starts at lane S1's milestone M1 (its `NOTES.md` entry saying `Val`, `Shape` and `Canonical`
compile with fixed statements) **and** after S1 has released the machine's one `lake`
(its `REPORT.md` exists, or the coordinator says so). The general rules are `BRIEF.md`'s;
the rulings are `docs/research/2026-09-04-cas-trait-facts.md` §5, Q3, Q4, Q6, Q7, Q8; the
module rows are `docs/research/2026-09-04-cas-trait-plan.md` §2. Namespace `Effect4.Store`;
modules `Cas.Node`, `Cas.Store`, `Cas.Word`, `Cas.Traits` under `workshop/Cas/Cas/`; add
them to `workshop/Cas/Cas.lean`. Build with `lake build Cas` only.

**Amendments after S1 (2026-09-05 00:50).** S1 is done and frozen (`REPORT-S1.md`,
`NOTES.md`, `RECEIPTS.md`): read them first, then `Cas/Digest.lean`, `Cas/Val.lean`,
`Cas/Kind.lean`, `Cas/Shape.lean`, `Cas/Canonical.lean` for the exact signatures (they differ
from this brief's sketches where S1 recorded a departure; the code wins). `Digest` is
`{bytes : Bytes, length_eq : bytes.length = 32}`, so `zeroDigest := ⟨List.replicate 32 0, by
simp⟩`, `Node.spec : Digest` needs no length hypothesis, and `Node.decode_encode` drops `hs`.
`Val.WF` is decidable (`decWF`); `Val.decode`'s family is in `namespace Val`. Lane G runs
concurrently with only `lake env lean`; **you own the machine's one `lake build Cas`**. Keep
your notes in `workshop/Cas/NOTES-S2.md` (S1's `NOTES.md` is frozen).

`Canonical Document` does not exist until lane G derives it (or S1's stretch lands it). Every
definition that needs it — `spec`, the meta-schema, the genesis rule, `address`, `put`,
`get` — is written under `variable [Content Document]` in a section, so the module compiles
now and instantiates later. The node layer below that assumption is tested directly with
explicit spec digests.

## `Cas/Node.lean`

```lean
structure Ref (α : Type) where digest : Digest            -- deriving DecidableEq, Repr
structure AnyRef where kind : Kind; digest : Digest         -- deriving DecidableEq, Repr
class Content (α : Type) extends Canonical α where kind : Kind

instance [Content α] : Canonical (Ref α)   -- toVal r = .ref (kind α).byte r.digest.bytes;
                                           -- ofVal refuses a wrong kind byte or a length ≠ 32;
                                           -- shape = .ref (kind α); the three laws
instance : Canonical AnyRef                -- toVal = .ref k.byte d.bytes; shape = .anyRef

structure Node where version : UInt8; kind : Kind; spec : Digest; payload : Val
def Node.encode (n : Node) : Bytes := n.version :: n.kind.byte :: (n.spec.bytes ++ Val.encode n.payload)
def Node.decode : Bytes → Option Node       -- version must be 0, kind byte must be a Kind,
                                           -- 32 spec bytes, then Val.decode of the whole rest
theorem Node.decode_encode (h : n.payload.WF) (hs : n.spec.bytes.length = 32) (hv : n.version = 0) : decode (encode n) = some n
theorem Node.decode_exact : decode b = some n → b = encode n ∧ n.payload.WF ∧ n.spec.bytes.length = 32 ∧ n.version = 0
def Node.refsOf (n : Node) : List AnyRef    -- every `Val.ref k d` in `payload`, traversal order,
                                           -- with `Kind.ofByte? k = some kind` and `d.length = 32`
def Node.malformedRef (n : Node) : Bool      -- a `Val.ref` whose kind byte or length is wrong
def Node.edges (n : Node) : List AnyRef := ⟨.schema, n.spec⟩ :: n.refsOf   -- edge 0 is the spec

def zeroDigest : Digest := ⟨List.replicate 32 0⟩
section variable [Content Document]
def metaSchema : Document := (Canonical.shape Document).document
def specOf (α : Type) [Content α] : Digest       -- the address of `(shape α).document` as a
                                                 -- schema node; the meta-schema itself gets `zeroDigest`
def nodeOf [Content α] (a : α) : Node := ⟨0, Content.kind α, specOf α, Canonical.toVal a⟩
def address [Content α] (a : α) : Ref α := ⟨sha256 (Node.encode (nodeOf a))⟩
theorem address_congr; theorem address_eq_or_collision   -- level 0, as Foldlab's Core/Address.lean
theorem address_inj (hInj : Function.Injective sha256)   -- level 1, the premise named, never an instance
example : ∃ n m : Node, n ≠ m ∧ (fun _ => ()) (Node.encode n) = (fun _ => ()) (Node.encode m)  -- level 2 empty
theorem metaSchema_accepts : (Canonical.shape Document).accepts (Canonical.toVal metaSchema) = true  -- the genesis theorem, by `decide` once the instance exists; state it, prove it when instantiable
end
```

## `Cas/Store.lean`

```lean
inductive RootKind | stdlib | journal | daemon | schema | char   -- deriving DecidableEq, Repr; `name`
structure Root where name : String; rootKind : RootKind; kind : Kind; digest : Digest; version : Nat
structure Store where nodes : List (Digest × Node); roots : List Root
def Store.empty; def Store.find (s : Store) (d : Digest) : Option Node
inductive Admission
  | dangling (missing : Digest) | wrongKind (ref : Digest) (expected actual : Kind)
  | malformedRef | oversize | badVersion | staleRoot (name : String) (expected actual : Nat)
inductive Outcome | fresh | duplicate | conflict (occupant : Node)
def Store.checkEdges (s : Store) (n : Node) : Except Admission Unit
  -- every edge resolves at its kind; the spec edge is exempt exactly when `n.kind = .schema ∧ n.spec = zeroDigest` (the genesis)
def Store.putNode (s : Store) (n : Node) : Except Admission (Outcome × Digest × Store)
  -- refuse `oversize` (¬ n.payload.WF), `badVersion`, `malformedRef`, then `checkEdges`;
  -- the address `sha256 (Node.encode n)`; `duplicate` when the resident equals `n`;
  -- `conflict resident` when it differs (never overwritten); `fresh` appends
def Store.getNode (s : Store) (d : Digest) : Option Node := s.find d
section variable [Content Document]
def Store.put [Content α] (a : α) (s : Store) : Except Admission (Outcome × Ref α × Store)
def Store.get [Content α] (r : Ref α) (s : Store) : Option α   -- find, kind check, then `Canonical.ofVal`
theorem get_put : s.put a = .ok (o, r, s') → s'.get r = some a
theorem put_duplicate : s.find (address a).digest = some (nodeOf a) → s.put a = .ok (.duplicate, address a, s)
theorem put_preserves : s.find d = some n → s.put a = .ok (o, r, s') → s'.find d = some n
end
def Closed (s : Store) : Prop   -- every resident node's edges resolve at their kinds, the genesis exempt
theorem empty_closed; theorem putNode_fresh_closed : Closed s → s.putNode n = .ok (o, d, s') → Closed s'
def Store.putRoot (s : Store) (r : Root) : Except Admission Store   -- compare-and-set: refuse `staleRoot` unless `r.version` = resident version + 1 (or 1 when absent); the target must resolve at `r.kind`
def Store.root? (s : Store) (name : String) : Option Root
```

## `Cas/Word.lean`

```lean
structure Binding where digest : Digest; node : Node
abbrev Word := List Binding
def Word.wf : Word → Bool        -- children-first: every edge of each binding resolves among the earlier bindings at its kind (genesis exempt), and `digest = sha256 (encode node)`
def Word.apply : Word → Store → Except Admission Store   -- fold `putNode`; `duplicate` is fine, `conflict` refuses
theorem wf_closed : w.wf = true → ∃ s, apply w empty = .ok s ∧ Closed s
theorem apply_idempotent : apply w s = .ok s' → apply w s' = .ok s'
def Store.closure (s : Store) (r : AnyRef) : Word       -- the reachable subgraph of `r`, children first, fuel `s.nodes.length`, each digest once
theorem closure_closed : Closed s → s.find r.digest = some n → ∃ s', apply (s.closure r) empty = .ok s' ∧ Closed s' ∧ s'.find r.digest = some n
structure Layered where local remote : Store
def Layered.getNode (l : Layered) (d : Digest) : Option Node := (l.local.find d).orElse (fun _ => l.remote.find d)
def Store.sub (a b : Store) : Prop := ∀ d n, a.find d = some n → b.find d = some n
theorem layered_get : l.local.sub l.remote → l.getNode d = l.remote.find d
def Layered.preload (l : Layered) (r : AnyRef) : Except Admission Layered   -- apply the remote's closure into the local
structure LocalFirst where local : Store; outbox : Word
def LocalFirst.putNode (l : LocalFirst) (n : Node) : Except Admission (Outcome × Digest × LocalFirst)   -- put locally; on `fresh` append the binding
def LocalFirst.sync (l : LocalFirst) (remote : Store) : Except Admission Store := l.outbox.apply remote
theorem outbox_wf : l built from `LocalFirst.empty` by `putNode` → l.outbox.wf = true
theorem sync_sub : l.sync remote = .ok r → l.local.sub r   -- under the hypothesis that `l.local` was `remote ∪ outbox`, state it as the plan does
inductive VerifyError | digestMismatch (d : Digest) | undecodable (d : Digest) | dangling … | rootUnresolved (name : String)
def Store.verify (s : Store) : Except VerifyError Unit   -- recompute every address over `Node.encode`, re-decode, check edges, resolve roots at their kinds
theorem verify_sound : s.verify = .ok () → Closed s ∧ ∀ d n, s.find d = some n → d = sha256 (Node.encode n)
```

## `Cas/Traits.lean`

```lean
structure Annotation (τ : Type) where subject : AnyRef; value : τ; prev : Option (Ref (Annotation τ))
instance [Canonical τ] : Canonical (Annotation τ)   -- a structure: `.ctor 0 [toVal subject, toVal value, toVal prev]`, shape a struct
instance [Canonical τ] : Content (Annotation τ) := ⟨.annotation⟩
def Store.annotationsOf (s : Store) (subject : AnyRef) : List (Digest × Node)   -- kind 6 nodes whose first `Val.ref` is `subject` (the subject is field 0, so it is edge 1 after the spec)
def Store.superseded (s : Store) (d : Digest) : Bool   -- some annotation names `d` as `prev`
def Store.traitsOf (s : Store) (subject : AnyRef) : List (Digest × Node)   -- the heads: annotations of the subject that nothing supersedes
def Store.effective (s : Store) (registry : Digest) (n : AnyRef) (key : Digest) : List (Digest × Node)
  -- `key` is the trait's spec digest; candidates in order: the node's own heads with that spec, then its spec node's heads, then the registry node's heads; the first non-empty list
theorem address_ignores_traits : address a = address a   -- state the real fact instead: `nodeOf` and `address` mention no store, so a trait can only add nodes; `put_preserves` is the store half
theorem effective_deterministic : s = s' → effective s reg n k = effective s' reg n k   -- trivial, but state that resolution is a function of the store; the substantive law is that `traitsOf` is insensitive to the order of `nodes` (state and prove as `Perm`-invariance if cheap, else record as owed)
```

Guards to write (a `Cas/Probe.lean` battery inside the spike, using the facts note's §6 values):
the entry node bytes and address `1437a1…705b` with today's document digest as the explicit
spec; the kind-6 twin `ca0785…0990`; `putNode` twice → `fresh` then `duplicate`; `dangling` and
`wrongKind` on those addresses; a two-binding word `wf`, applied twice; a closure; a layered
read; an outbox synced twice; `verify` passing then refusing after one byte of a payload is
flipped; a trait on the entry node leaving its bytes unchanged.
