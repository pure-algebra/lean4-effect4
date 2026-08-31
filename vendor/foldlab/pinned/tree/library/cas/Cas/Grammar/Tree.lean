import Cas.Codec.NodeCodec
import Cas.Core.Canonical
import Cas.Grammar.Sorts
import Cas.IR.Word

/-!
# The sorted trees — the data grammar

One indexed family covers every node form: the sort index makes an
ill-kinded reference unrepresentable, elaboration (`node`) projects a
term onto the store's carrier through the real codec, the content
address is a fold over the tree under the abstract `H`, and `flatten`
emits the children-first store word.

Bounds are carried by the constructors (`Payload`, `Name`, fixed-width
scalars), so elaborated nodes are well-formed by construction — the
same move the sort index makes for kinds, applied to the codec's byte
bounds (ledger L4). `address` IS the digest of the canonical pre-image
by definition (ledger L2); nothing here re-derives an encoding.

`flatten_wf` (ledger L3) sits at Level 1 of the hash-hypothesis
lattice: under an injective `H`, every grammar term's word admits.
Level 0 cannot state it — a colliding `H` can alias two sorts at one
address, and the word's first-binding resolution would then answer the
wrong kind. The premise is named, never assumed silently (CAS-003).
-/

namespace Cas.Grammar

/-- A payload within the codec's byte bound. `ofBytes` totalizes by
clamping AT the bound — unreachable for any honest input (the bound is
2^32 − 1 bytes); the honest partial constructor is `ofBytes?`. -/
abbrev Payload := { b : Bytes // b.length < 4294967296 }

def Payload.ofBytes (b : Bytes) : Payload :=
  ⟨b.take 4294967295,
    Nat.lt_of_le_of_lt (List.length_take_le ..) (by omega)⟩

def Payload.ofBytes? (b : Bytes) : Option Payload :=
  if h : b.length < 4294967296 then some ⟨b, h⟩ else none

/-- UTF-8 bytes of a string. -/
def utf8 (s : String) : Bytes := s.toUTF8.toList

def Payload.utf8 (s : String) : Payload := Payload.ofBytes (Grammar.utf8 s)

/-- A short byte field (a file name, a media type): bounded so that a
framed pair of them stays inside one payload bound. -/
abbrev Name := { b : Bytes // b.length < 65536 }

def Name.ofBytes (b : Bytes) : Name :=
  ⟨b.take 65535,
    Nat.lt_of_le_of_lt (List.length_take_le ..) (by omega)⟩

def Name.utf8 (s : String) : Name := Name.ofBytes (Grammar.utf8 s)

/-- The grammar: a term of `Tree t` is a well-kinded node graph of
sort `t` with children inline. An ill-kinded edge does not typecheck. -/
inductive Tree : Ty → Type where
  /-- An opaque value payload. -/
  | value (payload : Payload) : Tree .value
  /-- Position-free chunk data (profile tag 8). -/
  | chunk (bytes : Payload) : Tree .chunk
  /-- A schema leaf (tag 0x53): the payload is the schema's canonical
  bytes, handed over by the schema plane — opaque at this layer, refs
  empty in v0. The payload-is-rendering law arrives with the schema
  commission's Lean Ast codec; schemas referencing schemas as typed
  edges is the named follow-up. -/
  | schema (bytes : Payload) : Tree .schema
  /-- A blob leaf: absolute chunk index and declared length (tag 9). -/
  | leaf (index len : UInt32) (data : Tree .chunk) : Tree .tree
  /-- A blob interior node: two ordered subtrees (tag 9). -/
  | parent (left right : Tree .tree) : Tree .tree
  /-- The recipe-1 manifest: recipe id, total bytes, leaf count
  (tag 10). -/
  | manifest (recipe : UInt32) (total : UInt64) (leaves : UInt32)
      (root : Tree .tree) : Tree .manifest
  /-- A named file over a blob manifest (illustrative tag 11). -/
  | file (name mediaType : Name) (content : Tree .manifest) : Tree .file
  /-- The journal's genesis entry (illustrative tag 12). -/
  | genesis : Tree .entry
  /-- One journal entry: a note, an item, the previous entry. -/
  | entry (note : Payload) (item : Tree .file) (prev : Tree .entry) :
      Tree .entry
  /-- A git object as content: the payload IS the loose-object
  preimage (`"<type> <len>\0" ++ content`), so the git SHA-1 identity
  is derivable from the payload alone by any host — dual identity
  with no declared field. References empty in v0: git's internal
  SHA-1 edges stay opaque, and typed git edges are a named follow-up
  exactly like the schema sort's $defs graph. -/
  | git (obj : Payload) : Tree .git

section Elaboration

variable (H : Bytes → Addr32)

/-- Elaboration: project a term onto the store carrier. Children
appear only as addresses — the digest of the canonical pre-image of
their own elaboration. -/
def Tree.node : Tree t → Node
  | .value p => ⟨schemeVersion, Ty.value.wireTag, p.val, []⟩
  | .chunk p => ⟨schemeVersion, Ty.chunk.wireTag, p.val, []⟩
  | .schema p => ⟨schemeVersion, Ty.schema.wireTag, p.val, []⟩
  | .leaf i l d =>
    ⟨schemeVersion, Ty.tree.wireTag, nat32 i.toNat ++ nat32 l.toNat,
      [⟨Ty.chunk.wireTag, H (encodeNode (d.node))⟩]⟩
  | .parent l r =>
    ⟨schemeVersion, Ty.tree.wireTag, [],
      [⟨Ty.tree.wireTag, H (encodeNode (l.node))⟩,
       ⟨Ty.tree.wireTag, H (encodeNode (r.node))⟩]⟩
  | .manifest re tot le root =>
    ⟨schemeVersion, Ty.manifest.wireTag,
      nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat,
      [⟨Ty.tree.wireTag, H (encodeNode (root.node))⟩]⟩
  | .file name mt c =>
    ⟨schemeVersion, Ty.file.wireTag, frame name.val ++ frame mt.val,
      [⟨Ty.manifest.wireTag, H (encodeNode (c.node))⟩]⟩
  | .genesis => ⟨schemeVersion, Ty.entry.wireTag, [], []⟩
  | .entry note item prev =>
    ⟨schemeVersion, Ty.entry.wireTag, note.val,
      [⟨Ty.file.wireTag, H (encodeNode (item.node))⟩,
       ⟨Ty.entry.wireTag, H (encodeNode (prev.node))⟩]⟩
  | .git obj => ⟨schemeVersion, Ty.git.wireTag, obj.val, []⟩

/-- The content address: the abstract digest of the canonical
pre-image of the elaborated node (ledger L2 — by definition, which is
the point). -/
def Tree.address (tr : Tree t) : Addr32 := H (encodeNode (tr.node H))

@[simp] theorem Tree.address_spec (tr : Tree t) :
    tr.address H = H (encodeNode (tr.node H)) := rfl

/-- Elaboration stamps the sort's own tag. -/
theorem Tree.node_tag (tr : Tree t) : (tr.node H).tag = t.wireTag := by
  cases tr <;> rfl

/-- Ledger L4: elaborated nodes are well-formed by construction — the
constructor bounds do the work, no side condition survives to here. -/
theorem Tree.node_wf (tr : Tree t) : (tr.node H).WF := by
  cases tr with
  | value p =>
    refine ⟨p.property, ?_⟩
    simp only [Tree.node, List.length_nil]
    omega
  | chunk p =>
    refine ⟨p.property, ?_⟩
    simp only [Tree.node, List.length_nil]
    omega
  | schema p =>
    refine ⟨p.property, ?_⟩
    simp only [Tree.node, List.length_nil]
    omega
  | leaf i l d =>
    refine ⟨?_, ?_⟩ <;>
      simp only [Tree.node, List.length_append, nat32_length,
        List.length_cons, List.length_nil] <;>
      omega
  | parent l r =>
    refine ⟨?_, ?_⟩ <;>
      simp only [Tree.node, List.length_cons, List.length_nil] <;>
      omega
  | manifest re tot le root =>
    refine ⟨?_, ?_⟩ <;>
      simp only [Tree.node, List.length_append, nat32_length, nat64_length,
        List.length_cons, List.length_nil] <;>
      omega
  | file name mt c =>
    have hn := name.property
    have hm := mt.property
    refine ⟨?_, ?_⟩ <;>
      simp only [Tree.node, frame, List.length_append, nat32_length,
        List.length_cons, List.length_nil] <;>
      omega
  | genesis =>
    refine ⟨?_, ?_⟩ <;> simp only [Tree.node, List.length_nil] <;> omega
  | entry note item prev =>
    refine ⟨note.property, ?_⟩
    simp only [Tree.node, List.length_cons, List.length_nil]
    omega

  | git obj =>
    refine ⟨obj.property, ?_⟩
    simp only [Tree.node, List.length_nil]
    omega

/-- Trees are addressable through elaboration: the admitted node a
term projects to. Not a `Canonical` instance — the elaboration embeds
child addresses, so a tree's encoding is `H`-relative by nature. -/
def Tree.toAdmitted (tr : Tree t) : AdmittedNode :=
  ⟨tr.node H, tr.node_wf H⟩

/-- The grammar's address IS the CAS typeclass's address of the
elaborated node. -/
theorem Tree.address_eq_canonical (tr : Tree t) :
    tr.address H = Canonical.address H (tr.toAdmitted H) := rfl

/-- The store word of a term: children first, the term's own binding
last — the admission order, the transfer order, the vector. -/
def Tree.flatten : (tr : Tree t) → Word
  | tr@(.value _) => [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.chunk _) => [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.schema _) => [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.leaf _ _ d) =>
    d.flatten ++ [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.parent l r) =>
    l.flatten ++ r.flatten ++ [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.manifest _ _ _ root) =>
    root.flatten ++ [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.file _ _ c) =>
    c.flatten ++ [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.genesis) => [Binding.mk (tr.address H) (tr.node H)]
  | tr@(.entry _ item prev) =>
    item.flatten ++ prev.flatten ++
      [Binding.mk (tr.address H) (tr.node H)]

  | tr@(.git _) => [Binding.mk (tr.address H) (tr.node H)]

/-- One store binding per grammar node. -/
def Tree.size : Tree t → Nat
  | .value _ => 1
  | .chunk _ => 1
  | .schema _ => 1
  | .leaf _ _ d => d.size + 1
  | .parent l r => l.size + r.size + 1
  | .manifest _ _ _ root => root.size + 1
  | .file _ _ c => c.size + 1
  | .genesis => 1
  | .entry _ item prev => item.size + prev.size + 1
  | .git _ => 1

theorem Tree.length_flatten (tr : Tree t) :
    (tr.flatten H).length = tr.size := by
  induction tr <;> simp [Tree.flatten, Tree.size, *] <;> omega

/-- The term's own binding is in its word (its last entry). -/
theorem Tree.self_mem_flatten (tr : Tree t) :
    Binding.mk (tr.address H) (tr.node H) ∈ tr.flatten H := by
  cases tr <;> simp [Tree.flatten]

/-- Every grammar term contributes its own final binding. -/
theorem Tree.flatten_nonempty (tr : Tree t) : tr.flatten H ≠ [] := by
  intro h
  have hmem := Tree.self_mem_flatten H tr
  rw [h] at hmem
  simp at hmem

/-- An honest word binds each address to the digest of its node's
canonical pre-image, and every bound node is well-formed. `flatten`
emits only honest words. -/
def Honest (w : Word) : Prop :=
  ∀ p ∈ w, p.address = H (encodeNode p.node) ∧ p.node.WF

theorem Honest.append {w v : Word} (hw : Honest H w) (hv : Honest H v) :
    Honest H (w ++ v) := by
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hw p h
  · exact hv p h

theorem Honest.nil : Honest H [] := by
  intro p hp
  simp at hp

theorem Tree.flatten_honest (tr : Tree t) : Honest H (tr.flatten H) := by
  induction tr with
  | git obj =>
    intro q hq
    simp only [Tree.flatten, List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | value p =>
    intro q hq
    simp only [Tree.flatten, List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | chunk p =>
    intro q hq
    simp only [Tree.flatten, List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | schema p =>
    intro q hq
    simp only [Tree.flatten, List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | genesis =>
    intro q hq
    simp only [Tree.flatten, List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | leaf i l d ih =>
    refine Honest.append H ih ?_
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | parent l r ihl ihr =>
    refine Honest.append H (Honest.append H ihl ihr) ?_
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | manifest re tot le root ih =>
    refine Honest.append H ih ?_
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | file name mt c ih =>
    refine Honest.append H ih ?_
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩
  | entry note item prev ihi ihp =>
    refine Honest.append H (Honest.append H ihi ihp) ?_
    intro q hq
    simp only [List.mem_singleton] at hq
    subst hq
    exact ⟨rfl, Tree.node_wf H _⟩

/-- In an honest word, finding at a well-formed node's own address
answers that node — Level 1: `hInj` turns address equality into
pre-image equality, and codec exactness does the rest. -/
theorem find_honest (hInj : Function.Injective H) {w : Word}
    (hw : Honest H w) {n : Node} (hn : n.WF) {m : Node}
    (hf : Word.find w (H (encodeNode n)) = some m) : m = n := by
  obtain ⟨hkey, hwf⟩ := hw _ (Word.find_mem hf)
  exact encodeNode_injOn hwf hn (hInj hkey.symm)

/-- F2, aliasing half (Level 1): an honest word never binds one
address to two nodes — the address determines the canonical bytes
under `hInj`, and codec non-malleability does the rest. With the
shadowing lemma (`Word.toStore_append_shadowed`), this is word
deduplication: re-binding an address an honest word already binds can
only repeat the same node, and the repetition is inert. -/
theorem Honest.no_alias (hInj : Function.Injective H) {w : Word}
    (hw : Honest H w) {a : Addr32} {n m : Node}
    (hn : Binding.mk a n ∈ w) (hm : Binding.mk a m ∈ w) : n = m := by
  obtain ⟨hkn, hwn⟩ := hw _ hn
  obtain ⟨hkm, hwm⟩ := hw _ hm
  exact encodeNode_injOn hwn hwm (hInj (hkn.symm.trans hkm))

/-- A subterm's typed edge resolves in any honest word containing the
subterm's binding. -/
theorem resolves_child (hInj : Function.Injective H) {w : Word}
    (hw : Honest H w) {s : Ty} (c : Tree s)
    (hmem : Binding.mk (c.address H) (c.node H) ∈ w) :
    Word.resolvesIn w ⟨s.wireTag, c.address H⟩ = true := by
  have hsome := Word.find_isSome_of_mem hmem
  cases hf : Word.find w (c.address H) with
  | none => rw [hf] at hsome; exact absurd hsome (by simp)
  | some m =>
    have hm : m = c.node H :=
      find_honest H hInj hw (Tree.node_wf H c) hf
    refine Word.resolvesIn_iff.mpr ⟨m, hf, ?_⟩
    rw [hm]
    exact Tree.node_tag H c

/-- Ledger L3, interior form: over any honest prefix, a term's word
admits — every reference resolves at its declared kind, children
first. Level 1 (`hInj` named), per the CAS-003 lattice. -/
theorem Tree.flatten_wfFrom (hInj : Function.Injective H) (tr : Tree t)
    (prior : Word) (hprior : Honest H prior) :
    Word.wfFrom prior (tr.flatten H) = true := by
  induction tr generalizing prior with
  | value p => simp [Tree.flatten, Word.wfFrom, Tree.node]
  | chunk p => simp [Tree.flatten, Word.wfFrom, Tree.node]
  | schema p => simp [Tree.flatten, Word.wfFrom, Tree.node]
  | genesis => simp [Tree.flatten, Word.wfFrom, Tree.node]
  | git obj => simp [Tree.flatten, Word.wfFrom, Tree.node]
  | leaf i l d ih =>
    simp only [Tree.flatten]
    rw [Word.wfFrom_append]
    simp only [Bool.and_eq_true]
    refine ⟨ih prior hprior, ?_⟩
    have hhonest : Honest H (prior ++ d.flatten H) :=
      Honest.append H hprior (Tree.flatten_honest H d)
    have hmem : Binding.mk (d.address H) (d.node H) ∈
        prior ++ d.flatten H :=
      List.mem_append_right _ (Tree.self_mem_flatten H d)
    simp only [Word.wfFrom, Bool.and_true, List.all_cons, List.all_nil,
      Tree.node, Bool.and_true]
    exact resolves_child H hInj hhonest d hmem
  | parent l r ihl ihr =>
    simp only [Tree.flatten]
    rw [Word.wfFrom_append, Word.wfFrom_append]
    have hl := ihl prior hprior
    have hpl : Honest H (prior ++ l.flatten H) :=
      Honest.append H hprior (Tree.flatten_honest H l)
    have hr := ihr (prior ++ l.flatten H) hpl
    have hplr : Honest H (prior ++ (l.flatten H ++ r.flatten H)) :=
      Honest.append H hprior
        (Honest.append H (Tree.flatten_honest H l) (Tree.flatten_honest H r))
    simp only [Bool.and_eq_true]
    refine ⟨⟨hl, hr⟩, ?_⟩
    have hmeml : Binding.mk (l.address H) (l.node H)
        ∈ prior ++ (l.flatten H ++ r.flatten H) :=
      List.mem_append_right _
        (List.mem_append_left _ (Tree.self_mem_flatten H l))
    have hmemr : Binding.mk (r.address H) (r.node H)
        ∈ prior ++ (l.flatten H ++ r.flatten H) :=
      List.mem_append_right _
        (List.mem_append_right _ (Tree.self_mem_flatten H r))
    simp only [Word.wfFrom, Bool.and_true, List.all_cons, List.all_nil,
      Tree.node, Bool.and_true, Bool.and_eq_true]
    exact ⟨resolves_child H hInj hplr l hmeml,
      resolves_child H hInj hplr r hmemr⟩
  | manifest re tot le root ih =>
    simp only [Tree.flatten]
    rw [Word.wfFrom_append]
    simp only [Bool.and_eq_true]
    refine ⟨ih prior hprior, ?_⟩
    have hhonest : Honest H (prior ++ root.flatten H) :=
      Honest.append H hprior (Tree.flatten_honest H root)
    have hmem : Binding.mk (root.address H) (root.node H) ∈
        prior ++ root.flatten H :=
      List.mem_append_right _ (Tree.self_mem_flatten H root)
    simp only [Word.wfFrom, Bool.and_true, List.all_cons, List.all_nil,
      Tree.node, Bool.and_true]
    exact resolves_child H hInj hhonest root hmem
  | file name mt c ih =>
    simp only [Tree.flatten]
    rw [Word.wfFrom_append]
    simp only [Bool.and_eq_true]
    refine ⟨ih prior hprior, ?_⟩
    have hhonest : Honest H (prior ++ c.flatten H) :=
      Honest.append H hprior (Tree.flatten_honest H c)
    have hmem : Binding.mk (c.address H) (c.node H) ∈
        prior ++ c.flatten H :=
      List.mem_append_right _ (Tree.self_mem_flatten H c)
    simp only [Word.wfFrom, Bool.and_true, List.all_cons, List.all_nil,
      Tree.node, Bool.and_true]
    exact resolves_child H hInj hhonest c hmem
  | entry note item prev ihi ihp =>
    simp only [Tree.flatten]
    rw [Word.wfFrom_append, Word.wfFrom_append]
    have hi := ihi prior hprior
    have hpi : Honest H (prior ++ item.flatten H) :=
      Honest.append H hprior (Tree.flatten_honest H item)
    have hp := ihp (prior ++ item.flatten H) hpi
    have hpip : Honest H (prior ++ (item.flatten H ++ prev.flatten H)) :=
      Honest.append H hprior
        (Honest.append H (Tree.flatten_honest H item)
          (Tree.flatten_honest H prev))
    simp only [Bool.and_eq_true]
    refine ⟨⟨hi, hp⟩, ?_⟩
    have hmemi : Binding.mk (item.address H) (item.node H)
        ∈ prior ++ (item.flatten H ++ prev.flatten H) :=
      List.mem_append_right _
        (List.mem_append_left _ (Tree.self_mem_flatten H item))
    have hmemp : Binding.mk (prev.address H) (prev.node H)
        ∈ prior ++ (item.flatten H ++ prev.flatten H) :=
      List.mem_append_right _
        (List.mem_append_right _ (Tree.self_mem_flatten H prev))
    simp only [Word.wfFrom, Bool.and_true, List.all_cons, List.all_nil,
      Tree.node, Bool.and_true, Bool.and_eq_true]
    exact ⟨resolves_child H hInj hpip item hmemi,
      resolves_child H hInj hpip prev hmemp⟩

/-- Ledger L3: under an injective digest, every grammar term's word
admits. Level 1 — the premise is named, never assumed. -/
theorem Tree.flatten_wf (hInj : Function.Injective H) (tr : Tree t) :
    Word.wf (tr.flatten H) = true :=
  Tree.flatten_wfFrom H hInj tr [] (Honest.nil H)

end Elaboration

end Cas.Grammar
