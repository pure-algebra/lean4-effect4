import Effect4.Store.Word

/-!
# Store.Traits

Owner: traits as typed annotation nodes (Q8, plane B), supersession as a forest through `prev`,
and the resolution node → spec → registry.

A trait is an `Annotation τ`: a `subject : AnyRef` (one node, a schema node, or the registry
row), a typed `value : τ` that is itself content, and `prev : Option (Ref (Annotation τ))` for
supersession. It files at kind `annotation` (byte 6) like every other annotation carrier, and its
value tree is the structure rule of Q5 — constructor `0` with the three fields in declaration
order — so `Canonical (Annotation τ)` is written exactly as the generator would write it, except
for `prev`: its frame is written by hand (`prevToVal`/`prevOfVal`), because the instance for
`Ref (Annotation τ)` would need the `Content (Annotation τ)` this module is defining.

The four rules of Q8 as this module keeps them. Traits never enter identity: a carrier's node
bytes and address are functions of the value alone (`nodeOf` and `address` take no store), so a
trait can only add a node, and `put_preserves` says the store half — every resident node stays
where it was (`trait_put_preserves`). A trait's payload is content: it is a `Canonical τ` value in
an ordinary node, admitted by the same rules as every other node, so an unknown key is a spec
edge that dangles and is refused. The alphabet grows by spec version: a trait's key is its spec
digest, edge 0 of its node. Resolution is a function of the store: `traitsOf` answers the heads
of the supersession forest (the annotations of a subject that no annotation names as `prev`),
`effective` answers the most specific non-empty set under a key — the node's own heads, then its
spec node's, then the registry node's — and both are insensitive to the order the store lists
its nodes in (`traitsOf_perm`).
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Document)

/-! ## The carrier -/

/-- A trait: a typed value about a subject, with the trait it supersedes. -/
structure Annotation (τ : Type) where
  subject : AnyRef
  value : τ
  prev : Option (Ref (Annotation τ))

namespace Annotation

variable {τ : Type}

/-- The `prev` field's tree: `none`, or a `ref` frame at kind `annotation`. Written by hand: the
instance for `Ref (Annotation τ)` would need the `Content (Annotation τ)` being defined. -/
def prevToVal : Option (Ref (Annotation τ)) → Val
  | none => .none
  | some r => .some (.ref Kind.annotation.byte r.digest.bytes)

/-- The reader of `prev`: refuses another kind byte or a digest that is not thirty-two bytes. -/
def prevOfVal : Val → Option (Option (Ref (Annotation τ)))
  | .none => some none
  | .some (.ref b d) =>
    if b = Kind.annotation.byte then (Digest.ofBytes? d).map fun dg => some ⟨dg⟩ else none
  | _ => none

theorem prevOfVal_prevToVal (p : Option (Ref (Annotation τ))) : prevOfVal (prevToVal p) = some p := by
  cases p with
  | none => rfl
  | some r =>
    show (if Kind.annotation.byte = Kind.annotation.byte then
      (Digest.ofBytes? r.digest.bytes).map (fun dg => some (Ref.mk dg)) else none) = some (some r)
    rw [if_pos rfl, Digest.ofBytes?_bytes, Option.map_some]

theorem prevOfVal_exact {v : Val} {p : Option (Ref (Annotation τ))} (h : prevOfVal v = some p) :
    v = prevToVal p := by
  unfold prevOfVal at h
  split at h
  · injection h with h
    subst h
    rfl
  · next b d =>
    split at h
    · next hb =>
      obtain ⟨dg, hdg, hp⟩ := Option.map_eq_some_iff.mp h
      subst hp
      show Val.some (.ref b d) = Val.some (.ref Kind.annotation.byte dg.bytes)
      rw [hb, Digest.ofBytes?_exact hdg]
    · exact nomatch h
  · exact nomatch h

/-- The shape: a struct of the subject, the value and the optional reference, over the value
type's table. -/
def shapeDoc (τ : Type) [Canonical τ] : ShapeDoc :=
  ⟨.struct "Annotation"
    [("subject", .anyRef), ("value", (shape τ).root), ("prev", .option (.ref .annotation))],
   (shape τ).defs⟩

/-- Constructor `0` with the three fields in declaration order. -/
def toVal [Canonical τ] (a : Annotation τ) : Val :=
  .ctor 0 [Canonical.toVal a.subject, Canonical.toVal a.value, prevToVal a.prev]

def ofVal [Canonical τ] : Val → Option (Annotation τ)
  | .ctor 0 [s₁, v₁, p₁] =>
    match Canonical.ofVal (α := AnyRef) s₁, Canonical.ofVal (α := τ) v₁, prevOfVal (τ := τ) p₁ with
    | some subject, some value, some prev => some ⟨subject, value, prev⟩
    | _, _, _ => none
  | _ => none

theorem ofVal_toVal [Canonical τ] (a : Annotation τ) : ofVal (toVal a) = some a := by
  obtain ⟨s, v, p⟩ := a
  simp [toVal, ofVal, Canonical.ofVal_toVal, prevOfVal_prevToVal]

theorem ofVal_exact [Canonical τ] {v : Val} {a : Annotation τ} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  · next s₁ v₁ p₁ =>
    split at h
    · next subject value prev hs hv hp =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact hs, Canonical.ofVal_exact hv, prevOfVal_exact hp]
    · exact nomatch h
  · exact nomatch h

theorem fits [Canonical τ] (a : Annotation τ) : (shapeDoc τ).accepts (toVal a) = true := by
  obtain ⟨s, v, p⟩ := a
  apply accepts_struct
  refine acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_cons _ _ _ _ _ _ ?_
    (acceptsFields_cons _ _ _ _ _ _ ?_ (acceptsFields_nil _)))
  · exact acceptsIn_mono_of_subset (d1 := []) (fun _ hp => (List.not_mem_nil hp).elim) _ _
      (Canonical.fits s)
  · exact Canonical.fits v
  · cases p with
    | none => exact accepts_option_none _ _
    | some r =>
      apply accepts_option_some
      show acceptsIn (shape τ).defs (.ref .annotation) (.ref Kind.annotation.byte r.digest.bytes) = true
      rw [acceptsIn_of_not_named (shape τ).defs (.ref .annotation) _ (fun _ h => nomatch h)]
      simp [acceptsAt, r.digest.length_eq]

end Annotation

/-- The trait as content: the structure rule, the three laws. -/
instance instCanonicalAnnotation {τ : Type} [Canonical τ] : Canonical (Annotation τ) where
  shape := Annotation.shapeDoc τ
  toVal := Annotation.toVal
  ofVal := Annotation.ofVal
  ofVal_toVal := Annotation.ofVal_toVal
  ofVal_exact := Annotation.ofVal_exact
  fits := Annotation.fits

/-- Traits file at kind `annotation`. -/
instance instContentAnnotation {τ : Type} [Canonical τ] : Content (Annotation τ) := ⟨.annotation⟩

/-! ## Reading traits off a store -/

namespace Node

/-- The subject of an annotation node: its first reference (the subject is field 0, so it is
edge 1 after the spec). -/
def subjectOf (n : Node) : Option AnyRef := n.refsOf.head?

/-- The `prev` of an annotation node: the third field, when it is a reference at kind
`annotation`. -/
def prevOf (n : Node) : Option Digest :=
  match n.payload with
  | .ctor 0 [_, _, .some (.ref b d)] => if b = Kind.annotation.byte then Digest.ofBytes? d else none
  | _ => none

end Node

/-- The annotation nodes whose subject is `subject`, in store order. -/
def Store.annotationsOf (s : Store) (subject : AnyRef) : List (Digest × Node) :=
  s.nodes.filter fun p => p.2.kind = .annotation && p.2.subjectOf = some subject

/-- Whether some annotation node names `d` as its `prev`. -/
def Store.superseded (s : Store) (d : Digest) : Bool :=
  s.nodes.any fun p => p.2.kind = .annotation && p.2.prevOf = some d

/-- The heads of the supersession forest: annotations of the subject that nothing supersedes. -/
def Store.traitsOf (s : Store) (subject : AnyRef) : List (Digest × Node) :=
  (s.annotationsOf subject).filter fun p => !s.superseded p.1

/-- The heads of a subject under a key (a trait's spec digest). -/
def Store.headsUnder (s : Store) (subject : AnyRef) (key : Digest) : List (Digest × Node) :=
  (s.traitsOf subject).filter fun p => p.2.spec = key

/-- The effective traits under a key: the node's own heads with that spec, else its spec node's,
else the registry node's; the first non-empty list. -/
def Store.effective (s : Store) (registry : Digest) (n : AnyRef) (key : Digest) : List (Digest × Node) :=
  let own := s.headsUnder n key
  if own.isEmpty then
    let atSpec := match s.find n.digest with
      | some m => s.headsUnder ⟨.schema, m.spec⟩ key
      | none => []
    if atSpec.isEmpty then
      match s.find registry with
      | some m => s.headsUnder ⟨m.kind, registry⟩ key
      | none => []
    else atSpec
  else own

/-! ## The laws -/

section Content

variable [Content Document]

/-- Traits never enter identity. A carrier's node bytes are a function of the value alone — the
header, the spec chosen for the value, the value tree — and mention no store; this is the
definition, so the theorem is `rfl`. -/
theorem nodeBytes_trait_free {α : Type} [Content α] (a : α) :
    (nodeOf a).encode = 0 :: (Content.kind α).byte :: ((specFor a).bytes ++ Val.encode (toVal a)) := rfl

/-- The store half: putting a trait leaves every resident node where it was, so no address a
store answers moves. -/
theorem trait_put_preserves {τ : Type} [Canonical τ] {t : Annotation τ} {s s' : Store} {o : Outcome}
    {r : Ref (Annotation τ)} (h : s.put t = .ok (o, r, s')) :
    ∀ d n, s.find d = some n → s'.find d = some n :=
  fun _ _ hd => put_preserves hd h

/-- Putting a trait leaves every typed read as it was. -/
theorem trait_get_preserves {τ β : Type} [Canonical τ] [Content β] {t : Annotation τ} {s s' : Store}
    {o : Outcome} {r : Ref (Annotation τ)} {q : Ref β} {b : β} (hg : s.get q = some b)
    (h : s.put t = .ok (o, r, s')) : s'.get q = some b :=
  get_preserves hg h

end Content

/-- Resolution is a function of the store. -/
theorem effective_deterministic {s s' : Store} (h : s = s') (registry : Digest) (n : AnyRef) (key : Digest) :
    s.effective registry n key = s'.effective registry n key := by
  subst h
  rfl

theorem superseded_perm {s s' : Store} (h : s.nodes.Perm s'.nodes) (d : Digest) :
    s.superseded d = s'.superseded d :=
  List.Perm.any_eq h

theorem annotationsOf_perm {s s' : Store} (h : s.nodes.Perm s'.nodes) (subject : AnyRef) :
    (s.annotationsOf subject).Perm (s'.annotationsOf subject) :=
  List.Perm.filter _ h

/-- The heads do not depend on the order the store lists its nodes in. -/
theorem traitsOf_perm {s s' : Store} (h : s.nodes.Perm s'.nodes) (subject : AnyRef) :
    (s.traitsOf subject).Perm (s'.traitsOf subject) := by
  unfold Store.traitsOf
  have h1 : ((s.annotationsOf subject).filter fun p => !s.superseded p.1).Perm
      ((s'.annotationsOf subject).filter fun p => !s.superseded p.1) :=
    List.Perm.filter _ (annotationsOf_perm h subject)
  have h2 : ((s'.annotationsOf subject).filter fun p => !s.superseded p.1) =
      (s'.annotationsOf subject).filter fun p => !s'.superseded p.1 :=
    List.filter_congr fun p _ => by rw [superseded_perm h]
  rw [h2] at h1
  exact h1

/-- The heads under a key do not depend on the order either. -/
theorem headsUnder_perm {s s' : Store} (h : s.nodes.Perm s'.nodes) (subject : AnyRef) (key : Digest) :
    (s.headsUnder subject key).Perm (s'.headsUnder subject key) :=
  List.Perm.filter _ (traitsOf_perm h subject)

/-! ## Traits on the probe store, guarded

A trait-spec node under the stand-in genesis, a trait on the entry, a superseding trait, a trait
on the entry's spec node, a registry node with a default trait, and two more export nodes to
resolve at the spec and registry levels. The entry's bytes and address are unchanged throughout. -/

/-- The entry's reference. -/
def entryRef : AnyRef := ⟨.«export», probeEntryAddress⟩

/-- A trait's spec node, itself a schema node under the stand-in genesis. -/
def traitSpec : Node := ⟨0, .schema, probeSchemaAddress, .str "trait-spec"⟩

def traitSpecAddress : Digest := sha256 traitSpec.encode

/-- A trait on the entry. -/
def trait1 : Annotation String := ⟨entryRef, "trusted", none⟩

def trait1Node : Node := ⟨0, .annotation, traitSpecAddress, Canonical.toVal trait1⟩

def trait1Address : Digest := sha256 trait1Node.encode

/-- The trait that supersedes it. -/
def trait2 : Annotation String := ⟨entryRef, "revoked", some ⟨trait1Address⟩⟩

def trait2Node : Node := ⟨0, .annotation, traitSpecAddress, Canonical.toVal trait2⟩

def trait2Address : Digest := sha256 trait2Node.encode

/-- A trait on the entry's spec node. -/
def trait3 : Annotation String := ⟨⟨.schema, probeSchemaAddress⟩, "at-spec", none⟩

def trait3Node : Node := ⟨0, .annotation, traitSpecAddress, Canonical.toVal trait3⟩

/-- The registry node: a tree under the stand-in genesis. -/
def registryNode : Node := ⟨0, .tree, probeSchemaAddress, .list []⟩

def registryAddress : Digest := sha256 registryNode.encode

/-- The registry's default trait. -/
def trait4 : Annotation String := ⟨⟨.tree, registryAddress⟩, "registry-default", none⟩

def trait4Node : Node := ⟨0, .annotation, traitSpecAddress, Canonical.toVal trait4⟩

/-- A second export under the stand-in spec (resolves at the spec level). -/
def export2 : Node := ⟨0, .«export», probeSchemaAddress, .nat 5⟩

/-- A third export under the trait spec (resolves at the registry level). -/
def export3 : Node := ⟨0, .«export», traitSpecAddress, .nat 7⟩

/-- The probe store with the trait world put on top. -/
def traitStore : Store :=
  afterPut (afterPut (afterPut (afterPut (afterPut (afterPut (afterPut probeStore traitSpec)
    trait1Node) trait3Node) registryNode) trait4Node) export2) export3

#guard (Canonical.encode trait1).length = 9 + 9 + 42 + (9 + 7) + 9
#guard (Canonical.ofVal (α := Annotation String) (Canonical.toVal trait1)).map Canonical.toVal
  = some (Canonical.toVal trait1)
#guard (Canonical.ofVal (α := Annotation String) (Canonical.toVal trait2)).map Canonical.toVal
  = some (Canonical.toVal trait2)
#guard ((Canonical.decode (α := Annotation String) (Canonical.encode trait2)).map Canonical.toVal
  = some (Canonical.toVal trait2))
#guard (Canonical.shape (Annotation String)).accepts (Canonical.toVal trait2) = true
#guard Canonical.ofVal (α := Annotation String)
  (.ctor 0 [Canonical.toVal entryRef, .str "x", .some (.ref 2 trait1Address.bytes)]) = none
#guard Canonical.ofVal (α := Annotation String)
  (.ctor 0 [Canonical.toVal entryRef, .str "x", .some (.ref 6 (trait1Address.bytes.drop 1))]) = none
#guard Canonical.ofVal (α := Annotation String) (.ctor 1 [Canonical.toVal entryRef, .str "x", .none]) = none
#guard Content.kind (Annotation String) = .annotation
#guard trait1Node.refsOf = [entryRef]
#guard trait1Node.subjectOf = some entryRef
#guard trait2Node.prevOf = some trait1Address
#guard trait1Node.prevOf = none
#guard outcomeIs (probeStore.putNode trait1Node) .fresh = false
#guard refusedWith (probeStore.putNode trait1Node) (.dangling traitSpecAddress)
#guard outcomeIs ((afterPut probeStore traitSpec).putNode trait1Node) .fresh
#guard traitStore.nodes.length = 9
#guard traitStore.find probeEntryAddress = some probeEntry
#guard (traitStore.find probeEntryAddress).map Node.encode = some probeEntry.encode
#guard traitStore.traitsOf entryRef = [(trait1Address, trait1Node)]
#guard traitStore.effective registryAddress entryRef traitSpecAddress = [(trait1Address, trait1Node)]
#guard traitStore.effective registryAddress entryRef probeSchemaAddress = []
#guard traitStore.effective registryAddress ⟨.«export», sha256 export2.encode⟩ traitSpecAddress
  = [(sha256 trait3Node.encode, trait3Node)]
#guard traitStore.effective registryAddress ⟨.«export», sha256 export3.encode⟩ traitSpecAddress
  = [(sha256 trait4Node.encode, trait4Node)]
#guard traitStore.effective zeroDigest ⟨.«export», sha256 export3.encode⟩ traitSpecAddress = []
#guard outcomeIs (traitStore.putNode trait2Node) .fresh
#guard (afterPut traitStore trait2Node).traitsOf entryRef = [(trait2Address, trait2Node)]
#guard (afterPut traitStore trait2Node).superseded trait1Address = true
#guard (afterPut traitStore trait2Node).superseded trait2Address = false
#guard (afterPut traitStore trait2Node).effective registryAddress entryRef traitSpecAddress
  = [(trait2Address, trait2Node)]
#guard (afterPut traitStore trait2Node).find probeEntryAddress = some probeEntry
#guard verified (afterPut traitStore trait2Node).verify

/-! ## Receipts -/

#print axioms Annotation.prevToVal
#print axioms Annotation.prevOfVal
#print axioms Annotation.prevOfVal_prevToVal
#print axioms Annotation.prevOfVal_exact
#print axioms Annotation.shapeDoc
#print axioms Annotation.toVal
#print axioms Annotation.ofVal
#print axioms Annotation.ofVal_toVal
#print axioms Annotation.ofVal_exact
#print axioms Annotation.fits
#print axioms instCanonicalAnnotation
#print axioms instContentAnnotation
#print axioms Node.subjectOf
#print axioms Node.prevOf
#print axioms Store.annotationsOf
#print axioms Store.superseded
#print axioms Store.traitsOf
#print axioms Store.headsUnder
#print axioms Store.effective
#print axioms nodeBytes_trait_free
#print axioms trait_put_preserves
#print axioms trait_get_preserves
#print axioms effective_deterministic
#print axioms superseded_perm
#print axioms annotationsOf_perm
#print axioms traitsOf_perm
#print axioms headsUnder_perm
#print axioms traitStore

end Effect4.Store
