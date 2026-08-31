import Effects.Cas.Node
import Effects.Wire.Nat32

/-!
# The canonical node codec

Pass-B resolution of the ratified provisional pre-image shape
(`versionByte ++ kindTag ++ frame(encode(canon node))`): the serialized form
leads with the scheme-version byte and the kind-tag byte — the two
domain-separation bytes the separation theorems quantify over — followed by
the framed payload, the reference count, and the fixed-width typed
references (one expected-tag byte plus thirty-two address bytes each).
Internal framing replaces one outer frame; determinism and exactness are
what the provisional shape existed to guarantee, and both are proved here.

Codec-law vocabulary follows the surveyed EverParse taxonomy
(`research/cas-soundness-roundtrip-references.md`):

- **forward correctness**: `decode (encodeNode n) = some n` for admitted
  nodes;
- **image exactness**: `decode b = some n → b = encodeNode n ∧ n.WF` — the
  decoder accepts nothing outside the encoder's image, so an admitted node
  has ONE byte representation (CAS-001's substance);
- **non-malleability / uniqueness**: `encodeNode_injOn`, a corollary; and
- **closed-input discipline**: `decode` rejects trailing bytes by
  construction.

Proof discipline, profiler-informed: parsers are `Option.bind` chains over
named stage readers with projection lambdas — no `match` anywhere in a
composition — and **no composition exceeds two stages**. Kernel re-checking
of composed rewrite motives scales badly with stages per proof (measured:
two-stage proofs check instantly; three-stage exhausts the kernel), so the
node parser factors as header → body → count, every layer two calls wide.
No recursion-budget options appear. Everything here is hash-lattice
Level 0: no premise about any hash appears.
-/

namespace Effects.Cas

open Effects.Wire

/-! ## Stage: one byte -/

def readByte : Bytes → Option (UInt8 × Bytes)
  | x :: rest => some (x, rest)
  | [] => none

theorem readByte_cons (x : UInt8) (rest : Bytes) :
    readByte (x :: rest) = some (x, rest) := rfl

theorem readByte_exact {b : Bytes} {x : UInt8} {rest : Bytes}
    (h : readByte b = some (x, rest)) : b = x :: rest := by
  match b with
  | [] => simp [readByte] at h
  | y :: r =>
    injection h with h
    injection h with h₁ h₂
    rw [h₁, h₂]

/-! ## Stage: one 32-byte address -/

def readAddr (b : Bytes) : Option (Addr32 × Bytes) :=
  match readChunk 32 b with
  | some (c, rest) => if h : c.length = 32 then some (⟨c, h⟩, rest) else none
  | none => none

theorem readAddr_append (a : Addr32) (rest : Bytes) :
    readAddr (a.val ++ rest) = some (a, rest) := by
  simp only [readAddr, readChunk_append rest a.property, dif_pos a.property]

theorem readAddr_exact {b : Bytes} {a : Addr32} {rest : Bytes}
    (h : readAddr b = some (a, rest)) : b = a.val ++ rest := by
  unfold readAddr at h
  split at h
  next c r hc =>
    split at h
    next hlen =>
      injection h with h
      injection h with h₁ h₂
      subst h₁ h₂
      exact (readChunk_exact hc).1
    next hlen => simp at h
  next hc => simp at h

/-! ## Stage: one typed reference -/

def encodeRef (r : Ref) : Bytes := r.expectedTag :: r.addr.val

def parseRef (b : Bytes) : Option (Ref × Bytes) :=
  (readByte b).bind fun tr =>
  (readAddr tr.2).bind fun ar =>
  some (⟨tr.1, ar.1⟩, ar.2)

theorem parseRef_encodeRef (r : Ref) (rest : Bytes) :
    parseRef (encodeRef r ++ rest) = some (r, rest) := by
  simp only [encodeRef, List.cons_append, parseRef, readByte_cons,
    Option.bind_some, readAddr_append]

theorem parseRef_exact {b : Bytes} {r : Ref} {rest : Bytes}
    (h : parseRef b = some (r, rest)) : b = encodeRef r ++ rest := by
  simp only [parseRef, Option.bind_eq_some_iff] at h
  obtain ⟨tr, h₁, ar, h₂, hlast⟩ := h
  injection hlast with hlast
  injection hlast with hr hrest
  subst hr hrest
  rw [readByte_exact h₁, readAddr_exact h₂, encodeRef, List.cons_append]

/-! ## Layer: the counted reference sequence -/

def parseCount (b : Bytes) : Option (List Ref × Bytes) :=
  (readNat32 b).bind fun cr =>
  readN parseRef cr.1 cr.2

theorem parseCount_encode (refs : List Ref) (hc : refs.length < 4294967296)
    (rest : Bytes) :
    parseCount (nat32 refs.length ++ ((refs.map encodeRef).flatten ++ rest))
      = some (refs, rest) := by
  simp only [parseCount, readNat32_nat32 refs.length hc _, Option.bind_some,
    readN_encode parseRef_encodeRef refs rest]

theorem parseCount_exact {b : Bytes} {refs : List Ref} {rest : Bytes}
    (h : parseCount b = some (refs, rest)) :
    b = nat32 refs.length ++ ((refs.map encodeRef).flatten ++ rest)
      ∧ refs.length < 4294967296 := by
  simp only [parseCount, Option.bind_eq_some_iff] at h
  obtain ⟨cr, hn, hrn⟩ := h
  obtain ⟨hb₁, hclt⟩ := readNat32_some _ _ _ hn
  obtain ⟨hb₂, hlen⟩ :=
    readN_exact (fun _b _a _r hh => parseRef_exact hh) cr.1 cr.2 refs rest hrn
  refine ⟨?_, by omega⟩
  rw [hb₁, hb₂, ← hlen]

/-! ## Layer: the node body -/

def parseBody (b : Bytes) : Option ((Bytes × List Ref) × Bytes) :=
  (readFrame b).bind fun pr =>
  (parseCount pr.2).bind fun cr =>
  some ((pr.1, cr.1), cr.2)

theorem parseBody_encode (payload : Bytes) (refs : List Ref)
    (hp : payload.length < 4294967296) (hc : refs.length < 4294967296)
    (rest : Bytes) :
    parseBody (frame payload ++
        (nat32 refs.length ++ ((refs.map encodeRef).flatten ++ rest)))
      = some ((payload, refs), rest) := by
  have h1 := readFrame_frame payload hp
    (nat32 refs.length ++ ((refs.map encodeRef).flatten ++ rest))
  have h2 := parseCount_encode refs hc rest
  calc parseBody (frame payload ++
          (nat32 refs.length ++ ((refs.map encodeRef).flatten ++ rest)))
      = (parseCount (nat32 refs.length ++
            ((refs.map encodeRef).flatten ++ rest))).bind
          (fun cr => some ((payload, cr.1), cr.2)) := by
        unfold parseBody; rw [h1, Option.bind_some]
    _ = some ((payload, refs), rest) := by rw [h2, Option.bind_some]

theorem parseBody_exact {b : Bytes} {payload : Bytes} {refs : List Ref}
    {rest : Bytes}
    (h : parseBody b = some ((payload, refs), rest)) :
    b = frame payload ++
        (nat32 refs.length ++ ((refs.map encodeRef).flatten ++ rest))
      ∧ payload.length < 4294967296 ∧ refs.length < 4294967296 := by
  simp only [parseBody, Option.bind_eq_some_iff] at h
  obtain ⟨pr, hf, cr, hcnt, hlast⟩ := h
  injection hlast with hlast
  injection hlast with hpr hrest
  injection hpr with hpay hrefs
  subst hpay hrefs hrest
  obtain ⟨hb₁, hplen⟩ := readFrame_exact hf
  obtain ⟨hb₂, hclen⟩ := parseCount_exact hcnt
  exact ⟨by rw [hb₁, hb₂], hplen, hclen⟩

/-! ## Layer: the node header -/

def parseHeader (b : Bytes) : Option ((UInt8 × UInt8) × Bytes) :=
  (readByte b).bind fun vb =>
  (readByte vb.2).bind fun tr =>
  some ((vb.1, tr.1), tr.2)

theorem parseHeader_cons (v t : UInt8) (rest : Bytes) :
    parseHeader (v :: t :: rest) = some ((v, t), rest) := by
  simp only [parseHeader, readByte_cons, Option.bind_some]

theorem parseHeader_exact {b : Bytes} {vt : UInt8 × UInt8} {rest : Bytes}
    (h : parseHeader b = some (vt, rest)) : b = vt.1 :: vt.2 :: rest := by
  simp only [parseHeader, Option.bind_eq_some_iff] at h
  obtain ⟨vb, h₀, tr, h₁, hlast⟩ := h
  injection hlast with hlast
  injection hlast with hvt hrest
  subst hvt hrest
  rw [readByte_exact h₀, readByte_exact h₁]

/-! ## The node codec -/

def encodeNode (n : Node) : Bytes :=
  n.version :: n.tag ::
    (frame n.payload ++ nat32 n.refs.length ++ (n.refs.map encodeRef).flatten)

def parseNode (b : Bytes) : Option (Node × Bytes) :=
  (parseHeader b).bind fun hd =>
  (parseBody hd.2).bind fun br =>
  some (⟨hd.1.1, hd.1.2, br.1.1, br.1.2⟩, br.2)

theorem parseNode_encodeNode (n : Node) (h : n.WF) (rest : Bytes) :
    parseNode (encodeNode n ++ rest) = some (n, rest) := by
  obtain ⟨hp, hc⟩ := h
  have h1 : parseHeader (encodeNode n ++ rest)
      = some ((n.version, n.tag),
          frame n.payload ++
            (nat32 n.refs.length ++ ((n.refs.map encodeRef).flatten ++ rest))) := by
    unfold encodeNode
    simp only [List.cons_append, List.append_assoc]
    rw [parseHeader_cons]
  have h2 := parseBody_encode n.payload n.refs hp hc rest
  calc parseNode (encodeNode n ++ rest)
      = (parseBody (frame n.payload ++
            (nat32 n.refs.length ++ ((n.refs.map encodeRef).flatten ++ rest)))).bind
          (fun br => some (⟨n.version, n.tag, br.1.1, br.1.2⟩, br.2)) := by
        unfold parseNode; rw [h1, Option.bind_some]
    _ = some (n, rest) := by rw [h2, Option.bind_some]

theorem parseNode_exact {b : Bytes} {n : Node} {rest : Bytes}
    (h : parseNode b = some (n, rest)) :
    b = encodeNode n ++ rest ∧ n.WF := by
  simp only [parseNode, Option.bind_eq_some_iff] at h
  obtain ⟨hd, h₀, br, hb, hlast⟩ := h
  injection hlast with hlast
  injection hlast with hnode hrest
  subst hnode hrest
  obtain ⟨hbody, hplen, hclen⟩ := parseBody_exact hb
  constructor
  · rw [parseHeader_exact h₀, hbody, encodeNode]
    simp [List.append_assoc]
  · exact ⟨hplen, hclen⟩

/-! ## The closed codec -/

/-- Decode a complete node: parse, then reject any trailing bytes. -/
def decode (b : Bytes) : Option Node :=
  (parseNode b).bind fun nr =>
  if _h : nr.2 = [] then some nr.1 else none

/-- The round trip with no remainder. -/
theorem parseNode_encodeNode' (n : Node) (h : n.WF) :
    parseNode (encodeNode n) = some (n, []) := by
  have := parseNode_encodeNode n h []
  rwa [List.append_nil] at this

theorem decode_encodeNode (n : Node) (h : n.WF) :
    decode (encodeNode n) = some n := by
  simp [decode, parseNode_encodeNode' n h]

theorem decode_exact {b : Bytes} {n : Node} (h : decode b = some n) :
    b = encodeNode n ∧ n.WF := by
  simp only [decode, Option.bind_eq_some_iff] at h
  obtain ⟨nr, hp, hlast⟩ := h
  split at hlast
  next hrest =>
    injection hlast with hlast
    subst hlast
    obtain ⟨hb, hwf⟩ := parseNode_exact hp
    rw [hrest, List.append_nil] at hb
    exact ⟨hb, hwf⟩
  next hrest => simp at hlast

/-- Non-malleability: one byte representation per admitted node — the
encoder is injective on the well-formed domain, a corollary of the round
trip. -/
theorem encodeNode_injOn {n m : Node} (hn : n.WF) (hm : m.WF)
    (h : encodeNode n = encodeNode m) : n = m := by
  have h1 := decode_encodeNode n hn
  rw [h, decode_encodeNode m hm] at h1
  injection h1 with h1
  exact h1.symm

/-! ## The admitted-node codec surface

The public laws over `AdmittedNode` — the carrier the CODEC schema instance
uses. The carrier admits no redundancy (its declared equivalence is
equality), so canonicalization is the identity and the canonicality content
lives where it belongs: in decoder exactness. -/

def encodeAdmitted (n : AdmittedNode) : Bytes := encodeNode n.val

def decodeAdmitted (b : Bytes) : Option AdmittedNode :=
  (decode b).bind fun n =>
  if h : n.WF then some ⟨n, h⟩ else none

theorem decodeAdmitted_encodeAdmitted (n : AdmittedNode) :
    decodeAdmitted (encodeAdmitted n) = some n := by
  simp only [decodeAdmitted, encodeAdmitted,
    decode_encodeNode n.val n.property, Option.bind_some,
    dif_pos n.property]

theorem decodeAdmitted_exact {b : Bytes} {n : AdmittedNode}
    (h : decodeAdmitted b = some n) : b = encodeAdmitted n := by
  simp only [decodeAdmitted, Option.bind_eq_some_iff] at h
  obtain ⟨m, hm, hlast⟩ := h
  split at hlast
  next hwf =>
    injection hlast with hlast
    subst hlast
    exact (decode_exact hm).1
  next hwf => simp at hlast

theorem encodeAdmitted_inj {n m : AdmittedNode}
    (h : encodeAdmitted n = encodeAdmitted m) : n = m :=
  Subtype.ext (encodeNode_injOn n.property m.property h)

end Effects.Cas
