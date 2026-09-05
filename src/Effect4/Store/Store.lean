import Effect4.Store.Node

/-!
# Store.Store

Owner: the heterogeneous node store, admission, the three put outcomes, the typed `put`/`get`
face over `Content`, closure as a theorem, and the roots plane.

The store is a list of nodes keyed by digest and a list of roots (Q3): ids are gone, names live
in the roots plane, and a node is found by its digest (`find`, the first binding). Admission
(`putNode`) refuses, in this order, a payload some frame of which is `2^64` bytes or longer
(`oversize`: the length prefix would lie), a version byte other than `0` (`badVersion`), a `ref`
frame with an unregistered kind byte or a wrong length (`malformedRef`), then an edge that names
no node (`dangling`) or a node of another kind (`wrongKind`). The spec edge is exempt exactly
for the genesis — kind `schema` with the zero spec — and for nothing else (Q6), so a zero spec
anywhere else is `dangling zeroDigest`. After admission the address is `sha256 (Node.encode n)`
and the outcome is `fresh` (appended), `duplicate` (the resident is `n`; nothing changes), or
`conflict occupant` (the resident differs: an exhibited collision, surfaced and never
overwritten — the store is grow-only).

`Closed` says every resident node's checked edges resolve at their kinds. It is a theorem about
stores, not a subtype: `empty_closed`, and `putNode_closed` for every outcome. `Sound` is the
full invariant a store built by `putNode` keeps — every resident node is version `0`, has a
well-formed payload and no malformed reference, sits at its own address, and the store is
`Closed`; `Word.verify` re-establishes it from bytes. `putNode_ok` is the one characterization
of a successful put; every other law of this module and of `Store.Word` is a corollary.

The typed face, under `variable [Content Document]`: `put a` is `putNode (nodeOf a)` with the
digest typed as `Ref α`, `get r` finds the node, checks its kind and reads the payload with
`ofVal`. `get_put` holds for `fresh` and `duplicate`; a `conflict` is the case where the
address is occupied by another node, and `put_conflict` says exactly that. `put_duplicate`
takes what the resident's own admission established (a well-formed payload, no malformed
reference, a closed store), because `putNode` checks admission before it looks the digest up.
Roots (Q7): the one mutable plane, moved by compare-and-set on an optimistic version
(`putRoot`), each root's target resolving at its kind.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4 (Document)

/-! ## Roots and the store -/

/-- The plane a root belongs to. -/
inductive RootKind where
  | stdlib
  | journal
  | daemon
  | schema
  | char
deriving DecidableEq, Repr, Inhabited

/-- The root kind's spelling. -/
def RootKind.name : RootKind → String
  | .stdlib => "stdlib"
  | .journal => "journal"
  | .daemon => "daemon"
  | .schema => "schema"
  | .char => "char"

/-- A root: a name for a node, with the kind the node must have and an optimistic version. -/
structure Root where
  name : String
  rootKind : RootKind
  kind : Kind
  digest : Digest
  version : Nat
deriving DecidableEq, Repr

/-- The store: nodes keyed by digest, in insertion order, and the roots. -/
structure Store where
  nodes : List (Digest × Node)
  roots : List Root
deriving Repr

/-- The empty store. -/
def Store.empty : Store := ⟨[], []⟩

/-- The first node filed under a digest. -/
def findIn : List (Digest × Node) → Digest → Option Node
  | [], _ => none
  | (d', n) :: rest, d => if d' = d then some n else findIn rest d

/-- The node at a digest, if any. -/
def Store.find (s : Store) (d : Digest) : Option Node := findIn s.nodes d

/-- The untyped read. -/
def Store.getNode (s : Store) (d : Digest) : Option Node := s.find d

theorem findIn_append_some {l₁ l₂ : List (Digest × Node)} {d : Digest} {n : Node}
    (h : findIn l₁ d = some n) : findIn (l₁ ++ l₂) d = some n := by
  induction l₁ with
  | nil => exact nomatch h
  | cons p rest ih =>
    obtain ⟨d', m⟩ := p
    by_cases hd : d' = d
    · simp only [findIn, List.cons_append, if_pos hd] at h ⊢
      exact h
    · simp only [findIn, List.cons_append, if_neg hd] at h ⊢
      exact ih h

theorem findIn_append_none {l₁ l₂ : List (Digest × Node)} {d : Digest}
    (h : findIn l₁ d = none) : findIn (l₁ ++ l₂) d = findIn l₂ d := by
  induction l₁ with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨d', m⟩ := p
    by_cases hd : d' = d
    · simp only [findIn, if_pos hd] at h
      exact nomatch h
    · simp only [findIn, List.cons_append, if_neg hd] at h ⊢
      exact ih h

/-- What is found is a binding of the list. -/
theorem findIn_mem {l : List (Digest × Node)} {d : Digest} {n : Node} (h : findIn l d = some n) :
    (d, n) ∈ l := by
  induction l with
  | nil => exact nomatch h
  | cons p rest ih =>
    obtain ⟨d', m⟩ := p
    by_cases hd : d' = d
    · simp only [findIn, if_pos hd] at h
      injection h with h
      subst hd h
      exact List.Mem.head _
    · simp only [findIn, if_neg hd] at h
      exact List.Mem.tail _ (ih h)

/-- A find in a list with one binding appended: the old answer, or the new binding when the old
answer was nothing. -/
theorem findIn_append_single {l : List (Digest × Node)} {d d' : Digest} {n m : Node}
    (h : findIn (l ++ [(d, n)]) d' = some m) :
    findIn l d' = some m ∨ (findIn l d' = none ∧ d' = d ∧ m = n) := by
  cases hl : findIn l d' with
  | some k =>
    rw [findIn_append_some hl] at h
    injection h with h
    exact Or.inl (by rw [h])
  | none =>
    rw [findIn_append_none hl] at h
    simp only [findIn] at h
    split at h
    · next hd =>
      injection h with h
      exact Or.inr ⟨rfl, hd.symm, h.symm⟩
    · exact nomatch h

/-! ## Admission -/

/-- Why a put or a root move is refused. -/
inductive Admission where
  /-- An edge names no node. -/
  | dangling (missing : Digest)
  /-- An edge names a node of another kind. -/
  | wrongKind (ref : Digest) (expected actual : Kind)
  /-- A `ref` frame with an unregistered kind byte or a digest that is not thirty-two bytes. -/
  | malformedRef
  /-- Some frame's payload is `2^64` bytes or longer: the length prefix would lie. -/
  | oversize
  /-- A version byte other than `0`. -/
  | badVersion
  /-- A root move whose version is not the resident's plus one. -/
  | staleRoot (name : String) (expected actual : Nat)
  /-- A word's binding whose address holds a different node: an exhibited collision, surfaced by
  `Word.apply`, never overwritten. -/
  | conflict (address : Digest) (occupant : Node)
deriving DecidableEq, Repr

/-- What a put did. -/
inductive Outcome where
  /-- The node was appended. -/
  | fresh
  /-- The node was already resident at its address; nothing changed. -/
  | duplicate
  /-- Another node is resident at the address; nothing changed, and the occupant is exhibited. -/
  | conflict (occupant : Node)
deriving DecidableEq, Repr

/-- An edge resolves: its digest is filed, at its kind. -/
def Store.Resolves (s : Store) (e : AnyRef) : Prop :=
  ∃ m, s.find e.digest = some m ∧ m.kind = e.kind

/-- One edge, checked. -/
def Store.checkEdge (s : Store) (e : AnyRef) : Except Admission Unit :=
  match s.find e.digest with
  | some m => if m.kind = e.kind then .ok () else .error (.wrongKind e.digest e.kind m.kind)
  | none => .error (.dangling e.digest)

/-- Edges checked in order; the first refusal is the answer. -/
def Store.checkAll (s : Store) : List AnyRef → Except Admission Unit
  | [] => .ok ()
  | e :: es =>
    match s.checkEdge e with
    | .ok () => s.checkAll es
    | .error a => .error a

/-- Every checked edge of a node resolves at its kind; the genesis's spec edge is exempt
(`Node.checkedEdges`). -/
def Store.checkEdges (s : Store) (n : Node) : Except Admission Unit := s.checkAll n.checkedEdges

theorem checkEdge_ok_iff (s : Store) (e : AnyRef) : s.checkEdge e = .ok () ↔ s.Resolves e := by
  unfold Store.checkEdge Store.Resolves
  constructor
  · intro h
    split at h
    · next m hm =>
      split at h
      · next hk => exact ⟨m, hm, hk⟩
      · exact nomatch h
    · exact nomatch h
  · intro ⟨m, hm, hk⟩
    simp only [hm, if_pos hk]

theorem checkAll_ok_iff (s : Store) :
    ∀ es : List AnyRef, s.checkAll es = .ok () ↔ ∀ e ∈ es, s.Resolves e
  | [] => by simp [Store.checkAll]
  | e :: es => by
    constructor
    · intro h
      simp only [Store.checkAll] at h
      split at h
      · next hce =>
        intro e' he'
        rcases List.mem_cons.mp he' with rfl | he'
        · exact (checkEdge_ok_iff s e').mp hce
        · exact ((checkAll_ok_iff s es).mp h) e' he'
      · exact nomatch h
    · intro h
      simp only [Store.checkAll, (checkEdge_ok_iff s e).mpr (h e (List.Mem.head _))]
      exact (checkAll_ok_iff s es).mpr fun e' he' => h e' (List.Mem.tail _ he')

theorem checkEdges_ok_iff (s : Store) (n : Node) :
    s.checkEdges n = .ok () ↔ ∀ e ∈ n.checkedEdges, s.Resolves e :=
  checkAll_ok_iff s n.checkedEdges

/-! ## Closure and growth -/

/-- Every resident node's checked edges resolve at their kinds. -/
def Closed (s : Store) : Prop :=
  ∀ d n, s.find d = some n → ∀ e ∈ n.checkedEdges, s.Resolves e

theorem empty_closed : Closed Store.empty := fun _ _ h => nomatch h

/-- Every node of `a` is a node of `b`, at the same digest. -/
def Store.sub (a b : Store) : Prop := ∀ d n, a.find d = some n → b.find d = some n

theorem Store.sub_refl (s : Store) : s.sub s := fun _ _ h => h

theorem Store.sub_trans {a b c : Store} (h₁ : a.sub b) (h₂ : b.sub c) : a.sub c :=
  fun d n h => h₂ d n (h₁ d n h)

/-- Resolution survives growth. -/
theorem resolves_mono {a b : Store} (h : a.sub b) {e : AnyRef} (hr : a.Resolves e) : b.Resolves e :=
  let ⟨m, hm, hk⟩ := hr
  ⟨m, h _ _ hm, hk⟩

/-! ## The put -/

/-- Admission, then the address, then the outcome. -/
def Store.putNode (s : Store) (n : Node) : Except Admission (Outcome × Digest × Store) :=
  if n.payload.WF then
    if n.version = 0 then
      if n.malformedRef then .error .malformedRef
      else
        match s.checkEdges n with
        | .error a => .error a
        | .ok () =>
          match s.find (sha256 n.encode) with
          | some m =>
            if m = n then .ok (.duplicate, sha256 n.encode, s)
            else .ok (.conflict m, sha256 n.encode, s)
          | none => .ok (.fresh, sha256 n.encode, { s with nodes := s.nodes ++ [(sha256 n.encode, n)] })
    else .error .badVersion
  else .error .oversize

theorem bool_eq_false_of_not {b : Bool} (h : ¬ b = true) : b = false := by
  cases b
  · rfl
  · exact absurd rfl h

/-- The one characterization of a successful put: what admission established, the address, and
the outcome with the store it left. -/
theorem putNode_ok {s : Store} {n : Node} {o : Outcome} {d : Digest} {s' : Store}
    (h : s.putNode n = .ok (o, d, s')) :
    n.payload.WF ∧ n.version = 0 ∧ n.malformedRef = false ∧
      (∀ e ∈ n.checkedEdges, s.Resolves e) ∧ d = sha256 n.encode ∧
      ((o = .fresh ∧ s.find d = none ∧ s' = { s with nodes := s.nodes ++ [(d, n)] }) ∨
       (o = .duplicate ∧ s.find d = some n ∧ s' = s) ∨
       (∃ m, o = .conflict m ∧ s.find d = some m ∧ m ≠ n ∧ s' = s)) := by
  unfold Store.putNode at h
  split at h
  · next hwf =>
    split at h
    · next hv =>
      split at h
      · exact nomatch h
      · next hm =>
        split at h
        · exact nomatch h
        · next hce =>
          have hres := (checkEdges_ok_iff s n).mp hce
          have hm' := bool_eq_false_of_not hm
          split at h
          · next m hfind =>
            split at h
            · next heq =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨ho, hd, hs⟩ := h
              subst heq
              refine ⟨hwf, hv, hm', hres, hd.symm, Or.inr (Or.inl ⟨ho.symm, ?_, hs.symm⟩)⟩
              rw [← hd]
              exact hfind
            · next hne =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨ho, hd, hs⟩ := h
              refine ⟨hwf, hv, hm', hres, hd.symm, Or.inr (Or.inr ⟨m, ho.symm, ?_, hne, hs.symm⟩)⟩
              rw [← hd]
              exact hfind
          · next hfind =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨ho, hd, hs⟩ := h
            refine ⟨hwf, hv, hm', hres, hd.symm, Or.inl ⟨ho.symm, ?_, ?_⟩⟩
            · rw [← hd]
              exact hfind
            · rw [← hs, hd]
    · exact nomatch h
  · exact nomatch h

/-- The put of an admissible node whose address is free: `fresh`, appended. -/
theorem putNode_fresh {s : Store} {n : Node} (hwf : n.payload.WF) (hv : n.version = 0)
    (hm : n.malformedRef = false) (he : ∀ e ∈ n.checkedEdges, s.Resolves e)
    (hf : s.find (sha256 n.encode) = none) :
    s.putNode n = .ok (.fresh, sha256 n.encode, { s with nodes := s.nodes ++ [(sha256 n.encode, n)] }) := by
  unfold Store.putNode
  rw [if_pos hwf, if_pos hv, hm, if_neg Bool.false_ne_true, (checkEdges_ok_iff s n).mpr he]
  simp only [hf]

/-- The put of an admissible node already resident at its address: `duplicate`, unchanged. -/
theorem putNode_duplicate {s : Store} {n : Node} (hwf : n.payload.WF) (hv : n.version = 0)
    (hm : n.malformedRef = false) (he : ∀ e ∈ n.checkedEdges, s.Resolves e)
    (hf : s.find (sha256 n.encode) = some n) :
    s.putNode n = .ok (.duplicate, sha256 n.encode, s) := by
  unfold Store.putNode
  rw [if_pos hwf, if_pos hv, hm, if_neg Bool.false_ne_true, (checkEdges_ok_iff s n).mpr he]
  simp only [hf, if_true]

/-- A put never removes or replaces a node: the store is grow-only. -/
theorem putNode_sub {s : Store} {n : Node} {o : Outcome} {d : Digest} {s' : Store}
    (h : s.putNode n = .ok (o, d, s')) : s.sub s' := by
  obtain ⟨_, _, _, _, _, hcase⟩ := putNode_ok h
  intro d' m hm
  rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨k, _, _, _, rfl⟩
  · exact findIn_append_some hm
  · exact hm
  · exact hm

/-- After a `fresh` or `duplicate` put, the node is resident at its address. -/
theorem putNode_find {s : Store} {n : Node} {o : Outcome} {d : Digest} {s' : Store}
    (h : s.putNode n = .ok (o, d, s')) (ho : ∀ m, o ≠ .conflict m) : s'.find d = some n := by
  obtain ⟨_, _, _, _, _, hcase⟩ := putNode_ok h
  rcases hcase with ⟨_, hf, rfl⟩ | ⟨_, hf, rfl⟩ | ⟨k, hk, _, _, _⟩
  · show findIn (s.nodes ++ [(d, n)]) d = some n
    rw [findIn_append_none hf]
    simp [findIn]
  · exact hf
  · exact absurd hk (ho k)

/-- Closure survives every put: the resident nodes keep their edges, and a fresh node's edges
were resolved at admission. -/
theorem putNode_closed {s : Store} {n : Node} {o : Outcome} {d : Digest} {s' : Store}
    (hc : Closed s) (h : s.putNode n = .ok (o, d, s')) : Closed s' := by
  obtain ⟨_, _, _, hres, _, hcase⟩ := putNode_ok h
  have hsub := putNode_sub h
  rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨k, _, _, _, rfl⟩
  · intro d' m hm e he
    have hm' : findIn (s.nodes ++ [(d, n)]) d' = some m := hm
    rcases findIn_append_single hm' with hold | ⟨_, rfl, rfl⟩
    · exact resolves_mono hsub (hc d' m hold e he)
    · exact resolves_mono hsub (hres e he)
  · exact hc
  · exact hc

/-- The brief's name for closure preservation. -/
theorem putNode_fresh_closed {s : Store} {n : Node} {o : Outcome} {d : Digest} {s' : Store}
    (hc : Closed s) (h : s.putNode n = .ok (o, d, s')) : Closed s' :=
  putNode_closed hc h

/-- The invariant a store built by `putNode` keeps: every resident node would be admitted into
the store around it, and sits at its own address. -/
structure Store.Sound (s : Store) : Prop where
  version : ∀ d n, s.find d = some n → n.version = 0
  wf : ∀ d n, s.find d = some n → n.payload.WF
  refs : ∀ d n, s.find d = some n → n.malformedRef = false
  addressed : ∀ d n, s.find d = some n → d = sha256 n.encode
  closed : Closed s

theorem empty_sound : Store.empty.Sound :=
  ⟨(fun _ _ h => nomatch h), (fun _ _ h => nomatch h), (fun _ _ h => nomatch h),
    (fun _ _ h => nomatch h), empty_closed⟩

theorem putNode_sound {s : Store} {n : Node} {o : Outcome} {d : Digest} {s' : Store}
    (hs : s.Sound) (h : s.putNode n = .ok (o, d, s')) : s'.Sound := by
  obtain ⟨hwf, hv, hm, _, hd, hcase⟩ := putNode_ok h
  have hcl := putNode_closed hs.closed h
  rcases hcase with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ | ⟨k, _, _, _, rfl⟩
  · refine ⟨?_, ?_, ?_, ?_, hcl⟩
    · intro d' m hm'
      rcases findIn_append_single (l := s.nodes) hm' with hold | ⟨_, _, rfl⟩
      · exact hs.version d' m hold
      · exact hv
    · intro d' m hm'
      rcases findIn_append_single (l := s.nodes) hm' with hold | ⟨_, _, rfl⟩
      · exact hs.wf d' m hold
      · exact hwf
    · intro d' m hm'
      rcases findIn_append_single (l := s.nodes) hm' with hold | ⟨_, _, rfl⟩
      · exact hs.refs d' m hold
      · exact hm
    · intro d' m hm'
      rcases findIn_append_single (l := s.nodes) hm' with hold | ⟨_, rfl, rfl⟩
      · exact hs.addressed d' m hold
      · exact hd
  · exact hs
  · exact hs

/-! ## The typed face: under `Content Document` -/

section Content

variable [Content Document]

/-- The typed put: the carrier's node, its address as a `Ref α`. -/
def Store.put {α : Type} [Content α] (a : α) (s : Store) : Except Admission (Outcome × Ref α × Store) :=
  match s.putNode (nodeOf a) with
  | .ok (o, d, s') => .ok (o, ⟨d⟩, s')
  | .error e => .error e

/-- The typed get: find, check the kind, read the payload. -/
def Store.get {α : Type} [Content α] (r : Ref α) (s : Store) : Option α :=
  match s.find r.digest with
  | some n => if n.kind = Content.kind α then ofVal n.payload else none
  | none => none

theorem put_ok {α : Type} [Content α] {a : α} {s : Store} {o : Outcome} {r : Ref α} {s' : Store}
    (h : s.put a = .ok (o, r, s')) :
    s.putNode (nodeOf a) = .ok (o, r.digest, s') ∧ r = address a := by
  unfold Store.put at h
  split at h
  · next o' d s'' hp =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    refine ⟨hp, ?_⟩
    obtain ⟨_, _, _, _, hd, _⟩ := putNode_ok hp
    exact Ref.ext hd
  · exact nomatch h

/-- What was put reads back, unless the address was occupied by another node. -/
theorem get_put {α : Type} [Content α] {a : α} {s : Store} {o : Outcome} {r : Ref α} {s' : Store}
    (h : s.put a = .ok (o, r, s')) (hc : ∀ m, o ≠ .conflict m) : s'.get r = some a := by
  obtain ⟨hp, _⟩ := put_ok h
  have hf := putNode_find hp hc
  unfold Store.get
  simp only [hf, nodeOf_kind, nodeOf_payload, ofVal_toVal, if_true]

/-- A conflict: the store is unchanged and another node sits at the carrier's address. -/
theorem put_conflict {α : Type} [Content α] {a : α} {s : Store} {m : Node} {r : Ref α} {s' : Store}
    (h : s.put a = .ok (.conflict m, r, s')) :
    s' = s ∧ s.find r.digest = some m ∧ m ≠ nodeOf a := by
  obtain ⟨hp, _⟩ := put_ok h
  obtain ⟨_, _, _, _, _, hcase⟩ := putNode_ok hp
  rcases hcase with ⟨ho, _, _⟩ | ⟨ho, _, _⟩ | ⟨k, ho, hf, hne, hs⟩
  · exact nomatch ho
  · exact nomatch ho
  · injection ho with ho
    subst ho
    exact ⟨hs, hf, hne⟩

/-- Putting a carrier whose node is resident is a `duplicate` that changes nothing. The premises
are what the resident's own admission established. -/
theorem put_duplicate {α : Type} [Content α] {a : α} {s : Store}
    (hres : s.find (address a).digest = some (nodeOf a)) (hwf : (toVal a).WF)
    (hm : (nodeOf a).malformedRef = false) (hc : Closed s) :
    s.put a = .ok (.duplicate, address a, s) := by
  have hp := putNode_duplicate (s := s) (n := nodeOf a) hwf rfl hm (hc _ _ hres) hres
  unfold Store.put
  rw [hp]
  rfl

/-- A put leaves every resident node where it was. -/
theorem put_preserves {α : Type} [Content α] {a : α} {s : Store} {d : Digest} {n : Node}
    {o : Outcome} {r : Ref α} {s' : Store} (hd : s.find d = some n) (h : s.put a = .ok (o, r, s')) :
    s'.find d = some n :=
  putNode_sub (put_ok h).1 d n hd

/-- A put leaves every typed read as it was. -/
theorem get_preserves {α β : Type} [Content α] [Content β] {a : α} {s : Store} {o : Outcome}
    {r : Ref α} {s' : Store} {q : Ref β} {b : β} (hg : s.get q = some b) (h : s.put a = .ok (o, r, s')) :
    s'.get q = some b := by
  unfold Store.get at hg ⊢
  split at hg
  · next n hn =>
    simp only [put_preserves hn h]
    exact hg
  · exact nomatch hg

end Content

/-! ## The roots plane -/

/-- The root with a name, if any. -/
def Store.root? (s : Store) (name : String) : Option Root := s.roots.find? fun r => r.name = name

/-- The version a root move must carry: the resident's plus one, or `1` when absent. -/
def Store.nextVersion (s : Store) (name : String) : Nat :=
  match s.root? name with
  | some old => old.version + 1
  | none => 1

/-- Compare-and-set on a root: the version must be the next one, the target must resolve at the
root's kind; the resident root of that name is replaced. -/
def Store.putRoot (s : Store) (r : Root) : Except Admission Store :=
  if r.version = s.nextVersion r.name then
    match s.find r.digest with
    | some m =>
      if m.kind = r.kind then .ok { s with roots := r :: s.roots.filter fun q => q.name ≠ r.name }
      else .error (.wrongKind r.digest r.kind m.kind)
    | none => .error (.dangling r.digest)
  else .error (.staleRoot r.name (s.nextVersion r.name) r.version)

/-- A root move touches no node. -/
theorem putRoot_nodes {s s' : Store} {r : Root} (h : s.putRoot r = .ok s') : s'.nodes = s.nodes := by
  unfold Store.putRoot at h
  split at h
  · split at h
    · split at h
      · injection h with h
        subst h
        rfl
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-- After a root move, the name answers the new root. -/
theorem putRoot_root? {s s' : Store} {r : Root} (h : s.putRoot r = .ok s') : s'.root? r.name = some r := by
  unfold Store.putRoot at h
  split at h
  · split at h
    · split at h
      · injection h with h
        subst h
        simp [Store.root?, List.find?]
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

/-! ## Admission and the outcomes, guarded

A genesis-shaped schema node (kind `schema`, zero spec) enters an empty store; a node whose spec
is that address enters fresh, then duplicates; a zero spec anywhere else dangles; a reference of
the wrong kind, a bad version and a malformed reference refuse; a hand-built occupant exhibits a
conflict; a root moves under compare-and-set. -/

/-- A stand-in for the genesis: kind `schema`, zero spec, any payload. -/
def probeSchema : Node := ⟨0, .schema, zeroDigest, .str "schema"⟩

/-- Its address. -/
def probeSchemaAddress : Digest := sha256 probeSchema.encode

/-- The census entry under the stand-in spec. -/
def probeEntry : Node := ⟨0, .«export», probeSchemaAddress, sampleEntry⟩

/-- Its address. -/
def probeEntryAddress : Digest := sha256 probeEntry.encode

/-- Whether a put answered a given outcome. -/
def outcomeIs (r : Except Admission (Outcome × Digest × Store)) (o : Outcome) : Bool :=
  match r with
  | .ok (o', _, _) => o' = o
  | .error _ => false

/-- Whether a put refused with a given reason. -/
def refusedWith (r : Except Admission (Outcome × Digest × Store)) (a : Admission) : Bool :=
  match r with
  | .error a' => a' = a
  | .ok _ => false

/-- The store after a put, or the store before it when the put refused. -/
def afterPut (s : Store) (n : Node) : Store :=
  match s.putNode n with
  | .ok (_, _, s') => s'
  | .error _ => s

/-- The stand-in genesis, then the entry. -/
def probeStore : Store := afterPut (afterPut Store.empty probeSchema) probeEntry

#guard outcomeIs (Store.empty.putNode probeSchema) .fresh
#guard outcomeIs ((afterPut Store.empty probeSchema).putNode probeEntry) .fresh
#guard outcomeIs (probeStore.putNode probeEntry) .duplicate
#guard outcomeIs (probeStore.putNode probeSchema) .duplicate
#guard probeStore.nodes.length = 2
#guard probeStore.find probeEntryAddress = some probeEntry
#guard probeStore.getNode probeSchemaAddress = some probeSchema
#guard probeStore.find zeroDigest = none
#guard refusedWith (Store.empty.putNode probeEntry) (.dangling probeSchemaAddress)
#guard refusedWith (probeStore.putNode ⟨0, .«export», zeroDigest, sampleEntry⟩) (.dangling zeroDigest)
#guard refusedWith (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 2 probeSchemaAddress.bytes⟩)
  (.wrongKind probeSchemaAddress .«export» .schema)
#guard outcomeIs (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 2 probeEntryAddress.bytes⟩) .fresh
#guard refusedWith (probeStore.putNode ⟨1, .«export», probeSchemaAddress, sampleEntry⟩) .badVersion
#guard refusedWith (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 16 probeEntryAddress.bytes⟩) .malformedRef
#guard refusedWith (probeStore.putNode ⟨0, .tree, probeSchemaAddress, .ref 2 (probeEntryAddress.bytes.drop 1)⟩) .malformedRef
#guard outcomeIs ((Store.mk [(probeSchemaAddress, probeSchema), (probeEntryAddress, ⟨0, .«export», probeSchemaAddress, .nat 1⟩)] []).putNode probeEntry)
  (.conflict ⟨0, .«export», probeSchemaAddress, .nat 1⟩)
#guard (afterPut (Store.mk [(probeSchemaAddress, probeSchema), (probeEntryAddress, ⟨0, .«export», probeSchemaAddress, .nat 1⟩)] []) probeEntry).nodes.length = 2
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩ with
  | .ok s => s.root? "stdlib/rc112" = some ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩
  | .error _ => false)
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 2⟩ with
  | .error (.staleRoot "stdlib/rc112" 1 2) => true
  | _ => false)
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .schema, probeEntryAddress, 1⟩ with
  | .error (.wrongKind _ .schema .«export») => true
  | _ => false)
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», zeroDigest, 1⟩ with
  | .error (.dangling _) => true
  | _ => false)
#guard (match probeStore.putRoot ⟨"stdlib/rc112", .stdlib, .«export», probeEntryAddress, 1⟩ with
  | .ok s =>
    match s.putRoot ⟨"stdlib/rc112", .stdlib, .schema, probeSchemaAddress, 2⟩ with
    | .ok s' => s'.root? "stdlib/rc112" = some ⟨"stdlib/rc112", .stdlib, .schema, probeSchemaAddress, 2⟩ ∧ s'.roots.length = 1
    | .error _ => false
  | .error _ => false)

/-! ## Receipts -/

#print axioms RootKind.name
#print axioms Store.empty
#print axioms findIn
#print axioms Store.find
#print axioms Store.getNode
#print axioms findIn_append_some
#print axioms findIn_append_none
#print axioms findIn_mem
#print axioms findIn_append_single
#print axioms Store.Resolves
#print axioms Store.checkEdge
#print axioms Store.checkAll
#print axioms Store.checkEdges
#print axioms checkEdge_ok_iff
#print axioms checkAll_ok_iff
#print axioms checkEdges_ok_iff
#print axioms Closed
#print axioms empty_closed
#print axioms Store.sub
#print axioms Store.sub_refl
#print axioms Store.sub_trans
#print axioms resolves_mono
#print axioms Store.putNode
#print axioms bool_eq_false_of_not
#print axioms putNode_ok
#print axioms putNode_fresh
#print axioms putNode_duplicate
#print axioms putNode_sub
#print axioms putNode_find
#print axioms putNode_closed
#print axioms putNode_fresh_closed
#print axioms empty_sound
#print axioms putNode_sound
#print axioms Store.put
#print axioms Store.get
#print axioms put_ok
#print axioms get_put
#print axioms put_conflict
#print axioms put_duplicate
#print axioms put_preserves
#print axioms get_preserves
#print axioms Store.root?
#print axioms Store.nextVersion
#print axioms Store.putRoot
#print axioms putRoot_nodes
#print axioms putRoot_root?
#print axioms probeStore

end Effect4.Store
