import Effects.Merkle.Verify

/-!
# The verified-streaming decoder — a sans-io machine

State and one parsed input in; the successor state and decisions out.
The machine consumes a pre-order encoding stream (bao's layout:
verification order equals read order, no seeking) against an expected
root and a declared chunk count, holding a stack of expected subtree
addresses. A chunk is emitted ONLY in the branch where it verified
against its expected address — the emission gate is structural. The
length is validated exactly when the final chunk validates (bao's
final-chunk requirement), and a slice range makes out-of-range
subtrees skippable: the extractor omits their contents and the decoder
pops them on an explicit skip token, their addresses already bound by
their parents.

Byte-level parsing sits below this altitude in the codec layer; the
machine's input alphabet is parsed nodes, which is exactly what makes
transport fragmentation semantically irrelevant here (the run is a
pure fold — the composition law is this obligation's carrier).
-/

namespace Effects.Merkle

open Effects.Cas (Bytes)

variable {A : Type}

/-- A parsed encoding node: a parent's two child addresses, a chunk's
bytes, or the explicit skip token a slice extractor emits for an
omitted subtree. -/
inductive DInput (A : Type) where
  | parentNode (left right : A)
  | chunkNode (bytes : Bytes)
  | skipNode
  deriving DecidableEq

/-- One expected subtree: its address, the absolute index of its first
chunk, and its chunk count. -/
structure Frame (A : Type) where
  expected : A
  base : Nat
  count : Nat
  deriving DecidableEq

inductive DStatus where
  | active
  | rejected
  | done
  deriving DecidableEq

structure DState (A : Type) where
  stack : List (Frame A)
  status : DStatus

/-- The decoder's environment: the address function, the declared chunk
count (untrusted declaration — the geometry it induces is verified
chunk by chunk), the expected root, and the requested slice range in
chunk indices. The whole decode is the full range. -/
structure DParams (A : Type) where
  P : HP A
  total : Nat
  expectedRoot : A
  lo : Nat
  hi : Nat

inductive DDecision (A : Type) where
  | emitted (index : Nat) (bytes : Bytes)
  | lengthValidated
  | rejectedNode
  deriving DecidableEq

structure DStep (A : Type) where
  state : DState A
  decisions : List (DDecision A)

def initState (D : DParams A) : DState A :=
  { stack := [⟨D.expectedRoot, 0, D.total⟩], status := .active }

/-- A frame entirely outside the requested range. -/
def DParams.disjoint (D : DParams A) (f : Frame A) : Prop :=
  f.base + f.count ≤ D.lo ∨ D.hi ≤ f.base

instance (D : DParams A) (f : Frame A) : Decidable (D.disjoint f) := by
  unfold DParams.disjoint
  infer_instance

def rejectOut (s : DState A) : DStep A :=
  ⟨⟨s.stack, .rejected⟩, [.rejectedNode]⟩

def popped (rest : List (Frame A)) : DState A :=
  ⟨rest, if rest.isEmpty then .done else .active⟩

/-- The total decoder step. -/
def dstep [DecidableEq A] (D : DParams A) (s : DState A) (i : DInput A) :
    DStep A :=
  match s.status with
  | .rejected => ⟨s, []⟩
  | .done => ⟨s, []⟩
  | .active =>
    match s.stack with
    | [] => ⟨s, []⟩
    | f :: rest =>
      if D.disjoint f then
        match i with
        | .skipNode => ⟨popped rest, []⟩
        | _ => rejectOut s
      else if f.count ≤ 1 then
        match i with
        | .chunkNode c =>
          if D.P.H (.leaf f.base c) = f.expected then
            ⟨popped rest,
              if f.base + 1 = D.total then
                [.emitted f.base c, .lengthValidated]
              else [.emitted f.base c]⟩
          else rejectOut s
        | _ => rejectOut s
      else
        match i with
        | .parentNode l r =>
          if D.P.H (.parent l r) = f.expected then
            ⟨⟨⟨l, f.base, pow2Below f.count⟩ ::
               ⟨r, f.base + pow2Below f.count, f.count - pow2Below f.count⟩ ::
               rest, .active⟩, []⟩
          else rejectOut s
        | _ => rejectOut s

/-- Run the decoder over an input list, collecting decisions. -/
def drun [DecidableEq A] (D : DParams A) :
    DState A → List (DInput A) → DState A × List (DDecision A)
  | s, [] => (s, [])
  | s, i :: is =>
    ((drun D (dstep D s i).state is).1,
      (dstep D s i).decisions ++ (drun D (dstep D s i).state is).2)

/-- The model-side extractor: the pre-order encoding stream for a
subtree, with out-of-range subtrees replaced by the skip token. The
whole encoding is the full range. -/
def genStream (P : HP A) (lo hi base : Nat) (chunks : List Bytes) :
    List (DInput A) :=
  if base + chunks.length ≤ lo ∨ hi ≤ base then [.skipNode]
  else if _h : chunks.length ≤ 1 then [.chunkNode (chunks.headD [])]
  else
    .parentNode (root P base (chunks.take (pow2Below chunks.length)))
        (root P (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length))) ::
      (genStream P lo hi base (chunks.take (pow2Below chunks.length)) ++
        genStream P lo hi (base + pow2Below chunks.length)
          (chunks.drop (pow2Below chunks.length)))
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

/-- The emissions a range decode owes: the indexed chunks of the
subtree, restricted to the range, in index order. -/
def rangedEmissions (lo hi base : Nat) (chunks : List Bytes) :
    List (Nat × Bytes) :=
  if base + chunks.length ≤ lo ∨ hi ≤ base then []
  else if _h : chunks.length ≤ 1 then [(base, chunks.headD [])]
  else
    rangedEmissions lo hi base (chunks.take (pow2Below chunks.length)) ++
      rangedEmissions lo hi (base + pow2Below chunks.length)
        (chunks.drop (pow2Below chunks.length))
termination_by chunks.length
decreasing_by
  · have hk := pow2Below_lt chunks.length (by omega)
    simp only [List.length_take]
    omega
  · have hk := pow2Below_pos chunks.length
    simp only [List.length_drop]
    omega

/-- One frame's accepting consumption: the derivation-tree relation the
machine's runs decompose into. Skip consumes the token for a disjoint
frame without verifying anything (its address was bound by its parent);
a leaf consumes its verified chunk; a node consumes its verified parent
followed by both children's consumptions. -/
inductive Consumes [DecidableEq A] (D : DParams A) :
    Frame A → List (DInput A) → List (Nat × Bytes) → Prop where
  | skip {f : Frame A} (hd : D.disjoint f) :
      Consumes D f [.skipNode] []
  | leaf {f : Frame A} {c : Bytes} (hd : ¬ D.disjoint f)
      (hc : f.count ≤ 1) (hh : D.P.H (.leaf f.base c) = f.expected) :
      Consumes D f [.chunkNode c] [(f.base, c)]
  | node {f : Frame A} {l r : A} {in₁ in₂ : List (DInput A)}
      {es₁ es₂ : List (Nat × Bytes)}
      (hd : ¬ D.disjoint f) (hc : ¬ f.count ≤ 1)
      (hh : D.P.H (.parent l r) = f.expected)
      (h₁ : Consumes D ⟨l, f.base, pow2Below f.count⟩ in₁ es₁)
      (h₂ : Consumes D ⟨r, f.base + pow2Below f.count,
              f.count - pow2Below f.count⟩ in₂ es₂) :
      Consumes D f (.parentNode l r :: (in₁ ++ in₂)) (es₁ ++ es₂)

/-- Sequential consumption of a frame stack. -/
inductive ConsumesStack [DecidableEq A] (D : DParams A) :
    List (Frame A) → List (DInput A) → List (Nat × Bytes) → Prop where
  | nil : ConsumesStack D [] [] []
  | cons {f : Frame A} {fs : List (Frame A)} {in₁ in₂ : List (DInput A)}
      {es₁ es₂ : List (Nat × Bytes)}
      (h₁ : Consumes D f in₁ es₁) (h₂ : ConsumesStack D fs in₂ es₂) :
      ConsumesStack D (f :: fs) (in₁ ++ in₂) (es₁ ++ es₂)

end Effects.Merkle
