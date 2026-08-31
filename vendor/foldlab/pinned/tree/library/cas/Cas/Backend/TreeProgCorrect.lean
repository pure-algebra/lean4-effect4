import Cas.Backend.EmitProg
import Cas.Backend.ProgProse
import Cas.Lang.TreeProg
import Cas.Lang.Wp
import Cas.Vectors.Registry
import Cas.Codec.Sha256

/-!
# `treeProg` correctness — the emitted table IS the term's program

The contract packet is `library/cas/contracts/PDD-9.contract.md`; every
law below is named there with its falsifier.

Three lowerings of one grammar term live at HEAD and no theorem related
any pair (THE-ALGEBRA §3.31): `Tree.progK` into `Prog`
(`Cas/Lang/TreeProg.lean:40`), `treeProg` into `PProg`
(`Cas/Backend/EmitProg.lean:85`), and `Tree.table` into `PProg`
(`Cas/Backend/ProgProse.lean:268`). `ProgProse.lean:225` says outright
that the two `PProg` walks agreeing is prose. This module closes the
triangle and then RUNS it.

## The pin device — why there is a third walk here

`putNode` (`EmitProg.lean:46`) and `putLine` (`ProgProse.lean:227`) are
`private` to their modules, and both files are fenced: a theorem
elsewhere may not name them and no edit may unseal them. So the walk is
restated once more, privately, as `seg` — offset-indexed, because the
answer operands are relative to a starting line index and an
offset-blind restatement could not state `embed_treeProg` at all — and
PINNED to both shipped walkers by kernel-checked theorems
(`treeProg_eq_seg`, `table_eq_seg`), through one `rfl`-proved clause
lemma per constructor per walker.

This is PDD-1's device (`Cas/Backend/Canon.lean:115-129`, private
`canonDedup` pinned to the shipped `canonServices`) used for the same
reason. The pin is a THEOREM, not an assumption: if either shipped walk
drifts from `seg`, its clause lemma stops elaborating and `lake build`
goes red. No trust is added and no fenced byte moves.

## The laws

- `treeProg_eq_seg` / `table_eq_seg` — the pins (LAW S).
- `table_eq_treeProg` — L232, the sentence `ProgProse.lean:225` calls
  prose (LAW W).
- `treeProg_length` — the table's length is the term's size, which is
  what turns `runP`'s `p.length + 1` into `putTree_correct`'s
  `tr.size + 1` (LAW F).
- `embed_treeProg` — L231 in its strong form: the emitted table's
  denotation IS the term's store program, as an equality in
  `Prog CasSig Addr32` (LAW M).
- `treeProg_run` and `treeProg_two_state` — the run's meaning on all
  three axes (ANSWER, GROWTH, STORE), the latter in PDD-2's
  vocabulary (`library/cas/contracts/PDD-2.contract.md`,
  `Cas/Lang/Wp.lean:552`); `treeProg_run_empty` is the corollary the
  executed consequence runs, and `treeProg_Triple` is the
  refusal-exclusion form, which carries ANSWER and the two invariants
  and NOT the frame — see its own docstring (LAW R).
- the `Executed` section — L127: `runP` acquires an executed
  consequence on all seven registered programs, kernel-decided at a toy
  address function and `#eval`-decided at the production digest
  (LAW X).

What this module does NOT say is in the packet's claim-scope section;
the load-bearing entries are that nothing here reaches the TypeScript,
that the word's growth is a SUBLIST of `flatten` and never `flatten`
itself, and that `Function.Injective H` is a named hypothesis rather
than a proved property of any digest.
-/

namespace Cas.Backend

open Cas.Grammar Cas.Lang

/-! ## The restatement -/

/-- The children-first walk once more, offset-indexed and pure:
`seg tr n` is the pair (the lines the term occupies when its first line
sits at index `n`, the index of the term's OWN line). Every clause emits
`.put` with `.ans` operands alone — which is why the emitter's refusal
arms (`EmitProg.lean:93-108`) are unreachable on this image, and why
`resolveRefs` never takes its `none` branch in `embed_treeProg`. -/
private def seg : Tree t → Nat → List PLine × Nat
  | .value p, n => ([.put schemeVersion Ty.value.wireTag p.val []], n)
  | .chunk p, n => ([.put schemeVersion Ty.chunk.wireTag p.val []], n)
  | .schema p, n => ([.put schemeVersion Ty.schema.wireTag p.val []], n)
  | .git o, n => ([.put schemeVersion Ty.git.wireTag o.val []], n)
  | .genesis, n => ([.put schemeVersion Ty.entry.wireTag [] []], n)
  | .leaf i l d, n =>
    ((seg d n).1 ++
      [.put schemeVersion Ty.tree.wireTag (nat32 i.toNat ++ nat32 l.toNat)
        [(Ty.chunk.wireTag, .ans (seg d n).2)]],
     n + (seg d n).1.length)
  | .parent l r, n =>
    ((seg l n).1 ++ (seg r (n + (seg l n).1.length)).1 ++
      [.put schemeVersion Ty.tree.wireTag []
        [(Ty.tree.wireTag, .ans (seg l n).2),
         (Ty.tree.wireTag, .ans (seg r (n + (seg l n).1.length)).2)]],
     n + (seg l n).1.length + (seg r (n + (seg l n).1.length)).1.length)
  | .manifest re tot le root, n =>
    ((seg root n).1 ++
      [.put schemeVersion Ty.manifest.wireTag
        (nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat)
        [(Ty.tree.wireTag, .ans (seg root n).2)]],
     n + (seg root n).1.length)
  | .file name mt c, n =>
    ((seg c n).1 ++
      [.put schemeVersion Ty.file.wireTag (frame name.val ++ frame mt.val)
        [(Ty.manifest.wireTag, .ans (seg c n).2)]],
     n + (seg c n).1.length)
  | .entry note item prev, n =>
    ((seg item n).1 ++ (seg prev (n + (seg item n).1.length)).1 ++
      [.put schemeVersion Ty.entry.wireTag note.val
        [(Ty.file.wireTag, .ans (seg item n).2),
         (Ty.entry.wireTag, .ans (seg prev (n + (seg item n).1.length)).2)]],
     n + (seg item n).1.length +
       (seg prev (n + (seg item n).1.length)).1.length)

/-- The segment has one line per node — the arithmetic every offset
below rests on. -/
private theorem seg_length : ∀ {t : Ty} (tr : Tree t) (n : Nat),
    (seg tr n).1.length = tr.size := by
  intro t tr
  induction tr with
  | value p => intro n; rfl
  | chunk p => intro n; rfl
  | schema p => intro n; rfl
  | git o => intro n; rfl
  | genesis => intro n; rfl
  | leaf i l d ih => intro n; simp [seg, Tree.size, ih]
  | parent l r ihl ihr => intro n; simp [seg, Tree.size, ihl, ihr]; omega
  | manifest re tot le root ih => intro n; simp [seg, Tree.size, ih]
  | file name mt c ih => intro n; simp [seg, Tree.size, ih]
  | entry note item prev ihi ihp =>
    intro n; simp [seg, Tree.size, ihi, ihp]; omega

/-- The term's own line is the LAST of its segment. Stated without
subtraction so no `Nat` truncation ever enters a proof: the own index
plus one is the index one past the segment. -/
private theorem seg_index : ∀ {t : Ty} (tr : Tree t) (n : Nat),
    (seg tr n).2 + 1 = n + tr.size := by
  intro t tr
  induction tr with
  | value p => intro n; simp [seg, Tree.size]
  | chunk p => intro n; simp [seg, Tree.size]
  | schema p => intro n; simp [seg, Tree.size]
  | git o => intro n; simp [seg, Tree.size]
  | genesis => intro n; simp [seg, Tree.size]
  | leaf i l d ih => intro n; simp [seg, Tree.size, seg_length]; omega
  | parent l r ihl ihr => intro n; simp [seg, Tree.size, seg_length]; omega
  | manifest re tot le root ih =>
    intro n; simp [seg, Tree.size, seg_length]; omega
  | file name mt c ih => intro n; simp [seg, Tree.size, seg_length]; omega
  | entry note item prev ihi ihp =>
    intro n; simp [seg, Tree.size, seg_length]; omega

/-! ## The emitter's walk, clause by clause

Ten `rfl` lemmas, one per constructor: the private `putNode`
(`EmitProg.lean:46`) is unnameable here, so its effect on the state is
recorded definitionally instead. A drifted clause makes its lemma stop
elaborating — that is the pin's first half. -/

section LowerTree

variable (arr : Array PLine)

private theorem lt_value (p : Payload) :
    lowerTree (Tree.value p) arr
      = (arr.size, arr.push (.put schemeVersion Ty.value.wireTag p.val [])) := rfl

private theorem lt_chunk (p : Payload) :
    lowerTree (Tree.chunk p) arr
      = (arr.size, arr.push (.put schemeVersion Ty.chunk.wireTag p.val [])) := rfl

private theorem lt_schema (p : Payload) :
    lowerTree (Tree.schema p) arr
      = (arr.size, arr.push (.put schemeVersion Ty.schema.wireTag p.val [])) := rfl

private theorem lt_git (o : Payload) :
    lowerTree (Tree.git o) arr
      = (arr.size, arr.push (.put schemeVersion Ty.git.wireTag o.val [])) := rfl

private theorem lt_genesis :
    lowerTree Tree.genesis arr
      = (arr.size, arr.push (.put schemeVersion Ty.entry.wireTag [] [])) := rfl

private theorem lt_leaf (i l : UInt32) (d : Tree .chunk) :
    lowerTree (Tree.leaf i l d) arr
      = ((lowerTree d arr).2.size,
         (lowerTree d arr).2.push
           (.put schemeVersion Ty.tree.wireTag (nat32 i.toNat ++ nat32 l.toNat)
             [(Ty.chunk.wireTag, .ans (lowerTree d arr).1)])) := rfl

private theorem lt_parent (l r : Tree .tree) :
    lowerTree (Tree.parent l r) arr
      = ((lowerTree r (lowerTree l arr).2).2.size,
         (lowerTree r (lowerTree l arr).2).2.push
           (.put schemeVersion Ty.tree.wireTag []
             [(Ty.tree.wireTag, .ans (lowerTree l arr).1),
              (Ty.tree.wireTag, .ans (lowerTree r (lowerTree l arr).2).1)])) := rfl

private theorem lt_manifest (re : UInt32) (tot : UInt64) (le : UInt32)
    (root : Tree .tree) :
    lowerTree (Tree.manifest re tot le root) arr
      = ((lowerTree root arr).2.size,
         (lowerTree root arr).2.push
           (.put schemeVersion Ty.manifest.wireTag
             (nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat)
             [(Ty.tree.wireTag, .ans (lowerTree root arr).1)])) := rfl

private theorem lt_file (name mt : Name) (c : Tree .manifest) :
    lowerTree (Tree.file name mt c) arr
      = ((lowerTree c arr).2.size,
         (lowerTree c arr).2.push
           (.put schemeVersion Ty.file.wireTag (frame name.val ++ frame mt.val)
             [(Ty.manifest.wireTag, .ans (lowerTree c arr).1)])) := rfl

private theorem lt_entry (note : Payload) (item : Tree .file)
    (prev : Tree .entry) :
    lowerTree (Tree.entry note item prev) arr
      = ((lowerTree prev (lowerTree item arr).2).2.size,
         (lowerTree prev (lowerTree item arr).2).2.push
           (.put schemeVersion Ty.entry.wireTag note.val
             [(Ty.file.wireTag, .ans (lowerTree item arr).1),
              (Ty.entry.wireTag,
                .ans (lowerTree prev (lowerTree item arr).2).1)])) := rfl

end LowerTree

/-- **THE FIRST PIN.** The emitter's walk (`EmitProg.lean:55`) computes
`seg`, from every starting array. -/
private theorem lowerTree_seg : ∀ {t : Ty} (tr : Tree t) (arr : Array PLine),
    (lowerTree tr arr).1 = (seg tr arr.size).2 ∧
      (lowerTree tr arr).2.toList = arr.toList ++ (seg tr arr.size).1 := by
  intro t tr
  induction tr with
  | value p => intro arr; simp [lt_value, seg]
  | chunk p => intro arr; simp [lt_chunk, seg]
  | schema p => intro arr; simp [lt_schema, seg]
  | git o => intro arr; simp [lt_git, seg]
  | genesis => intro arr; simp [lt_genesis, seg]
  | leaf i l d ih =>
    intro arr
    obtain ⟨ih1, ih2⟩ := ih arr
    have hs : (lowerTree d arr).2.size = arr.size + (seg d arr.size).1.length := by
      rw [← Array.length_toList, ih2]; simp
    simp only [lt_leaf, Array.toList_push, ih1, ih2, hs, seg]
    exact ⟨trivial, by simp [List.append_assoc]⟩
  | parent l r ihl ihr =>
    intro arr
    obtain ⟨ihl1, ihl2⟩ := ihl arr
    have hsl : (lowerTree l arr).2.size = arr.size + (seg l arr.size).1.length := by
      rw [← Array.length_toList, ihl2]; simp
    obtain ⟨ihr1, ihr2⟩ := ihr (lowerTree l arr).2
    rw [hsl] at ihr1 ihr2
    have hsr : (lowerTree r (lowerTree l arr).2).2.size
        = arr.size + (seg l arr.size).1.length
            + (seg r (arr.size + (seg l arr.size).1.length)).1.length := by
      rw [← Array.length_toList, ihr2, ihl2]; simp; omega
    simp only [lt_parent, Array.toList_push, ihl1, ihl2, ihr1, ihr2, hsr, seg]
    exact ⟨trivial, by simp [List.append_assoc]⟩
  | manifest re tot le root ih =>
    intro arr
    obtain ⟨ih1, ih2⟩ := ih arr
    have hs : (lowerTree root arr).2.size
        = arr.size + (seg root arr.size).1.length := by
      rw [← Array.length_toList, ih2]; simp
    simp only [lt_manifest, Array.toList_push, ih1, ih2, hs, seg]
    exact ⟨trivial, by simp [List.append_assoc]⟩
  | file name mt c ih =>
    intro arr
    obtain ⟨ih1, ih2⟩ := ih arr
    have hs : (lowerTree c arr).2.size = arr.size + (seg c arr.size).1.length := by
      rw [← Array.length_toList, ih2]; simp
    simp only [lt_file, Array.toList_push, ih1, ih2, hs, seg]
    exact ⟨trivial, by simp [List.append_assoc]⟩
  | entry note item prev ihi ihp =>
    intro arr
    obtain ⟨ihi1, ihi2⟩ := ihi arr
    have hsi : (lowerTree item arr).2.size
        = arr.size + (seg item arr.size).1.length := by
      rw [← Array.length_toList, ihi2]; simp
    obtain ⟨ihp1, ihp2⟩ := ihp (lowerTree item arr).2
    rw [hsi] at ihp1 ihp2
    have hsp : (lowerTree prev (lowerTree item arr).2).2.size
        = arr.size + (seg item arr.size).1.length
            + (seg prev (arr.size + (seg item arr.size).1.length)).1.length := by
      rw [← Array.length_toList, ihp2, ihi2]; simp; omega
    simp only [lt_entry, Array.toList_push, ihi1, ihi2, ihp1, ihp2, hsp, seg]
    exact ⟨trivial, by simp [List.append_assoc]⟩

/-- **LAW S, first half.** The emitted table is the restatement at
offset zero. -/
theorem treeProg_eq_seg {t : Ty} (tr : Tree t) : treeProg tr = (seg tr 0).1 :=
  (lowerTree_seg tr #[]).2

/-- The table's length is the term's node count (LAW F). Load-bearing
twice: it turns `runP`'s fuel bound `p.length + 1` into
`putTree_correct`'s `tr.size + 1`, and it is what kills the adversarial
lowering that emits nothing. -/
theorem treeProg_length {t : Ty} (tr : Tree t) : (treeProg tr).length = tr.size := by
  rw [treeProg_eq_seg, seg_length]

/-! ## The verbalizer's walk, clause by clause

The same ten `rfl` lemmas for `Cas/Backend/ProgProse.lean`'s walk, whose
`putLine` is private there for the same reason. The state carries an
explicit counter beside the array; the counter is what the answer
indices are read off, and the array merely accumulates — so no
`n = arr.size` invariant is needed and none is assumed. -/

section LowerTable

variable (s : Array PLine × Nat)

private theorem lb_value (p : Payload) :
    lowerTable (Tree.value p) s
      = (s.2, (s.1.push (.put schemeVersion Ty.value.wireTag p.val []), s.2 + 1)) :=
  rfl

private theorem lb_chunk (p : Payload) :
    lowerTable (Tree.chunk p) s
      = (s.2, (s.1.push (.put schemeVersion Ty.chunk.wireTag p.val []), s.2 + 1)) :=
  rfl

private theorem lb_schema (p : Payload) :
    lowerTable (Tree.schema p) s
      = (s.2, (s.1.push (.put schemeVersion Ty.schema.wireTag p.val []), s.2 + 1)) :=
  rfl

private theorem lb_git (o : Payload) :
    lowerTable (Tree.git o) s
      = (s.2, (s.1.push (.put schemeVersion Ty.git.wireTag o.val []), s.2 + 1)) :=
  rfl

private theorem lb_genesis :
    lowerTable Tree.genesis s
      = (s.2, (s.1.push (.put schemeVersion Ty.entry.wireTag [] []), s.2 + 1)) :=
  rfl

private theorem lb_leaf (i l : UInt32) (d : Tree .chunk) :
    lowerTable (Tree.leaf i l d) s
      = ((lowerTable d s).2.2,
         ((lowerTable d s).2.1.push
            (.put schemeVersion Ty.tree.wireTag (nat32 i.toNat ++ nat32 l.toNat)
              [(Ty.chunk.wireTag, .ans (lowerTable d s).1)]),
          (lowerTable d s).2.2 + 1)) := rfl

private theorem lb_parent (l r : Tree .tree) :
    lowerTable (Tree.parent l r) s
      = ((lowerTable r (lowerTable l s).2).2.2,
         ((lowerTable r (lowerTable l s).2).2.1.push
            (.put schemeVersion Ty.tree.wireTag []
              [(Ty.tree.wireTag, .ans (lowerTable l s).1),
               (Ty.tree.wireTag, .ans (lowerTable r (lowerTable l s).2).1)]),
          (lowerTable r (lowerTable l s).2).2.2 + 1)) := rfl

private theorem lb_manifest (re : UInt32) (tot : UInt64) (le : UInt32)
    (root : Tree .tree) :
    lowerTable (Tree.manifest re tot le root) s
      = ((lowerTable root s).2.2,
         ((lowerTable root s).2.1.push
            (.put schemeVersion Ty.manifest.wireTag
              (nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat)
              [(Ty.tree.wireTag, .ans (lowerTable root s).1)]),
          (lowerTable root s).2.2 + 1)) := rfl

private theorem lb_file (name mt : Name) (c : Tree .manifest) :
    lowerTable (Tree.file name mt c) s
      = ((lowerTable c s).2.2,
         ((lowerTable c s).2.1.push
            (.put schemeVersion Ty.file.wireTag (frame name.val ++ frame mt.val)
              [(Ty.manifest.wireTag, .ans (lowerTable c s).1)]),
          (lowerTable c s).2.2 + 1)) := rfl

private theorem lb_entry (note : Payload) (item : Tree .file)
    (prev : Tree .entry) :
    lowerTable (Tree.entry note item prev) s
      = ((lowerTable prev (lowerTable item s).2).2.2,
         ((lowerTable prev (lowerTable item s).2).2.1.push
            (.put schemeVersion Ty.entry.wireTag note.val
              [(Ty.file.wireTag, .ans (lowerTable item s).1),
               (Ty.entry.wireTag,
                 .ans (lowerTable prev (lowerTable item s).2).1)]),
          (lowerTable prev (lowerTable item s).2).2.2 + 1)) := rfl

end LowerTable

/-- **THE SECOND PIN.** The verbalizer's walk (`ProgProse.lean:238`)
computes the same `seg`, from every starting state. -/
private theorem lowerTable_seg : ∀ {t : Ty} (tr : Tree t) (s : Array PLine × Nat),
    (lowerTable tr s).1 = (seg tr s.2).2 ∧
      (lowerTable tr s).2.1.toList = s.1.toList ++ (seg tr s.2).1 ∧
      (lowerTable tr s).2.2 = s.2 + tr.size := by
  intro t tr
  induction tr with
  | value p => intro s; simp [lb_value, seg, Tree.size]
  | chunk p => intro s; simp [lb_chunk, seg, Tree.size]
  | schema p => intro s; simp [lb_schema, seg, Tree.size]
  | git o => intro s; simp [lb_git, seg, Tree.size]
  | genesis => intro s; simp [lb_genesis, seg, Tree.size]
  | leaf i l d ih =>
    intro s
    obtain ⟨ih1, ih2, ih3⟩ := ih s
    simp only [lb_leaf, Array.toList_push, ih1, ih2, ih3, seg, Tree.size,
      seg_length]
    refine ⟨?_, ?_, ?_⟩ <;>
      first | trivial | omega | simp [List.append_assoc]
  | parent l r ihl ihr =>
    intro s
    obtain ⟨ihl1, ihl2, ihl3⟩ := ihl s
    obtain ⟨ihr1, ihr2, ihr3⟩ := ihr (lowerTable l s).2
    rw [ihl3] at ihr1 ihr2 ihr3
    simp only [lb_parent, Array.toList_push, ihl1, ihl2, ihr1, ihr2, ihr3,
      seg, Tree.size, seg_length]
    refine ⟨?_, ?_, ?_⟩ <;>
      first | trivial | omega | simp [List.append_assoc]
  | manifest re tot le root ih =>
    intro s
    obtain ⟨ih1, ih2, ih3⟩ := ih s
    simp only [lb_manifest, Array.toList_push, ih1, ih2, ih3, seg, Tree.size,
      seg_length]
    refine ⟨?_, ?_, ?_⟩ <;>
      first | trivial | omega | simp [List.append_assoc]
  | file name mt c ih =>
    intro s
    obtain ⟨ih1, ih2, ih3⟩ := ih s
    simp only [lb_file, Array.toList_push, ih1, ih2, ih3, seg, Tree.size,
      seg_length]
    refine ⟨?_, ?_, ?_⟩ <;>
      first | trivial | omega | simp [List.append_assoc]
  | entry note item prev ihi ihp =>
    intro s
    obtain ⟨ihi1, ihi2, ihi3⟩ := ihi s
    obtain ⟨ihp1, ihp2, ihp3⟩ := ihp (lowerTable item s).2
    rw [ihi3] at ihp1 ihp2 ihp3
    simp only [lb_entry, Array.toList_push, ihi1, ihi2, ihp1, ihp2, ihp3,
      seg, Tree.size, seg_length]
    refine ⟨?_, ?_, ?_⟩ <;>
      first | trivial | omega | simp [List.append_assoc]

/-- **LAW S, second half.** -/
theorem table_eq_seg {t : Ty} (tr : Tree t) : tr.table = (seg tr 0).1 :=
  (lowerTable_seg tr (#[], 0)).2.1

/-- **LAW W — L232: THE TWO WALKS AGREE.** `Cas/Backend/ProgProse.lean:225`
says of exactly this sentence: "The two walks agreeing is prose, not a
theorem." It is a theorem now, for every sort and every term.

The consequence a reader should take: `Tree.envelope`, `Tree.docLines`
and every generated docstring assembled from them
(`tools/EmitPrograms.lean:124`) describe the table the generated
TypeScript was printed from — not a second table that happens to look
like it. THE-ALGEBRA §3.31's error state ("a generated module can carry
prose describing table A above code lowered from table B") is closed. -/
theorem table_eq_treeProg {t : Ty} (tr : Tree t) : tr.table = treeProg tr := by
  rw [table_eq_seg, treeProg_eq_seg]

/-! ## The table's denotation is the term's program -/
/-! ## The table's denotation is the term's program -/

/-- An answer operand naming the last address of a prefix resolves to
it. This is the whole content of "the reference names the line that put
the child": the operand index is a prefix length, and the history at a
prefix length is the entry that follows the prefix. -/
private theorem resolve_last (pre post : List Addr32) (a : Addr32) {i : Nat}
    (hi : i = pre.length) :
    PIn.resolve (pre ++ a :: post) (.ans i) = some a := by
  subst hi
  simp [PIn.resolve]

/-- One resolved put line, with its continuation supplied pointwise —
the step every clause of the induction below takes. -/
private theorem embedFrom_put {env : List Addr32} {v tg : UInt8}
    {payload : Bytes} {refs : List (UInt8 × PIn)} {rs : List Ref}
    {rest : PProg} {k : Addr32 → Prog CasSig Addr32}
    (hrefs : resolveRefs env refs = some rs)
    (hk : ∀ c, embedFrom (env ++ [c]) rest = k c) :
    embedFrom env (.put v tg payload refs :: rest)
      = .vis (.put ⟨v, tg, payload, rs⟩) k := by
  simp only [embedFrom, hrefs]
  congr 1
  funext c
  exact hk c

/-- The interior of LAW M, packaged for induction: a term's segment,
embedded from ANY answer history at ANY suffix, is the term's `progK` at
the continuation the suffix denotes. The hypothesis is what "the suffix
denotes" means — every way of extending the history by the term's own
`size` answers ends at `k` applied to the LAST of them, which is the
term's own. -/
private theorem embedFrom_seg : ∀ {t : Ty} (tr : Tree t) (env : List Addr32)
    (k : Addr32 → Prog CasSig Addr32) (rest : PProg),
    (∀ (ans : List Addr32) (a : Addr32), ans.length + 1 = tr.size →
       embedFrom (env ++ (ans ++ [a])) rest = k a) →
    embedFrom env ((seg tr env.length).1 ++ rest) = tr.progK k := by
  intro t tr
  induction tr with
  | value p =>
    intro env k rest hk
    simp only [seg, List.singleton_append, Tree.progK]
    refine embedFrom_put (rs := []) (by simp [resolveRefs]) ?_
    intro c
    exact hk [] c (by simp [Tree.size])
  | chunk p =>
    intro env k rest hk
    simp only [seg, List.singleton_append, Tree.progK]
    refine embedFrom_put (rs := []) (by simp [resolveRefs]) ?_
    intro c
    exact hk [] c (by simp [Tree.size])
  | schema p =>
    intro env k rest hk
    simp only [seg, List.singleton_append, Tree.progK]
    refine embedFrom_put (rs := []) (by simp [resolveRefs]) ?_
    intro c
    exact hk [] c (by simp [Tree.size])
  | git o =>
    intro env k rest hk
    simp only [seg, List.singleton_append, Tree.progK]
    refine embedFrom_put (rs := []) (by simp [resolveRefs]) ?_
    intro c
    exact hk [] c (by simp [Tree.size])
  | genesis =>
    intro env k rest hk
    simp only [seg, List.singleton_append, Tree.progK]
    refine embedFrom_put (rs := []) (by simp [resolveRefs]) ?_
    intro c
    exact hk [] c (by simp [Tree.size])
  | leaf i l d ih =>
    intro env k rest hk
    simp only [seg, List.append_assoc, List.singleton_append, Tree.progK]
    refine ih env _ _ ?_
    intro ans a hlen
    have hidx : (seg d env.length).2 = (env ++ ans).length := by
      have h1 := seg_index d env.length
      simp only [List.length_append]
      omega
    have hres : PIn.resolve (env ++ (ans ++ [a])) (.ans (seg d env.length).2)
        = some a := by
      have hE : env ++ (ans ++ [a]) = (env ++ ans) ++ a :: [] := by simp
      rw [hE]
      exact resolve_last _ _ _ hidx
    refine embedFrom_put (rs := [Ref.mk Ty.chunk.wireTag a])
      (by simp [resolveRefs, hres]) ?_
    intro c
    have h := hk (ans ++ [a]) c (by simp [Tree.size]; omega)
    simpa [List.append_assoc] using h
  | parent l r ihl ihr =>
    intro env k rest hk
    simp only [seg, List.append_assoc, List.singleton_append, Tree.progK]
    refine ihl env _ _ ?_
    intro ansl al hlenl
    have hoff : (env ++ (ansl ++ [al])).length
        = env.length + (seg l env.length).1.length := by
      simp only [List.length_append, List.length_cons, List.length_nil,
        seg_length]
      omega
    rw [← hoff]
    refine ihr _ _ _ ?_
    intro ansr ar hlenr
    have hidxl : (seg l env.length).2 = (env ++ ansl).length := by
      have h1 := seg_index l env.length
      simp only [List.length_append]
      omega
    have hidxr : (seg r (env ++ (ansl ++ [al])).length).2
        = (env ++ (ansl ++ [al]) ++ ansr).length := by
      have h1 := seg_index r (env ++ (ansl ++ [al])).length
      simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
      omega
    have hresl : PIn.resolve (env ++ (ansl ++ [al]) ++ (ansr ++ [ar]))
        (.ans (seg l env.length).2) = some al := by
      have hE : env ++ (ansl ++ [al]) ++ (ansr ++ [ar])
          = (env ++ ansl) ++ al :: (ansr ++ [ar]) := by simp
      rw [hE]
      exact resolve_last _ _ _ hidxl
    have hresr : PIn.resolve (env ++ (ansl ++ [al]) ++ (ansr ++ [ar]))
        (.ans (seg r (env ++ (ansl ++ [al])).length).2) = some ar := by
      have hE : env ++ (ansl ++ [al]) ++ (ansr ++ [ar])
          = (env ++ (ansl ++ [al]) ++ ansr) ++ ar :: [] := by simp
      rw [hE]
      exact resolve_last _ _ _ hidxr
    refine embedFrom_put
      (rs := [Ref.mk Ty.tree.wireTag al, Ref.mk Ty.tree.wireTag ar])
      (by simp only [resolveRefs, List.mapM_cons, List.mapM_nil, hresl,
            hresr]; rfl) ?_
    intro c
    have h := hk (ansl ++ [al] ++ (ansr ++ [ar])) c (by simp [Tree.size]; omega)
    simpa [List.append_assoc] using h
  | manifest re tot le root ih =>
    intro env k rest hk
    simp only [seg, List.append_assoc, List.singleton_append, Tree.progK]
    refine ih env _ _ ?_
    intro ans a hlen
    have hidx : (seg root env.length).2 = (env ++ ans).length := by
      have h1 := seg_index root env.length
      simp only [List.length_append]
      omega
    have hres : PIn.resolve (env ++ (ans ++ [a]))
        (.ans (seg root env.length).2) = some a := by
      have hE : env ++ (ans ++ [a]) = (env ++ ans) ++ a :: [] := by simp
      rw [hE]
      exact resolve_last _ _ _ hidx
    refine embedFrom_put (rs := [Ref.mk Ty.tree.wireTag a])
      (by simp [resolveRefs, hres]) ?_
    intro c
    have h := hk (ans ++ [a]) c (by simp [Tree.size]; omega)
    simpa [List.append_assoc] using h
  | file name mt c ih =>
    intro env k rest hk
    simp only [seg, List.append_assoc, List.singleton_append, Tree.progK]
    refine ih env _ _ ?_
    intro ans a hlen
    have hidx : (seg c env.length).2 = (env ++ ans).length := by
      have h1 := seg_index c env.length
      simp only [List.length_append]
      omega
    have hres : PIn.resolve (env ++ (ans ++ [a])) (.ans (seg c env.length).2)
        = some a := by
      have hE : env ++ (ans ++ [a]) = (env ++ ans) ++ a :: [] := by simp
      rw [hE]
      exact resolve_last _ _ _ hidx
    refine embedFrom_put (rs := [Ref.mk Ty.manifest.wireTag a])
      (by simp [resolveRefs, hres]) ?_
    intro b
    have h := hk (ans ++ [a]) b (by simp [Tree.size]; omega)
    simpa [List.append_assoc] using h
  | entry note item prev ihi ihp =>
    intro env k rest hk
    simp only [seg, List.append_assoc, List.singleton_append, Tree.progK]
    refine ihi env _ _ ?_
    intro ansi ai hleni
    have hoff : (env ++ (ansi ++ [ai])).length
        = env.length + (seg item env.length).1.length := by
      simp only [List.length_append, List.length_cons, List.length_nil,
        seg_length]
      omega
    rw [← hoff]
    refine ihp _ _ _ ?_
    intro ansp ap hlenp
    have hidxi : (seg item env.length).2 = (env ++ ansi).length := by
      have h1 := seg_index item env.length
      simp only [List.length_append]
      omega
    have hidxp : (seg prev (env ++ (ansi ++ [ai])).length).2
        = (env ++ (ansi ++ [ai]) ++ ansp).length := by
      have h1 := seg_index prev (env ++ (ansi ++ [ai])).length
      simp only [List.length_append, List.length_cons, List.length_nil] at h1 ⊢
      omega
    have hresi : PIn.resolve (env ++ (ansi ++ [ai]) ++ (ansp ++ [ap]))
        (.ans (seg item env.length).2) = some ai := by
      have hE : env ++ (ansi ++ [ai]) ++ (ansp ++ [ap])
          = (env ++ ansi) ++ ai :: (ansp ++ [ap]) := by simp
      rw [hE]
      exact resolve_last _ _ _ hidxi
    have hresp : PIn.resolve (env ++ (ansi ++ [ai]) ++ (ansp ++ [ap]))
        (.ans (seg prev (env ++ (ansi ++ [ai])).length).2) = some ap := by
      have hE : env ++ (ansi ++ [ai]) ++ (ansp ++ [ap])
          = (env ++ (ansi ++ [ai]) ++ ansp) ++ ap :: [] := by simp
      rw [hE]
      exact resolve_last _ _ _ hidxp
    refine embedFrom_put
      (rs := [Ref.mk Ty.file.wireTag ai, Ref.mk Ty.entry.wireTag ap])
      (by simp only [resolveRefs, List.mapM_cons, List.mapM_nil, hresi,
            hresp]; rfl) ?_
    intro c
    have h := hk (ansi ++ [ai] ++ (ansp ++ [ap])) c (by simp [Tree.size]; omega)
    simpa [List.append_assoc] using h

/-- **LAW M — L231: THE EMITTED TABLE IS THE TERM'S PROGRAM.** Equality
in `Prog CasSig Addr32` — the carrier's own equality, not an
observational one and not an agreement of runs.

THE-ALGEBRA §3.31 records three lowerings related by no theorem. This is
the pair that matters: `treeProg`, the walk the seven generated programs
and their lift documents are printed from, denotes exactly `Tree.prog`
— so everything already proved about `Tree.prog` (`putTree_correct` and
its corollaries) becomes a statement about the emitted table, by
rewriting rather than by a second proof. -/
theorem embed_treeProg {t : Ty} (tr : Tree t) : embed (treeProg tr) = tr.prog := by
  rw [treeProg_eq_seg]
  have h := embedFrom_seg tr [] Prog.pure []
    (by intro ans a _; simp [embedFrom])
  simpa [embed, Tree.prog] using h

/-! ## The run's meaning

Everything here is `Tree.putTree_correct` transported across LAW M. That
is the point of stating LAW M as an equality of programs: the run's
meaning is not re-proved, it is REWRITTEN, and the fuel `p.length + 1`
that `runP_embed_agree` demands is `tr.size + 1` by LAW F. -/

section Run

variable (H : Bytes → Addr32)

/-- **LAW R — L231/L127: THE EMITTED TABLE'S RUN COMPUTES THE TERM.**
Under an injective digest, from any admissible honest word, the direct
interpreter over `treeProg tr` HALTS DONE at exactly the term's fold
address; the word grows by a SUBLIST of the term's `flatten` — shared
subterms deduplicate, which is why this is a sublist and not `flatten`
itself — and the projected store is exactly `flatten`'s.

Three axes, and all three are load-bearing: the ANSWER alone is met by a
table that writes nothing, and the GROWTH alone by one that writes the
wrong nodes. -/
theorem treeProg_run (hInj : Function.Injective H) {t : Ty} (tr : Tree t)
    {w : Word} (hw : Word.wf w = true) (hhon : Honest H w) :
    ∃ v, v.Sublist (tr.flatten H)
      ∧ runP H (treeProg tr) w = (.done (tr.address H), w ++ v)
      ∧ Word.toStore (w ++ v) = Word.toStore (w ++ tr.flatten H)
      ∧ Word.wf (w ++ v) = true ∧ Honest H (w ++ v) := by
  obtain ⟨v, hsub, hrun, hstore, hwf', hhon'⟩ :=
    tr.putTree_correct H hInj hw hhon
  refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
  rw [← runP_embed_agree, treeProg_length, embed_treeProg]
  exact hrun

/-- LAW R from nothing: the empty word is admissible and honest, so the
emitted table builds its own store — the corollary the executed
consequence below runs, at the digests it runs at. -/
theorem treeProg_run_empty (hInj : Function.Injective H) {t : Ty} (tr : Tree t) :
    ∃ v, v.Sublist (tr.flatten H)
      ∧ runP H (treeProg tr) [] = (.done (tr.address H), v)
      ∧ Word.toStore v = Word.toStore (tr.flatten H)
      ∧ Word.wf v = true ∧ Honest H v := by
  obtain ⟨v, hsub, hrun, hstore, hwf', hhon'⟩ :=
    treeProg_run H hInj tr (w := []) rfl (Honest.nil H)
  exact ⟨v, hsub, hrun, hstore, hwf', hhon'⟩

/-- **LAW R as a TRIPLE**, in PDD-2's vocabulary
(`library/cas/contracts/PDD-2.contract.md`, `Cas/Lang/Wp.lean:552`): the
specification language is that packet's and is used here rather than
re-minted. `Triple` is total correctness over the fueled run — refusal
excluded by `done`, divergence excluded by the carrier — so this says
the emitted table never refuses on an admissible honest word.

The two-state reading, with `old` the starting word, is
`treeProg_two_state` below; `Triple`'s own postcondition sees only the
final state, which is exactly why the estate's `old` is a logical
variable and not a second carrier.

WHAT THIS ONE DOES NOT CARRY, said outright rather than left to a
reader of the postcondition (the breaker's NOTE-2,
`contracts/attacks/PDD-9/RESULTS.md`): ANSWER and the two invariants,
and NOT the FRAME. `paddedShared` — this table with one unrelated put
prepended and every operand shifted — answers the same address and
ends admissible and honest while writing a binding that is nowhere in
`tr.flatten H`, and nothing below excludes it. `treeProg_run` and
`treeProg_two_state` are the axis-carriers; this is the
refusal-exclusion form, and the frame is two-state by nature. -/
theorem treeProg_Triple (hInj : Function.Injective H) {t : Ty} (tr : Tree t) :
    Triple H (treeProg tr)
      (fun w => Word.wf w = true ∧ Honest H w)
      (fun a w' => a = tr.address H ∧ Word.wf w' = true ∧ Honest H w') := by
  intro w hw
  obtain ⟨v, _, hrun, _, hwf', hhon'⟩ := treeProg_run H hInj tr hw.1 hw.2
  exact ⟨tr.address H, w ++ v, hrun, rfl, hwf', hhon'⟩

/-- **LAW R, two-state.** The starting word enters as a logical variable
through PDD-2's `Triple_two_state_rel` — the estate's `old`. This is the
form the debt object's `σ` asks for, and it carries the FRAME: the final
word is the starting word EXTENDED, by a sublist of `flatten` and by
nothing else. -/
theorem treeProg_two_state (hInj : Function.Injective H) {t : Ty} (tr : Tree t) :
    ∀ w₀, (Word.wf w₀ = true ∧ Honest H w₀) →
      Triple H (treeProg tr) (fun w => w = w₀)
        (fun a w' => a = tr.address H ∧ ∃ v, v.Sublist (tr.flatten H)
          ∧ w' = w₀ ++ v
          ∧ Word.toStore w' = Word.toStore (w₀ ++ tr.flatten H)
          ∧ Word.wf w' = true ∧ Honest H w') := by
  refine (Triple_two_state_rel H (treeProg tr) _ _).mpr ?_
  intro w₀ hp
  obtain ⟨v, hsub, hrun, hstore, hwf', hhon'⟩ :=
    treeProg_run H hInj tr hp.1 hp.2
  exact ⟨tr.address H, w₀ ++ v, hrun, rfl, v, hsub, rfl, hstore, hwf', hhon'⟩

end Run

/-! ## LAW X — the executed consequence

THE-ALGEBRA L127 records that NOTHING anywhere executes `runP`, and
§3.5's falsifier is "change `runP`'s word semantics — make a duplicate
put append — and exhibit a red gate", with the witness "no gate goes
red". This section is that gate.

The shape is PDD-2's battery (`Cas/Lang/Wp.lean:880-903`): a kernel
`#guard` at a toy address function and an `#eval` IO assert at the
production digest, because this lane's standing rule is that digest
computation runs in `#eval` and never in kernel `decide`
(`library/cas/AGENTS.md`).

The terms are the REGISTERED ones — the same `Cas/Vectors/Registry.lean`
values the seven generated programs are lowered from
(`tools/EmitPrograms.lean:45-60`) — so the fact executed is about the
estate's flagship artifact and not about a convenient toy table.

`blobSharedChunk` is the sharp witness. Its `flatten` carries the shared
chunk's binding TWICE, so the run's word must be one binding shorter:
the duplicate put deduplicates. `eraseIdx 2` names exactly which
occurrence is dropped — the second, at the position `flatten` puts it —
so an appending duplicate put fails this guard on the nose. -/

namespace Executed

open Cas.Vectors.Registry

/-- A toy address function: a 32-bit mix of the pre-image, spread over
the 32 bytes. It is not a digest and claims nothing — its only job is
to separate the witnesses' nodes inside the kernel, and the guards
below would fail outright if it did not (a collision would deduplicate
a node the term puts distinctly, shortening the word). No injectivity
is assumed anywhere: the guards check the CONCLUSION. -/
private def toyMix (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => (acc * 257 + b.toNat + 1) % 4294967296) 7

private def toyAddr (bs : Bytes) : Addr32 :=
  ⟨(List.range 32).map (fun i => UInt8.ofNat (toyMix bs / 256 ^ (i % 4))),
   by simp⟩

/-- THE VERDICT, as a decision: the emitted table's run is DONE, its
answer is the term's own `Tree.address`, and its final word is the one
named. Everything on the right-hand side comes from the GRAMMAR — this
is what ties `runP` to `Tree.prog`'s meaning by execution rather than by
prose. -/
def runVerdict (H : Bytes → Addr32) {t : Ty} (tr : Tree t)
    (expected : Word) : Bool :=
  match runP H (treeProg tr) [] with
  | (.done a, w) => a == tr.address H && w == expected && Word.wf w
  | _ => false

/-- The word a term's run must answer, as a function of the TERM: its
`flatten` with LATER duplicates dropped. Every expectation below is
this, so no witness needs a hand-computed erasure and the coverage
extends to a term by naming it rather than by measuring it.

Adopted from the independent breaker's attack record with credit —
`expected H tr := (Tree.flatten H tr).eraseDups`,
`library/cas/contracts/attacks/PDD-9/Attack.lean` §2, branch
`attack/opus-cc-mac/pdd-9`, commit `e2703228`. The packet's first draft
named the deduplicated word by a hand-chosen `eraseIdx 2` on one
witness, which is sharper there and generalizes nowhere; both are kept,
and the guard below pins them to each other. -/
def expectedWord (H : Bytes → Addr32) {t : Ty} (tr : Tree t) : Word :=
  (tr.flatten H).eraseDups

/-- The registry's schema term. `tools/EmitPrograms.lean:63-70` builds
it in `IO` because it needs the payload-bound witness; `Payload.ofBytes`
is total and answers the same payload whenever the bytes fit, which
`check` verifies rather than assumes — so this is the registered term
and not a truncated lookalike. -/
def schemaTerm : Tree .schema :=
  .schema (Payload.ofBytes (Cas.Grammar.utf8 vectorDocumentCode.payload))

/-! ### Kernel-decided, at the toy address function -/

-- The smallest registered program: one put, one binding, no dedup.
#guard runVerdict toyAddr helloValue (helloValue.flatten toyAddr)

-- The registered `shared-chunk` program. `flatten` has five bindings and
-- the run's word has four: the second occurrence of the shared chunk
-- deduplicates. THIS is §3.5's falsifier made red-able — an appending
-- duplicate put answers `flatten` itself and fails here.
#guard (blobSharedChunk.flatten toyAddr).length == 5

#guard ((blobSharedChunk.flatten toyAddr).eraseIdx 2).length == 4

#guard runVerdict toyAddr blobSharedChunk
  ((blobSharedChunk.flatten toyAddr).eraseIdx 2)

-- The general oracle agrees with that hand-chosen index on the witness
-- it was chosen for. This is what lets every other row below be named
-- rather than measured.
#guard expectedWord toyAddr blobSharedChunk
  == (blobSharedChunk.flatten toyAddr).eraseIdx 2

-- §3.5's mutation, REFUTED by execution rather than by argument: the
-- appending duplicate put would answer `flatten` itself. It does not.
-- A guard that cannot fail proves nothing, so the negative is kept
-- beside the positive.
#guard !runVerdict toyAddr blobSharedChunk (blobSharedChunk.flatten toyAddr)

-- The registered `blob-two-leaves` program: every blob sort, a
-- two-reference node, and no sharing — so here the word IS `flatten`.
#guard runVerdict toyAddr blobTwoLeaves (blobTwoLeaves.flatten toyAddr)

-- The registered `journal-two-entries` program: eleven nodes, the
-- registry's deepest reference chain, and the only term reaching
-- `.genesis` and `.entry` — the constructor with the two-child offset
-- arithmetic. Added on the breaker's HOLE-1; it had no executed
-- consequence anywhere before, at either digest.
#guard runVerdict toyAddr journalTwo (expectedWord toyAddr journalTwo)

-- And the two walks agree on the witnesses, executed as well as proved.
#guard blobSharedChunk.table == treeProg blobSharedChunk

#guard blobTwoLeaves.table == treeProg blobTwoLeaves

/-! ### The same verdict at the production digest, as a build-time
assert. `Cas.sha256Addr` is the digest the vector lane and the generated
programs run under, so this is the registered artifact's own run.

ALL SEVEN registered rows (`tools/EmitPrograms.lean:45-70`) appear here,
and through them all ten of the grammar's clauses. `journalTwo` and
`schemaTerm` were added on the breaker's HOLE-1
(`contracts/attacks/PDD-9/RESULTS.md`, commit `e2703228`): before them
`.genesis`, `.entry` and `.schema` had no executed consequence anywhere
in the estate, while this module's build line already said "the
registered programs". -/

def check : IO Unit := do
  unless runVerdict Cas.sha256Addr helloValue
      (helloValue.flatten Cas.sha256Addr) do
    throw (IO.userError
      "PDD-9: value-single's run does not answer its term")
  unless runVerdict Cas.sha256Addr blobTwoLeaves
      (blobTwoLeaves.flatten Cas.sha256Addr) do
    throw (IO.userError
      "PDD-9: blob-two-leaves' run does not answer its term")
  unless runVerdict Cas.sha256Addr fileReadme
      (fileReadme.flatten Cas.sha256Addr) do
    throw (IO.userError
      "PDD-9: file-readme's run does not answer its term")
  unless runVerdict Cas.sha256Addr gitPinCommit
      (gitPinCommit.flatten Cas.sha256Addr) do
    throw (IO.userError
      "PDD-9: git-pin-commit's run does not answer its term")
  unless runVerdict Cas.sha256Addr journalTwo
      (expectedWord Cas.sha256Addr journalTwo) do
    throw (IO.userError
      "PDD-9: journal-two-entries' run does not answer its term")
  unless (Cas.Grammar.utf8 vectorDocumentCode.payload).length
      < 4294967296 do
    throw (IO.userError
      "PDD-9: the schema payload exceeds the node byte bound, so \
       schemaTerm is not the registered term")
  unless runVerdict Cas.sha256Addr schemaTerm
      (expectedWord Cas.sha256Addr schemaTerm) do
    throw (IO.userError
      "PDD-9: schema-vector-document's run does not answer its term")
  unless runVerdict toyAddr schemaTerm (expectedWord toyAddr schemaTerm) do
    throw (IO.userError
      "PDD-9: schema-vector-document's run disagrees at the toy digest")
  unless (blobSharedChunk.flatten Cas.sha256Addr).length == 5 do
    throw (IO.userError
      "PDD-9: shared-chunk's flatten is no longer the five-binding word")
  unless runVerdict Cas.sha256Addr blobSharedChunk
      ((blobSharedChunk.flatten Cas.sha256Addr).eraseIdx 2) do
    throw (IO.userError
      "PDD-9: shared-chunk's run does not deduplicate to four bindings")
  IO.println
    ("PDD-9: runP executed on all seven registered programs at the "
      ++ "production digest — every answer is its term's address, and "
      ++ "shared-chunk deduplicates to four bindings from flatten's five")

#eval check

end Executed

end Cas.Backend
