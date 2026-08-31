import Cas.Grammar.Tree
import Cas.Lang.Interp

/-!
# The tree program — layer 2, derivable inside layer 3 (F1)

`Tree.progK` writes a grammar term as a program of the store language:
admit the children, then admit the node built from their ANSWERED
addresses — the leaf-up construction the TypeScript projection runs.
Nothing here consults `H`: the program learns every address from the
interpreter.

`putTree_correct` is the agreement theorem: under an injective digest
(Level 1, premise named), running a term's program over any honest,
admissible word answers exactly the term's fold address
(`Tree.address`), extends the word by a SUBLIST of the term's
`flatten` (shared subterms deduplicate through `put`'s duplicate
outcome — F2 in action), and reaches exactly `flatten`'s store through
the bridge. Layer 2's elaboration is not a parallel construction the
interpreter might drift from: it is what the program computes.

The proof leans on one packaged step (`step_put_honest`): admitting a
well-formed node whose references resolve over an honest word either
appends its binding fresh or deduplicates against the identical
resident — the conflict clause is unreachable precisely because honest
words never alias under `hInj` (`Honest.no_alias`'s substance, applied
through `find_honest`).
-/

namespace Cas.Lang

open Cas.Grammar

section TreeProg

variable (H : Bytes → Addr32)

/-- The store program of a grammar term, continuation-passing: admit
children, then admit the node over their answered addresses. -/
def _root_.Cas.Grammar.Tree.progK :
    Tree t → (Addr32 → Prog CasSig A) → Prog CasSig A
  | .value p, k => .vis (.put ⟨schemeVersion, Ty.value.wireTag, p.val, []⟩) k
  | .chunk p, k => .vis (.put ⟨schemeVersion, Ty.chunk.wireTag, p.val, []⟩) k
  | .schema p, k => .vis (.put ⟨schemeVersion, Ty.schema.wireTag, p.val, []⟩) k
  | .leaf i l d, k =>
    d.progK fun ca =>
      .vis (.put ⟨schemeVersion, Ty.tree.wireTag,
        nat32 i.toNat ++ nat32 l.toNat, [⟨Ty.chunk.wireTag, ca⟩]⟩) k
  | .parent l r, k =>
    l.progK fun la => r.progK fun ra =>
      .vis (.put ⟨schemeVersion, Ty.tree.wireTag, [],
        [⟨Ty.tree.wireTag, la⟩, ⟨Ty.tree.wireTag, ra⟩]⟩) k
  | .manifest re tot le root, k =>
    root.progK fun ra =>
      .vis (.put ⟨schemeVersion, Ty.manifest.wireTag,
        nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat,
        [⟨Ty.tree.wireTag, ra⟩]⟩) k
  | .file name mt c, k =>
    c.progK fun ca =>
      .vis (.put ⟨schemeVersion, Ty.file.wireTag,
        frame name.val ++ frame mt.val, [⟨Ty.manifest.wireTag, ca⟩]⟩) k
  | .git obj, k =>
    .vis (.put ⟨schemeVersion, Ty.git.wireTag, obj.val, []⟩) k
  | .genesis, k => .vis (.put ⟨schemeVersion, Ty.entry.wireTag, [], []⟩) k
  | .entry note item prev, k =>
    item.progK fun ia => prev.progK fun pa =>
      .vis (.put ⟨schemeVersion, Ty.entry.wireTag, note.val,
        [⟨Ty.file.wireTag, ia⟩, ⟨Ty.entry.wireTag, pa⟩]⟩) k

/-- The store program of a grammar term. -/
def _root_.Cas.Grammar.Tree.prog (tr : Tree t) : Prog CasSig Addr32 :=
  tr.progK .pure

/-- One honest put, packaged: a well-formed node whose references
resolve either appends fresh or deduplicates — and either way the step
answers the node's address, the extension is a sublist of the node's
own binding, and the projected store is exactly the appended one.
Conflict is unreachable: the honest resident at the node's address IS
the node (Level 1). -/
theorem step_put_honest {A} (hInj : Function.Injective H)
    {w : Word} (hw : Word.wf w = true) (hhon : Honest H w)
    {n : Node} (hn : n.WF)
    (hrefs : RefsOk (Word.toStore w) n.refs)
    (k : Addr32 → Prog CasSig A) :
    ∃ v, v.Sublist [Binding.mk (H (encodeNode n)) n]
      ∧ step H (.vis (.put n) k) w
          = (.running (k (H (encodeNode n))), w ++ v)
      ∧ Word.toStore (w ++ v) =
          Word.toStore (w ++ [Binding.mk (H (encodeNode n)) n])
      ∧ Word.wf (w ++ v) = true ∧ Honest H (w ++ v) := by
  have hchk : checkRefs (Word.toStore w) n.refs = .ok () :=
    checkRefs_ok_iff.mpr hrefs
  have haddr : addr H (⟨n, hn⟩ : AdmittedNode) = H (encodeNode n) := rfl
  have hresolves : ∀ r ∈ n.refs, Word.resolvesIn w r = true := by
    intro r hr
    obtain ⟨m, hm, ht⟩ := hrefs r hr
    exact Word.resolvesIn_iff.mpr ⟨m, hm, ht⟩
  cases hσ : Word.toStore w (H (encodeNode n)) with
  | none =>
    have hput : _root_.Cas.put H (Word.toStore w) ⟨n, hn⟩
        = .ok (.fresh (H (encodeNode n))
            ((Word.toStore w).set (H (encodeNode n)) n)) := by
      simp only [_root_.Cas.put, hchk, haddr, hσ]
    refine ⟨[Binding.mk (H (encodeNode n)) n],
      List.Sublist.refl _, ?_, rfl, ?_, ?_⟩
    · simp only [step, dif_pos hn, hput]
    · exact Word.wf_snoc hw hresolves
    · refine Honest.append H hhon ?_
      intro p hp
      simp only [List.mem_singleton] at hp
      subst hp
      exact ⟨rfl, hn⟩
  | some m =>
    have hm : m = n :=
      find_honest H hInj hhon hn hσ
    subst hm
    have hput : _root_.Cas.put H (Word.toStore w) ⟨m, hn⟩
        = .ok (.duplicate (H (encodeNode m))) := by
      simp only [_root_.Cas.put, hchk, haddr, hσ]
      rw [if_pos trivial]
    refine ⟨[], List.nil_sublist _, ?_, ?_, ?_, ?_⟩
    · simp only [step, dif_pos hn, hput, List.append_nil]
    · rw [List.append_nil,
        Word.toStore_append_shadowed (by rw [show Word.find w (H (encodeNode m)) = some m from hσ]; rfl) m]
    · rw [List.append_nil]; exact hw
    · rw [List.append_nil]; exact hhon

/-- The interior of F1: running a term's program with exactly its
node-count of extra fuel lands in the continuation at the term's fold
address, over a word that grew by a sublist of `flatten` and projects
to exactly `flatten`'s store. -/
theorem _root_.Cas.Grammar.Tree.progK_run {A}
    (hInj : Function.Injective H) {t : Ty} (tr : Tree t) :
    ∀ (k : Addr32 → Prog CasSig A) (fuel : Nat) (w : Word),
      Word.wf w = true → Honest H w →
      ∃ v, v.Sublist (tr.flatten H)
        ∧ run H (tr.size + fuel) (tr.progK k) w
            = run H fuel (k (tr.address H)) (w ++ v)
        ∧ Word.toStore (w ++ v) = Word.toStore (w ++ tr.flatten H)
        ∧ Word.wf (w ++ v) = true ∧ Honest H (w ++ v) := by
  induction tr with
  | value p =>
    intro k fuel w hw hhon
    obtain ⟨v, hsub, hstep, hstore, hwf', hhon'⟩ :=
      step_put_honest H hInj hw hhon (Tree.node_wf H (.value p))
        (by intro r hr; simp [Tree.node] at hr) k
    refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
    rw [Nat.add_comm]
    exact run_step_running H hstep fuel
  | chunk p =>
    intro k fuel w hw hhon
    obtain ⟨v, hsub, hstep, hstore, hwf', hhon'⟩ :=
      step_put_honest H hInj hw hhon (Tree.node_wf H (.chunk p))
        (by intro r hr; simp [Tree.node] at hr) k
    refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
    rw [Nat.add_comm]
    exact run_step_running H hstep fuel
  | schema p =>
    intro k fuel w hw hhon
    obtain ⟨v, hsub, hstep, hstore, hwf', hhon'⟩ :=
      step_put_honest H hInj hw hhon (Tree.node_wf H (.schema p))
        (by intro r hr; simp [Tree.node] at hr) k
    refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
    rw [Nat.add_comm]
    exact run_step_running H hstep fuel
  | genesis =>
    intro k fuel w hw hhon
    obtain ⟨v, hsub, hstep, hstore, hwf', hhon'⟩ :=
      step_put_honest H hInj hw hhon (Tree.node_wf H .genesis)
        (by intro r hr; simp [Tree.node] at hr) k
    refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
    rw [Nat.add_comm]
    exact run_step_running H hstep fuel
  | git obj =>
    intro k fuel w hw hhon
    obtain ⟨v, hsub, hstep, hstore, hwf', hhon'⟩ :=
      step_put_honest H hInj hw hhon (Tree.node_wf H (.git obj))
        (by intro r hr; simp [Tree.node] at hr) k
    refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
    rw [Nat.add_comm]
    exact run_step_running H hstep fuel
  | leaf i l d ih =>
    intro k fuel w hw hhon
    obtain ⟨v₁, hsub₁, hrun₁, hstore₁, hwf₁, hhon₁⟩ :=
      ih (fun ca =>
          .vis (.put ⟨schemeVersion, Ty.tree.wireTag,
            nat32 i.toNat ++ nat32 l.toNat, [⟨Ty.chunk.wireTag, ca⟩]⟩) k)
        (1 + fuel) w hw hhon
    have hhonflat : Honest H (w ++ d.flatten H) :=
      Honest.append H hhon (Tree.flatten_honest H d)
    have hmem : Binding.mk (d.address H) (d.node H) ∈
        w ++ d.flatten H :=
      List.mem_append_right _ (Tree.self_mem_flatten H d)
    obtain ⟨mm, hmm, htag⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat d hmem)
    have hrefs : RefsOk (Word.toStore (w ++ v₁))
        [⟨Ty.chunk.wireTag, d.address H⟩] := by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨mm, ?_, htag⟩
      show Word.toStore (w ++ v₁) (d.address H) = some mm
      rw [hstore₁]
      exact hmm
    obtain ⟨v₂, hsub₂, hstep₂, hstore₂, hwf₂, hhon₂⟩ :=
      step_put_honest H hInj hwf₁ hhon₁ (Tree.node_wf H (.leaf i l d)) hrefs k
    refine ⟨v₁ ++ v₂, List.Sublist.append hsub₁ hsub₂, ?_, ?_, ?_, ?_⟩
    · calc run H ((Tree.leaf i l d).size + fuel) ((Tree.leaf i l d).progK k) w
          = run H (d.size + (1 + fuel)) ((Tree.leaf i l d).progK k) w := by
            rw [show (Tree.leaf i l d).size + fuel = d.size + (1 + fuel) from by
              simp only [Tree.size]; omega]
        _ = run H (1 + fuel) _ (w ++ v₁) := hrun₁
        _ = run H fuel (k ((Tree.leaf i l d).address H)) ((w ++ v₁) ++ v₂) := by
            rw [Nat.add_comm]
            exact run_step_running H hstep₂ fuel
        _ = run H fuel (k ((Tree.leaf i l d).address H)) (w ++ (v₁ ++ v₂)) := by
            rw [List.append_assoc]
    · rw [← List.append_assoc, hstore₂,
        Word.toStore_append_congr hstore₁, List.append_assoc]
      exact rfl
    · rw [← List.append_assoc]; exact hwf₂
    · rw [← List.append_assoc]; exact hhon₂
  | manifest re tot le root ih =>
    intro k fuel w hw hhon
    obtain ⟨v₁, hsub₁, hrun₁, hstore₁, hwf₁, hhon₁⟩ :=
      ih (fun ra =>
          .vis (.put ⟨schemeVersion, Ty.manifest.wireTag,
            nat32 re.toNat ++ nat64 tot.toNat ++ nat32 le.toNat,
            [⟨Ty.tree.wireTag, ra⟩]⟩) k)
        (1 + fuel) w hw hhon
    have hhonflat : Honest H (w ++ root.flatten H) :=
      Honest.append H hhon (Tree.flatten_honest H root)
    have hmem : Binding.mk (root.address H) (root.node H) ∈
        w ++ root.flatten H :=
      List.mem_append_right _ (Tree.self_mem_flatten H root)
    obtain ⟨mm, hmm, htag⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat root hmem)
    have hrefs : RefsOk (Word.toStore (w ++ v₁))
        [⟨Ty.tree.wireTag, root.address H⟩] := by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨mm, ?_, htag⟩
      show Word.toStore (w ++ v₁) (root.address H) = some mm
      rw [hstore₁]
      exact hmm
    obtain ⟨v₂, hsub₂, hstep₂, hstore₂, hwf₂, hhon₂⟩ :=
      step_put_honest H hInj hwf₁ hhon₁
        (Tree.node_wf H (.manifest re tot le root)) hrefs k
    refine ⟨v₁ ++ v₂, List.Sublist.append hsub₁ hsub₂, ?_, ?_, ?_, ?_⟩
    · calc run H ((Tree.manifest re tot le root).size + fuel)
            ((Tree.manifest re tot le root).progK k) w
          = run H (root.size + (1 + fuel))
              ((Tree.manifest re tot le root).progK k) w := by
            rw [show (Tree.manifest re tot le root).size + fuel
                = root.size + (1 + fuel) from by
              simp only [Tree.size]; omega]
        _ = run H (1 + fuel) _ (w ++ v₁) := hrun₁
        _ = run H fuel (k ((Tree.manifest re tot le root).address H))
              ((w ++ v₁) ++ v₂) := by
            rw [Nat.add_comm]
            exact run_step_running H hstep₂ fuel
        _ = run H fuel (k ((Tree.manifest re tot le root).address H))
              (w ++ (v₁ ++ v₂)) := by
            rw [List.append_assoc]
    · rw [← List.append_assoc, hstore₂,
        Word.toStore_append_congr hstore₁, List.append_assoc]
      exact rfl
    · rw [← List.append_assoc]; exact hwf₂
    · rw [← List.append_assoc]; exact hhon₂
  | file name mt c ih =>
    intro k fuel w hw hhon
    obtain ⟨v₁, hsub₁, hrun₁, hstore₁, hwf₁, hhon₁⟩ :=
      ih (fun ca =>
          .vis (.put ⟨schemeVersion, Ty.file.wireTag,
            frame name.val ++ frame mt.val, [⟨Ty.manifest.wireTag, ca⟩]⟩) k)
        (1 + fuel) w hw hhon
    have hhonflat : Honest H (w ++ c.flatten H) :=
      Honest.append H hhon (Tree.flatten_honest H c)
    have hmem : Binding.mk (c.address H) (c.node H) ∈
        w ++ c.flatten H :=
      List.mem_append_right _ (Tree.self_mem_flatten H c)
    obtain ⟨mm, hmm, htag⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat c hmem)
    have hrefs : RefsOk (Word.toStore (w ++ v₁))
        [⟨Ty.manifest.wireTag, c.address H⟩] := by
      intro r hr
      simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨mm, ?_, htag⟩
      show Word.toStore (w ++ v₁) (c.address H) = some mm
      rw [hstore₁]
      exact hmm
    obtain ⟨v₂, hsub₂, hstep₂, hstore₂, hwf₂, hhon₂⟩ :=
      step_put_honest H hInj hwf₁ hhon₁ (Tree.node_wf H (.file name mt c)) hrefs k
    refine ⟨v₁ ++ v₂, List.Sublist.append hsub₁ hsub₂, ?_, ?_, ?_, ?_⟩
    · calc run H ((Tree.file name mt c).size + fuel)
            ((Tree.file name mt c).progK k) w
          = run H (c.size + (1 + fuel)) ((Tree.file name mt c).progK k) w := by
            rw [show (Tree.file name mt c).size + fuel
                = c.size + (1 + fuel) from by
              simp only [Tree.size]; omega]
        _ = run H (1 + fuel) _ (w ++ v₁) := hrun₁
        _ = run H fuel (k ((Tree.file name mt c).address H))
              ((w ++ v₁) ++ v₂) := by
            rw [Nat.add_comm]
            exact run_step_running H hstep₂ fuel
        _ = run H fuel (k ((Tree.file name mt c).address H))
              (w ++ (v₁ ++ v₂)) := by
            rw [List.append_assoc]
    · rw [← List.append_assoc, hstore₂,
        Word.toStore_append_congr hstore₁, List.append_assoc]
      exact rfl
    · rw [← List.append_assoc]; exact hwf₂
    · rw [← List.append_assoc]; exact hhon₂
  | parent l r ihl ihr =>
    intro k fuel w hw hhon
    obtain ⟨v₁, hsub₁, hrun₁, hstore₁, hwf₁, hhon₁⟩ :=
      ihl (fun la => r.progK fun ra =>
          .vis (.put ⟨schemeVersion, Ty.tree.wireTag, [],
            [⟨Ty.tree.wireTag, la⟩, ⟨Ty.tree.wireTag, ra⟩]⟩) k)
        (r.size + (1 + fuel)) w hw hhon
    obtain ⟨v₂, hsub₂, hrun₂, hstore₂, hwf₂, hhon₂⟩ :=
      ihr (fun ra =>
          .vis (.put ⟨schemeVersion, Ty.tree.wireTag, [],
            [⟨Ty.tree.wireTag, l.address H⟩, ⟨Ty.tree.wireTag, ra⟩]⟩) k)
        (1 + fuel) (w ++ v₁) hwf₁ hhon₁
    have hchain : Word.toStore ((w ++ v₁) ++ v₂)
        = Word.toStore (w ++ (l.flatten H ++ r.flatten H)) := by
      rw [hstore₂, Word.toStore_append_congr hstore₁, List.append_assoc]
    have hhonflat : Honest H (w ++ (l.flatten H ++ r.flatten H)) :=
      Honest.append H hhon
        (Honest.append H (Tree.flatten_honest H l) (Tree.flatten_honest H r))
    have hmeml : Binding.mk (l.address H) (l.node H) ∈
        w ++ (l.flatten H ++ r.flatten H) :=
      List.mem_append_right _
        (List.mem_append_left _ (Tree.self_mem_flatten H l))
    have hmemr : Binding.mk (r.address H) (r.node H) ∈
        w ++ (l.flatten H ++ r.flatten H) :=
      List.mem_append_right _
        (List.mem_append_right _ (Tree.self_mem_flatten H r))
    obtain ⟨ml, hml, htagl⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat l hmeml)
    obtain ⟨mr, hmr, htagr⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat r hmemr)
    have hrefs : RefsOk (Word.toStore ((w ++ v₁) ++ v₂))
        [⟨Ty.tree.wireTag, l.address H⟩, ⟨Ty.tree.wireTag, r.address H⟩] := by
      intro q hq
      rw [List.mem_cons, List.mem_singleton] at hq
      rcases hq with hq | hq <;> subst hq
      · refine ⟨ml, ?_, htagl⟩
        show Word.toStore ((w ++ v₁) ++ v₂) (l.address H) = some ml
        rw [hchain]
        exact hml
      · refine ⟨mr, ?_, htagr⟩
        show Word.toStore ((w ++ v₁) ++ v₂) (r.address H) = some mr
        rw [hchain]
        exact hmr
    obtain ⟨v₃, hsub₃, hstep₃, hstore₃, hwf₃, hhon₃⟩ :=
      step_put_honest H hInj hwf₂ hhon₂ (Tree.node_wf H (.parent l r)) hrefs k
    refine ⟨(v₁ ++ v₂) ++ v₃,
      List.Sublist.append (List.Sublist.append hsub₁ hsub₂) hsub₃,
      ?_, ?_, ?_, ?_⟩
    · calc run H ((Tree.parent l r).size + fuel) ((Tree.parent l r).progK k) w
          = run H (l.size + (r.size + (1 + fuel)))
              ((Tree.parent l r).progK k) w := by
            rw [show (Tree.parent l r).size + fuel
                = l.size + (r.size + (1 + fuel)) from by
              simp only [Tree.size]; omega]
        _ = run H (r.size + (1 + fuel)) _ (w ++ v₁) := hrun₁
        _ = run H (1 + fuel) _ ((w ++ v₁) ++ v₂) := hrun₂
        _ = run H fuel (k ((Tree.parent l r).address H))
              (((w ++ v₁) ++ v₂) ++ v₃) := by
            rw [Nat.add_comm]
            exact run_step_running H hstep₃ fuel
        _ = run H fuel (k ((Tree.parent l r).address H))
              (w ++ ((v₁ ++ v₂) ++ v₃)) := by
            rw [← List.append_assoc, ← List.append_assoc]
    · have hflip : Word.toStore (w ++ ((v₁ ++ v₂) ++ v₃))
          = Word.toStore (((w ++ v₁) ++ v₂) ++ v₃) := by
        rw [← List.append_assoc, ← List.append_assoc]
      rw [hflip, hstore₃, Word.toStore_append_congr hchain]
      simp only [Tree.flatten, Tree.address, List.append_assoc]
    · rw [← List.append_assoc, ← List.append_assoc]; exact hwf₃
    · rw [← List.append_assoc, ← List.append_assoc]; exact hhon₃
  | entry note item prev ihi ihp =>
    intro k fuel w hw hhon
    obtain ⟨v₁, hsub₁, hrun₁, hstore₁, hwf₁, hhon₁⟩ :=
      ihi (fun ia => prev.progK fun pa =>
          .vis (.put ⟨schemeVersion, Ty.entry.wireTag, note.val,
            [⟨Ty.file.wireTag, ia⟩, ⟨Ty.entry.wireTag, pa⟩]⟩) k)
        (prev.size + (1 + fuel)) w hw hhon
    obtain ⟨v₂, hsub₂, hrun₂, hstore₂, hwf₂, hhon₂⟩ :=
      ihp (fun pa =>
          .vis (.put ⟨schemeVersion, Ty.entry.wireTag, note.val,
            [⟨Ty.file.wireTag, item.address H⟩, ⟨Ty.entry.wireTag, pa⟩]⟩) k)
        (1 + fuel) (w ++ v₁) hwf₁ hhon₁
    have hchain : Word.toStore ((w ++ v₁) ++ v₂)
        = Word.toStore (w ++ (item.flatten H ++ prev.flatten H)) := by
      rw [hstore₂, Word.toStore_append_congr hstore₁, List.append_assoc]
    have hhonflat : Honest H (w ++ (item.flatten H ++ prev.flatten H)) :=
      Honest.append H hhon
        (Honest.append H (Tree.flatten_honest H item)
          (Tree.flatten_honest H prev))
    have hmemi : Binding.mk (item.address H) (item.node H)
        ∈ w ++ (item.flatten H ++ prev.flatten H) :=
      List.mem_append_right _
        (List.mem_append_left _ (Tree.self_mem_flatten H item))
    have hmemp : Binding.mk (prev.address H) (prev.node H)
        ∈ w ++ (item.flatten H ++ prev.flatten H) :=
      List.mem_append_right _
        (List.mem_append_right _ (Tree.self_mem_flatten H prev))
    obtain ⟨mi, hmi, htagi⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat item hmemi)
    obtain ⟨mp, hmp, htagp⟩ :=
      Word.resolvesIn_iff.mp (resolves_child H hInj hhonflat prev hmemp)
    have hrefs : RefsOk (Word.toStore ((w ++ v₁) ++ v₂))
        [⟨Ty.file.wireTag, item.address H⟩,
         ⟨Ty.entry.wireTag, prev.address H⟩] := by
      intro q hq
      rw [List.mem_cons, List.mem_singleton] at hq
      rcases hq with hq | hq <;> subst hq
      · refine ⟨mi, ?_, htagi⟩
        show Word.toStore ((w ++ v₁) ++ v₂) (item.address H) = some mi
        rw [hchain]
        exact hmi
      · refine ⟨mp, ?_, htagp⟩
        show Word.toStore ((w ++ v₁) ++ v₂) (prev.address H) = some mp
        rw [hchain]
        exact hmp
    obtain ⟨v₃, hsub₃, hstep₃, hstore₃, hwf₃, hhon₃⟩ :=
      step_put_honest H hInj hwf₂ hhon₂
        (Tree.node_wf H (.entry note item prev)) hrefs k
    refine ⟨(v₁ ++ v₂) ++ v₃,
      List.Sublist.append (List.Sublist.append hsub₁ hsub₂) hsub₃,
      ?_, ?_, ?_, ?_⟩
    · calc run H ((Tree.entry note item prev).size + fuel)
            ((Tree.entry note item prev).progK k) w
          = run H (item.size + (prev.size + (1 + fuel)))
              ((Tree.entry note item prev).progK k) w := by
            rw [show (Tree.entry note item prev).size + fuel
                = item.size + (prev.size + (1 + fuel)) from by
              simp only [Tree.size]; omega]
        _ = run H (prev.size + (1 + fuel)) _ (w ++ v₁) := hrun₁
        _ = run H (1 + fuel) _ ((w ++ v₁) ++ v₂) := hrun₂
        _ = run H fuel (k ((Tree.entry note item prev).address H))
              (((w ++ v₁) ++ v₂) ++ v₃) := by
            rw [Nat.add_comm]
            exact run_step_running H hstep₃ fuel
        _ = run H fuel (k ((Tree.entry note item prev).address H))
              (w ++ ((v₁ ++ v₂) ++ v₃)) := by
            rw [← List.append_assoc, ← List.append_assoc]
    · have hflip : Word.toStore (w ++ ((v₁ ++ v₂) ++ v₃))
          = Word.toStore (((w ++ v₁) ++ v₂) ++ v₃) := by
        rw [← List.append_assoc, ← List.append_assoc]
      rw [hflip, hstore₃, Word.toStore_append_congr hchain]
      simp only [Tree.flatten, Tree.address, List.append_assoc]
    · rw [← List.append_assoc, ← List.append_assoc]; exact hwf₃
    · rw [← List.append_assoc, ← List.append_assoc]; exact hhon₃

/-- F1, `putTree_correct`: under an injective digest, running a
grammar term's program with node-count-plus-one fuel over any honest
admissible word completes at exactly the term's fold address, the word
grows by a sublist of the term's `flatten` (shared subterms
deduplicate), and the projected store is exactly `flatten`'s — layer
2's elaboration, computed by layer 3. -/
theorem _root_.Cas.Grammar.Tree.putTree_correct
    (hInj : Function.Injective H) {t : Ty} (tr : Tree t) {w : Word}
    (hw : Word.wf w = true) (hhon : Honest H w) :
    ∃ v, v.Sublist (tr.flatten H)
      ∧ run H (tr.size + 1) tr.prog w = (.done (tr.address H), w ++ v)
      ∧ Word.toStore (w ++ v) = Word.toStore (w ++ tr.flatten H)
      ∧ Word.wf (w ++ v) = true ∧ Honest H (w ++ v) := by
  obtain ⟨v, hsub, hrun, hstore, hwf', hhon'⟩ :=
    tr.progK_run H hInj .pure 1 w hw hhon
  refine ⟨v, hsub, ?_, hstore, hwf', hhon'⟩
  simp only [Tree.prog]
  rw [hrun]
  rfl

/-- F1 from nothing: the empty word is honest and admissible, so every
grammar term's program builds its own store from scratch — and with no
prior bindings to deduplicate against, the word IS `flatten`'s store. -/
theorem _root_.Cas.Grammar.Tree.putTree_correct_empty
    (hInj : Function.Injective H) {t : Ty} (tr : Tree t) :
    ∃ v, v.Sublist (tr.flatten H)
      ∧ run H (tr.size + 1) tr.prog [] = (.done (tr.address H), v)
      ∧ Word.toStore v = Word.toStore (tr.flatten H)
      ∧ Word.wf v = true ∧ Honest H v := by
  obtain ⟨v, hsub, hrun, hstore, hwf', hhon'⟩ :=
    tr.putTree_correct H hInj (w := []) rfl (Honest.nil H)
  exact ⟨v, hsub, hrun, hstore, hwf', hhon'⟩

end TreeProg

end Cas.Lang
