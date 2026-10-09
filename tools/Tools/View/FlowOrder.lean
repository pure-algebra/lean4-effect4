import Tools.View.FlowLaws
import Tools.View.AlgGraph

/-!
# A flow's order, and the layout that keeps it (slice D1's faithfulness)

Slice D1 of `docs/research/2026-10-09-program-graph-design.md`, placed in its section 6. A flow's
**order** is what its structure says comes before what: a fold of the flow into the algebraic graph
(`Tools.View.AGraph`). A series connects its parts, so each part comes before every later part;
branches side by side overlay, so no branch comes before another; a region and a loop keep their
body's order. The order of a fiber forked beside its parent is overlaid with the parent's
continuation: the drawing reads no order between them.

**The law** (`lay_realizes`): the layout realizes the order. Every vertex of the order is a node of
the layout, and every edge of the order runs from a node to a later node that it reaches along the
layout's edges. With `place_descends` it gives `place_keeps_order`: when a flow orders one node
before another, the layout draws the first above the second. "Above means before" is a theorem.

The proof of a series follows the left fold of `stackIn`, and turns the order's right-nested
connects into it by the associativity of connect (`AGraph.connect_assoc`) and its unit
(`AGraph.connect_empty`): two of D1's axioms at work.

**What it does not establish.** The order is the flow's structural reading; it says nothing of when
a fiber runs. The converse (a node above another comes before it) is false: branches side by side
stand at heights of their own. Waits are not in the order; the layout meets them as edges where
they close no cycle. Each law is a tool's named law (decisions row 336, point 8), serving concept 7
of `docs/core/semantics.md` (`initial-algebras-folds`).
-/

namespace Tools.View.Flow

open Tools.View.AGraph

mutual
/-- **A flow's order**, a fold of the flow into the algebraic graph. -/
def Flow.order : Flow → AGraph Key
  | .node k _ _ _ => .vertex k
  | .seq ps => orderSeq ps
  | .par _ _ bs => orderPar bs
  | .region _ _ b => b.order
  | .loop _ b => b.order
/-- Parts in series: each connected before the rest. -/
def orderSeq : List Flow → AGraph Key
  | [] => .empty
  | f :: fs => .connect f.order (orderSeq fs)
/-- Branches side by side: overlaid. -/
def orderPar : List Flow → AGraph Key
  | [] => .empty
  | f :: fs => .overlay f.order (orderPar fs)
end

/-- **A part realizes an order**: each vertex is a node of the part, and each edge runs from a node
to a later node that it reaches along the part's edges. -/
structure Realizes (g : AGraph Key) (b : Box) : Prop where
  shows : ∀ k, (denote g).has k → ∃ (i : Nat) (p : Placed), b.items[i]? = some p ∧ p.key = k ∧ p.node.isSome
  keeps : ∀ u v, (denote g).edge u v → ∃ (i j : Nat) (p q : Placed), i < j ∧ b.items[i]? = some p ∧ p.key = u ∧
    p.node.isSome ∧ b.items[j]? = some q ∧ q.key = v ∧ q.node.isSome ∧ Reach b.edges i j

theorem Realizes.congr {g g' : AGraph Key} {b : Box} (h : denote g = denote g') (r : Realizes g b) :
    Realizes g' b :=
  ⟨fun k hk => r.shows k (by rw [h]; exact hk), fun u v he => r.keeps u v (by rw [h]; exact he)⟩

/-- A graph with no vertex is realized by every part. -/
theorem realizes_none {g : AGraph Key} (b : Box) (h : ∀ k, ¬ (denote g).has k) : Realizes g b :=
  ⟨fun k hk => (h k hk).elim, fun u _ he => (h u (edge_has g he).1).elim⟩

/-- A part moved across realizes what it realized. -/
theorem Realizes.moved {g : AGraph Key} {b b' : Box} (r : Realizes g b) {d : Int}
    (hitems : b'.items = b.items.map (moveX d)) (hedges : b'.edges = b.edges) : Realizes g b' := by
  refine ⟨fun k hk => ?_, fun u v he => ?_⟩
  · obtain ⟨i, p, hp, hk, hn⟩ := r.shows k hk
    exact ⟨i, moveX d p, by rw [hitems, List.getElem?_map, hp]; rfl, hk, hn⟩
  · obtain ⟨i, j, p, q, hij, hp, hu, hpn, hq, hv, hqn, hr⟩ := r.keeps u v he
    exact ⟨i, j, moveX d p, moveX d q, hij, by rw [hitems, List.getElem?_map, hp]; rfl, hu, hpn,
      by rw [hitems, List.getElem?_map, hq]; rfl, hv, hqn, hedges ▸ hr⟩

/-! ## Series -/

theorem series_subL (s m : Box) : ∀ e ∈ s.edges, e ∈ (s.series m).edges := fun e he => by
  rw [series_edges]; exact List.mem_append_left _ (List.mem_append_left _ he)

theorem series_subR (s m : Box) : ∀ e ∈ m.edges.map (Edge.reindex s.items.length), e ∈ (s.series m).edges :=
  fun e he => by rw [series_edges]; exact List.mem_append_left _ (List.mem_append_right _ he)

/-- In a series, every item of the first part reaches every item of the second. -/
theorem series_across {s m : Box} (hs : Good s) (hm : Good m) {i j : Nat} (hi : i < s.items.length) (hj1 : s.items.length ≤ j) (hj2 : j < s.items.length + m.items.length) :
    Reach (s.series m).edges i j := by
  have join : joinEdge s m ∈ (s.series m).edges := by
    rw [series_edges]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have r1 := ((hs.toSnk i hi).mono (series_subL s m)).trans (Reach.edge join)
  have r2 := (Reach.unshift (Nat.le_add_left _ _) hj1
    (by rw [Nat.add_sub_cancel]; exact (hm.fromSrc (j - s.items.length) (by omega)).reindex _)).mono (series_subR s m)
  exact r1.trans r2

theorem realizes_series {g h : AGraph Key} {s m : Box} (hs : Good s) (hm : Good m) (rs : Realizes g s) (rm : Realizes h m) : Realizes (.connect g h) (s.series m) := by
  have hitems : (s.series m).items = s.items ++ m.items := rfl
  have left : ∀ {i p}, s.items[i]? = some p → (s.series m).items[i]? = some p := fun {i} {p} hp => by
    rw [hitems, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hp).1]; exact hp
  have right : ∀ {t p}, m.items[t]? = some p → (s.series m).items[s.items.length + t]? = some p := fun {t} {p} hp => by
    rw [hitems, List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]; exact hp
  have lenR : ∀ {t p}, m.items[t]? = some p → t < m.items.length := fun hp => (List.getElem?_eq_some_iff.mp hp).1
  have lenL : ∀ {i p}, s.items[i]? = some p → i < s.items.length := fun hp => (List.getElem?_eq_some_iff.mp hp).1
  refine ⟨fun k hk => ?_, fun u v he => ?_⟩
  · rcases hk with hk | hk
    · obtain ⟨i, p, hp, h1, h2⟩ := rs.shows k hk
      exact ⟨i, p, left hp, h1, h2⟩
    · obtain ⟨t, p, hp, h1, h2⟩ := rm.shows k hk
      exact ⟨_, p, right hp, h1, h2⟩
  · rcases he with he | he | ⟨hu, hv⟩
    · obtain ⟨i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩ := rs.keeps u v he
      exact ⟨i, j, p, q, hij, left hp, h1, h2, left hq, h3, h4, hr.mono (series_subL s m)⟩
    · obtain ⟨i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩ := rm.keeps u v he
      refine ⟨_, _, p, q, by omega, right hp, h1, h2, right hq, h3, h4, ?_⟩
      have := (hr.reindex s.items.length).mono (series_subR s m)
      rw [Nat.add_comm i, Nat.add_comm j] at this
      exact this
    · obtain ⟨i, p, hp, h1, h2⟩ := rs.shows u hu
      obtain ⟨t, q, hq, h3, h4⟩ := rm.shows v hv
      have hi := lenL hp
      have ht := lenR hq
      exact ⟨i, _, p, q, by omega, left hp, h1, h2, right hq, h3, h4,
        series_across hs hm hi (Nat.le_add_right _ _) (by omega)⟩

/-! ## Orders with no vertex -/

theorem orderSeq_has : ∀ (ps : List Flow) (k : Key), (denote (orderSeq ps)).has k → ∃ f ∈ ps, (denote f.order).has k
  | [], _, h => h.elim
  | f :: fs, k, h => by
    rcases h with h | h
    · exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨f', hf', h'⟩ := orderSeq_has fs k h
      exact ⟨f', List.mem_cons_of_mem _ hf', h'⟩

theorem orderPar_has : ∀ (bs : List Flow) (k : Key), (denote (orderPar bs)).has k → ∃ f ∈ bs, (denote f.order).has k
  | [], _, h => h.elim
  | f :: fs, k, h => by
    rcases h with h | h
    · exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨f', hf', h'⟩ := orderPar_has fs k h
      exact ⟨f', List.mem_cons_of_mem _ hf', h'⟩

theorem orderPar_edge : ∀ (bs : List Flow) (u v : Key), (denote (orderPar bs)).edge u v →
    ∃ f ∈ bs, (denote f.order).edge u v
  | [], _, _, h => h.elim
  | f :: fs, u, v, h => by
    rcases h with h | h
    · exact ⟨f, List.mem_cons_self, h⟩
    · obtain ⟨f', hf', h'⟩ := orderPar_edge fs u v h
      exact ⟨f', List.mem_cons_of_mem _ hf', h'⟩

/-- A connect after a graph with no vertex is the second graph. -/
theorem connect_none_left {g h : AGraph Key} (hg : ∀ k, ¬ (denote g).has k) : denote (.connect g h) = denote h := by
  refine Rel.ext' (fun a => ⟨fun h' => h'.elim (fun x => (hg a x).elim) id, .inr⟩)
    (fun a b => ⟨fun h' => ?_, fun h' => .inr (.inl h')⟩)
  rcases h' with h' | h' | ⟨ha, _⟩
  · exact (hg a (edge_has g h').1).elim
  · exact h'
  · exact (hg a ha).elim

/-- Connect respects equal models on its right. -/
theorem connect_congr_right (g : AGraph Key) {h h' : AGraph Key} (e : denote h = denote h') :
    denote (.connect g h) = denote (.connect g h') := by
  show Rel.mk _ _ = Rel.mk _ _
  rw [e]

/-! ## Stacks -/

theorem layAllWith_map (width : GNode → Int) : ∀ ps : List Flow, layAllWith width ps = ps.map (layWith width)
  | [] => rfl
  | f :: fs => by
    show layWith width f :: layAllWith width fs = layWith width f :: fs.map (layWith width)
    rw [layAllWith_map width fs]

/-- **Parts in series after `s` realize the connect of `s`'s order with theirs.** The left fold of
`stackIn` meets the order's right-nested connects by associativity. -/
theorem stackIn_realizes {width : GNode → Int} (W : Int) :
    ∀ (ps : List Flow) (s : Box) (acc : AGraph Key), Good s → s.items ≠ [] → s.w = W → Realizes acc s →
      (∀ f ∈ ps, Realizes f.order (layWith width f) ∧ Good (layWith width f) ∧
        ((layWith width f).items ≠ [] → (layWith width f).w ≤ W)) →
      Realizes (.connect acc (orderSeq ps)) (stackIn W s ((ps.map (layWith width)).filter (!·.empty)))
  | [], s, acc, _, _, _, r, _ => r.congr (connect_empty acc).symm
  | f :: fs, s, acc, hs, hn, hw, r, hps => by
    have hf := hps f List.mem_cons_self
    have hrest : ∀ f' ∈ fs, Realizes f'.order (layWith width f') ∧ Good (layWith width f') ∧
        ((layWith width f').items ≠ [] → (layWith width f').w ≤ W) :=
      fun f' h' => hps f' (List.mem_cons_of_mem _ h')
    by_cases he : (layWith width f).empty = true
    · have hnil : (layWith width f).items = [] := List.isEmpty_iff.mp he
      have hnone : ∀ k, ¬ (denote f.order).has k := fun k hk => by
        obtain ⟨i, p, hp, _, _⟩ := hf.1.shows k hk
        rw [hnil] at hp; exact absurd hp (by simp only [List.getElem?_nil, reduceCtorEq, not_false_eq_true])
      have := stackIn_realizes W fs s acc hs hn hw r hrest
      rw [List.map_cons, List.filter_cons, if_neg (by simp only [he, Bool.not_true, Bool.false_eq_true, not_false_eq_true])]
      exact this.congr (connect_congr_right acc (connect_none_left hnone).symm)
    · rw [List.map_cons, List.filter_cons, if_pos (by simp only [Bool.not_eq_true'] at he ⊢; simp only [he])]
      have hfn : (layWith width f).items ≠ [] := fun h => he (by simp only [Box.empty, h, List.isEmpty_nil])
      let m := (layWith width f).shift ((W - (layWith width f).w) / 2)
      have hm : Good { m with w := W } := good_centred hf.2.1 (hf.2.2 hfn)
      have hmn : m.items ≠ [] := by
        show ((layWith width f).shift ((W - (layWith width f).w) / 2)).items ≠ []
        rw [map_moveX_shift]; intro h; exact hfn (List.map_eq_nil_iff.mp h)
      have rm : Realizes f.order { m with w := W } := hf.1.moved rfl rfl
      have hser : Good (s.series { m with w := W }) := good_series hs hm hw hn hmn
      have rser : Realizes (.connect acc f.order) (s.series { m with w := W }) := realizes_series hs hm r rm
      have hne : (s.series m).items ≠ [] := by
        show s.items ++ _ ≠ []
        intro h; exact hn (List.append_eq_nil_iff.mp h).1
      have := stackIn_realizes W fs (s.series m) (.connect acc f.order) hser hne hw rser hrest
      show Realizes _ (stackIn W (s.series m) _)
      exact this.congr (connect_assoc acc f.order (orderSeq fs)).symm

/-- **A series realizes its order**: its parts, centred in the widest one's width, in series. -/
theorem stack_realizes {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) :
    ∀ (ps : List Flow), (∀ f ∈ ps, Realizes f.order (layWith width f)) →
      Realizes (orderSeq ps) (stack ((ps.map (layWith width)).filter (!·.empty))) := by
  intro ps hps
  -- the widest part's width bounds every part
  generalize hbs : (ps.map (layWith width)).filter (!·.empty) = bs
  cases bs with
  | nil =>
    refine realizes_none _ fun k hk => ?_
    obtain ⟨f, hf, hk⟩ := orderSeq_has ps k hk
    obtain ⟨i, p, hp, _, _⟩ := (hps f hf).shows k hk
    have hin : layWith width f ∈ (ps.map (layWith width)).filter (!·.empty) := by
      refine List.mem_filter.mpr ⟨List.mem_map_of_mem hf, ?_⟩
      have hne : (layWith width f).items ≠ [] := fun h => by rw [h] at hp; simp only [List.getElem?_nil, reduceCtorEq] at hp
      simp only [Box.empty, Bool.not_eq_true', List.isEmpty_eq_false_iff]; exact hne
    rw [hbs] at hin; exact absurd hin List.not_mem_nil
  | cons first rest =>
    let W : Int := (first :: rest).foldl (fun m b => max m b.w) 0
    have hW := foldl_max_ge (first :: rest) 0
    -- split `ps` at its first part that is not empty
    have key : ∀ (qs : List Flow), (∀ f ∈ qs, Realizes f.order (layWith width f)) →
        (∀ f ∈ qs, (layWith width f).items ≠ [] → (layWith width f).w ≤ W) →
        (qs.map (layWith width)).filter (!·.empty) = first :: rest →
        Realizes (orderSeq qs) (stackIn W { first.shift ((W - first.w) / 2) with w := W } rest) := by
      intro qs
      induction qs with
      | nil => intro _ _ h; simp only [List.map_nil, List.filter_nil, reduceCtorEq] at h
      | cons f fs ih =>
        intro hq hwq h
        by_cases he : (layWith width f).empty = true
        · have hnil : (layWith width f).items = [] := List.isEmpty_iff.mp he
          have hnone : ∀ k, ¬ (denote f.order).has k := fun k hk => by
            obtain ⟨i, p, hp, _, _⟩ := (hq f List.mem_cons_self).shows k hk
            rw [hnil] at hp; simp only [List.getElem?_nil, reduceCtorEq] at hp
          rw [List.map_cons, List.filter_cons, if_neg (by simp only [he, Bool.not_true, Bool.false_eq_true, not_false_eq_true])] at h
          exact (ih (fun f' h' => hq f' (List.mem_cons_of_mem _ h')) (fun f' h' => hwq f' (List.mem_cons_of_mem _ h')) h).congr
            (connect_none_left hnone).symm
        · rw [List.map_cons, List.filter_cons,
            if_pos (by simp only [Bool.not_eq_true'] at he ⊢; simp only [he])] at h
          obtain ⟨rfl, rfl⟩ := List.cons.inj h
          have hfn : (layWith width f).items ≠ [] := fun h' => he (by simp only [Box.empty, h', List.isEmpty_nil])
          have hfg := lay_good hw f
          have hfirst : Good { (layWith width f).shift ((W - (layWith width f).w) / 2) with w := W } :=
            good_centred hfg (hwq f List.mem_cons_self hfn)
          have hfirstn : ((layWith width f).shift ((W - (layWith width f).w) / 2)).items ≠ [] := by
            rw [map_moveX_shift]; intro h'; exact hfn (List.map_eq_nil_iff.mp h')
          have r0 : Realizes f.order { (layWith width f).shift ((W - (layWith width f).w) / 2) with w := W } :=
            (hq f List.mem_cons_self).moved rfl rfl
          have := stackIn_realizes (width := width) W fs _ f.order hfirst hfirstn rfl r0
            (fun f' h' => ⟨hq f' (List.mem_cons_of_mem _ h'), lay_good hw f', hwq f' (List.mem_cons_of_mem _ h')⟩)
          exact this.congr rfl
    show Realizes _ (stackIn W _ rest)
    refine key ps hps (fun f hf hne => hW.2 _ ?_) hbs
    rw [← hbs]
    refine List.mem_filter.mpr ⟨List.mem_map_of_mem hf, ?_⟩
    simp only [Box.empty, Bool.not_eq_true', List.isEmpty_eq_false_iff]; exact hne

/-! ## Parallel parts -/

/-- **A parallel part realizes an order that its branches realize**: each vertex and edge of it is
found in one branch, and the branch stands in its slot, its positions moved on. -/
theorem parAround_realizes {how : Branching} {k : Key} {W : Int} {ends : Bool} {s0 : Box}
    {L : List (Box × Nat)} {r : Box × List (Nat × Box)} (hspec : WBSpec (how != .choice) 0 s0 L r)
    {g : AGraph Key}
    (hg : ∀ u, (denote g).has u → ∃ bi ∈ L, ∃ (t : Nat) (p : Placed), bi.1.items[t]? = some p ∧ p.key = u ∧ p.node.isSome)
    (hge : ∀ u v, (denote g).edge u v → ∃ bi ∈ L, ∃ (i j : Nat) (p q : Placed), i < j ∧ bi.1.items[i]? = some p ∧
      p.key = u ∧ p.node.isSome ∧ bi.1.items[j]? = some q ∧ q.key = v ∧ q.node.isSome ∧ Reach bi.1.edges i j) :
    Realizes g (parAround how k W ends r.1 r.2) := by
  have Fitems : (parAround how k W ends r.1 r.2).items =
      r.1.items ++ (parBottom how k (W / 2 - CELL) ends r.1.items.length r.2).2.1 := rfl
  have bodySub : ∀ e ∈ r.1.edges, e ∈ (parAround how k W ends r.1 r.2).edges := fun e he => by
    show e ∈ (parTop how k r.2).1 ++ r.1.edges ++ _
    exact List.mem_append_left _ (List.mem_append_right _ he)
  -- an item of an input at its place in the part
  have place : ∀ bi ∈ L, ∃ sl ∈ r.2, ∃ x', sl.2 = bi.1.shift x' ∧ ∀ t (p : Placed), bi.1.items[t]? = some p →
      (parAround how k W ends r.1 r.2).items[sl.1 + t]? = some (moveX x' p) := by
    intro bi hbi
    obtain ⟨sl, hsl, x', hx'⟩ := hspec.inputs bi hbi
    refine ⟨sl, hsl, x', hx', fun t p hp => ?_⟩
    have ht : t < sl.2.items.length := by
      rw [hx', map_moveX_shift, List.length_map]; exact (List.getElem?_eq_some_iff.mp hp).1
    have hb := (hspec.slots sl hsl).2.2
    rw [Fitems, List.getElem?_append_left (by omega), hspec.at_ sl hsl t ht, hx', map_moveX_shift,
      List.getElem?_map, hp]
    rfl
  refine ⟨fun u hu => ?_, fun u v he => ?_⟩
  · obtain ⟨bi, hbi, t, p, hp, h1, h2⟩ := hg u hu
    obtain ⟨sl, _, x', _, hpl⟩ := place bi hbi
    exact ⟨_, moveX x' p, hpl t p hp, h1, h2⟩
  · obtain ⟨bi, hbi, i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩ := hge u v he
    obtain ⟨sl, hsl, x', hx', hpl⟩ := place bi hbi
    refine ⟨_, _, moveX x' p, moveX x' q, by omega, hpl i p hp, h1, h2, hpl j q hq, h3, h4, ?_⟩
    have hr' : Reach sl.2.edges i j := by rw [hx']; exact hr
    have := (hr'.reindex sl.1).mono (fun e he => by
      obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      exact bodySub _ ((hspec.edges _).mpr (.inr ⟨sl, hsl, e0, he0, rfl⟩)))
    rw [Nat.add_comm i, Nat.add_comm j] at this
    exact this

/-- **Branches side by side realize their overlay.** -/
theorem sideBySide_realizes (how : Branching) (k : Key) (bs : List Flow) (D : Flow → Box)
    (hbs : ∀ f ∈ bs, Realizes f.order (D f) ∧ Good (D f)) :
    Realizes (orderPar bs) (sideBySide how k (bs.map D)) := by
  let bs1 := (bs.map D).zipIdx.map fun (b, i) => if b.empty then point (k ++ "/" ++ toString i) else b
  have hgood : ∀ b ∈ bs.map D, Good b := fun b hb => by
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hb; exact (hbs f hf).2
  have h1 : ∀ b ∈ bs1, Good b := by
    intro b hb
    obtain ⟨⟨b0, i⟩, hbi, rfl⟩ := List.mem_map.mp hb
    have hb0 : b0 ∈ bs.map D := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hbi)
    by_cases he : b0.empty = true
    · simp only [he, if_true]; exact good_point _
    · simp only [he, if_false, Bool.false_eq_true]; exact hgood b0 hb0
  let W : Int := if bs1.isEmpty then CELL * GAP else span bs1
  let L := bs1.zipIdx
  let s0 : Box := { w := W, items := [pointAt (k ++ "/fork") (W / 2 - CELL)] }
  have hspec := withBranches_spec (how != .choice) k L 0 s0 (Int.le_refl 0)
    (fun bi hbi => h1 bi.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hbi)))
  -- a branch with a node is one of the inputs, as it is
  have input : ∀ f ∈ bs, (D f).items ≠ [] → ∃ i, (D f, i) ∈ L := by
    intro f hf hne
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hf
    refine ⟨i, List.mem_zipIdx_iff_getElem?.mpr ?_⟩
    show bs1[i]? = some (D f)
    have hm : (bs.map D)[i]? = some (D f) := by rw [List.getElem?_map, hi]; rfl
    have hz : ((bs.map D).zipIdx)[i]? = some (D f, i) := by
      rw [List.getElem?_zipIdx, hm, Option.map_some, Nat.zero_add]
    have hne' : (D f).empty = false := by
      simp only [Box.empty, List.isEmpty_eq_false_iff]; exact hne
    show (((bs.map D).zipIdx).map _)[i]? = _
    rw [List.getElem?_map, hz]
    simp only [Option.map_some, hne', Bool.false_eq_true, if_false]
  have nonempty : ∀ {f : Flow} {t : Nat} {p : Placed}, (D f).items[t]? = some p → (D f).items ≠ [] :=
    fun hp h => by rw [h] at hp; simp only [List.getElem?_nil, reduceCtorEq] at hp
  show Realizes _ (parAround how k W _ _ _)
  refine parAround_realizes hspec (fun u hu => ?_) (fun u v he => ?_)
  · obtain ⟨f, hf, hu⟩ := orderPar_has bs u hu
    obtain ⟨t, p, hp, h1, h2⟩ := (hbs f hf).1.shows u hu
    obtain ⟨i, hi⟩ := input f hf (nonempty hp)
    exact ⟨_, hi, t, p, hp, h1, h2⟩
  · obtain ⟨f, hf, he⟩ := orderPar_edge bs u v he
    obtain ⟨i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩ := (hbs f hf).1.keeps u v he
    obtain ⟨n, hn⟩ := input f hf (nonempty hp)
    exact ⟨_, hn, i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩

/-- A part with its shares split realizes what it realized: the split moves no item and no edge's
ends. -/
theorem Realizes.reshare {g : AGraph Key} {b : Box} (r : Realizes g b) (f : Nat) : Realizes g (b.reshare f) := by
  have hF : ∀ e : Edge, ({ e with share := e.share * f / 1000000 } : Edge).fr = e.fr ∧
      ({ e with share := e.share * f / 1000000 } : Edge).to = e.to := fun _ => ⟨rfl, rfl⟩
  refine ⟨r.shows, fun u v he => ?_⟩
  obtain ⟨i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩ := r.keeps u v he
  exact ⟨i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr.map hF⟩

/-! ## The fold's law -/

mutual
/-- **The layout realizes the flow's order** (slice D1): every vertex of the order is a node of the
layout, and every edge of the order runs from a node to a later node that it reaches along the
layout's edges. By fold induction over the flow, at any width of the nodes no less than zero. A
tool's named law; its consumer is `place_keeps_order`. -/
theorem lay_realizes {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) : ∀ f : Flow, Realizes f.order (layWith width f)
  | .node k l1 l2 w => by
    refine ⟨fun u hu => ⟨0, _, rfl, hu.symm, rfl⟩, fun u v he => he.elim⟩
  | .seq ps => by
    show Realizes (orderSeq ps) (stack ((layAllWith width ps).filter (!·.empty)))
    rw [layAllWith_map]
    exact stack_realizes hw ps (layAll_realizes hw ps)
  | .par how k bs => by
    show Realizes (orderPar bs) (sideBySide how k (shares how (layAllWith width bs)))
    rw [layAllWith_map]
    have e : shares how (bs.map (layWith width)) = bs.map (fun f =>
        if how = .choice then layWith width f else (layWith width f).reshare (Grow.split bs.length)) := by
      unfold shares
      by_cases hc : how = .choice
      · rw [if_pos hc]; exact (List.map_congr_left fun f _ => if_pos hc).symm
      · rw [if_neg hc, List.map_map, List.length_map]
        exact List.map_congr_left fun f _ => (if_neg hc).symm
    rw [e]
    refine sideBySide_realizes how k bs _ fun f hf => ?_
    by_cases hc : how = .choice
    · rw [if_pos hc]; exact ⟨layAll_realizes hw bs f hf, lay_good hw f⟩
    · rw [if_neg hc]; exact ⟨(layAll_realizes hw bs f hf).reshare _, good_reshare (lay_good hw f) _⟩
  | .region name k body => (lay_realizes hw body).moved (d := MARGIN) rfl rfl
  | .loop _ body => ⟨(lay_realizes hw body).shows, (lay_realizes hw body).keeps⟩
/-- Every flow of a list realizes its order. -/
theorem layAll_realizes {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) :
    ∀ fs : List Flow, ∀ f ∈ fs, Realizes f.order (layWith width f)
  | [], _, h => absurd h List.not_mem_nil
  | f :: fs, g, h => by
    rcases List.mem_cons.mp h with hg | h
    · rw [hg]; exact lay_realizes hw f
    · exact layAll_realizes hw fs g h
end

/-- **What a flow orders, its layout draws above** (slice D1 with D3): when a flow's order puts one
node before another, the layout places the first's bottom at or above the second's top. "Above
means before", for every flow and every node width no less than zero. A tool's named law; its
consumer is the reading of the program graph. -/
theorem place_keeps_order {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) (f : Flow) {u v : Key}
    (h : (denote f.order).edge u v) :
    ∃ (i j : Nat) (p q : Placed), (placeWith width f).placed[i]? = some p ∧ p.key = u ∧ p.node.isSome ∧
      (placeWith width f).placed[j]? = some q ∧ q.key = v ∧ q.node.isSome ∧ p.y + itemH p ≤ q.y := by
  obtain ⟨i, j, p, q, hij, hp, h1, h2, hq, h3, h4, hr⟩ := (lay_realizes hw f).keeps u v h
  have hy := (heightsOf_reach (lay_good hw f) hr).2 (Nat.ne_of_lt hij)
  have hh : hAt (layWith width f).items i = itemH p := by unfold hAt; rw [hp]; rfl
  refine ⟨i, j, { p with y := heightsOf (layWith width f) i }, { q with y := heightsOf (layWith width f) j },
    by rw [place_placed, hp]; rfl, h1, h2, by rw [place_placed, hq]; rfl, h3, h4, ?_⟩
  show heightsOf (layWith width f) i + itemH p ≤ heightsOf (layWith width f) j
  rw [← hh]; exact hy

end Tools.View.Flow
