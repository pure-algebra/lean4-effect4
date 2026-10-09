import Tools.View.Flow

/-!
# The laws of a flow's layout (slice D3)

Slice D3 of `docs/research/2026-10-09-program-graph-design.md`, placed in its section 6. Each law
serves concept 7 of `docs/core/semantics.md` (`initial-algebras-folds`): the layout is a fold of
the flow (`lay`), and its invariant is proved by fold induction. Each is a tool's named law
(decisions row 336, point 8), not a registry claim.

- `lay_good`: every part the layout fold lays out is well formed (`Good`): its edges run forward
  among its items, its entry reaches every item and every item its exit, its nodes stand inside its
  width, and of two nodes, either they stand side by side or the first reaches the second.
- `assign_meets`: heights assigned along an order meet every constraint whose source comes before
  its target in that order.
- `place_descends`: in every flow's placement, each edge's target stands at or below its source's
  bottom.
- `place_apart`: in every flow's placement, any two boxes stand apart.

**The reach.** The laws hold for every flow, at every width of the nodes no less than zero
(`layWith`), at the level of item positions. The view's width (`nodeWidth`) reads the lines'
lengths, which reach `Classical.choice` through core's `String.length`; the laws, stated over the
width, rest on `propext` and `Quot.sound` alone. A route is drawn between two items' keys, so the
key-level checks (`Laid.edgesDescend`, `Laid.boxesApart`) agree with these laws when keys are
distinct, which `ofProgram`'s addresses give and no theorem states yet.

**What they do not establish.** No law says when a fiber runs: the layout's order reads the
program's structure, and the hidden edge from a detached fiber's exit makes room in the drawing.
Drawn lines may cross; a lane crosses what lies between its ends. Kahn's algorithm orders the
waits; when its check fails the layout keeps the flow's own edges and draws every wait in a lane,
so the laws hold either way, and that Kahn's algorithm orders every graph with no cycle stays a
finite fact. Points are not boxes, and the laws say nothing of their width.

**The proofs avoid three traps** that reach `Classical.choice`: `omega` closing a conjunction or a
goal that is not arithmetic (split the goal, or `absurd`), `omega` over a division (generalize
it), and the core lemmas `List.nodup_range` and `List.getElem?_mapIdx` (`nodup_range'` and
`atHeights_get` replace them).
-/

namespace Tools.View.Flow

/-! ## Reaching along edges -/

/-- Positions reached from a position along edges, in any number of steps. -/
inductive Reach (es : List Edge) : Nat → Nat → Prop
  | refl (i : Nat) : Reach es i i
  | step {k : Nat} (e : Edge) : e ∈ es → Reach es e.to k → Reach es e.fr k

theorem Reach.mono {es es' : List Edge} (h : ∀ e ∈ es, e ∈ es') {i j : Nat} (r : Reach es i j) :
    Reach es' i j := by
  induction r with
  | refl i => exact .refl i
  | step e he _ ih => exact .step e (h e he) ih

theorem Reach.trans {es : List Edge} {i j k : Nat} (r : Reach es i j) (s : Reach es j k) : Reach es i k := by
  induction r with
  | refl => exact s
  | step e he _ ih => exact .step e he (ih s)

theorem Reach.edge {es : List Edge} {e : Edge} (he : e ∈ es) : Reach es e.fr e.to := .step e he (.refl _)

theorem Reach.reindex {es : List Edge} (d : Nat) {i j : Nat} (r : Reach es i j) :
    Reach (es.map (Edge.reindex d)) (i + d) (j + d) := by
  induction r with
  | refl i => exact .refl _
  | step e he _ ih => exact .step (e.reindex d) (List.mem_map_of_mem he) ih

/-! ## Heights along an order -/

theorem relax_ge_start (h : Nat → Int) (y : Nat → Int) (v : Nat) :
    ∀ (l : List Edge) (m : Int),
      m ≤ l.foldl (fun m e => if e.to = v then max m (y e.fr + h e.fr + VGAP + e.pad) else m) m
  | [], _ => Int.le_refl _
  | e :: l, m => by
    refine Int.le_trans ?_ (relax_ge_start h y v l _)
    by_cases hv : e.to = v
    · simp only [hv, if_true]; omega
    · simp only [hv, if_false]; omega

theorem relax_ge_term (h : Nat → Int) (y : Nat → Int) (v : Nat) {e : Edge} (hv : e.to = v) :
    ∀ (l : List Edge) (m : Int), e ∈ l →
      y e.fr + h e.fr + VGAP + e.pad ≤
        l.foldl (fun m e => if e.to = v then max m (y e.fr + h e.fr + VGAP + e.pad) else m) m
  | [], _, he => absurd he List.not_mem_nil
  | d :: l, m, he => by
    rcases List.mem_cons.mp he with rfl | he
    · refine Int.le_trans ?_ (relax_ge_start h y v l _)
      simp only [hv, if_true]; omega
    · exact relax_ge_term h y v hv l _ he

theorem assign_not_mem (h : Nat → Int) (es : List Edge) (start : Int) :
    ∀ (vs : List Nat) (y : Nat → Int) (v : Nat), v ∉ vs → assign h es start vs y v = y v
  | [], _, _, _ => rfl
  | w :: ws, y, v, hv => by
    simp only [List.mem_cons, not_or] at hv
    show assign h es start ws (fun k => if k = w then relax h es y start w else y k) v = y v
    rw [assign_not_mem h es start ws _ v hv.2]
    simp only [hv.1, if_false]

theorem assign_append (h : Nat → Int) (es : List Edge) (start : Int) :
    ∀ (as bs : List Nat) (y : Nat → Int), assign h es start (as ++ bs) y = assign h es start bs (assign h es start as y)
  | [], _, _ => rfl
  | _ :: as, bs, _ => assign_append h es start as bs _

/-- **Heights along an order meet the constraints it serves**: when an edge's source stands before
its target in an order with no position twice, the heights assigned along it place the target at
least the source's height, a gap and the edge's room below the source. A tool's named law; its
consumers are `place_descends` and `place_apart`. -/
theorem assign_meets {h : Nat → Int} {es : List Edge} {start : Int} {ord : List Nat} {y : Nat → Int}
    {e : Edge} (he : e ∈ es) (nd : ord.Nodup) {i j : Nat} (hij : i < j)
    (hi : ord[i]? = some e.fr) (hj : ord[j]? = some e.to) :
    assign h es start ord y e.fr + h e.fr + VGAP + e.pad ≤ assign h es start ord y e.to := by
  have hjl : j < ord.length := (List.getElem?_eq_some_iff.mp hj).1
  have hsplit : ord = ord.take j ++ e.to :: ord.drop (j + 1) := by
    have h1 := (List.take_append_drop j ord).symm
    rw [List.drop_eq_getElem_cons hjl] at h1
    have h2 : ord[j] = e.to := (List.getElem?_eq_some_iff.mp hj).2
    rw [h2] at h1
    exact h1
  have hfr : e.fr ∈ ord.take j := by
    apply List.mem_of_getElem? (i := i)
    rw [List.getElem?_take, if_pos hij, hi]
  rw [hsplit] at nd
  have nd' := List.nodup_append.mp nd
  have hto_post : e.to ∉ ord.drop (j + 1) := (List.nodup_cons.mp nd'.2.1).1
  have hfr_ne : e.fr ≠ e.to := fun heq => nd'.2.2 _ hfr _ List.mem_cons_self heq
  have hfr_post : e.fr ∉ ord.drop (j + 1) := fun hm => nd'.2.2 _ hfr _ (List.mem_cons_of_mem _ hm) rfl
  rw [hsplit, assign_append]
  show assign h es start (ord.drop (j + 1)) _ e.fr + h e.fr + VGAP + e.pad ≤
    assign h es start (ord.drop (j + 1)) _ e.to
  rw [assign_not_mem h es start _ _ _ hfr_post, assign_not_mem h es start _ _ _ hto_post]
  simp only [hfr_ne, if_false, if_true]
  exact relax_ge_term h _ e.to rfl es start he

/-! ## A well-formed part

A part the fold lays out is well formed (`Good`): its edges run forward among its items, from an
earlier to a later one, with room no less than minus a gap; its entry reaches every item and every
item reaches its exit; its nodes stand inside its width; and of two nodes, either they stand side
by side, or the first reaches the second. Points are not nodes: the laws say nothing of their
width. -/

/-- Two places side by side: one ends, across, before the other starts. -/
def XApart (p q : Placed) : Prop := p.x + p.w ≤ q.x ∨ q.x + q.w ≤ p.x

/-- Every node among the places stands across between `lo` and `hi`. -/
def Within (items : List Placed) (lo hi : Int) : Prop :=
  ∀ p ∈ items, p.node.isSome → lo ≤ p.x ∧ p.x + p.w ≤ hi

/-- Of two nodes, either they stand side by side, or the first reaches the second. -/
def Sep (items : List Placed) (es : List Edge) : Prop :=
  ∀ i j p q, i < j → items[i]? = some p → items[j]? = some q → p.node.isSome → q.node.isSome →
    XApart p q ∨ Reach es i j

/-- **A well-formed part.** -/
structure Good (b : Box) : Prop where
  fwd : ∀ e ∈ b.edges, e.fr < e.to ∧ e.to < b.items.length
  pad : ∀ e ∈ b.edges, -VGAP ≤ e.pad
  src : b.items ≠ [] → b.src < b.items.length
  snk : b.items ≠ [] → b.snk < b.items.length
  fromSrc : ∀ i, i < b.items.length → Reach b.edges b.src i
  toSnk : ∀ i, i < b.items.length → Reach b.edges i b.snk
  inside : Within b.items 0 b.w
  width : 0 ≤ b.w
  topPad : 0 ≤ b.topPad
  botPad : 0 ≤ b.botPad
  sep : Sep b.items b.edges

theorem VGAP_pos : 0 < VGAP := by decide

theorem pointWidth_nonneg : (0 : Int) ≤ CELL * GAP := by decide

/-- A place moved across. -/
def moveX (d : Int) (p : Placed) : Placed := { p with x := p.x + d }

theorem Within.moveX {items : List Placed} {lo hi : Int} (h : Within items lo hi) (d : Int) :
    Within (items.map (moveX d)) (lo + d) (hi + d) := by
  intro p hp hn
  obtain ⟨p0, hp0, rfl⟩ := List.mem_map.mp hp
  obtain ⟨h1, h2⟩ := h p0 hp0 hn
  exact ⟨Int.add_le_add_right h1 d, by show p0.x + d + p0.w ≤ hi + d; omega⟩

theorem Within.mono {items : List Placed} {lo hi lo' hi' : Int} (h : Within items lo hi) (hl : lo' ≤ lo)
    (hh : hi ≤ hi') : Within items lo' hi' := by
  intro p hp hn
  obtain ⟨h1, h2⟩ := h p hp hn
  exact ⟨by omega, by omega⟩

theorem Sep.moveX {items : List Placed} {es : List Edge} (h : Sep items es) (d : Int) :
    Sep (items.map (moveX d)) es := by
  intro i j p q hij hp hq hpn hqn
  rw [List.getElem?_map] at hp hq
  obtain ⟨p0, hp0, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  rcases h i j p0 q0 hij hp0 hq0 hpn hqn with hx | hr
  · left
    unfold XApart at hx ⊢
    simp only [Tools.View.Flow.moveX]
    omega
  · exact .inr hr

theorem Sep.mono {items : List Placed} {es es' : List Edge} (h : Sep items es) (hs : ∀ e ∈ es, e ∈ es') :
    Sep items es' := by
  intro i j p q hij hp hq hpn hqn
  rcases h i j p q hij hp hq hpn hqn with hx | hr
  · exact .inl hx
  · exact .inr (hr.mono hs)

/-- **A part moved across and widened is well formed**, when its items move by `d ≥ 0` and still
fit the new width. A step of `lay_good` (centring in a series, a region's margin). -/
theorem good_moved {b b' : Box} (hb : Good b) {d : Int} (hd : 0 ≤ d) (hw : d + b.w ≤ b'.w)
    (hitems : b'.items = b.items.map (moveX d)) (hedges : b'.edges = b.edges) (hsrc : b'.src = b.src)
    (hsnk : b'.snk = b.snk) (htop : 0 ≤ b'.topPad) (hbot : 0 ≤ b'.botPad) : Good b' := by
  have hlen : b'.items.length = b.items.length := by rw [hitems, List.length_map]
  have hne : b'.items ≠ [] → b.items ≠ [] := fun h h' => h (by rw [hitems, h', List.map_nil])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htop, hbot, ?_⟩
  · intro e he; rw [hlen]; exact hb.fwd e (hedges ▸ he)
  · intro e he; exact hb.pad e (hedges ▸ he)
  · intro h; rw [hlen, hsrc]; exact hb.src (hne h)
  · intro h; rw [hlen, hsnk]; exact hb.snk (hne h)
  · intro i hi; rw [hedges, hsrc]; exact hb.fromSrc i (hlen ▸ hi)
  · intro i hi; rw [hedges, hsnk]; exact hb.toSnk i (hlen ▸ hi)
  · rw [hitems]
    refine (hb.inside.moveX d).mono ?_ ?_ <;> omega
  · have := hb.width; omega
  · rw [hitems, hedges]; exact hb.sep.moveX d

theorem map_moveX_shift (b : Box) (d : Int) : (b.shift d).items = b.items.map (moveX d) := rfl

theorem good_point (k : Key) : Good (point k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, pointWidth_nonneg, Int.le_refl _, Int.le_refl _, ?_⟩
  · intro e he; exact absurd he List.not_mem_nil
  · intro e he; exact absurd he List.not_mem_nil
  · intro _; exact Nat.zero_lt_one
  · intro _; exact Nat.zero_lt_one
  · intro i hi
    have : i = 0 := by simp only [point, List.length_singleton] at hi; omega
    subst this; exact .refl _
  · intro i hi
    have : i = 0 := by simp only [point, List.length_singleton] at hi; omega
    subst this; exact .refl _
  · intro p hp hn
    simp only [point, List.mem_singleton] at hp
    subst hp; simp only [pointAt, Option.isSome_none, Bool.false_eq_true] at hn
  · intro i j p q hij _ hq _ _
    have : j < 1 := (List.getElem?_eq_some_iff.mp hq).1
    exact absurd this (by omega)

theorem good_nodeBox {width : GNode → Int} (hw0 : ∀ n, 0 ≤ width n) (k l1 l2 : String) (waits : List Key) :
    Good (nodeBox width k l1 l2 waits) := by
  have hw := hw0 { key := k, line1 := l1, line2 := l2 }
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hw, Int.le_refl _, Int.le_refl _, ?_⟩
  · intro e he; exact absurd he List.not_mem_nil
  · intro e he; exact absurd he List.not_mem_nil
  · intro _; exact Nat.zero_lt_one
  · intro _; exact Nat.zero_lt_one
  · intro i hi
    have : i = 0 := by simp only [nodeBox, List.length_singleton] at hi; omega
    subst this; exact .refl _
  · intro i hi
    have : i = 0 := by simp only [nodeBox, List.length_singleton] at hi; omega
    subst this; exact .refl _
  · intro p hp _
    simp only [nodeBox, List.mem_singleton] at hp
    subst hp
    exact ⟨Int.le_refl _, by simp only [nodeBox]; omega⟩
  · intro i j p q hij _ hq _ _
    have : j < 1 := (List.getElem?_eq_some_iff.mp hq).1
    exact absurd this (by omega)

theorem good_looped {b : Box} (hb : Good b) : Good (looped b) :=
  ⟨hb.fwd, hb.pad, hb.src, hb.snk, hb.fromSrc, hb.toSnk, hb.inside, hb.width, hb.topPad, hb.botPad, hb.sep⟩

theorem MARGIN_nonneg : (0 : Int) ≤ MARGIN := by decide

theorem LABEL_nonneg : (0 : Int) ≤ LABEL := by decide

theorem good_framed (name k : String) {b : Box} (hb : Good b) : Good (framed name k b) := by
  have hm := MARGIN_nonneg
  have hl := LABEL_nonneg
  have ht := hb.topPad
  have hbt := hb.botPad
  refine good_moved hb hm ?_ rfl rfl rfl rfl ?_ ?_
  · show MARGIN + b.w ≤ b.w + 2 * MARGIN; omega
  · show 0 ≤ b.topPad + MARGIN + LABEL; omega
  · show 0 ≤ b.botPad + MARGIN; omega

/-! ## Series -/

/-- The edge that joins `s`'s exit to `m`'s entry in `s.series m`. -/
def joinEdge (s m : Box) : Edge :=
  { fr := s.snk, to := m.src + s.items.length, pad := s.botPad + m.topPad, drawn := s.ends }

theorem series_edges (s m : Box) :
    (s.series m).edges = s.edges ++ m.edges.map (Edge.reindex s.items.length) ++ [joinEdge s m] := rfl

theorem Reach.unshift {es : List Edge} {d i j : Nat} (hi : d ≤ i) (hj : d ≤ j)
    (r : Reach (es.map (Edge.reindex d)) (i - d + d) (j - d + d)) : Reach (es.map (Edge.reindex d)) i j := by
  rw [Nat.sub_add_cancel hi, Nat.sub_add_cancel hj] at r
  exact r

/-- **Series keeps a part well formed.** A step of `lay_good`, through `stackIn`. -/
theorem good_series {s m : Box} (hs : Good s) (hm : Good m) (hw : s.w = m.w) (hsn : s.items ≠ [])
    (hmn : m.items ≠ []) : Good (s.series m) := by
  have sS := hs.src hsn
  have sK := hs.snk hsn
  have mS := hm.src hmn
  have mK := hm.snk hmn
  have hitems : (s.series m).items = s.items ++ m.items := rfl
  have hlen : (s.series m).items.length = s.items.length + m.items.length := by
    rw [hitems, List.length_append]
  have subL : ∀ e ∈ s.edges, e ∈ (s.series m).edges := fun e he => by
    rw [series_edges]; exact List.mem_append_left _ (List.mem_append_left _ he)
  have subR : ∀ e ∈ m.edges.map (Edge.reindex s.items.length), e ∈ (s.series m).edges := fun e he => by
    rw [series_edges]; exact List.mem_append_left _ (List.mem_append_right _ he)
  have join : joinEdge s m ∈ (s.series m).edges := by
    rw [series_edges]; exact List.mem_append_right _ (List.mem_singleton_self _)
  have toJoin : ∀ i, i < s.items.length → Reach (s.series m).edges i (m.src + s.items.length) :=
    fun i hi => ((hs.toSnk i hi).mono subL).trans (Reach.edge join)
  have fromJoin : ∀ j, s.items.length ≤ j → j < s.items.length + m.items.length →
      Reach (s.series m).edges (m.src + s.items.length) j := fun j h1 h2 =>
    (Reach.unshift (Nat.le_add_left _ _) h1
      (by rw [Nat.add_sub_cancel]; exact (hm.fromSrc (j - s.items.length) (by omega)).reindex _)).mono subR
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hs.width, hs.topPad, hm.botPad, ?_⟩
  · intro e he
    rw [hlen]
    rw [series_edges, List.mem_append, List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | rfl
    · have := hs.fwd e he; exact ⟨by omega, by omega⟩
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      have := hm.fwd e0 he0
      simp only [Edge.reindex]; exact ⟨by omega, by omega⟩
    · simp only [joinEdge]; exact ⟨by omega, by omega⟩
  · intro e he
    rw [series_edges, List.mem_append, List.mem_append, List.mem_singleton] at he
    rcases he with (he | he) | rfl
    · exact hs.pad e he
    · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
      exact hm.pad e0 he0
    · have := hs.botPad; have := hm.topPad; have := VGAP_pos
      simp only [joinEdge]; omega
  · intro _; rw [hlen]; show s.src < _; omega
  · intro _; rw [hlen]; show m.snk + s.items.length < _; omega
  · intro i hi
    rw [hlen] at hi
    show Reach _ s.src i
    by_cases h : i < s.items.length
    · exact (hs.fromSrc i h).mono subL
    · exact (toJoin s.snk sK).trans (fromJoin i (by omega) hi) |> fun r =>
        ((hs.fromSrc s.snk sK).mono subL).trans r
  · intro i hi
    rw [hlen] at hi
    show Reach _ i (m.snk + s.items.length)
    by_cases h : i < s.items.length
    · exact (toJoin i h).trans (fromJoin _ (by omega) (by omega))
    · exact (Reach.unshift (by omega) (Nat.le_add_left _ _)
        (by rw [Nat.add_sub_cancel]; exact (hm.toSnk (i - s.items.length) (by omega)).reindex _)).mono subR
  · intro p hp hn
    rw [hitems, List.mem_append] at hp
    rcases hp with hp | hp
    · exact hs.inside p hp hn
    · show 0 ≤ p.x ∧ p.x + p.w ≤ s.w
      rw [hw]; exact hm.inside p hp hn
  · intro i j p q hij hp hq hpn hqn
    rw [hitems] at hp hq
    have hjl : j < s.items.length + m.items.length := by
      have := (List.getElem?_eq_some_iff.mp hq).1; rw [List.length_append] at this; exact this
    by_cases hj : j < s.items.length
    · rw [List.getElem?_append_left (by omega)] at hp
      rw [List.getElem?_append_left hj] at hq
      exact (hs.sep i j p q hij hp hq hpn hqn).imp id (fun r => r.mono subL)
    · rw [List.getElem?_append_right (by omega)] at hq
      by_cases hi : i < s.items.length
      · exact .inr ((toJoin i hi).trans (fromJoin j (by omega) hjl))
      · rw [List.getElem?_append_right (by omega)] at hp
        refine (hm.sep _ _ p q (by omega) hp hq hpn hqn).imp id (fun r => ?_)
        exact (Reach.unshift (by omega) (by omega) (r.reindex _)).mono subR

/-! ## Stacks -/

theorem centre_bounds {W w : Int} (h : w ≤ W) : 0 ≤ (W - w) / 2 ∧ (W - w) / 2 + w ≤ W := by
  have h0 : 0 ≤ W - w := by omega
  have h1 := Int.ediv_nonneg h0 (show (0 : Int) ≤ 2 by decide)
  have h2 := Int.ediv_le_self 2 h0
  generalize (W - w) / 2 = d at h1 h2 ⊢
  exact ⟨h1, by omega⟩

/-- A part centred in the width `W`, where it fits. -/
theorem good_centred {m : Box} (hm : Good m) {W : Int} (h : m.w ≤ W) :
    Good { m.shift ((W - m.w) / 2) with w := W } :=
  good_moved hm (centre_bounds h).1 (centre_bounds h).2 rfl rfl rfl rfl hm.topPad hm.botPad

theorem good_stackIn (W : Int) : ∀ (ms : List Box) (s : Box), Good s → s.items ≠ [] → s.w = W →
    (∀ m ∈ ms, Good m ∧ m.items ≠ [] ∧ m.w ≤ W) →
    Good (stackIn W s ms) ∧ (stackIn W s ms).items ≠ [] ∧ (stackIn W s ms).w = W
  | [], _, hs, hn, hw, _ => ⟨hs, hn, hw⟩
  | m :: ms, s, hs, hn, hw, hms => by
    obtain ⟨hm, hmn, hmw⟩ := hms m List.mem_cons_self
    have hg : Good (s.series { m.shift ((W - m.w) / 2) with w := W }) :=
      good_series hs (good_centred hm hmw) hw hn (by
        show (m.shift _).items ≠ []
        rw [map_moveX_shift]; intro h; exact hmn (List.map_eq_nil_iff.mp h))
    have hne : (s.series (m.shift ((W - m.w) / 2))).items ≠ [] := by
      show s.items ++ _ ≠ []
      intro h; exact hn (List.append_eq_nil_iff.mp h).1
    exact good_stackIn W ms (s.series (m.shift ((W - m.w) / 2))) hg hne hw
      (fun m' hm' => hms m' (List.mem_cons_of_mem _ hm'))

theorem foldl_max_ge : ∀ (bs : List Box) (m0 : Int),
    m0 ≤ bs.foldl (fun m b => max m b.w) m0 ∧ ∀ b ∈ bs, b.w ≤ bs.foldl (fun m b => max m b.w) m0
  | [], _ => ⟨Int.le_refl _, fun _ h => absurd h List.not_mem_nil⟩
  | b :: bs, m0 => by
    have ih := foldl_max_ge bs (max m0 b.w)
    refine ⟨Int.le_trans (Int.le_max_left _ _) ih.1, fun b' hb' => ?_⟩
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact Int.le_trans (Int.le_max_right _ _) ih.1
    · exact ih.2 b' hb'

/-- **Series of well-formed parts is well formed.** A step of `lay_good`. -/
theorem good_stack : ∀ bs : List Box, (∀ b ∈ bs, Good b ∧ b.items ≠ []) → Good (stack bs)
  | [], _ => by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Int.le_refl _, Int.le_refl _, Int.le_refl _, ?_⟩
    · intro e he; exact absurd he List.not_mem_nil
    · intro e he; exact absurd he List.not_mem_nil
    · intro h; exact absurd rfl h
    · intro h; exact absurd rfl h
    · intro i hi; exact absurd hi (Nat.not_lt_zero _)
    · intro i hi; exact absurd hi (Nat.not_lt_zero _)
    · intro p hp; exact absurd hp List.not_mem_nil
    · intro i j p q _ hp; exact absurd hp (by simp only [stack, List.getElem?_nil, reduceCtorEq, not_false_eq_true])
  | first :: rest, h => by
    have hW := foldl_max_ge (first :: rest) 0
    have hf := h first List.mem_cons_self
    show Good (stackIn _ _ rest)
    refine (good_stackIn _ rest _ (good_centred hf.1 (hW.2 first List.mem_cons_self)) ?_ rfl
      (fun m hm => ⟨(h m (List.mem_cons_of_mem _ hm)).1, (h m (List.mem_cons_of_mem _ hm)).2,
        hW.2 m (List.mem_cons_of_mem _ hm)⟩)).1
    show (first.shift _).items ≠ []
    rw [map_moveX_shift]; intro h'; exact hf.2 (List.map_eq_nil_iff.mp h')

/-! ## Parts side by side -/

theorem append_items (s m : Box) : (s.append m).items = s.items ++ m.items := rfl

theorem append_edges (s m : Box) : (s.append m).edges = s.edges ++ m.edges.map (Edge.reindex s.items.length) := rfl

/-- **Two parts after one another keep their nodes apart** when every node of the first ends,
across, before every node of the second starts. -/
theorem sep_append {s m : Box} (hs : Sep s.items s.edges) (hm : Sep m.items m.edges)
    (hx : ∀ p ∈ s.items, ∀ q ∈ m.items, p.node.isSome → q.node.isSome → p.x + p.w ≤ q.x) :
    Sep (s.append m).items (s.append m).edges := by
  intro i j p q hij hp hq hpn hqn
  rw [append_items] at hp hq
  have subL : ∀ e ∈ s.edges, e ∈ (s.append m).edges := fun e he => by
    rw [append_edges]; exact List.mem_append_left _ he
  have subR : ∀ e ∈ m.edges.map (Edge.reindex s.items.length), e ∈ (s.append m).edges := fun e he => by
    rw [append_edges]; exact List.mem_append_right _ he
  by_cases hj : j < s.items.length
  · rw [List.getElem?_append_left (by omega)] at hp
    rw [List.getElem?_append_left hj] at hq
    exact (hs i j p q hij hp hq hpn hqn).imp id (fun r => r.mono subL)
  · rw [List.getElem?_append_right (by omega)] at hq
    by_cases hi : i < s.items.length
    · rw [List.getElem?_append_left hi] at hp
      exact .inl (.inl (hx p (List.mem_of_getElem? hp) q (List.mem_of_getElem? hq) hpn hqn))
    · rw [List.getElem?_append_right (by omega)] at hp
      refine (hm _ _ p q (by omega) hp hq hpn hqn).imp id (fun r => ?_)
      exact (Reach.unshift (by omega) (by omega) (r.reindex _)).mono subR

/-- A list of places with no node: every place a point. -/
def NoNode (items : List Placed) : Prop := ∀ p ∈ items, p.node.isSome → False

theorem noNode_pointAt (k : Key) (x : Int) : NoNode [pointAt k x] := by
  intro p hp hn
  rw [List.mem_singleton] at hp
  subst hp
  simp only [pointAt, Option.isSome_none, Bool.false_eq_true] at hn

/-- Appending places with no node keeps a part's separation. -/
theorem sep_append_points {items extra : List Placed} {es es' : List Edge} (h : Sep items es)
    (hx : NoNode extra) (hs : ∀ e ∈ es, e ∈ es') : Sep (items ++ extra) es' := by
  intro i j p q hij hp hq hpn hqn
  by_cases hj : j < items.length
  · rw [List.getElem?_append_left (by omega)] at hp
    rw [List.getElem?_append_left hj] at hq
    exact (h i j p q hij hp hq hpn hqn).imp id (fun r => r.mono hs)
  · rw [List.getElem?_append_right (by omega)] at hq
    exact (hx q (List.mem_of_getElem? hq) hqn).elim

theorem within_append_points {items extra : List Placed} {lo hi : Int} (h : Within items lo hi)
    (hx : NoNode extra) : Within (items ++ extra) lo hi := by
  intro p hp hn
  rcases List.mem_append.mp hp with hp | hp
  · exact h p hp hn
  · exact (hx p hp hn).elim

/-- The width of branches side by side is no less than zero. -/
theorem span_nonneg : ∀ (bs : List Box), (∀ b ∈ bs, 0 ≤ b.w) → 0 ≤ span bs
  | [], _ => Int.le_refl _
  | [b], h => h b List.mem_cons_self
  | b :: c :: bs, h => by
    have h1 := h b List.mem_cons_self
    have h2 := span_nonneg (c :: bs) (fun d hd => h d (List.mem_cons_of_mem _ hd))
    have h3 := pointWidth_nonneg
    show 0 ≤ b.w + CELL * GAP + span (c :: bs)
    omega

/-- **What assembling the branches gives.** The part keeps the first part's items as a prefix, and
its entry, width and room. Each branch is one of the inputs moved across, after the earlier items
(and its port), inside the part. The part's edges are the first part's and the branches', moved
on. Each later item is a port or an item of a branch. The nodes stand inside the branches' span,
and stay apart. -/
structure WBSpec (ported : Bool) (x : Int) (s : Box) (L : List (Box × Nat)) (r : Box × List (Nat × Box)) :
    Prop where
  pre : ∃ rest, r.1.items = s.items ++ rest
  src : r.1.src = s.src
  w : r.1.w = s.w
  topPad : r.1.topPad = s.topPad
  botPad : r.1.botPad = s.botPad
  len : r.2.length = L.length
  slots : ∀ sl ∈ r.2, (∃ bi ∈ L, ∃ x', sl.2 = bi.1.shift x') ∧
    s.items.length + (if ported then 1 else 0) ≤ sl.1 ∧ sl.1 + sl.2.items.length ≤ r.1.items.length
  edges : ∀ e, e ∈ r.1.edges ↔ e ∈ s.edges ∨ ∃ sl ∈ r.2, ∃ e0 ∈ sl.2.edges, e = e0.reindex sl.1
  cover : ∀ i, s.items.length ≤ i → i < r.1.items.length →
    ∃ sl ∈ r.2, (ported = true ∧ i + 1 = sl.1) ∨ (sl.1 ≤ i ∧ i < sl.1 + sl.2.items.length)
  within : Within s.items 0 x → Within r.1.items 0 (x + span (L.map (·.1)))
  sep : Within s.items 0 x → Sep s.items s.edges → Sep r.1.items r.1.edges
  inputs : ∀ bi ∈ L, ∃ sl ∈ r.2, ∃ x', sl.2 = bi.1.shift x'
  at_ : ∀ sl ∈ r.2, ∀ t, t < sl.2.items.length → r.1.items[sl.1 + t]? = sl.2.items[t]?

theorem withBranches_spec (ported : Bool) (k : Key) :
    ∀ (L : List (Box × Nat)) (x : Int) (s : Box), 0 ≤ x → (∀ bi ∈ L, Good bi.1) →
      WBSpec ported x s L (withBranches ported k x s L)
  | [], x, s, _, _ => by
    refine ⟨⟨[], (List.append_nil _).symm⟩, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, fun h hs => hs,
      fun bi h => absurd h List.not_mem_nil, fun sl h => absurd h List.not_mem_nil⟩
    · intro sl hsl; exact absurd hsl List.not_mem_nil
    · intro e; exact ⟨.inl, fun h => h.elim id (fun ⟨_, h, _⟩ => absurd h List.not_mem_nil)⟩
    · intro i h1 h2; exact absurd h2 (by show ¬ i < s.items.length; omega)
    · intro h; show Within s.items 0 (x + 0); rw [Int.add_zero]; exact h
  | (b, i) :: L, x, s, hx, hL => by
    have hb : Good b := hL (b, i) List.mem_cons_self
    let port : Box := { w := 0, items := [pointAt (k ++ "/fork/" ++ toString i) ((b.shift x).middleAt (b.shift x).src - CELL)] }
    let s1 : Box := if ported then s.append port else s
    have s1items : s1.items = s.items ++ (if ported then port.items else []) := by
      cases ported
      · exact (List.append_nil _).symm
      · rfl
    have s1len : s1.items.length = s.items.length + (if ported then 1 else 0) := by
      rw [s1items, List.length_append]; cases ported <;> rfl
    have s1edges : s1.edges = s.edges := by
      cases ported
      · rfl
      · show s.edges ++ [] = s.edges; exact List.append_nil _
    have s1src : s1.src = s.src := by cases ported <;> rfl
    have s1w : s1.w = s.w := by cases ported <;> rfl
    have s1top : s1.topPad = s.topPad := by cases ported <;> rfl
    have s1bot : s1.botPad = s.botPad := by cases ported <;> rfl
    have s1nn : NoNode (if ported then port.items else []) := by
      cases ported
      · intro p hp; exact absurd hp List.not_mem_nil
      · exact noNode_pointAt _ _
    let s2 := s1.append (b.shift x)
    have hw0 := hb.width
    have G0 := pointWidth_nonneg
    have ih := withBranches_spec ported k L (x + (b.shift x).w + CELL * GAP) s2 (by show 0 ≤ x + b.w + CELL * GAP; omega)
      (fun bi h => hL bi (List.mem_cons_of_mem _ h))
    have hr : withBranches ported k x s ((b, i) :: L) =
        ((withBranches ported k (x + (b.shift x).w + CELL * GAP) s2 L).1,
         (s1.items.length, b.shift x) :: (withBranches ported k (x + (b.shift x).w + CELL * GAP) s2 L).2) := rfl
    rw [hr]
    obtain ⟨rest, hrest⟩ := ih.pre
    have s2items : s2.items = s1.items ++ (b.shift x).items := rfl
    have rlen : s1.items.length + b.items.length ≤
        (withBranches ported k (x + (b.shift x).w + CELL * GAP) s2 L).1.items.length := by
      rw [hrest, List.length_append, s2items, List.length_append, map_moveX_shift, List.length_map]; omega
    -- the nodes of `s2` stand inside `0 … x + b.w`, and stay apart
    have within2 : Within s.items 0 x → Within s2.items 0 (x + b.w) := by
      intro h p hp hn
      rw [s2items, s1items, List.mem_append, List.mem_append] at hp
      rcases hp with (hp | hp) | hp
      · have := h p hp hn; exact ⟨by omega, by omega⟩
      · exact (s1nn p hp hn).elim
      · rw [map_moveX_shift] at hp
        have := (hb.inside.moveX x) p hp hn
        exact ⟨by omega, by omega⟩
    refine ⟨⟨(if ported then port.items else []) ++ (b.shift x).items ++ rest, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [hrest, s2items, s1items]; simp only [List.append_assoc]
    · show _ = s.src; rw [ih.src]; show s1.src = _; exact s1src
    · show _ = s.w; rw [ih.w]; show s1.w = _; exact s1w
    · show _ = s.topPad; rw [ih.topPad]; show s1.topPad = _; exact s1top
    · show _ = s.botPad; rw [ih.botPad]; show s1.botPad = _; exact s1bot
    · show _ + 1 = L.length + 1; rw [ih.len]
    · intro sl hsl
      rcases List.mem_cons.mp hsl with rfl | hsl
      · refine ⟨⟨(b, i), List.mem_cons_self, x, rfl⟩, by rw [s1len]; exact Nat.le_refl _, ?_⟩
        show s1.items.length + (b.shift x).items.length ≤ _
        rw [map_moveX_shift, List.length_map]; exact rlen
      · obtain ⟨⟨bi, hbi, x', hx'⟩, h1, h2⟩ := ih.slots sl hsl
        refine ⟨⟨bi, List.mem_cons_of_mem _ hbi, x', hx'⟩, ?_, h2⟩
        have : s2.items.length = s1.items.length + b.items.length := by
          rw [s2items, List.length_append, map_moveX_shift, List.length_map]
        rw [this, s1len] at h1; omega
    · intro e
      rw [ih.edges e]
      show (e ∈ s1.edges ++ (b.shift x).edges.map (Edge.reindex s1.items.length) ∨ _) ↔ _
      rw [s1edges, List.mem_append]
      constructor
      · rintro ((h | h) | ⟨sl, hsl, e0, he0, rfl⟩)
        · exact .inl h
        · obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp h
          exact .inr ⟨_, List.mem_cons_self, e0, he0, rfl⟩
        · exact .inr ⟨sl, List.mem_cons_of_mem _ hsl, e0, he0, rfl⟩
      · rintro (h | ⟨sl, hsl, e0, he0, rfl⟩)
        · exact .inl (.inl h)
        · rcases List.mem_cons.mp hsl with rfl | hsl
          · exact .inl (.inr (List.mem_map_of_mem he0))
          · exact .inr ⟨sl, hsl, e0, he0, rfl⟩
    · intro j h1 h2
      by_cases hj1 : j < s1.items.length
      · have hs1 := s1len
        by_cases hp : ported = true
        · rw [if_pos hp] at hs1
          exact ⟨_, List.mem_cons_self, .inl ⟨hp, by show j + 1 = s1.items.length; omega⟩⟩
        · rw [if_neg hp] at hs1
          omega
      · by_cases hj2 : j < s1.items.length + b.items.length
        · exact ⟨_, List.mem_cons_self, .inr ⟨by omega, by
            show j < s1.items.length + (b.shift x).items.length
            rw [map_moveX_shift, List.length_map]; exact hj2⟩⟩
        · have : s2.items.length ≤ j := by
            rw [s2items, List.length_append, map_moveX_shift, List.length_map]; omega
          obtain ⟨sl, hsl, h⟩ := ih.cover j this h2
          exact ⟨sl, List.mem_cons_of_mem _ hsl, h⟩
    · intro h
      have h2 := within2 h
      cases L with
      | nil =>
        show Within s2.items 0 (x + b.w)
        exact h2
      | cons l L =>
        have := ih.within (h2.mono (Int.le_refl _) (by show x + b.w ≤ x + b.w + CELL * GAP; omega))
        refine this.mono (Int.le_refl _) ?_
        show x + b.w + CELL * GAP + span ((l :: L).map (·.1)) ≤ x + span (b :: (l :: L).map (·.1))
        show _ ≤ x + (b.w + CELL * GAP + span ((l :: L).map (·.1)))
        omega
    · intro h hs
      refine ih.sep ((within2 h).mono (Int.le_refl _) (by show x + b.w ≤ x + b.w + CELL * GAP; omega)) ?_
      have sep1 : Sep s1.items s1.edges := by
        rw [s1items, s1edges]; exact sep_append_points hs s1nn (fun e he => he)
      refine sep_append sep1 (by rw [map_moveX_shift]; exact hb.sep.moveX x) ?_
      intro p hp q hq hpn hqn
      rw [s1items, List.mem_append] at hp
      rcases hp with hp | hp
      · have h1 := h p hp hpn
        rw [map_moveX_shift] at hq
        have h3 := (hb.inside.moveX x) q hq hqn
        omega
      · exact (s1nn p hp hpn).elim
    · intro bi hbi
      rcases List.mem_cons.mp hbi with rfl | hbi
      · exact ⟨_, List.mem_cons_self, x, rfl⟩
      · obtain ⟨sl, hsl, x', hx'⟩ := ih.inputs bi hbi
        exact ⟨sl, List.mem_cons_of_mem _ hsl, x', hx'⟩
    · intro sl hsl t ht
      rcases List.mem_cons.mp hsl with rfl | hsl
      · show (withBranches ported k _ s2 L).1.items[s1.items.length + t]? = (b.shift x).items[t]?
        rw [hrest, s2items, List.append_assoc, List.getElem?_append_right (Nat.le_add_right _ _),
          Nat.add_sub_cancel_left, List.getElem?_append_left ht]
      · exact ih.at_ sl hsl t ht

/-! ## The top and the bottom of a parallel part -/

/-- An edge from `a` to `b`. -/
def Link (es : List Edge) (a b : Nat) : Prop := ∃ e ∈ es, e.fr = a ∧ e.to = b

theorem Link.reach {es : List Edge} {a b : Nat} (h : Link es a b) : Reach es a b := by
  obtain ⟨e, he, rfl, rfl⟩ := h
  exact Reach.edge he

theorem Link.mono {es es' : List Edge} {a b : Nat} (h : Link es a b) (hs : ∀ e ∈ es, e ∈ es') : Link es' a b := by
  obtain ⟨e, he, h1, h2⟩ := h
  exact ⟨e, hs e he, h1, h2⟩

/-- A branch's place in a parallel part of `J` items: after the fork's point and its port, inside
the part, with its entry and exit among its items and its room no less than zero. -/
def SlotOk (ported : Bool) (J : Nat) (sl : Nat × Box) : Prop :=
  1 + (if ported then 1 else 0) ≤ sl.1 ∧ sl.1 + sl.2.items.length ≤ J ∧
  sl.2.src < sl.2.items.length ∧ sl.2.snk < sl.2.items.length ∧ 0 ≤ sl.2.topPad ∧ 0 ≤ sl.2.botPad

theorem mem_zipIdx_of_mem {α : Type} {l : List α} {a : α} (h : a ∈ l) : ∃ t, (a, t) ∈ l.zipIdx := by
  obtain ⟨t, ht⟩ := List.mem_iff_getElem?.mp h
  exact ⟨t, List.mem_zipIdx_iff_getElem?.mpr ht⟩

theorem parTop_fine {how : Branching} {k : Key} {slots : List (Nat × Box)} {J : Nat}
    (h : ∀ sl ∈ slots, SlotOk (how != .choice) J sl) :
    ∀ e ∈ (parTop how k slots).1, e.fr < e.to ∧ e.to < J ∧ -VGAP ≤ e.pad := by
  have hv := VGAP_pos
  intro e he
  unfold parTop at he
  by_cases hc : (how != .choice) = true
  · rw [if_pos hc] at he
    obtain ⟨sl, hsl, he⟩ := List.mem_flatMap.mp he
    have hs := h sl hsl
    unfold SlotOk at hs
    rw [if_pos hc] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl <;> (simp only; exact ⟨by omega, by omega, by omega⟩)
  · rw [if_neg hc] at he
    obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp he
    have hs := h sl hsl
    unfold SlotOk at hs
    rw [if_neg hc] at hs
    simp only; exact ⟨by omega, by omega, by omega⟩

theorem parTop_links_ported {how : Branching} {k : Key} {slots : List (Nat × Box)} (hc : (how != .choice) = true)
    {sl : Nat × Box} (hsl : sl ∈ slots) :
    Link (parTop how k slots).1 0 (sl.1 - 1) ∧ Link (parTop how k slots).1 (sl.1 - 1) (sl.1 + sl.2.src) := by
  unfold parTop
  rw [if_pos hc]
  exact ⟨⟨_, List.mem_flatMap.mpr ⟨sl, hsl, List.mem_cons_self⟩, rfl, rfl⟩,
         ⟨_, List.mem_flatMap.mpr ⟨sl, hsl, List.mem_cons_of_mem _ List.mem_cons_self⟩, rfl, rfl⟩⟩

theorem parTop_link_choice {how : Branching} {k : Key} {slots : List (Nat × Box)} (hc : ¬ (how != .choice) = true)
    {sl : Nat × Box} (hsl : sl ∈ slots) : Link (parTop how k slots).1 0 (sl.1 + sl.2.src) := by
  unfold parTop
  rw [if_neg hc]
  exact ⟨_, List.mem_map_of_mem hsl, rfl, rfl⟩

/-- The exit's position of a parallel part of `J` items before its bottom. -/
theorem parBottom_snk (how : Branching) (k : Key) (mid : Int) (ends : Bool) (J : Nat) (slots : List (Nat × Box)) :
    (parBottom how k mid ends J slots).1 = if how = .spawn then J else J + slots.length := by
  unfold parBottom
  by_cases hs : how = .spawn
  · rw [if_pos hs, if_pos hs]
  · rw [if_neg hs, if_neg hs]

theorem parBottom_items (how : Branching) (k : Key) (mid : Int) (ends : Bool) (J : Nat) (slots : List (Nat × Box)) :
    NoNode (parBottom how k mid ends J slots).2.1 ∧
      (parBottom how k mid ends J slots).2.1.length = if how = .spawn then 1 else slots.length + 1 := by
  unfold parBottom
  by_cases hs : how = .spawn
  · rw [if_pos hs, if_pos hs]
    exact ⟨noNode_pointAt _ _, rfl⟩
  · rw [if_neg hs, if_neg hs]
    refine ⟨?_, by simp only [List.length_append, List.length_map, List.length_zipIdx, List.length_singleton]⟩
    intro p hp hn
    rcases List.mem_append.mp hp with hp | hp
    · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
      simp only [pointAt, Option.isSome_none, Bool.false_eq_true] at hn
    · exact noNode_pointAt _ _ p hp hn

theorem parBottom_fine {how : Branching} {k : Key} {mid : Int} {ends : Bool} {J : Nat} {slots : List (Nat × Box)}
    {ported : Bool} (h : ∀ sl ∈ slots, SlotOk ported J sl) (hJ : 1 ≤ J) :
    ∀ e ∈ (parBottom how k mid ends J slots).2.2.1,
      e.fr < e.to ∧ e.to < J + (if how = .spawn then 1 else slots.length + 1) ∧ -VGAP ≤ e.pad := by
  have hv := VGAP_pos
  intro e he
  unfold parBottom at he
  by_cases hs : how = .spawn
  · rw [if_pos hs] at he
    rw [if_pos hs]
    rcases List.mem_append.mp he with he | he
    · obtain ⟨⟨sl, t⟩, hst, rfl⟩ := List.mem_map.mp he
      have := h sl (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hst))
      unfold SlotOk at this
      simp only; exact ⟨by omega, by omega, by omega⟩
    · by_cases he0 : slots.isEmpty = true
      · rw [if_pos he0, List.mem_singleton] at he
        subst he; simp only; exact ⟨by omega, by omega, by omega⟩
      · rw [if_neg he0] at he; exact absurd he List.not_mem_nil
  · rw [if_neg hs] at he
    rw [if_neg hs]
    simp only [List.mem_append] at he
    rcases he with ((he | he) | he) | he
    · obtain ⟨t, ht, he⟩ := List.mem_flatMap.mp he
      obtain ⟨sl, hsl, rfl⟩ := List.mem_map.mp he
      have := h sl hsl
      have ht' := List.mem_range.mp ht
      unfold SlotOk at this
      simp only; exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨⟨sl, t⟩, hst, rfl⟩ := List.mem_map.mp he
      have hg := List.mem_zipIdx_iff_getElem?.mp hst
      have := h sl (List.mem_of_getElem? hg)
      have ht : t < slots.length := (List.getElem?_eq_some_iff.mp hg).1
      unfold SlotOk at this
      simp only; exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨⟨sl, t⟩, hst, rfl⟩ := List.mem_map.mp he
      have hg := List.mem_zipIdx_iff_getElem?.mp hst
      have ht : t < slots.length := (List.getElem?_eq_some_iff.mp hg).1
      by_cases hch : how = .choice
      · simp only [hch, if_true]; exact ⟨by omega, by omega, by omega⟩
      · simp only [hch, if_false]; exact ⟨by omega, by omega, by omega⟩
    · by_cases he0 : slots.isEmpty = true
      · rw [if_pos he0, List.mem_singleton] at he
        subst he; simp only; exact ⟨by omega, by omega, by omega⟩
      · rw [if_neg he0] at he; exact absurd he List.not_mem_nil

theorem parBottom_links_spawn {how : Branching} {k : Key} {mid : Int} {ends : Bool} {J : Nat}
    {slots : List (Nat × Box)} (hs : how = .spawn) :
    (∀ sl ∈ slots, Link (parBottom how k mid ends J slots).2.2.1 (sl.1 + sl.2.snk) J) ∧
      (slots = [] → Link (parBottom how k mid ends J slots).2.2.1 0 J) := by
  unfold parBottom
  rw [if_pos hs]
  refine ⟨fun sl hsl => ?_, fun he => ?_⟩
  · obtain ⟨t, ht⟩ := mem_zipIdx_of_mem hsl
    exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem ht), rfl, rfl⟩
  · subst he
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

theorem parBottom_links {how : Branching} {k : Key} {mid : Int} {ends : Bool} {J : Nat}
    {slots : List (Nat × Box)} (hs : ¬ how = .spawn) :
    (∀ sl ∈ slots, ∀ t, t < slots.length → Link (parBottom how k mid ends J slots).2.2.1 (sl.1 + sl.2.snk) (J + t)) ∧
      (∀ t, t < slots.length → Link (parBottom how k mid ends J slots).2.2.1 (J + t) (J + slots.length)) ∧
      (slots = [] → Link (parBottom how k mid ends J slots).2.2.1 0 J) := by
  unfold parBottom
  rw [if_neg hs]
  refine ⟨fun sl hsl t ht => ?_, fun t ht => ?_, fun he => ?_⟩
  · exact ⟨_, List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨t, List.mem_range.mpr ht, List.mem_map_of_mem hsl⟩))), rfl, rfl⟩
  · have hm : (slots[t], t) ∈ slots.zipIdx := List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem ht)
    by_cases hch : how = .choice
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm)),
        by simp only [hch, if_true], by simp only [hch, if_true]⟩
    · exact ⟨_, List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hm)),
        by simp only [hch, if_false], by simp only [hch, if_false]⟩
  · subst he
    exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), rfl, rfl⟩

/-! ## Parallel parts -/

/-- **A parallel part around well-formed branches is well formed.** Its entry, the fork's point,
reaches every item: a port by its edge, a branch's item through the branch's entry, a port below
through a branch's exit, the join through a port, or across when there is no branch. Every item
reaches its exit the same way down. Its nodes are its branches', side by side. A step of
`lay_good`, through `good_sideBySide`. -/
theorem good_parAround {how : Branching} {k : Key} {W : Int} {ends : Bool} {s0 : Box} {L : List (Box × Nat)}
    {r : Box × List (Nat × Box)}
    (hs0 : s0.items.length = 1) (hs0e : s0.edges = []) (hs0src : s0.src = 0) (hs0w : s0.w = W)
    (hs0t : s0.topPad = 0) (hs0b : s0.botPad = 0) (hs0n : NoNode s0.items)
    (hspec : WBSpec (how != .choice) 0 s0 L r) (hL : ∀ bi ∈ L, Good bi.1 ∧ bi.1.items ≠ [])
    (hW0 : 0 ≤ W) (hWs : span (L.map (·.1)) ≤ W) :
    Good (parAround how k W ends r.1 r.2) := by
  have hv := VGAP_pos
  have hJ : 1 ≤ r.1.items.length := by
    obtain ⟨rest, h⟩ := hspec.pre; rw [h, List.length_append, hs0]; omega
  -- each branch is a well-formed part moved across
  have slotGood : ∀ sl ∈ r.2, ∃ b, Good b ∧ b.items ≠ [] ∧ ∃ x', sl.2 = b.shift x' := by
    intro sl hsl
    obtain ⟨⟨bi, hbi, x', hx'⟩, _, _⟩ := hspec.slots sl hsl
    exact ⟨bi.1, (hL bi hbi).1, (hL bi hbi).2, x', hx'⟩
  have slotOk : ∀ sl ∈ r.2, SlotOk (how != .choice) r.1.items.length sl := by
    intro sl hsl
    obtain ⟨_, h1, h2⟩ := hspec.slots sl hsl
    obtain ⟨b, hb, hbn, x', hx'⟩ := slotGood sl hsl
    rw [hs0] at h1
    refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩ <;> rw [hx']
    · show b.src < (b.items.map (moveX x')).length; rw [List.length_map]; exact hb.src hbn
    · show b.snk < (b.items.map (moveX x')).length; rw [List.length_map]; exact hb.snk hbn
    · exact hb.topPad
    · exact hb.botPad
  have bodyEdges : ∀ e ∈ r.1.edges, ∃ sl ∈ r.2, ∃ e0 ∈ sl.2.edges, e = e0.reindex sl.1 := by
    intro e he
    rcases (hspec.edges e).mp he with h | h
    · rw [hs0e] at h; exact absurd h List.not_mem_nil
    · exact h
  have bodyHas : ∀ sl ∈ r.2, ∀ e0 ∈ sl.2.edges, e0.reindex sl.1 ∈ r.1.edges :=
    fun sl hsl e0 he0 => (hspec.edges _).mpr (.inr ⟨sl, hsl, e0, he0, rfl⟩)
  -- the whole part
  have Fitems : (parAround how k W ends r.1 r.2).items =
      r.1.items ++ (parBottom how k (W / 2 - CELL) ends r.1.items.length r.2).2.1 := rfl
  have Fedges : (parAround how k W ends r.1 r.2).edges =
      (parTop how k r.2).1 ++ r.1.edges ++ (parBottom how k (W / 2 - CELL) ends r.1.items.length r.2).2.2.1 := rfl
  have Fsrc : (parAround how k W ends r.1 r.2).src = 0 := by
    show r.1.src = 0; rw [hspec.src, hs0src]
  have Fsnk : (parAround how k W ends r.1 r.2).snk = (parBottom how k (W / 2 - CELL) ends r.1.items.length r.2).1 := rfl
  have bot := parBottom_items how k (W / 2 - CELL) ends r.1.items.length r.2
  have Flen : (parAround how k W ends r.1 r.2).items.length =
      r.1.items.length + (if how = .spawn then 1 else r.2.length + 1) := by
    rw [Fitems, List.length_append, bot.2]
  have topSub : ∀ e ∈ (parTop how k r.2).1, e ∈ (parAround how k W ends r.1 r.2).edges := fun e he => by
    rw [Fedges]; exact List.mem_append_left _ (List.mem_append_left _ he)
  have bodySub : ∀ e ∈ r.1.edges, e ∈ (parAround how k W ends r.1 r.2).edges := fun e he => by
    rw [Fedges]; exact List.mem_append_left _ (List.mem_append_right _ he)
  have botSub : ∀ e ∈ (parBottom how k (W / 2 - CELL) ends r.1.items.length r.2).2.2.1,
      e ∈ (parAround how k W ends r.1 r.2).edges := fun e he => by
    rw [Fedges]; exact List.mem_append_right _ he
  -- reaching inside a branch
  have inner : ∀ sl ∈ r.2, ∀ i, i < sl.2.items.length →
      Reach (parAround how k W ends r.1 r.2).edges (sl.1 + sl.2.src) (sl.1 + i) ∧
      Reach (parAround how k W ends r.1 r.2).edges (sl.1 + i) (sl.1 + sl.2.snk) := by
    intro sl hsl i hi
    have lift : ∀ a c, Reach sl.2.edges a c → Reach (parAround how k W ends r.1 r.2).edges (sl.1 + a) (sl.1 + c) := by
      intro a c hr
      have := (hr.reindex sl.1).mono (fun e he => by
        obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
        exact bodySub _ (bodyHas sl hsl e0 he0))
      rw [Nat.add_comm a, Nat.add_comm c] at this
      exact this
    obtain ⟨b, hb, _, x', hx'⟩ := slotGood sl hsl
    have hi' : i < b.items.length := by rw [hx'] at hi; rw [map_moveX_shift, List.length_map] at hi; exact hi
    refine ⟨lift _ _ ?_, lift _ _ ?_⟩ <;> rw [hx']
    · exact hb.fromSrc i hi'
    · exact hb.toSnk i hi'
  have srcSnk : ∀ sl ∈ r.2, Reach (parAround how k W ends r.1 r.2).edges (sl.1 + sl.2.src) (sl.1 + sl.2.snk) :=
    fun sl hsl => (inner sl hsl sl.2.snk (slotOk sl hsl).2.2.2.1).1
  -- from the fork's point to a branch's entry
  have R0 : ∀ sl ∈ r.2, Reach (parAround how k W ends r.1 r.2).edges 0 (sl.1 + sl.2.src) := by
    intro sl hsl
    by_cases hc : (how != .choice) = true
    · have ⟨l1, l2⟩ := parTop_links_ported (k := k) hc hsl
      exact ((l1.mono topSub).reach).trans ((l2.mono topSub).reach)
    · exact ((parTop_link_choice (k := k) hc hsl).mono topSub).reach
  have RS : ∀ sl ∈ r.2, Reach (parAround how k W ends r.1 r.2).edges 0 (sl.1 + sl.2.snk) :=
    fun sl hsl => (R0 sl hsl).trans (srcSnk sl hsl)
  -- from a branch's exit to the part's exit
  have RT : ∀ sl ∈ r.2, Reach (parAround how k W ends r.1 r.2).edges (sl.1 + sl.2.snk)
      (parAround how k W ends r.1 r.2).snk := by
    intro sl hsl
    rw [Fsnk, parBottom_snk]
    have hn : 0 < r.2.length := List.length_pos_of_mem hsl
    by_cases hs : how = .spawn
    · rw [if_pos hs]
      exact (((parBottom_links_spawn (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) hs).1 sl hsl).mono botSub).reach
    · rw [if_neg hs]
      have ⟨l1, l2, _⟩ := parBottom_links (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) (slots := r.2) hs
      exact ((l1 sl hsl 0 hn).mono botSub).reach.trans ((l2 0 hn).mono botSub).reach
  have hsnkv := parBottom_snk how k (W / 2 - CELL) ends r.1.items.length r.2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- forward edges
  · intro e he
    rw [Flen]
    rw [Fedges, List.mem_append, List.mem_append] at he
    rcases he with (he | he) | he
    · have := parTop_fine slotOk e he; exact ⟨by omega, by omega⟩
    · obtain ⟨sl, hsl, e0, he0, rfl⟩ := bodyEdges e he
      obtain ⟨b, hb, _, x', hx'⟩ := slotGood sl hsl
      have h2 := (slotOk sl hsl).2.1
      rw [hx'] at he0 h2
      rw [map_moveX_shift, List.length_map] at h2
      have := hb.fwd e0 he0
      simp only [Edge.reindex]; exact ⟨by omega, by omega⟩
    · exact (parBottom_fine slotOk hJ e he).imp_right And.left
  -- room
  · intro e he
    rw [Fedges, List.mem_append, List.mem_append] at he
    rcases he with (he | he) | he
    · exact (parTop_fine slotOk e he).2.2
    · obtain ⟨sl, hsl, e0, he0, rfl⟩ := bodyEdges e he
      obtain ⟨b, hb, _, x', hx'⟩ := slotGood sl hsl
      rw [hx'] at he0
      exact hb.pad e0 he0
    · exact (parBottom_fine slotOk hJ e he).2.2
  -- entry and exit among the items
  · intro _; rw [Fsrc, Flen]; omega
  · intro _; rw [Flen, Fsnk, hsnkv]
    by_cases hs : how = .spawn
    · rw [if_pos hs, if_pos hs]; omega
    · rw [if_neg hs, if_neg hs]; omega
  -- the entry reaches every item
  · intro i hi
    rw [Fsrc]
    rw [Flen] at hi
    by_cases h0 : i = 0
    · subst h0; exact .refl _
    by_cases hb : i < r.1.items.length
    · obtain ⟨sl, hsl, hcase⟩ := hspec.cover i (by rw [hs0]; omega) hb
      rcases hcase with ⟨hc, hi1⟩ | ⟨h1, h2⟩
      · have l1 := (parTop_links_ported (k := k) hc hsl).1
        have : i = sl.1 - 1 := by omega
        subst this; exact (l1.mono topSub).reach
      · have := (inner sl hsl (i - sl.1) (by omega)).1
        rw [Nat.add_sub_cancel' h1] at this
        exact (R0 sl hsl).trans this
    · by_cases hs : how = .spawn
      · rw [if_pos hs] at hi
        have hiJ : i = r.1.items.length := by omega
        subst hiJ
        have ⟨l1, l2⟩ := parBottom_links_spawn (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) (slots := r.2) hs
        by_cases hsl : r.2 = []
        · exact ((l2 hsl).mono botSub).reach
        · obtain ⟨sl0, h0m⟩ := List.exists_mem_of_ne_nil _ hsl
          exact (RS sl0 h0m).trans ((l1 sl0 h0m).mono botSub).reach
      · rw [if_neg hs] at hi
        have ⟨l1, l2, l3⟩ := parBottom_links (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) (slots := r.2) hs
        obtain ⟨t, rfl⟩ : ∃ t, i = r.1.items.length + t := ⟨i - r.1.items.length, by omega⟩
        by_cases hsl : r.2 = []
        · have ht : t = 0 := by rw [hsl] at hi; simp only [List.length_nil] at hi; omega
          subst ht
          exact ((l3 hsl).mono botSub).reach
        · obtain ⟨sl0, h0m⟩ := List.exists_mem_of_ne_nil _ hsl
          have hn : 0 < r.2.length := List.length_pos_of_mem h0m
          by_cases ht : t < r.2.length
          · exact (RS sl0 h0m).trans ((l1 sl0 h0m t ht).mono botSub).reach
          · have : t = r.2.length := by omega
            subst this
            exact ((RS sl0 h0m).trans ((l1 sl0 h0m 0 hn).mono botSub).reach).trans ((l2 0 hn).mono botSub).reach
  -- every item reaches the exit
  · intro i hi
    rw [Flen] at hi
    by_cases h0 : i = 0
    · subst h0
      by_cases hsl : r.2 = []
      · rw [Fsnk, hsnkv]
        by_cases hs : how = .spawn
        · rw [if_pos hs]
          exact (((parBottom_links_spawn (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) (slots := r.2) hs).2 hsl).mono botSub).reach
        · rw [if_neg hs]
          have := (((parBottom_links (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) (slots := r.2) hs).2.2 hsl).mono botSub).reach
          rw [hsl, List.length_nil, Nat.add_zero]
          rw [hsl] at this
          exact this
      · obtain ⟨sl0, h0m⟩ := List.exists_mem_of_ne_nil _ hsl
        exact (RS sl0 h0m).trans (RT sl0 h0m)
    by_cases hb : i < r.1.items.length
    · obtain ⟨sl, hsl, hcase⟩ := hspec.cover i (by rw [hs0]; omega) hb
      rcases hcase with ⟨hc, hi1⟩ | ⟨h1, h2⟩
      · have l2 := (parTop_links_ported (k := k) hc hsl).2
        have : i = sl.1 - 1 := by omega
        subst this
        exact ((l2.mono topSub).reach.trans (srcSnk sl hsl)).trans (RT sl hsl)
      · have := (inner sl hsl (i - sl.1) (by omega)).2
        rw [Nat.add_sub_cancel' h1] at this
        exact this.trans (RT sl hsl)
    · rw [Fsnk, hsnkv]
      by_cases hs : how = .spawn
      · rw [if_pos hs] at hi ⊢
        have : i = r.1.items.length := by omega
        subst this; exact .refl _
      · rw [if_neg hs] at hi ⊢
        obtain ⟨t, rfl⟩ : ∃ t, i = r.1.items.length + t := ⟨i - r.1.items.length, by omega⟩
        by_cases ht : t < r.2.length
        · exact (((parBottom_links (k := k) (mid := W / 2 - CELL) (ends := ends) (J := r.1.items.length) (slots := r.2) hs).2.1 t ht).mono botSub).reach
        · have : t = r.2.length := by omega
          subst this; exact .refl _
  -- the nodes stand inside the width
  · rw [Fitems]
    show Within _ 0 r.1.w
    rw [hspec.w, hs0w]
    refine within_append_points ((hspec.within ?_).mono (Int.le_refl _) (by omega)) bot.1
    intro p hp hn; exact (hs0n p hp hn).elim
  · show 0 ≤ r.1.w; rw [hspec.w, hs0w]; exact hW0
  · show 0 ≤ r.1.topPad; rw [hspec.topPad, hs0t]; exact Int.le_refl _
  · show 0 ≤ r.1.botPad; rw [hspec.botPad, hs0b]; exact Int.le_refl _
  -- the nodes stay apart
  · rw [Fitems]
    refine sep_append_points (hspec.sep ?_ ?_) bot.1 bodySub
    · intro p hp hn; exact (hs0n p hp hn).elim
    · intro i j p q hij _ hq hpn hqn
      have : j < 1 := by rw [← hs0]; exact (List.getElem?_eq_some_iff.mp hq).1
      exact absurd this (by omega)

/-- **Parallel well-formed parts are well formed**: an empty branch becomes a point, the branches
are assembled side by side, and the part stands around them. A step of `lay_good`. -/
theorem good_sideBySide (how : Branching) (k : Key) (bs : List Box) (h : ∀ b ∈ bs, Good b) :
    Good (sideBySide how k bs) := by
  let bs1 := bs.zipIdx.map fun (b, i) => if b.empty then point (k ++ "/" ++ toString i) else b
  have h1 : ∀ b ∈ bs1, Good b ∧ b.items ≠ [] := by
    intro b hb
    obtain ⟨⟨b0, i⟩, hbi, rfl⟩ := List.mem_map.mp hb
    have hb0 : b0 ∈ bs := List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hbi)
    by_cases he : b0.empty = true
    · simp only [he, if_true]
      exact ⟨good_point _, List.cons_ne_nil _ _⟩
    · simp only [he, if_false, Bool.false_eq_true]
      refine ⟨h b0 hb0, fun hn => he ?_⟩
      simp only [Box.empty, hn, List.isEmpty_nil]
  let W : Int := if bs1.isEmpty then CELL * GAP else span bs1
  have hspan := span_nonneg bs1 (fun b hb => (h1 b hb).1.width)
  have hW : 0 ≤ W ∧ span bs1 ≤ W := by
    by_cases he : bs1.isEmpty = true
    · have hnil : bs1 = [] := List.isEmpty_iff.mp he
      have : W = CELL * GAP := if_pos he
      rw [this, hnil]
      exact ⟨pointWidth_nonneg, pointWidth_nonneg⟩
    · have : W = span bs1 := if_neg he
      rw [this]; exact ⟨hspan, Int.le_refl _⟩
  let L := bs1.zipIdx
  have hL : ∀ bi ∈ L, Good bi.1 ∧ bi.1.items ≠ [] := fun bi hbi =>
    h1 bi.1 (List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.mp hbi))
  have hLmap : L.map (·.1) = bs1 := List.zipIdx_map_fst 0 bs1
  let s0 : Box := { w := W, items := [pointAt (k ++ "/fork") (W / 2 - CELL)] }
  exact good_parAround (s0 := s0) (L := L) rfl rfl rfl rfl rfl rfl (noNode_pointAt _ _)
    (withBranches_spec _ k L 0 s0 (Int.le_refl 0) (fun bi hbi => (hL bi hbi).1)) hL hW.1
    (by rw [hLmap]; exact hW.2)

/-! ## Shares -/

/-- Reaching along edges survives a map of the edges that keeps their ends. -/
theorem Reach.map {es : List Edge} {F : Edge → Edge} (hF : ∀ e, (F e).fr = e.fr ∧ (F e).to = e.to) {i j : Nat}
    (r : Reach es i j) : Reach (es.map F) i j := by
  induction r with
  | refl i => exact .refl i
  | step e he _ ih =>
    have := Reach.step (F e) (List.mem_map_of_mem he) (by rw [(hF e).2]; exact ih)
    rw [(hF e).1] at this
    exact this

/-- **A part's shares split is still well formed**: the split moves no edge's ends. A step of
`lay_good`. -/
theorem good_reshare {b : Box} (hb : Good b) (f : Nat) : Good (b.reshare f) := by
  let F : Edge → Edge := fun e => { e with share := e.share * f / 1000000 }
  have hF : ∀ e, (F e).fr = e.fr ∧ (F e).to = e.to := fun _ => ⟨rfl, rfl⟩
  have hedges : (b.reshare f).edges = b.edges.map F := rfl
  refine ⟨?_, ?_, hb.src, hb.snk, ?_, ?_, hb.inside, hb.width, hb.topPad, hb.botPad, ?_⟩
  · intro e he
    rw [hedges] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact hb.fwd e0 he0
  · intro e he
    rw [hedges] at he
    obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
    exact hb.pad e0 he0
  · intro i hi; rw [hedges]; exact (hb.fromSrc i hi).map hF
  · intro i hi; rw [hedges]; exact (hb.toSnk i hi).map hF
  · intro i j p q hij hp hq hpn hqn
    rw [hedges]
    exact (hb.sep i j p q hij hp hq hpn hqn).imp id (fun r => r.map hF)

theorem good_shares {how : Branching} {bs : List Box} (h : ∀ b ∈ bs, Good b) : ∀ b ∈ shares how bs, Good b := by
  intro b hb
  unfold shares at hb
  by_cases hc : how = .choice
  · rw [if_pos hc] at hb; exact h b hb
  · rw [if_neg hc] at hb
    obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
    exact good_reshare (h b0 hb0) _

/-! ## The fold's law -/

mutual
/-- **Every part the layout fold lays out is well formed** (slice D3): its edges run forward, its
entry reaches every item and every item its exit, its nodes stand inside its width, and of two
nodes either they stand side by side or the first reaches the second. By fold induction over the
flow, at any width of the nodes no less than zero. A tool's named law; its consumers are
`place_descends` and `place_apart`. -/
theorem lay_good {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) : ∀ f : Flow, Good (layWith width f)
  | .node k l1 l2 w => good_nodeBox hw k l1 l2 w
  | .seq ps => by
    show Good (stack ((layAllWith width ps).filter (!·.empty)))
    refine good_stack _ fun b hb => ?_
    obtain ⟨hb, he⟩ := List.mem_filter.mp hb
    refine ⟨layAll_good hw ps b hb, fun hn => ?_⟩
    simp only [Box.empty, hn, List.isEmpty_nil, Bool.not_true, Bool.false_eq_true] at he
  | .par how k bs => good_sideBySide how k _ (good_shares (layAll_good hw bs))
  | .region name k body => good_framed name k (lay_good hw body)
  | .loop _ body => good_looped (lay_good hw body)
/-- Every part of a list of flows laid out is well formed. -/
theorem layAll_good {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) : ∀ fs : List Flow, ∀ b ∈ layAllWith width fs, Good b
  | [], _, h => absurd h List.not_mem_nil
  | f :: fs, b, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact lay_good hw f
    · exact layAll_good hw fs b h
end

/-! ## The placement's laws -/

theorem before_spec : ∀ (ord : List Nat) (a b : Nat), before ord a b = true →
    ∃ i j : Nat, i < j ∧ ord[i]? = some a ∧ ord[j]? = some b
  | [], _, _, h => absurd h Bool.false_ne_true
  | x :: xs, a, b, h => by
    unfold before at h
    by_cases hb : x = b
    · rw [if_pos hb] at h; exact absurd h Bool.false_ne_true
    · rw [if_neg hb] at h
      by_cases ha : x = a
      · rw [if_pos ha] at h
        obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp (of_decide_eq_true h)
        exact ⟨0, j + 1, Nat.succ_pos _, by rw [ha]; rfl, hj⟩
      · rw [if_neg ha] at h
        obtain ⟨i, j, hij, hi, hj⟩ := before_spec xs a b h
        exact ⟨i + 1, j + 1, by omega, hi, hj⟩

/-- An order and the edges it serves: no position twice, and each edge's source before its target. -/
def Serves (es : List Edge) (ord : List Nat) : Prop :=
  ord.Nodup ∧ ∀ e ∈ es, ∃ i j : Nat, i < j ∧ ord[i]? = some e.fr ∧ ord[j]? = some e.to

theorem orders_serves {ord : List Nat} {es : List Edge} (h : orders ord es = true) : Serves es ord := by
  unfold orders at h
  rw [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true] at h
  exact ⟨h.1, fun e he => before_spec ord e.fr e.to (h.2 e he)⟩

theorem acceptWaits_keeps (n : Nat) (es : List Edge) (c : List (Nat × Nat)) :
    ∀ e ∈ es, e ∈ (acceptWaits n es c).1 := by
  have key : ∀ (c : List (Nat × Nat)) (acc : List Edge × List (Nat × Nat) × List (Nat × Nat)),
      (∀ e ∈ es, e ∈ acc.1) → ∀ e ∈ es, e ∈ (c.foldl (fun (acc : List Edge × List (Nat × Nat) × List (Nat × Nat)) (x : Nat × Nat) =>
        if reaches acc.1 (n + 1) [x.2] [x.2] x.1 then (acc.1, acc.2.1, acc.2.2 ++ [(x.1, x.2)])
        else (acc.1 ++ [{ fr := x.1, to := x.2, drawn := false }], acc.2.1 ++ [(x.1, x.2)], acc.2.2)) acc).1 := by
    intro c
    induction c with
    | nil => intro acc h; exact h
    | cons x c ih =>
      intro acc h
      refine ih _ ?_
      by_cases hr : reaches acc.1 (n + 1) [x.2] [x.2] x.1 = true
      · simp only [hr, if_true]; exact h
      · simp only [hr, if_false, Bool.false_eq_true]
        exact fun e he => List.mem_append_left _ (h e he)
  exact key c (es, [], []) (fun e he => he)

/-- The positions below `n` hold no position twice. (`List.nodup_range` reaches `Classical.choice`.) -/
theorem nodup_range' : ∀ n, (List.range n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => by
    rw [List.range_succ]
    refine List.nodup_append.mpr ⟨nodup_range' n, List.pairwise_singleton _ _, fun a ha b hb heq => ?_⟩
    rw [List.mem_singleton] at hb
    have := List.mem_range.mp ha
    omega

/-- **The order the heights follow serves the flow's own edges.** Kahn's order serves the edges and
the accepted waits when its check passes; else the items' own order serves the flow's edges, which
run forward (`lay_good`). -/
theorem orderFor_serves {n : Nat} {own dag : List Edge} (hsub : ∀ e ∈ own, e ∈ dag)
    (hfwd : ∀ e ∈ own, e.fr < e.to ∧ e.to < n) :
    (∀ e ∈ own, e ∈ (orderFor n own dag).1) ∧ Serves (orderFor n own dag).1 (orderFor n own dag).2 := by
  unfold orderFor
  by_cases h : orders (kahn n dag) dag = true
  · rw [if_pos h]; exact ⟨hsub, orders_serves h⟩
  · rw [if_neg h]
    refine ⟨fun e he => he, nodup_range' n, fun e he => ⟨e.fr, e.to, (hfwd e he).1, ?_, ?_⟩⟩
    · rw [List.getElem?_range (by have := hfwd e he; omega)]
    · rw [List.getElem?_range (hfwd e he).2]

theorem itemH_nonneg (p : Placed) : 0 ≤ itemH p := by
  unfold itemH
  by_cases h : p.node.isSome = true
  · rw [if_pos h]; decide
  · rw [if_neg h]; exact Int.le_refl _

theorem hAt_nonneg (items : List Placed) (i : Nat) : 0 ≤ hAt items i := by
  unfold hAt
  cases items[i]? with
  | none => exact Int.le_refl _
  | some p => exact itemH_nonneg p

/-- Every edge of the flow stands its target below its source's bottom, by the heights. -/
theorem heightsOf_edge {b : Box} (hb : Good b) {e : Edge} (he : e ∈ b.edges) :
    heightsOf b e.fr + hAt b.items e.fr ≤ heightsOf b e.to := by
  have hs := orderFor_serves (n := b.items.length) (dag := (acceptWaits b.items.length b.edges b.waitEdges).1)
    (acceptWaits_keeps _ _ _) (fun e he => hb.fwd e he)
  obtain ⟨i, j, hij, hi, hj⟩ := hs.2.2 e (hs.1 e he)
  have := assign_meets (h := hAt b.items) (start := b.topPad) (y := fun _ => b.topPad) (hs.1 e he) hs.2.1 hij hi hj
  have hp := hb.pad e he
  unfold heightsOf
  omega

theorem heightsOf_reach {b : Box} (hb : Good b) {i j : Nat} (r : Reach b.edges i j) :
    heightsOf b i ≤ heightsOf b j ∧ (i ≠ j → heightsOf b i + hAt b.items i ≤ heightsOf b j) := by
  induction r with
  | refl => exact ⟨Int.le_refl _, fun h => absurd rfl h⟩
  | step e he _ ih =>
    have h1 := heightsOf_edge hb he
    have h2 := hAt_nonneg b.items e.fr
    exact ⟨by omega, fun _ => by omega⟩

theorem atHeights_get (y : Nat → Int) : ∀ (k : Nat) (l : List Placed) (i : Nat),
    (atHeights y k l)[i]? = (l[i]?).map fun p => { p with y := y (k + i) }
  | _, [], _ => rfl
  | k, p :: ps, 0 => by show some _ = some _; rw [Nat.add_zero]
  | k, p :: ps, i + 1 => by
    show (atHeights y (k + 1) ps)[i]? = _
    rw [atHeights_get y (k + 1) ps i, Nat.add_right_comm, Nat.add_assoc]
    rfl

theorem place_placed (width : GNode → Int) (f : Flow) (i : Nat) :
    (placeWith width f).placed[i]? = ((layWith width f).items[i]?).map fun p => { p with y := heightsOf (layWith width f) i } := by
  show (atHeights (heightsOf (layWith width f)) 0 (layWith width f).items)[i]? = _
  rw [atHeights_get, Nat.zero_add]

/-- **Every edge of a flow's layout descends** (slice D3): its target's top stands at or below its
source's bottom. For every flow, at the level of item positions; the waits accepted as edges are
met too. A tool's named law; its consumer is the drawing, where a forward edge takes no arrowhead
(row 337, point 1), and the finite check `graph-edges-descend`. -/
theorem place_descends {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) (f : Flow) {e : Edge}
    (he : e ∈ (layWith width f).edges) {p q : Placed}
    (hp : (placeWith width f).placed[e.fr]? = some p) (hq : (placeWith width f).placed[e.to]? = some q) :
    p.y + itemH p ≤ q.y := by
  rw [place_placed] at hp hq
  obtain ⟨p0, hp0, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨q0, _, rfl⟩ := Option.map_eq_some_iff.mp hq
  have := heightsOf_edge (lay_good hw f) he
  unfold hAt at this
  rw [hp0] at this
  exact this

/-- **Any two boxes of a flow's layout stand apart** (slice D3): side by side, or one above the
other. For every flow, at the level of item positions. Of two nodes, the fold puts them in
different branches, which stand side by side, or puts the first before the second along edges,
which descend. A tool's named law; its consumer is the drawing, and the finite check
`graph-boxes-apart`. -/
theorem place_apart {width : GNode → Int} (hw : ∀ n, 0 ≤ width n) (f : Flow) {i j : Nat} (hij : i ≠ j)
    {p q : Placed} (hp : (placeWith width f).placed[i]? = some p) (hq : (placeWith width f).placed[j]? = some q)
    (hpn : p.node.isSome) (hqn : q.node.isSome) :
    p.x + p.w ≤ q.x ∨ q.x + q.w ≤ p.x ∨ p.y + ROWH * BOXROWS ≤ q.y ∨ q.y + ROWH * BOXROWS ≤ p.y := by
  have hb := lay_good hw f
  rw [place_placed] at hp hq
  obtain ⟨p0, hp0, rfl⟩ := Option.map_eq_some_iff.mp hp
  obtain ⟨q0, hq0, rfl⟩ := Option.map_eq_some_iff.mp hq
  have hH : ∀ (k : Nat) (r : Placed), (layWith width f).items[k]? = some r → r.node.isSome = true →
      hAt (layWith width f).items k = ROWH * BOXROWS := by
    intro k r hk hn
    unfold hAt itemH
    rw [hk]
    simp only [Option.map_some, Option.getD_some, hn, if_true]
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · rcases hb.sep i j p0 q0 h hp0 hq0 hpn hqn with hx | r
    · unfold XApart at hx
      rcases hx with hx | hx
      · exact .inl hx
      · exact .inr (.inl hx)
    · have := (heightsOf_reach hb r).2 hij
      rw [hH i p0 hp0 hpn] at this
      exact .inr (.inr (.inl this))
  · rcases hb.sep j i q0 p0 h hq0 hp0 hqn hpn with hx | r
    · unfold XApart at hx
      rcases hx with hx | hx
      · exact .inr (.inl hx)
      · exact .inl hx
    · have := (heightsOf_reach hb r).2 (Ne.symm hij)
      rw [hH j q0 hq0 hqn] at this
      exact .inr (.inr (.inr this))

end Tools.View.Flow
