import Effect4.Laws.Program.FinalizerRun
import Effect4.Laws.Program.FinalizerSourceHistory
import ProofGraph.GoalTag

/-!
# Probe: the finalizer goal is the source ledger plus one custody balance

Concept: scope-lifetime-finalization, R11. Question: the planned goal
`FinalizerRun.once_placed_outside_census` (`src/Effect4/Laws/Program/FinalizerRun.lean`), a step of
the claim `once-placed-finalizer`. Consumer: `FinalizerRun.once_placed_pushes_once`, the claim's
witness.

Reach. Every native program, row table, compile budget and raw decision prefix
(`Guard.Reachable`), and every once-placed source path. The assembly needs no `¬ Census` premise:
it holds for every once-placed path, so the census case is an instance too.

What it shows. `FinalizerSource.source_funded_reachable` (proved) bounds the source ledger:
`spent + held ≤ issued + 1`. The ledger spends one credit per selected `onExit` push and moves the
release descendant into custody at each foreign-capture registration. It issues the descendant back
at each release-start push. So the registration bound needs one more fact: the release-start pushes
issue no more than the registrations transferred (`custody`). `custody` follows from the per-path
release balance (`release_custody`, the one planned goal of this probe) by summing over the capture
paths whose release body holds the source path (`custody_of_paths`, proved).
`outside_census_of_custody` derives the original goal from `custody`.

Does not establish. The per-path release balance beyond the direct fragment. No progress and no
finalizer start.
-/

set_option autoImplicit false

namespace Effect4.Program.RemainingWork.FinalizerAssembly

open Effect4 Effect4.Machine Effect4.Program

/-- The custody transfer that one frame event records: a foreign-capture registration hands its
selected release descendant to the scope. -/
def transferredFrame (q : List Nat) : FrameEvent EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .pushed (.onSuccess _ (.afterScopeAdd _ (.foreign capture))) =>
      FinalizerSource.releaseWeight q capture.path
  | _ => 0

/-- The custody transfer of a run event. -/
def transferred (q : List Nat) : ReleaseTrace.Event → Nat
  | .frame _ event => transferredFrame q event
  | _ => 0

/-! ## The custody balance from the per-path release balance

`ReleaseCustody.Control.Funded` (`src/Effect4/Laws/Program/ReleaseCustody/Control.lean`) bounds the
release starts at one capture path by its registrations, on the direct fragment. Its balance over
every program is the one planned goal of this probe (`release_custody`). The weighted balance that
the source ledger needs follows by summing over the paths whose release body holds `q`. -/

/-- **The per-path release balance** (planned goal of this probe). Along every raw decision prefix
of every program, the release starts at a capture path are no more than its registrations. Its
route: `ReleaseCustody.Control.Funded`, carried beyond the direct fragment (Codex's archived
`ReleaseCustody/Executable*.lean`). -/
proof_goal release_custody (p : NativeEff) (table : RowTable) (cf : Nat) (m : NativeMachine)
    (path : List Nat) : Guard.Reachable p table cf m →
      m.trace.countP (ReleaseTrace.releaseAt path) ≤ m.trace.countP (ReleaseTrace.registeredAt path)

/-- The numbers below `n`, in descending order. (`List.nodup_range` reaches `Classical.choice`.) -/
def below : Nat → List Nat
  | 0 => []
  | n + 1 => n :: below n

theorem mem_below : ∀ (n m : Nat), m ∈ below n ↔ m < n
  | 0, m => ⟨fun h => (nomatch h), fun h => absurd h (Nat.not_lt_zero m)⟩
  | n + 1, m => by
    rw [below, List.mem_cons, mem_below n m]
    constructor
    · intro h
      rcases h with same | lower
      · rw [same]
        exact Nat.lt_succ_self n
      · exact Nat.lt_succ_of_lt lower
    · intro h
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ h) with same | lower
      · exact Or.inl same
      · exact Or.inr lower

theorem nodup_below : ∀ (n : Nat), (below n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => List.nodup_cons.mpr ⟨fun h => Nat.lt_irrefl n ((mem_below n n).mp h), nodup_below n⟩

/-- The capture paths whose release body holds `q`: `q.take n` for each `n` with `q[n]? = some 1`. -/
def releasePaths (q : List Nat) : List (List Nat) :=
  ((below q.length).filter (fun n => q[n]? == some 1)).map (fun n => q.take n)

theorem nodup_filter {α : Type} (p : α → Bool) : ∀ (l : List α), l.Nodup → (l.filter p).Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    obtain ⟨notMem, rest⟩ := List.nodup_cons.mp h
    rw [List.filter_cons]
    split
    · exact List.nodup_cons.mpr ⟨fun m => notMem (List.mem_filter.mp m).1, nodup_filter p l rest⟩
    · exact nodup_filter p l rest

theorem nodup_map {α β : Type} (f : α → β) : ∀ (l : List α), l.Nodup →
    (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, h, inj => by
    obtain ⟨notMem, rest⟩ := List.nodup_cons.mp h
    rw [List.map_cons]
    refine List.nodup_cons.mpr ⟨fun m => ?_,
      nodup_map f l rest (fun x hx y hy same => inj x (.tail _ hx) y (.tail _ hy) same)⟩
    obtain ⟨b, hb, same⟩ := List.mem_map.mp m
    have equal : b = a := inj b (.tail _ hb) a (.head _) same
    rw [equal] at hb
    exact notMem hb

theorem releasePaths_nodup (q : List Nat) : (releasePaths q).Nodup := by
  apply nodup_map
  · exact nodup_filter _ _ (nodup_below q.length)
  · intro x hx y hy same
    have hx' := (mem_below _ _).mp (List.mem_filter.mp hx).1
    have hy' := (mem_below _ _).mp (List.mem_filter.mp hy).1
    have lx : (q.take x).length = x := List.length_take_of_le (Nat.le_of_lt hx')
    have ly : (q.take y).length = y := List.length_take_of_le (Nat.le_of_lt hy')
    rw [← lx, ← ly, same]

theorem mem_releasePaths (q x : List Nat) :
    x ∈ releasePaths q ↔ (x ++ [1]).isPrefixOf q = true := by
  constructor
  · intro member
    obtain ⟨n, hn, same⟩ := List.mem_map.mp member
    have one : q[n]? = some 1 := beq_iff_eq.mp (List.mem_filter.mp hn).2
    rw [List.isPrefixOf_iff_prefix, ← same]
    have whole : q.take n ++ [1] = q.take (n + 1) := by
      rw [List.take_add_one, one]
      rfl
    rw [whole]
    exact List.take_prefix _ _
  · intro prefixed
    have pre := List.isPrefixOf_iff_prefix.mp prefixed
    have len : x.length + 1 ≤ q.length := by
      have bound := pre.length_le
      rw [List.length_append] at bound
      exact bound
    have xpre : x <+: q := (List.prefix_append x [1]).trans pre
    have xeq : x = q.take x.length := List.prefix_iff_eq_take.mp xpre
    have full : x ++ [1] = q.take (x.length + 1) := by
      have taken := List.prefix_iff_eq_take.mp pre
      rw [List.length_append] at taken
      exact taken
    rw [List.take_add_one, ← xeq] at full
    have tail := List.append_cancel_left full
    have one : q[x.length]? = some 1 := by
      cases found : q[x.length]? with
      | none =>
        rw [found] at tail
        cases tail
      | some v =>
        rw [found] at tail
        cases tail
        rfl
    refine List.mem_map.mpr ⟨x.length, List.mem_filter.mpr ⟨(mem_below _ _).mpr (by omega), ?_⟩,
      xeq.symm⟩
    rw [one]
    rfl

theorem releaseWeight_eq (q x : List Nat) :
    FinalizerSource.releaseWeight q x = if x ∈ releasePaths q then 1 else 0 := by
  unfold FinalizerSource.releaseWeight SourceScope.Opportunities.below
  cases prefixed : (x ++ [1]).isPrefixOf q with
  | true => rw [if_pos rfl, if_pos ((mem_releasePaths q x).mpr prefixed)]
  | false =>
    have outside : ¬ x ∈ releasePaths q := fun m => by
      have back := (mem_releasePaths q x).mp m
      rw [prefixed] at back
      exact Bool.false_ne_true back
    rw [if_neg Bool.false_ne_true, if_neg outside]

theorem sum_indicator (a : List Nat) : ∀ (l : List (List Nat)), l.Nodup →
    (l.map (fun path => if (a == path) = true then 1 else 0)).sum = if a ∈ l then 1 else 0
  | [], _ => by
    rw [if_neg List.not_mem_nil]
    rfl
  | b :: l, h => by
    obtain ⟨notMem, rest⟩ := List.nodup_cons.mp h
    rw [List.map_cons, List.sum_cons, sum_indicator a l rest]
    cases same : (a == b) with
    | true =>
      have equal : a = b := beq_iff_eq.mp same
      rw [equal]
      rw [if_pos rfl, if_neg notMem, if_pos (.head _)]
    | false =>
      have differ : a ≠ b := fun equal => by
        rw [equal, beq_iff_eq.mpr rfl] at same
        exact Bool.false_ne_true same.symm
      have iff : a ∈ b :: l ↔ a ∈ l :=
        ⟨fun m => (List.mem_cons.mp m).resolve_left differ, fun m => .tail _ m⟩
      rw [if_neg Bool.false_ne_true, Nat.zero_add]
      rcases Decidable.em (a ∈ l) with inside | outside
      · rw [if_pos inside, if_pos (iff.mpr inside)]
      · rw [if_neg outside, if_neg (fun m => outside (iff.mp m))]

theorem sum_zero (l : List (List Nat)) (f : List Nat → Bool) (h : ∀ x, f x = false) :
    (l.map (fun x => if f x = true then 1 else 0)).sum = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.sum_cons, ih, h x]
    rfl

theorem produced_eq (p : NativeEff) (q : List Nat) (e : ReleaseTrace.Event) :
    (FinalizerSource.ledger p q).produced e =
      ((releasePaths q).map (fun path => if ReleaseTrace.releaseAt path e = true then 1 else 0)).sum := by
  cases e with
  | frame owner event =>
    cases event with
    | pushed code =>
      cases code with
      | onSuccess body callback =>
        cases callback with
        | releaseUnder point ctx exit =>
          show FinalizerSource.releaseWeight q point.path =
            ((releasePaths q).map (fun path => if (point.path == path) = true then 1 else 0)).sum
          rw [sum_indicator point.path (releasePaths q) (releasePaths_nodup q), releaseWeight_eq]
        | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
      | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
    | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
  | _ => exact (sum_zero _ _ (fun _ => rfl)).symm

theorem transferred_eq (q : List Nat) (e : ReleaseTrace.Event) :
    transferred q e =
      ((releasePaths q).map (fun path => if ReleaseTrace.registeredAt path e = true then 1 else 0)).sum := by
  cases e with
  | frame owner event =>
    cases event with
    | pushed code =>
      cases code with
      | onSuccess body callback =>
        cases callback with
        | afterScopeAdd a fin =>
          cases fin with
          | foreign capture =>
            show FinalizerSource.releaseWeight q capture.path =
              ((releasePaths q).map (fun path => if (capture.path == path) = true then 1 else 0)).sum
            rw [sum_indicator capture.path (releasePaths q) (releasePaths_nodup q), releaseWeight_eq]
          | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
        | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
      | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
    | _ => exact (sum_zero _ _ (fun _ => rfl)).symm
  | _ => exact (sum_zero _ _ (fun _ => rfl)).symm

theorem countP_sum (pr : ReleaseTrace.Event → Bool) : ∀ (trace : List ReleaseTrace.Event),
    trace.countP pr = (trace.map (fun e => if pr e = true then 1 else 0)).sum
  | [] => rfl
  | e :: rest => by
    rw [List.map_cons, List.sum_cons, ← countP_sum pr rest]
    cases selected : pr e with
    | true => rw [List.countP_cons_of_pos selected, if_pos rfl, Nat.add_comm]
    | false =>
      rw [List.countP_cons_of_neg (by rw [selected]; exact Bool.false_ne_true),
        if_neg Bool.false_ne_true, Nat.zero_add]

theorem sum_map_add {α : Type} (l : List α) (f g : α → Nat) :
    (l.map (fun x => f x + g x)).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, List.sum_cons, ih]
    omega

theorem sum_map_le {α : Type} (l : List α) (f g : α → Nat) (h : ∀ x ∈ l, f x ≤ g x) :
    (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => exact Nat.le_refl 0
  | cons x l ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
    have head := h x (.head _)
    have tail := ih (fun y member => h y (.tail _ member))
    omega

theorem sum_swap (paths : List (List Nat)) (g : List Nat → ReleaseTrace.Event → Nat) :
    ∀ (trace : List ReleaseTrace.Event),
      (trace.map (fun e => (paths.map (fun path => g path e)).sum)).sum =
        (paths.map (fun path => (trace.map (fun e => g path e)).sum)).sum
  | [] => by
    rw [List.map_nil, List.sum_nil]
    induction paths with
    | nil => rfl
    | cons x l ih => rw [List.map_cons, List.sum_cons, ← ih]; rfl
  | e :: rest => by
    rw [List.map_cons, List.sum_cons, sum_swap paths g rest]
    have split : (paths.map (fun path => ((e :: rest).map (fun e => g path e)).sum)) =
        paths.map (fun path => g path e + (rest.map (fun e => g path e)).sum) := by
      apply congrArg (fun f => paths.map f)
      funext path
      rw [List.map_cons, List.sum_cons]
    rw [split, sum_map_add]

/-- **The weighted custody from the per-path balance** (proved): sum the per-path balance over
the release paths of `q`. -/
theorem custody_of_paths (p : NativeEff) (q : List Nat) (trace : List ReleaseTrace.Event)
    (paths : ∀ path, trace.countP (ReleaseTrace.releaseAt path) ≤
      trace.countP (ReleaseTrace.registeredAt path)) :
    (trace.map (FinalizerSource.ledger p q).produced).sum ≤ (trace.map (transferred q)).sum := by
  have produced : (FinalizerSource.ledger p q).produced = fun e =>
      ((releasePaths q).map (fun path => if ReleaseTrace.releaseAt path e = true then 1 else 0)).sum :=
    funext (produced_eq p q)
  have moved : transferred q = fun e =>
      ((releasePaths q).map (fun path => if ReleaseTrace.registeredAt path e = true then 1 else 0)).sum :=
    funext (transferred_eq q)
  rw [produced, moved, sum_swap, sum_swap]
  apply sum_map_le
  intro path _
  rw [← countP_sum, ← countP_sum]
  exact paths path

/-- **The custody balance** (proved modulo `release_custody`). -/
theorem custody (p : NativeEff) (table : RowTable) (cf : Nat) (m : NativeMachine) (q : List Nat) :
    OncePlaced (.eff p) q = true → Guard.Reachable p table cf m →
      (m.trace.map (FinalizerSource.ledger p q).produced).sum ≤ (m.trace.map (transferred q)).sum :=
  fun _ reached => custody_of_paths p q m.trace (fun path => release_custody p table cf m path reached)

/-- A frame event spends at least its custody transfer. -/
theorem frame_transfer_le (p : NativeEff) (q : List Nat) (owner : FiberId)
    (event : FrameEvent EffName EffThunk Val Err Defect FiberId Ann) :
    transferred q (.frame owner event) ≤ (FinalizerSource.ledger p q).consumed (.frame owner event) := by
  cases event with
  | pushed code =>
    cases code with
    | onSuccess body callback =>
      cases callback with
      | afterScopeAdd a fin =>
        cases fin with
        | foreign capture =>
          show FinalizerSource.releaseWeight q capture.path ≤
            SourceScope.Opportunities.here q capture.path + FinalizerSource.releaseWeight q capture.path
          omega
        | _ => exact Nat.zero_le _
      | _ => exact Nat.zero_le _
    | _ => exact Nat.zero_le _
  | _ => exact Nat.zero_le _

/-- A selected registration spends one credit beside its (empty) custody transfer. -/
theorem frame_registered_le (p : NativeEff) (q : List Nat) (owner : FiberId)
    (event : FrameEvent EffName EffThunk Val Err Defect FiberId Ann)
    (selected : FinalizerRun.registeredAt q (.frame owner event) = true) :
    1 + transferred q (.frame owner event) ≤ (FinalizerSource.ledger p q).consumed (.frame owner event) := by
  cases event with
  | pushed code =>
    cases code with
    | onExit body name flag =>
      cases name with
      | fin point =>
        have same : point.path = q := beq_iff_eq.mp selected
        show 1 + 0 ≤ SourceScope.Opportunities.here q point.path
        unfold SourceScope.Opportunities.here
        split
        · exact Nat.le_refl 1
        · rename_i other
          exact absurd same other
      | _ => exact absurd selected Bool.false_ne_true
    | _ => exact absurd selected Bool.false_ne_true
  | _ => exact absurd selected Bool.false_ne_true

/-- A run event spends at least its custody transfer. -/
theorem event_transfer_le (p : NativeEff) (q : List Nat) (e : ReleaseTrace.Event) :
    transferred q e ≤ (FinalizerSource.ledger p q).consumed e := by
  cases e with
  | frame owner event => exact frame_transfer_le p q owner event
  | _ => exact Nat.zero_le _

/-- A selected run event spends one credit beside its custody transfer. -/
theorem event_registered_le (p : NativeEff) (q : List Nat) (e : ReleaseTrace.Event)
    (selected : FinalizerRun.registeredAt q e = true) :
    1 + transferred q e ≤ (FinalizerSource.ledger p q).consumed e := by
  cases e with
  | frame owner event => exact frame_registered_le p q owner event selected
  | _ => exact absurd selected Bool.false_ne_true

/-- A trace spends at least its selected registrations and its custody transfers. -/
theorem trace_le (p : NativeEff) (q : List Nat) : ∀ trace : List ReleaseTrace.Event,
    trace.countP (FinalizerRun.registeredAt q) + (trace.map (transferred q)).sum ≤
      (trace.map (FinalizerSource.ledger p q).consumed).sum
  | [] => Nat.le_refl 0
  | e :: rest => by
    have later := trace_le p q rest
    simp only [List.map_cons, List.sum_cons]
    cases selected : FinalizerRun.registeredAt q e with
    | true =>
      rw [List.countP_cons_of_pos selected]
      have here := event_registered_le p q e selected
      omega
    | false =>
      rw [List.countP_cons_of_neg (by rw [selected]; exact Bool.false_ne_true)]
      have here := event_transfer_le p q e
      omega

/-- **The registration bound from the source ledger and custody.** Every once-placed source pushes
its `onExit` finalizer at most once along every raw decision prefix, given the custody balance.
It needs no census premise. -/
theorem outside_census_of_custody (p : NativeEff) (table : RowTable) (cf : Nat) (m : NativeMachine)
    (q : List Nat) (placed : OncePlaced (.eff p) q = true) (reached : Guard.Reachable p table cf m)
    (balance : (m.trace.map (FinalizerSource.ledger p q).produced).sum ≤
      (m.trace.map (transferred q)).sum) :
    m.trace.countP (FinalizerRun.registeredAt q) ≤ 1 := by
  have funded := FinalizerSource.source_funded_reachable p q table placed cf m reached
  have spent := trace_le p q m.trace
  unfold PlaceLedger.Funded PlaceLedger.spent PlaceLedger.issued at funded
  omega

/-- The original goal's statement, modulo `custody` only. -/
theorem once_placed_outside_census_modulo (p : NativeEff) (table : RowTable) (cf : Nat)
    (m : NativeMachine) (q : List Nat) :
    OncePlaced (.eff p) q = true → ¬ FinalizerRun.Census p q → Guard.Reachable p table cf m →
      m.trace.countP (FinalizerRun.registeredAt q) ≤ 1 := fun placed _ reached =>
  outside_census_of_custody p table cf m q placed reached (custody p table cf m q placed reached)

/-- The statement is the planned goal's, word for word. -/
theorem same_statement :
    type_of% @once_placed_outside_census_modulo = type_of% @FinalizerRun.once_placed_outside_census :=
  rfl

end Effect4.Program.RemainingWork.FinalizerAssembly
