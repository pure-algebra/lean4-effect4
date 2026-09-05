import Effect4.Char.Queue.Inv
import Effect4.Char.Queue.Reading

/-!
# Char.Queue.Grade: conservation, its corollaries, the bundles, and what is owed

Hand-authored part 3 of the five, second half: the laws. From
`docs/research/2026-09-05-workshop-char/01-model/03-conservation.md` and `06-guarded-graded.md`.

Conservation is one application of the generic `Machine.conservation` to a
word-free local table, `queue_localBalance`, on the clean machine under
`QOpened`. Four rows are live, four are disabled by the invariant, two kinds are
excluded by the failure model, and no `QInv` clause is consumed. The corrected
orientation is `s₀.buffer ++ acc w = del w ++ s.buffer` (ruling R2,
`ALGEBRA.md` section 7.2): `offer` appends at the back (`EffectQueue.lean:76`,
`Queue.ts:666`), so the start residue sits on the left.

The second table, `queue_localBalanceLe` with `queue_sealing`, is on the
**unrestricted** machine with no invariant, and it is what gives `order` on
every run including the lossy ones (`queue_order`), through
`Machine.conservation_le`. The sealed region is "not `opened`": a refused
`offer` or a `shutdown` lands there, it never reopens, and inside it every step
delivers only from the buffer it already held.

`Queue.ts` citations are at rc.112, `vendor/effect-4.0.0-rc.112/src/Queue.ts`,
SHA-256 `dc355d1a…`.
-/

set_option autoImplicit false

namespace Effect4.Char.Queue

open Effect4.Char

/-! ## The local table on the clean machine -/

/-- The word-free table under `QOpened`. Rows `offer` (`List.nil_append`),
`takeAll` and `wake` (`chunk_forClient_comp`), `takePark` (`append_nil`,
`nil_append`); every other arm is disabled by the invariant or excluded by the
failure model. -/
theorem queue_localBalance (cap : Nat) :
    LocalBalance (queueClean cap) queueReading QOpened := by
  intro c s s' l hi hstep0
  cases c
  simp only [QOpened] at hi
  obtain ⟨hadm, hstep⟩ := Machine.step_restrict_some hstep0
  cases l <;>
    (try (simp [queueCrash, queueKinds, Failure.admits, qKind] at hadm)) <;>
    simp only [queue, hi] at hstep <;>
    (try split at hstep) <;>
    first
      | (injection hstep with heq
         subst heq
         simp_all [queueReading, Reading.acc, Reading.del, Reading.forClient,
           Reading.chunk_forClient_comp])
      | injection hstep

/-! ## Conservation and its three corollaries -/

/-- Conservation, generalized. On a run containing no excluded kind, what the
queue already held followed by what was offered is exactly what was delivered
followed by what it still holds. -/
theorem queue_conservation_gen (cap : Nat) (w : List QLabel) (s0 s : QState)
    (hopen : s0.status = QStatus.opened)
    (hrun : (queueClean cap).run s0 w = some s) :
    s0.buffer ++ queueReading.acc () w = queueReading.del () w ++ s.buffer :=
  Machine.conservation (qOpened_inductive cap) (queue_localBalance cap) hopen hrun ()

/-- Conservation from `init`, on the unrestricted machine, for a clean word.
This is the row the manifest carries. -/
theorem queue_conservation (cap : Nat) (w : List QLabel) (s : QState)
    (hclean : queueCrash.clean queueKinds w = true)
    (hrun : (queue cap).run (queue cap).init w = some s) :
    queueReading.acc () w = queueReading.del () w ++ s.buffer := by
  have hrun' : (queueClean cap).run (queueClean cap).init w = some s := by
    rw [show (queueClean cap).init = (queue cap).init from rfl]
    rw [queueClean, Machine.run_restrict _ _ _ _ hclean]
    exact hrun
  have hgen := queue_conservation_gen cap w (queueClean cap).init s rfl hrun'
  rw [show (queueClean cap).init.buffer = ([] : List Item) from rfl,
    List.nil_append] at hgen
  exact hgen

/-- `noLoss` at quiescence: a clean run that ends with an empty buffer delivered
exactly what it accepted. -/
theorem queue_noLoss_at_quiescence (cap : Nat) (w : List QLabel) (s : QState)
    (hclean : queueCrash.clean queueKinds w = true)
    (hrun : (queue cap).run (queue cap).init w = some s)
    (hq : s.buffer = []) :
    queueReading.acc () w = queueReading.del () w := by
  rw [queue_conservation cap w s hclean hrun, hq, List.append_nil]

/-- `order` on clean runs: what was delivered followed by what is held is a
prefix of what was accepted. -/
theorem queue_fifo (cap : Nat) (w : List QLabel) (s : QState)
    (hclean : queueCrash.clean queueKinds w = true)
    (hrun : (queue cap).run (queue cap).init w = some s) :
    (queueReading.del () w ++ queueReading.residue s ()).isPrefixOf
      (queueReading.acc () w) = true := by
  rw [queue_conservation cap w s hclean hrun]
  exact List.isPrefixOf_iff_prefix.mpr (List.prefix_refl _)

/-- `noDup` on clean runs, relative to a fresh word. `hfresh` is a hypothesis on
the word, never a theorem: a client that offers the same item twice is
delivered it twice, and that is correct behaviour. -/
theorem queue_noDup (cap : Nat) (w : List QLabel) (s : QState)
    (hclean : queueCrash.clean queueKinds w = true)
    (hrun : (queue cap).run (queue cap).init w = some s)
    (hfresh : nodupB (queueReading.acc () w) = true) :
    nodupB (queueReading.del () w) = true := by
  rw [queue_conservation cap w s hclean hrun] at hfresh
  exact nodupB_append_left _ _ hfresh

/-! ## The lossy table on the unrestricted machine, and `order` on every run -/

/-- The sealed region: a queue that is no longer `opened`. A refused `offer`
and a `shutdown` land here, `fail` lands here without losing anything, and
nothing reopens. -/
def queueDead (s : QState) : Prop := s.status ≠ QStatus.opened

/-- A `lost` remainder exists exactly when the right side is a prefix of the
left, so every row below is one `simp_all` and no witness is guessed. -/
theorem exists_append_eq_of_prefix {x y : List Item} (h : y <+: x) : ∃ t, x = y ++ t := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t, ht.symm⟩

/-- Q2's table on the unrestricted machine. No invariant is needed: the two
lossy rows are the refused `offer` (`lost = [m]`, `Queue.ts:647-648`) and
`shutdown` (`lost = s.buffer`, `Queue.ts:1196`); every other enabled arm has
`lost = []`. -/
theorem queue_localBalanceLe (cap : Nat) :
    LocalBalanceLe (queue cap) queueReading (fun _ => True) := by
  intro c s s' l _ hstep
  cases c
  cases l <;> cases hs : s.status <;>
    simp only [queue, hs] at hstep <;>
    (try split at hstep) <;>
    first
      | (injection hstep with heq
         subst heq
         exact exists_append_eq_of_prefix (by
           simp_all [queueReading, Reading.acc, Reading.del, Reading.forClient,
             Reading.chunk_forClient_comp]))
      | injection hstep

/-- The queue is sealed by "not `opened`". -/
theorem queue_sealing (cap : Nat) :
    Sealing (queue cap) queueReading (fun _ => True) queueDead where
  seals := by
    intro c s s' l _ hstep
    cases c
    cases l <;> cases hs : s.status <;>
      simp only [queue, hs] at hstep <;>
      (try split at hstep) <;>
      first
        | (injection hstep with heq
           subst heq
           first
             | (right; simp_all [queueDead]; done)
             | (left; simp_all [queueReading, Reading.acc, Reading.del,
                 Reading.forClient, Reading.chunk_forClient_comp]; done))
        | injection hstep
  closed := by
    intro s s' l _ hD hstep
    simp only [queueDead] at hD ⊢
    cases l <;> cases hs : s.status <;>
      simp only [queue, hs] at hstep <;>
      (try split at hstep) <;>
      first
        | (injection hstep with heq
           subst heq
           simp_all)
        | injection hstep
  drains := by
    intro c s s' l _ hD hstep
    cases c
    simp only [queueDead] at hD
    cases l <;> cases hs : s.status <;>
      simp only [queue, hs] at hstep <;>
      (try split at hstep) <;>
      first
        | (injection hstep with heq
           subst heq
           exact exists_append_eq_of_prefix (by
             simp_all [queueReading, Reading.del, Reading.chunk_forClient_comp]))
        | injection hstep

/-- Conservation up to loss, on every run of the unrestricted machine. -/
theorem queue_conservation_le (cap : Nat) (w : List QLabel) (s : QState)
    (hrun : (queue cap).run (queue cap).init w = some s) :
    ∃ lost, queueReading.acc () w = queueReading.del () w ++ s.buffer ++ lost := by
  have h := Machine.conservation_le (Inductive.true (queue cap)) (queue_localBalanceLe cap)
    (queue_sealing cap) trivial hrun ()
  rw [show queueReading.residue (queue cap).init () = ([] : List Item) from rfl,
    List.nil_append] at h
  exact h

/-- `order` on **every** run, lossy or not: FIFO survives a `fail`, a refused
`offer` and a `shutdown`. This is the `order` axis of the grade under `F-any`. -/
theorem queue_order (cap : Nat) (w : List QLabel) (s : QState)
    (hrun : (queue cap).run (queue cap).init w = some s) :
    (queueReading.del () w ++ queueReading.residue s ()).isPrefixOf
      (queueReading.acc () w) = true :=
  Machine.order_le (Inductive.true (queue cap)) (queue_localBalanceLe cap)
    (queue_sealing cap) trivial hrun () rfl

/-- `noDup` on every run, relative to a fresh word. -/
theorem queue_noDup_all (cap : Nat) (w : List QLabel) (s : QState)
    (hrun : (queue cap).run (queue cap).init w = some s)
    (hfresh : nodupB (queueReading.acc () w) = true) :
    nodupB (queueReading.del () w) = true :=
  Machine.noDup_le (Inductive.true (queue cap)) (queue_localBalanceLe cap)
    (queue_sealing cap) trivial hrun () rfl hfresh

/-! ## The bundles -/

/-- A `Guarded` row with reached witnesses: a run whose reached state is open
with an empty buffer has an empty residue. `pos_reached` and `neg_reached` are
each one `decide` over a two-label word at most. -/
def queueEmptyGuarded : Guarded QState QLabel Unit where
  id := "queue_residue_empty_when_drained"
  sentence := "a run whose reached state is open with an empty buffer has an empty residue"
  machine := queue 2
  guard := fun _ s => s.buffer.isEmpty && (s.status == QStatus.opened)
  claim := fun _ s => queueReading.residue s () == []
  law := by
    intro w s hg
    cases hb : s.buffer with
    | nil =>
      show (queueReading.residue s () == []) = true
      rw [queue_residue_eq_buffer, hb]
      rfl
    | cons a r =>
      rw [hb] at hg
      exact absurd hg (by simp)
  posWord := [.offer 1, .takeAll [1]]
  posState := { buffer := [], status := .opened, taker := false }
  pos_reached := by decide
  pos_guard := by decide
  negWord := [.offer 1]
  negState := { buffer := [1], status := .opened, taker := false }
  neg_reached := by decide
  neg_guard := by decide
  neg_claim := by decide

/-- The compiling `Graded` row at the bottom grade under `F-none`, which claims
nothing and is here as the elaboration measurement and the shape. The real row,
`queue_graded` at `Grade.top`, is owed and is refuted below as stated.
`escapes_reachable` is one `decide` over two two-label words. -/
def queueGradedBot : Graded QState QLabel Unit QKind where
  id := "queue_graded_bot"
  sentence := "the queue is sound at the bottom grade under F-none, which claims nothing"
  machine := queue 2
  reading := queueReading
  kinds := queueKinds
  failure := queueCrash
  grade := Grade.bot
  law := by intro c w s _; simp [Grade.holds, Grade.bot]
  escapeWitnesses :=
    [ ([.offer 1, .fail 7], { buffer := [1], status := .closing 7, taker := false })
    , ([.offer 1, .shutdown], { buffer := [], status := .shutdown, taker := false }) ]
  escapes_reachable := by decide
  escapes_covered := rfl
  quietWord := [.offer 1, .offer 2, .takeAll [1, 2]]
  quiet_clean := by decide
  vacuityMutant := "Q-W3"

/-- The `Entry` rows this module projects, for the manifest. -/
def queueEntries : List Entry :=
  [ queueEmptyGuarded.entry, queueGradedBot.entry ]

/-! ## Kept refutations -/

namespace Refute

/-- Without an invariant the queue has no true local table: the refused
`offer` accepts an item and leaves the state alone (`Queue.ts:647-648`), so its
row reads `b ++ [m] = [] ++ b`. Three `decide`s over literal states. -/
theorem localBalance_needs_invariant :
    ∃ (s s' : QState) (l : QLabel),
      queueCrash.admits queueKinds l = true ∧
      (queue 4).step s l = some s' ∧
      queueReading.residue s () ++ queueReading.acc () [l]
        ≠ queueReading.del () [l] ++ queueReading.residue s' () :=
  ⟨{ buffer := [9], status := .closing 7, taker := false },
   { buffer := [9], status := .closing 7, taker := false },
   .offer 1, by decide, by decide, by decide⟩

/-- The refuting state is reachable, by the run `[offer 9, fail 7]`. -/
theorem localBalance_witness_reachable :
    (queue 4).run (queue 4).init [.offer 9, .fail 7]
      = some { buffer := [9], status := .closing 7, taker := false } := by
  decide

/-- `queue_graded` as item 01 section 5 spells it, `Sound … Grade.top` under
`F-none`, is false: `Grade.holds`'s `noDup` axis carries no freshness
hypothesis, and the word `[offer 1, offer 1, takeAll [1, 1]]` is accepted, is
clean, and delivers a duplicate it was handed. The row stays owed, and this
says what it would take: either `holds` gains a freshness guard on `noDup`, or
the queue's honest grade under `F-none` is `⟨true, false, true⟩`. -/
theorem queue_graded_top_refuted :
    ¬ (queue 2).Sound queueReading queueKinds queueCrash Grade.top := by
  intro h
  have hw := h () [.offer 1, .offer 1, .takeAll [1, 1]]
    { buffer := [], status := .opened, taker := false } (by decide)
  exact absurd hw (by decide)

end Refute

/-! ## Owed

Five rows, each a manifest `claim` with evidence kind `assumed`, reaching no rung
and reported `held` (`docs/research/2026-09-05-workshop-char/01-model/01-queue-port-plan.md` section 5,
`REVIEW-01.md` section 5). Nothing here is stubbed; an owed row is visibly
owed.

| Owed id | Evidence | Sentence |
| --- | --- | --- |
| `queue_size_agrees_on_reachable` | `assumed` | on every reachable state, `sizeUnsafe`'s `Done → 0` arm (`Queue.ts:1789`) and the buffer length agree |
| `queue_graded` | `assumed` | `(queue cap).Sound queueReading queueKinds queueCrash Grade.top`; refuted as stated by `Refute.queue_graded_top_refuted`, so the row needs a ruling on `Grade.holds`'s `noDup` axis before it can be proved at any grade with `noDup = true` |
| `queue_offer_suspend` | `assumed` | an offer at capacity parks the publisher rather than being disabled (stage B2; `Queue.ts:653-659`) |
| `queue_runtime_integration` | `assumed` | `wake` is posted by the dispatcher (`Queue.ts:1974`) rather than taken as a label |
| `queue_transliteration` | `assumed` | `queue cap` is rc.112's bounded suspend-strategy queue; reaches `replayed` at best, through the pins and the replay |
-/

end Effect4.Char.Queue
