import Effect4.Program.Compile

/-!
# Invocation — the two syntactic forms of one call (v2 DI-61 (a), (b))

What this module owns: the facts the shared dispatcher of `Program/Compile.lean`
(`asyncRoute`) was extracted for, and an explicit statement of the one that is **not** proved
yet and why.

1. `compileEff_callback_eq_asyncRoute` — the extraction is exact: at positive fuel the
   `callback` arm *is* `asyncRoute`, for every operation. This is the behaviour-free half of
   DI-61 (a).

2. `compile_perform_eq_callback_of_await` — the two spellings already compile alike for an
   asynchronous built-in that is neither `sleep` nor an external index; among the 55 built-in
   values that is exactly `Deferred.await`, which is the historical case that made runtime
   unification the compatible choice (`Program/Wire.lean:81` and `OCaml5/Eff/Goldens.lean:285`
   both spell `perform .deferredAwait`; `Codegen/Print.lean:212`, `:263` print the two forms
   as one call, and `Codegen/Read.lean:259-261` reads that call back as `callback`).

3. `checkTable_none_externalRow` — a table this runner can register every row of is a table
   whose every row `externalRow` resolves. `Api.checkTable` (`src/Effect4/Api.lean`) is the
   decidable refusal; `externalRow` (`src/Effect4/Program/Compile.lean`) is what the
   registration hook actually consults, and this is the bridge between them.

**What is not here, and must not be assumed.** v2 DI-61 (a) asks for the unconditional
`compile_perform_eq_callback`: `(∃ i, op = .external i) ∨ op.row.kind = .async →
compileEff (.perform op r) p = compileEff (.callback op r) p`. It is **false at this commit**,
for `sleep` and for every external index, because the `perform` arm still routes by row kind
(`perform .sleep` reaches `badShape`; `perform (.external i)` reaches the frontier). The two
counterexamples are pinned as `#guard`s in `Test/Program/InvocationContract.lean`, so the gap
is measured rather than assumed. Routing the `perform` arm through `asyncRoute` is a two-line
change; what blocks it is that the reference denotation and three compiler-head mirrors spell
the old arm — `denoteR`'s own `perform` arm and `inlineYield`
(`src/Effect4/Laws/Program/DenoteR.lean`), `compileEff_perform`
(`src/Effect4/Laws/Program/Handles.lean:379`), `compileEff_perform_async` and
`compileEff_perform_program` (`src/Effect4/Laws/Program/Intro.lean:198`, `:206`) — and
`run_eq_ref` (`src/Effect4/Laws/Program/RuntimeR.lean:200`) relates the machine to that
denotation **with no premise**. Changing the compiler alone makes `run_eq_ref` false; changing
the denotation with it is a semantic decision v2 does not make. The build failures that
establish this are recorded in `docs/research/2026-09-09-seat-core-admission.md` §4 (an
untracked working note); what is tracked is this header and the `THE GAP` guards of
`Test/Program/InvocationContract.lean`.

What this module refuses in any case: any claim that the two forms *execute* alike beyond the
compiled code — the registration hook reads the supplied table when it runs (`interpOf`), and
a row with the wrong registration parks with its answer unused
(`docs/research/foundation-probes/Admission.lean:76-81`). And any claim about `perform` on a
**sync** row: that stays the sync route, and `callback` on a sync row stays `badShape`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## The shared dispatcher -/

/-- Fuel zero is the live frontier in both forms, before any operation is looked at
(`Compile.lean`, `compileEff`'s first match). -/
theorem compile_zero_fuel (e : NativeEff) (p : Point) (h : p.fuel = 0) :
    compileEff e p = frontier p := by
  unfold compileEff
  rw [h]

/-- The extraction is exact: at positive fuel `callback` compiles to the shared dispatcher,
for every operation and every request term. -/
theorem compileEff_callback_eq_asyncRoute (op : NativeOp) (r : Term) (p : Point) {k : Nat}
    (hf : p.fuel = k + 1) : compileEff (.callback op r) p = asyncRoute op r p := by
  unfold compileEff
  rw [hf]

/-- `Deferred.await` compiles alike under both spellings, at any fuel and any point: the
historical wire program's form and the reader's canonical form are one call. -/
theorem compile_perform_eq_callback_await (r : Term) (p : Point) :
    compileEff (.perform .deferredAwait r) p = compileEff (.callback .deferredAwait r) p := by
  unfold compileEff
  cases p.fuel <;> rfl

/-- The general form of the same fact, with the premises the current `perform` arm needs: an
asynchronous row that is neither `sleep` nor an external index. Among the 55 built-in values
`Deferred.await` is the only one that satisfies it; the premises `hns` and `hne` are exactly
what v2 DI-61 (a) removes. -/
theorem compile_perform_eq_callback_of_await (op : NativeOp) (r : Term) (p : Point)
    (hkind : (NativeOp.row op).kind = .async) (hne : ∀ i, op ≠ .external i) (hns : op ≠ .sleep) :
    compileEff (.perform op r) p = compileEff (.callback op r) p := by
  cases op with
  | deferredAwait => exact compile_perform_eq_callback_await r p
  | sleep => exact absurd rfl hns
  | external i => exact absurd rfl (hne i)
  | scopeMake strategy => exfalso; cases strategy <;> simp [NativeOp.row] at hkind
  | _ => exfalso; simp [NativeOp.row] at hkind

/-! ## The table check and the registration lookup -/

/-- An accepted table registers every row it holds: what `checkTable` decides is exactly what
the registration hook consults through `externalRow`. The converse direction (a rejected table
has a position `externalRow` refuses) is `checkTable`'s own `index`. -/
theorem checkTable_none_externalRow {table : RowTable} (h : checkTable table = none)
    (i : Nat) (row : Row) (hi : table[i]? = some row) : externalRow table i = some row := by
  have hlt : i < table.length := by
    rcases Nat.lt_or_ge i table.length with hlt | hge
    · exact hlt
    · rw [List.getElem?_eq_none hge] at hi
      simp at hi
  have hnone :
      (match table[i]? with
        | some row =>
          if row.registration ≠ .external then some (TableRefusal.notExternal i)
          else if row.kind ≠ .async then some (TableRefusal.notAsync i)
          else none
        | none => none) = none := by
    have := List.findSome?_eq_none_iff.mp h i (List.mem_range.mpr hlt)
    exact this
  rw [hi] at hnone
  by_cases hreg : row.registration = .external
  · by_cases hkind : row.kind = .async
    · simp [externalRow, hi, hreg, hkind, guard]
    · simp [hreg, hkind] at hnone
  · simp [hreg] at hnone

end Effect4.Program
