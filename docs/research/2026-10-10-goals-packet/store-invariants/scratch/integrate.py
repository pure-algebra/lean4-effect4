import re

probe = 'docs/research/2026-10-10-goals-packet/store-invariants/Probe.lean'
s = open(probe).read()

# 1. Cut the shop_sites_used goal and bounded_modulo out of section 4.
start = s.index("/-- The window's used capacity bounded by three")
goal_doc = s.index("/-- **The shop's write sites keep the used bound**")
section5 = s.index("/-! ## 5. The stages of the requests")
used_def = s[start:goal_doc]
s = s[:start] + used_def + s[section5:]

# 2. Replace the three family goals with proved theorems and their helpers.
fam_start = s.index("/-- **The deposit's write site keeps the used bound**")
fam_end = s.index("/-- One closed allocation request")
helpers = open('docs/research/2026-10-10-goals-packet/store-invariants/scratch/families-probe.lean').read()
s = s[:fam_start] + helpers + s[fam_end:]

# 3. Rename the decomposed theorem and assemble bounded after section 7.
s = s.replace("/-- **`shop_sites_used`, decomposed**: modulo the three family goals above. -/\ntheorem shop_sites_used_modulo",
              "/-- **The shop's write sites keep the used bound** (program-specific; proved). Each of the shop's\n31 `perform` sites keeps `UsedOk` at its level: the census (`shop_census`) puts each in a family,\nand each family keeps the bound. Placement: concept `store-typing`, requirement R4; a step of the\nscenario clause `bounded`; consumer `bounded_modulo`. -/\ntheorem shop_sites_used")
assemble = '''
/-! ## 8. `bounded`, assembled -/

/-- **`bounded`, modulo the cell invariant from write sites alone.** -/
theorem bounded_modulo : Bounded := by
  intro b moves hb
  have heap := heap_sites_keep b budget.compileFuel UsedOk (shop_sites_used b hb) _
    (scenario_history b moves)
  rw [observe_eq]
  show natField (Test.Dogfood.Scenario.play (opened b) moves).machine.state.refs[0]? "used" ≤ 3
  cases h0 : (Test.Dogfood.Scenario.play (opened b) moves).machine.state.refs[0]? with
  | none => exact Nat.zero_le 3
  | some v => exact heap 0 v h0

/-- The family's three clauses, modulo the planned goals of this probe. -/
theorem family_modulo : Bounded ∧ Counted ∧ Committed :=
  ⟨bounded_modulo, counted_modulo, committed_modulo⟩
'''
# remove the old family_modulo (defined in section 5 area)
old_family = """/-- The family's three clauses, modulo the three planned goals of this probe. -/
theorem family_modulo : Bounded ∧ Counted ∧ Committed :=
  ⟨bounded_modulo, counted_modulo, committed_modulo⟩
"""
assert old_family in s
s = s.replace(old_family, "")
marker = "\n#plan_status family_modulo"
s = s.replace(marker, assemble + marker, 1)
open(probe, 'w').write(s)
print("ok")
