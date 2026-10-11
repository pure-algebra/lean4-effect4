probe = 'docs/research/2026-10-10-goals-packet/store-invariants/Probe.lean'
s = open(probe).read()

# 1. cut build_elaborates out of section 7
b0 = s.index("/-- A build keeps the elaborated program and the module's table. -/")
b1 = s.index("/-- The shop's elaborated program. -/")
build = s[b0:b1]
s = s[:b0] + s[b1:]

# 2. insert build_elaborates + control section before section 3
control = open('docs/research/2026-10-10-goals-packet/store-invariants/scratch/control.lean').read()
m3 = s.index("/-! ## 3. The observation of a machine -/")
s = s[:m3] + build + control + "\n" + s[m3:]

# 3. restate G1 and S2 over control histories
old_g1 = "    ∀ m, HistoryOf b compileFuel m → HeapOk P m.state.refs"
assert old_g1 in s
s = s.replace(old_g1, "    ∀ m, ControlHistory b compileFuel m → HeapOk P m.state.refs")
s = s.replace("`bounded_modulo` here; every scenario goal that reads one cell. Reach: the native machine of a\nbuilt program, every history the session accepts (`HistoryOf`).",
              "`bounded_modulo` here; every scenario goal that reads one cell. Reach: the native machine of a\nbuilt program, every control history (`ControlHistory`); a program with no host row has no\nother (`history_control`).")
old_s2 = "    ∀ m, HistoryOf b compileFuel m → ∃ g, StagesFit g (observeM m)"
assert old_s2 in s
s = s.replace(old_s2, "    ∀ m, ControlHistory b compileFuel m → ∃ g, StagesFit g (observeM m)")
s = s.replace("built shop, every compile budget, every accepted history.", "built shop, every compile budget, every control history.")

# 4. uses
s = s.replace("""  have heap := heap_sites_keep b budget.compileFuel UsedOk (shop_sites_used b hb) _
    (scenario_history b moves)""", """  have heap := heap_sites_keep b budget.compileFuel UsedOk (shop_sites_used b hb) _
    (scenario_control b hb moves)""")
n = s.count("shop_stages b hb budget.compileFuel _ (scenario_history b moves)")
assert n == 2, n
s = s.replace("shop_stages b hb budget.compileFuel _ (scenario_history b moves)",
              "shop_stages b hb budget.compileFuel _ (scenario_control b hb moves)")
s = s.replace("#plan_status RunKeeps.scenario reached_history scenario_history history_keeps counted_of_fit",
              "#plan_status RunKeeps.scenario reached_history scenario_history history_keeps scenario_control\n  counted_of_fit")
open(probe, 'w').write(s)
print("ok")
