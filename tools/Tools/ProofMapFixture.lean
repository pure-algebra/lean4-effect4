import ProofGraph.Ledger

/-! Small imported expressions distinguish type vocabulary from actual proof references. -/
namespace Tools.ProofMapFixture
def Predicate (_ : Nat) : Prop := True
theorem independent : Predicate 0 := True.intro
theorem consumes : Predicate 0 := independent
theorem conditional (p : Prop) (h : p) : p := h
structure Restricted where
  permitted : True
  excluded : False
end Tools.ProofMapFixture
