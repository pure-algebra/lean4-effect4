import Effect4.Data.ClockMillis
import Effect4.Laws.Auto.Obligations

#auto_census Effect4.Data.ClockMillis using aesop

namespace Effect4.ClockMillis.M1

def ofNat_toNat (a : ClockMillis) : ProofGraph.Obligation (ofNat a.toNat = a) := ⟨⟩
#proof_wanted ofNat_toNat

def toNat_ofNat (n : Nat) : ProofGraph.Obligation ((ofNat n).toNat = n) := ⟨⟩
#proof_wanted toNat_ofNat

def toNat_add (a b : ClockMillis) : ProofGraph.Obligation ((a + b).toNat = a.toNat + b.toNat) := ⟨⟩
#proof_wanted toNat_add

def ofDecimal_toDecimal (a : ClockMillis) : ProofGraph.Obligation (ofDecimal a.toDecimal = some a) := ⟨⟩
#proof_wanted ofDecimal_toDecimal

def ofDecimal_exact (s : String) (a : ClockMillis) (_h : ofDecimal s = some a) :
    ProofGraph.Obligation (s = a.toDecimal) := ⟨⟩
#proof_wanted ofDecimal_exact

end Effect4.ClockMillis.M1
