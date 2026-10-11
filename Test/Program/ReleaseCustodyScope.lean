import Effect4.Laws.Program.ReleaseCustody.ScopeTransfer

/-!
Readers and controls for the scope-store premise of the worker release claim, R11.
The operation reader uses a real empty scope. The controls show why distinct scope identities
and fresh registration keys are required by the exact transfer equation.
These finite controls establish no history or host agreement.
-/
set_option autoImplicit false
namespace Test.Program.ReleaseCustodyScope
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody Effect4.Program.ReleaseCustody.ScopeTransfer

def scope : ScopeV := Scope.make .sequential

def initial : Stores := {Stores.empty with scopes := ⟨[⟨0, scope⟩]⟩, nextName := 1}

/-- Apply the exact registration law at the real open-scope store and its actual operation result. -/
example (q : List Nat) (fin : FinName) (next : Stores) (value : Val)
    (step : syncOpStep (.scopeAdd 0 fin) initial = some (next, value)) :
    storedCredits q next.scopes + afterAddCredits q fin value = credit q fin := by
  have unique : (initial.scopes.entries.map ScopeEntry.key).Nodup := by decide
  have fresh : initial.ScopeKeysFresh := by
    intro entry member key present
    have same : entry = ⟨0, scope⟩ := List.mem_singleton.mp member
    subst entry
    cases present
  have empty : storedCredits q initial.scopes = 0 := rfl
  simpa only [empty, Nat.zero_add] using ScopeTransfer.add q initial next 0 fin value unique fresh step

def fin : FinName := .foreign {path := [], env := [], fuel := 1, tape := [], ctx := emptyCtx}

def duplicate : Stores := {initial with scopes := ⟨[⟨0, scope⟩, ⟨0, scope⟩]⟩}

-- A duplicated scope identity duplicates the added credit: uniqueness is an essential premise.
#guard ((syncOpStep (.scopeAdd 0 fin) duplicate).map fun out =>
  storedCredits [] out.1.scopes) == some 2

def staleSupply : Stores :=
  {initial with scopes := ⟨[⟨0, scope.addUnsafe 1 fin⟩]⟩}

-- Reusing a held registration key replaces its entry: the exact additive law requires freshness.
#guard storedCredits [] staleSupply.scopes == 1
#guard ((syncOpStep (.scopeAdd 0 fin) staleSupply).map fun out =>
  storedCredits [] out.1.scopes) == some 1

-- An unknown scope remains a frontier; the transfer law assumes an actual returned result.
#guard (syncOpStep (.scopeAdd 99 fin) initial).isNone

end Test.Program.ReleaseCustodyScope
