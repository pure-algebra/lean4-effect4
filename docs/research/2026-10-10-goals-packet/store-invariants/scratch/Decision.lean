import Test.Dogfood.Scenario.Atomic

set_option autoImplicit false

open Effect4 Effect4.Machine Effect4.Program Test.Dogfood.Scenario.Atomic

namespace Scratch

def UsedOk (v : Val) : Prop := natField (some v) "used" ≤ 3

def HeapOk (P : Val → Prop) (refs : RefHeap) : Prop := ∀ (i : Nat) (v : Val), refs[i]? = some v → P v

def OpKeeps (P : Val → Prop) (o : SyncOp) : Prop :=
  ∀ (s s' : Stores) (ans : Val), syncOpStep o s = some (s', ans) → HeapOk P s.refs →
    HeapOk P s'.refs

/-- A record read after a set: the set field reads the new value, every other field what it read. -/
theorem read_after_set {v v' x : Val} {name : String} (h : Record.set v name x = some v')
    (n : String) :
    Record.read false v' n = if name = n then some x else Record.read false v n := by
  unfold Record.set at h
  cases he : Record.entries v with
  | none =>
    rw [he] at h
    cases h
  | some fields =>
    rw [he] at h
    have hv' : Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields)) = v' :=
      Option.some.inj h
    subst hv'
    have hnd := Field.canonBy_names_nodup (key := Field.bytesKey) Field.bytesKey_injective
      ((name, x) :: fields)
    have hentries : Record.entries (Record.frame (Field.canonBy Field.bytesKey ((name, x) :: fields))) =
        some (Field.canonBy Field.bytesKey ((name, x) :: fields)) := by
      simp only [Record.entries, Record.frame, Program.recordParts?, Option.bind_eq_bind,
        Option.bind_some, Typed.readColumns_frame, if_pos hnd]
    unfold Record.read Record.lookup
    rw [hentries, he]
    simp only [Option.map_some, Option.bind_some, Bool.false_eq_true, if_false,
      Field.firstOf_canonBy Field.bytesKey_injective, Field.firstOf]

end Scratch
