namespace CarrierFixture
structure Queue where
  entries : List Nat
structure Holder where
  queue : Queue
  marker : Nat
def make (marker : Nat) : Holder := ⟨⟨[]⟩, marker⟩
def remark (holder : Holder) (marker : Nat) : Holder := { holder with marker }
def nonempty (value : Nat) : Holder := ⟨⟨[value]⟩, value⟩
end CarrierFixture
