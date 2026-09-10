import Effect4.Laws.Program.ValueModel

namespace Test.Program.ValueModelContract
open Effect4 Effect4.Program Effect4.Store

def nested := ValueModel.option (ValueModel.option ValueModel.nat)
def pair := ValueModel.pair ValueModel.nat ValueModel.bool

#guard nested.type.toRaw = Ty.option (Ty.option Ty.nat)
#guard nested.image.toVal none != nested.image.toVal (some none)
#guard pair.image.toVal (7, true) = .list [.nat 7, .bool true]
#guard (Image.pair Image.nat Image.bool).toVal (7, true) != pair.image.toVal (7, true)
#guard (Image.sum Image.nat Image.nat).toVal (.inl 3) !=
  (Image.sum Image.nat Image.nat).toVal (.inr 3)
#guard (Image.except Image.nat Image.bool).ofVal (.ctor 1 [.bool true]) = some (.ok true)
#guard (Image.except Image.nat Image.bool).ofVal (.ctor 1 [.nat 3]) = none

theorem nested_member (allocated : List String) (n : Nat) :
    Program.Val.hasTy (nested.image.toVal (some (some n))) nested.type.toRaw allocated = true :=
  nested.member allocated (some (some n)) trivial

#print axioms nested_member
#print axioms ValueModel.ofImage
#print axioms ValueModel.list
#print axioms ValueModel.pair
#print axioms Image.sum
#print axioms Image.except

end Test.Program.ValueModelContract
