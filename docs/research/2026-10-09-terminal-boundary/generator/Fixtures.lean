namespace DeviceFoldFixture

mutual
inductive Stem where
  | tip (leaf : Leaf)
inductive Leaf where
  | value (n : Nat)
end

mutual
inductive Branch where
  | stop
  | next (twig : Twig) (tag : Tag)
inductive Twig where
  | stop
  | next (branch : Branch)
inductive Tag where
  | value (n : Nat)
end

end DeviceFoldFixture
