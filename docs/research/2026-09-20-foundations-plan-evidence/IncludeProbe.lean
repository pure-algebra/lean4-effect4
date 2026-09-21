section
variable {n : Nat} (h : n = n)
include h
def probeDef : Nat := 0
theorem probeThm : True := trivial
#check @probeDef
#check @probeThm
end
