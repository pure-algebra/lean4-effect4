import ProbeQV.Val
/-! Seat Q, the `Val` append (T's commit 3): the two frames' bytes, their round trips, a refusal
each, and the codec laws of the copy with their axioms. -/
open ProbeQV Effect4.Store

#guard (Val.int 5).encode = [13, 0,0,0,0,0,0,0,2, 0, 5]
#guard (Val.int (-1)).encode = [13, 0,0,0,0,0,0,0,1, 1]
#guard (Val.int 0).encode = [13, 0,0,0,0,0,0,0,1, 0]
#guard (Val.float ⟨0x3FF0000000000000⟩).encode = [14, 0,0,0,0,0,0,0,8, 0x3F, 0xF0, 0,0,0,0,0,0]
#guard [Val.int 5, .int (-1), .int (-300), .int 0, .float ⟨0⟩, .float ⟨0xFFFFFFFFFFFFFFFF⟩,
    .list [.int 3, .float ⟨7⟩]].all fun v => Val.decode v.encode == Option.some v
-- refusals: a sign byte other than 0 or 1, a leading zero digit, a short binary64 payload
#guard Val.decode [13, 0,0,0,0,0,0,0,2, 2, 5] = Option.none
#guard Val.decode [13, 0,0,0,0,0,0,0,2, 0, 0] = Option.none
#guard Val.decode [14, 0,0,0,0,0,0,0,7, 0,0,0,0,0,0,0] = Option.none
-- the old frames keep their bytes (the tree's `Val.encode (.nat 256)` guard, restated)
#guard (Val.nat 256).encode = [2, 0,0,0,0,0,0,0,2, 1, 0]

#print axioms Val.decode_encode
#print axioms Val.decode_exact
#print axioms Val.encode_injective
#print axioms Val.beq_iff
#print axioms Val.ind
