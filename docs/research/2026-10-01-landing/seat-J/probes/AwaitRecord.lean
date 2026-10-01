import Effect4.Api.RunnerBytes

/-! Seat J, step 4: what row 16 changes at the boundary. The tuple `Await` was
`FiberId × Nat × NativeOp × Val`, whose generic codec (`instCanonicalProd`) writes nested pairs with
no field name; the structure's generated codec writes one record whose fields are named. Both
shapes are computed here from the instances in the tree after the change: the tuple's from the
generic pair instance, the record's from `Api/RunnerDerived.lean`.
Run: `lake env lean -DwarningAsError=true docs/research/2026-10-01-landing/seat-J/probes/AwaitRecord.lean`. -/

open Effect4 Effect4.Store Effect4.Program

-- Before: nested pairs, three deep, no names.
#guard match (Canonical.shape (FiberId × Nat × NativeOp × Val)).root with
  | .pair _ (.pair _ (.pair _ _)) => true
  | _ => false

-- After: one record with the four field names, in declaration order.
#guard match (Canonical.shape Await).root with
  | .struct "Await" fields => fields.map (·.1) == ["fiber", "token", "op", "request"]
  | _ => false

-- The list a runner reports (`outstandingBytes`, `RunnerBytes.schemas`'s "Outstanding") is a list
-- of those records.
#guard match (Canonical.shape (List Await)).root with
  | .list (.named "Await") => true
  | .list (.struct "Await" _) => true
  | _ => false
