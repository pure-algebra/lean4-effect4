/-!
# Probe U — a copy of `Ty` with the wave's record constructor (question 3's boundary)

`Ty`'s twenty constructors and `record (fields : List (String × RecordTy))` appended, as row
119 gives it. Used only to run the fold generators on a nested block: the committed emitter's
nested path, and the extras emitter's refusal by name (`U/logs/gen-record.log`).
-/

namespace ProbeU

inductive RecordTy
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : RecordTy)
  | list (inner : RecordTy)
  | prod (left right : RecordTy)
  | except (error value : RecordTy)
  | exitOf (value error : RecordTy)
  | causeOf (error : RecordTy)
  | fiberOf (value error : RecordTy)
  | union (left right : RecordTy)
  | lit (value : String)
  | refOf (value : RecordTy)
  | deferredOf (value error : RecordTy)
  | var (index : Nat)
  | unknown
  | record (fields : List (String × RecordTy))

end ProbeU
