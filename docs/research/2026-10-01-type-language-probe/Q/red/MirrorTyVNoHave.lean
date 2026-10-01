import OCaml5.Eff.Goldens
import ProbeQW.Ty
/-! Seat Q, question 5, red control (expected to FAIL): `tyV` over the wave family with the record
arm written as the other list arms are (`attach` alone, no `have`). Lean cannot show termination
at the field triple, so every recursive mirror's record arm carries the field-size lemma. -/
set_option autoImplicit false
open Lean ProbeQW
open OCaml5.Eff (V)

def tyVNoHave : Ty → V
  | .never => .ctor ``Ty.never []
  | .unknown => .ctor ``Ty.unknown []
  | .unit => .ctor ``Ty.unit []
  | .nat => .ctor ``Ty.nat []
  | .int => .ctor ``Ty.int []
  | .string => .ctor ``Ty.string []
  | .bool => .ctor ``Ty.bool []
  | .handle target => .ctor ``Ty.handle [.str target]
  | .option inner => .ctor ``Ty.option [tyVNoHave inner]
  | .list inner => .ctor ``Ty.list [tyVNoHave inner]
  | .prod l r => .ctor ``Ty.prod [tyVNoHave l, tyVNoHave r]
  | .except e v => .ctor ``Ty.except [tyVNoHave e, tyVNoHave v]
  | .exitOf v e => .ctor ``Ty.exitOf [tyVNoHave v, tyVNoHave e]
  | .causeOf e => .ctor ``Ty.causeOf [tyVNoHave e]
  | .fiberOf v e => .ctor ``Ty.fiberOf [tyVNoHave v, tyVNoHave e]
  | .union l r => .ctor ``Ty.union [tyVNoHave l, tyVNoHave r]
  | .lit s => .ctor ``Ty.lit [.str s]
  | .refOf v => .ctor ``Ty.refOf [tyVNoHave v]
  | .deferredOf v e => .ctor ``Ty.deferredOf [tyVNoHave v, tyVNoHave e]
  | .var i => .ctor ``Ty.var [.nat i]
  | .record fs => .ctor ``Ty.record [.list (fs.attach.map fun ⟨(n, t, o), _⟩ => .pair (.str n) (.pair (tyVNoHave t) (.bool o)))]
  | .map k v => .ctor ``Ty.map [tyVNoHave k, tyVNoHave v]
  | .tuple xs => .ctor ``Ty.tuple [.list (xs.attach.map fun ⟨x, _⟩ => tyVNoHave x)]
  | .app n xs => .ctor ``Ty.app [.str n, .list (xs.attach.map fun ⟨x, _⟩ => tyVNoHave x)]
  | .null => .ctor ``Ty.null []
  | .undefined => .ctor ``Ty.undefined []
  | .number => .ctor ``Ty.number []
  | .bytes => .ctor ``Ty.bytes []
