import OCaml5.Eff.Goldens
import Effect4.Store.Domain.Derived.Program
import Effect4.Store.Domain.ShapeJson
open Effect4 Effect4.Program
#eval (OCaml5.Eff.effV (.succeed (.lit (.nat 1)))).json
#eval do
  let j := Effect4.Store.Canonical.print (α := NativeEff) (.succeed (.lit (.nat 1)))
  let bytes := Effect4.NatJson.render (Effect4.NatJson.ofBinary64 j)
  return String.ofList (bytes.map Char.ofNat)
