import Lean.PrettyPrinter

/-! One presentation policy for claim statements, graph statements and hypotheses.
Lean supplies delaboration, parentheses and formatting; these display bytes are not proof
evidence. See the metaprogramming book's Extra: Pretty Printing and the pinned toolchain's
Lean/PrettyPrinter.lean:20–45. No custom notation or unexpander is registered globally. -/
namespace Tools.Semantics.Display
open Lean Meta

private def options (opts : Options) : Options := Id.run do
  let mut result := opts
  for (key, _) in opts do
    if (`pp).isPrefixOf key then result := result.erase key
  return result.setBool `pp.fullNames true

def expression (e : Expr) : MetaM String :=
  withOptions options do
    return (← PrettyPrinter.ppExpr e).pretty 100

end Tools.Semantics.Display
