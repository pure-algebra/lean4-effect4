import Lean
import Effect4.Api.Author

open Lean Meta Elab Command
namespace ReviewPrinting

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

run_cmd liftTermElabM do
  let ty := (← getConstInfo ``Effect4.Program.nativeReservedServiceTypes).type
  let plain ← withOptions (fun _ => {}) <| srcOf ty
  let notationOff ← withOptions (fun _ => ({} : Options).setBool `pp.notation false) <| srcOf ty
  logInfo m!"default: {plain}\nnotation disabled: {notationOff}"
  unless plain != notationOff do throwError "the selected type did not distinguish the options"
  let restored ← withOptions (fun _ => {}) <| srcOf ty
  unless plain == restored do throwError "restoring the profile did not restore the text"

end ReviewPrinting
