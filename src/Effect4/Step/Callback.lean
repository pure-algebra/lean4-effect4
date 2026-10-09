module

public import Effect4.Step

/-!
# A step as a callback of an existing operation

The connector freezes each captured source at the caller's scope and path.
One inserted slot relocates binders inside the captured term.
The existing operation supplies the current-value binder and emits the sole Eff syntax.
The connector introduces neither a cell nor an operation family.
The program checker still checks captured source types and the operation's required callback result.
An arbitrary run argument supplies no claim about its binders or behavior.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Modules.Step
open Effect4.Program Effect4.Program.Authoring

/-- Freeze a source before one callback binder enters its scope.
The weakening relocates the captured term's own binders. -/
def callbackCapture (source : TermSrc) (env : Env) (path : List Nat) : TermSrc :=
  fun _ _ => (source env path).map (Term.weaken env.names.length)

/-- Supply the callback's current value and its frozen outer inputs. -/
def callbackSources {C : Ty} {Γ : List Ty}
    (captures : {t : Ty} → Input Γ t → TermSrc) (env : Env) (path : List Nat)
    (current : TermSrc) : {t : Ty} → Input (C :: Γ) t → TermSrc
  | _, .here _ _ => current
  | _, .there _ x => callbackCapture (captures x) env path

/-- Supply a typed step to an existing form with one current-value binder.
Resolve captures before the form extends the caller's scope.
The form remains responsible for the callback's result shape. -/
def callback {Op : Type} {C R : Ty} {Γ : List Ty}
    (body : Step (C :: Γ) R)
    (captures : {t : Ty} → Input Γ t → TermSrc)
    (run : (TermSrc → TermSrc) → Src Op) : Src Op :=
  fun env path =>
    run (fun current => body.term (callbackSources captures env path current)) env path

end Effect4.Modules.Step
