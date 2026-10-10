import Effect4.Program.Typing.Annotate
import Effect4.Program.Definitions
import Effect4.Codegen.PrintLeaf

/-!
# Codegen.CallbackRequirements — a callback's service row, refused at the target

A definition's header prints each parameter's type with the requirement row `never`
(`paramType`, `Codegen/Print.lean`). The checker lets a program passed to a parameter need a
service: the invocation's row is its definition's and its programs' (`Checker.check`'s `invoke`
arm). tsgo refuses such a call against the printed header (Codex's HO3-REQ-01). Until the target
binds a requirement variable on the header, the application face refuses the module at the
invocation's path (`PrintRefusal.callbackRequirement`, `Api.emitModule`).

The check annotates each body of the block at its signature and its request, and the main program
at the block's signature (`annotate`, `Program/Typing/Annotate.lean`), and reads the row the
checker answers at each invocation. It is a target profile's boundary: it states no typing law,
and the checker's verdict is unchanged.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4.Program

variable {Op : Type}

/-- **An invocation whose programs need a service**, the first at its path in the block: an
invocation whose checked requirement row is more than its definition's declared row. A program
that declares no definition has no invocation the checker admits. -/
def invokeRequirementFault (sig : Signature Op) : Eff Op → Option (List Nat)
  | .defs [] _ _ _ => none
  | .defs decls bodies main _ =>
    let sig' := sig.withDefs decls
    let fault (s : Signature Op) (env : TyEnv) (base : List Nat) (p : Eff Op) :
        Option (List Nat) :=
      (annotate s env p).findSome? fun e =>
        match (Node.eff p).at_ e.path, e.result with
        | some (.eff (.invoke k _ _)), some (.ok t) =>
          match sig'.defOf k with
          | some d =>
            if decide (t.requires = Effect4.Machine.Env.Requirement.ofList d.requires) then none
            else some (base ++ e.path)
          | none => none
        | _, _ => none
    ((decls.zip bodies.toList).zipIdx.findSome? fun (pair, k) =>
        fault (sig'.withParams pair.1.params) [pair.1.request] (0 :: List.replicate k 1 ++ [0])
          pair.2) <|>
      fault sig' [] [1] main
  | _ => none

end Effect4.Codegen
