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
invocation's path, or at the passed program's when its own row needs a service
(`PrintRefusal.callbackRequirement`, `Api.emitModule`).

The check annotates each body of the block at its signature and its request, and the main program
at the block's signature (`annotate`, `Program/Typing/Annotate.lean`), and reads the row the
checker answers at each invocation. It is a target profile's boundary: it states no typing law,
and the checker's verdict is unchanged.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4.Program

variable {Op : Type}

/-- The first program an invocation passes whose checked requirement row is not empty, by its
path: program `j` stands at child `0` of the spine's `j`-th node, under the invocation's child `0`
(`argSitesAt`, `Program/Compile.lean`). The printed parameter type requires nothing, so such a
program is a target error even when the definition declares the service (seat 3B's finding). -/
def passedRequirementFault (entries : List Table.Entry) (at_ : List Nat) (count : Nat) :
    Option (List Nat) :=
  (List.range count).findSome? fun j =>
    let q := at_ ++ [0] ++ List.replicate j 1 ++ [0]
    entries.findSome? fun a =>
      if a.path = q then
        match a.result with
        | some (.ok t) =>
          if decide (t.requires = Effect4.Machine.Env.Requirement.empty) then none else some q
        | _ => none
      else none

/-- **An invocation whose programs need a service**, the first at its path in the block: an
invocation whose checked requirement row is more than its definition's declared row, at the
invocation; or a passed program whose own row is not empty, at the program
(`passedRequirementFault`). A program that declares no definition has no invocation the checker
admits. -/
def invokeRequirementFault (sig : Signature Op) : Eff Op → Option (List Nat)
  | .defs [] _ _ _ => none
  | .defs decls bodies main _ =>
    let sig' := sig.withDefs decls
    let fault (s : Signature Op) (env : TyEnv) (base : List Nat) (p : Eff Op) :
        Option (List Nat) :=
      let entries := annotate s env p
      entries.findSome? fun e =>
        match (Node.eff p).at_ e.path, e.result with
        | some (.eff (.invoke k _ args)), some (.ok t) =>
          match sig'.defOf k with
          | some d =>
            if decide (t.requires = Effect4.Machine.Env.Requirement.ofList d.requires) then
              (passedRequirementFault entries e.path args.toList.length).map (base ++ ·)
            else some (base ++ e.path)
          | none => none
        | _, _ => none
    ((decls.zip bodies.toList).zipIdx.findSome? fun (pair, k) =>
        fault (sig'.withParams pair.1.params) [pair.1.request] (0 :: List.replicate k 1 ++ [0])
          pair.2) <|>
      fault sig' [] [1] main
  | _ => none

end Effect4.Codegen
