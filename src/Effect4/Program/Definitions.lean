module

public import Effect4.Program.Checker

/-!
# Program.Definitions — the definition block of a program, checked at its root

A **definition** is a closed program with a declared row (`DefDecl`, `Program/Eff.lean`). A
program keeps its definitions in one **definition block** at its root (`Eff.defs`), before its
main program. An **invocation** is a `perform` of the operation that names a definition
(`NativeOp.call k`), so the row check types it by the definition's declared row, as it types
any row (decisions row 328).

## The block's signature

`Signature.withDefs` extends a signature by a block: the invocation of definition `k` reads the
row that definition `k` declares, and it is in the domain exactly when the block has a
definition `k`. Every other operation reads the signature's own row and domain. A signature
says which operations are invocations by its field `callOf`. Outside a block an invocation is
outside the domain (`nativeSignature`), so the checker refuses it as `outsideDomain`.

## The whole module's check

`Checker.checkModule` checks a program at its root. At a block it checks each body against its
declaration, at the block's signature, and then the main program at the same signature. A body
reads one variable, the request, so it is checked at the environment of its declared request.
Recursion is typed by declaration: a body reads the declared rows of the whole block and never
another body. Any program with no block is checked as the checker checks it. A block below the
root is refused by the checker's own arm (`TypeReason.definitionBlock`).

The paths follow the node's children (`Node.child`): the bodies are child `0` and the main
program child `1`, and in the bodies' spine the head is child `0` and the rest child `1`. So
the body of definition `k` stands at `0 :: List.replicate k 1 ++ [0]`.

The whole program's typing is this check after the layer references (`typeOfProgram`,
`Program/Typing.lean`), and the program interface's located refusal is its refusal
(`Api.explain`). On a program with no block the check is the checker's own
(`checkModule_eq_check`, `Laws/Program/Definitions.lean`).

## What this module does not establish

- That a program with a block runs: the frame machine, the reference machine and the session
  meet a block in slice PROC-2 (decisions row 328, point 5).
- That a definition's declared row is inhabited (decisions row 127), or that its body
  terminates: a body that invokes itself without end runs to the frontier of its budget.
- Anything of generic definitions: the first stage's declarations are closed.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-- **A block's signature** (decisions row 328): the invocation of definition `k` reads the row
that definition `k` declares, in normal form. It is in the domain exactly when the block has a
definition `k` with no parameter whose value is a program: a definition with one is invoked by
`Eff.invoke`, which reads its declaration (`defOf`, decisions row 340). Every other operation
reads the signature's own row and domain. -/
def Signature.withDefs (sig : Signature Op) (decls : List DefDecl) : Signature Op :=
  { sig with
    rowOf := fun op => match sig.callOf op with
      | some k => match decls[k]? with
        | some d => d.row.normalizeTypes
        | none => sig.rowOf op
      | none => sig.rowOf op
    dom := fun op => match sig.callOf op with
      | some k => decls[k]?.any (·.params.isEmpty)
      | none => sig.dom op
    defOf := fun k => decls[k]?.or (sig.defOf k) }

/-- **A body's signature** (decisions row 340): the run of parameter `i` reads the row that
parameter `i` declares, in normal form, and it is in the domain exactly when the definition has a
parameter `i`. Every other operation reads the signature's own row and domain. At no parameter
the signature is unchanged, so a body with no parameter is checked as before: a signature built
on `nativeSignature` keeps every run of a parameter outside its domain. -/
def Signature.withParams (sig : Signature Op) : List ParamDecl → Signature Op
  | [] => sig
  | q :: qs =>
    { sig with
      rowOf := fun op => match sig.paramOf op with
        | some i => match (q :: qs)[i]? with
          | some d => d.row.normalizeTypes
          | none => sig.rowOf op
        | none => sig.rowOf op
      dom := fun op => match sig.paramOf op with
        | some i => decide (i < (q :: qs).length)
        | none => sig.dom op }

/-- A parameter of the first stage: its three type columns are closed, and the error alphabet
admits its error column (decisions row 340). -/
def ParamDecl.formed (d : ParamDecl) : Bool :=
  d.request.closed && d.answer.closed && d.error.closed && admittedErrTy d.error.normalize

namespace DefDecl

/-- A declaration of the first stage: its three type columns and each parameter's are closed,
and the error alphabet admits its error column and each parameter's. -/
def formed (d : DefDecl) : Bool :=
  d.request.closed && d.answer.closed && d.error.closed && admittedErrTy d.error.normalize &&
    d.params.all ParamDecl.formed

/-- A body's type is below its declaration: its answer and its error below the declared ones in
the checker's order, and its requirement row inside the declared one. -/
def admits (d : DefDecl) (t : EffTy) : Bool :=
  Ty.sub t.answer.normalize d.answer.normalize && Ty.sub t.error.normalize d.error.normalize &&
    decide (t.requires.Subset (Requirement.ofList d.requires))

end DefDecl

namespace Checker

/-- Check the bodies of a block at a signature, in order: each declaration is formed, and each
body, checked at the environment of its declared request and at the signature extended by its
parameters (`Signature.withParams`), is below its declaration. `p` is the path of the spine
node; the body is its child `0` and the rest of the spine its child `1`. -/
def checkBodies (sig : Signature Op) (p : List Nat) :
    List DefDecl → Effs Op → Except TypeRefusal Unit
  | d :: ds, .cons body rest => do
    unless d.formed do throw ⟨p ++ [0], .definitionColumns d.name⟩
    let t ← check (sig.withParams d.params) [d.request.normalize] (p ++ [0]) body
    unless d.admits t do throw ⟨p ++ [0], .bodyNotDeclared d.name t⟩
    checkBodies sig (p ++ [1]) ds rest
  | _, _ => pure ()

/-- **The whole module's check** (decisions row 328). At a definition block it checks the
declarations and the bodies, then the main program, each at the block's signature; the main
program's type is the module's. Any program with no block is checked as `check` checks it. -/
def checkModule (sig : Signature Op) : Eff Op → Except TypeRefusal EffTy
  | .defs decls bodies main => do
    unless decls.length = bodies.toList.length do
      throw ⟨[], .definitionsMismatch decls.length bodies.toList.length⟩
    let sig' := sig.withDefs decls
    checkBodies sig' [0] decls bodies
    check sig' [] [1] main
  | e => check sig [] [] e

end Checker

/-- The declarations of a program's definition block: the block's own at its root, none for a
program with no block. A block's program is checked at its signature extended by them
(`Signature.withDefs`). -/
def Eff.defsOf : Eff Op → List DefDecl
  | .defs decls _ _ => decls
  | _ => []

end Effect4.Program
