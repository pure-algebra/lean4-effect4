module

public import Effect4.Program.Typing.Call

/-!
# Program.Typing.Parts — the readers at an address of a whole program, with its block

**The question.** The focus, the call instance and the call table answer at an address of a
program checked at one signature (`focusAt`, `callAt`). A whole program is typed by
the module check (`Checker.checkModule`, `Program/Definitions.lean`, decisions row 328). At a
definition block it checks each body at the block's signature and its declared request. It
checks the main program at the block's signature and the empty environment. A reader that walks
a block at one signature reaches nothing inside it, because the checker refuses a block
(`TypeReason.definitionBlock`). So a session's call table was empty for every program with a
block (seat HOST, `docs/research/2026-10-08-host-authoring-boundary.md` §5.4; decisions row 333).

## The parts

A **part** of a program is a sub-program that the module check checks on its own, with the
signature and the environment that it is checked at (`Part`). A program with no block is one
part, itself. A block has one part for each body and one for the main program. `Eff.partAt`
answers the part that holds an address, and the rest of the address inside it. The body of
definition `k` stands at `0 :: List.replicate k 1 ++ [0]`, and the main program at `[1]`.

## The readers

`programFocusAt` and `programCallAt` are `focusAt` and `callAt` at the part that holds the
address. `programCalls` lists every call of the program with its instance. A typed program with
no block is its own part at every address (`Eff.partAt_of_hasTy`,
`Laws/Program/Typing/Parts.lean`). The session's call table is `programCalls`
(`Api.HostSession.callTable`).

## The laws

`Laws/Program/Typing/Parts.lean` has them:

- the part holds the node at the address (`Eff.partAt_at`);
- where `programCallAt` answers, the node is a call, typed at its part's signature
  (`programCallAt_rowTy`);
- on a program that the module check admits, `programCallAt` answers at every call
  (`checkModule_programCallAt`, the claim `block-call-instance`), and so does the session
  (`Api.HostSession.instanceAt_complete`);
- the call table's lookup is `programCallAt` (`lookup_programCalls`).

## What this module is not

- It is not a second checker. Each reader calls its structural reader on one part.
- A block below the root has no part: the checker refuses it, and no reader answers inside it.
- The root of a block and the nodes of its bodies' spine are no part's address.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

variable {Op : Type}

/-- **A part of a program**: a sub-program that the module check checks on its own, with the
signature and the environment that it is checked at (`Checker.checkModule`). -/
structure Part (Op : Type) where
  /-- the signature that the part is checked at: the block's, inside a block -/
  sig : Signature Op
  /-- the environment that the part is checked at: a body's declared request, or the root's -/
  env : TyEnv
  /-- the sub-program -/
  program : Eff Op

/-- **The body that holds an address of a block's bodies' spine**, at the block's signature
`sig`, and the rest of the address inside it. In the spine the head is child `0` and the rest
child `1`, as in `Checker.checkBodies`. -/
def Part.bodyAt (sig : Signature Op) :
    List DefDecl → Effs Op → List Nat → Option (Part Op × List Nat)
  | d :: _, .cons body _, 0 :: rest => some (⟨sig, [d.request.normalize], body⟩, rest)
  | _ :: ds, .cons _ bodies, 1 :: rest => bodyAt sig ds bodies rest
  | _, _, _ => none

/-- **The part that holds an address of a program**, and the rest of the address inside it. At
a root block: a body at the block's signature and its declared request (`Part.bodyAt`), or the
main program at the block's signature and the empty environment, as the module check checks
them. Any other program is one part, at the signature `s` and the root's environment `env0`.
The root of a block holds no part. -/
def Eff.partAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (Part Op × List Nat) :=
  match p with
  | .defs decls bodies main =>
    match path with
    | 0 :: rest => Part.bodyAt (s.withDefs decls) decls bodies rest
    | 1 :: rest => some (⟨s.withDefs decls, [], main⟩, rest)
    | _ => none
  | _ => some (⟨s, env0, p⟩, path)

/-- **The focus at an address of a whole program**: `focusAt` at the part that holds it. -/
def programFocusAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (Focus Op) :=
  (p.partAt s env0 path).bind fun (part, rest) => focusAt part.sig part.env part.program rest

/-- **The checked instance of the call at an address of a whole program**: `callAt` at the part
that holds it. On a program that the module check admits, it answers at every call
(`checkModule_programCallAt`, `Laws/Program/Typing/Parts.lean`). -/
def programCallAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) (path : List Nat) :
    Option (CallInstance Op) :=
  (p.partAt s env0 path).bind fun (part, rest) => callAt part.sig part.env part.program rest

/-- **Every call of a whole program with its checked instance**, in the order of the address
table. Its lookup is `programCallAt` (`lookup_programCalls`). -/
def programCalls (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    List (List Nat × CallInstance Op) :=
  (Node.addresses (.eff p)).filterMap fun a => (programCallAt s env0 p a).map fun c => (a, c)

end Effect4.Program
