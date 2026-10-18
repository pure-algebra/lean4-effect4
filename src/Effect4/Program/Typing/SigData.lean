import Effect4.Program.Typing.Source
set_option autoImplicit false
deriving instance DecidableEq for Effect4.Program.SigApp

namespace Effect4.Program

open Effect4 Effect4.Store

/-! ## The signature at an address, as data -/

/-- Which part of a whole program an address is in, as data. -/
inductive PartSig where
  /-- the application's signature with the hole table -/
  | root
  /-- a block's main program or its module layers: the block's signature -/
  | block (decls : List DefDecl)
  /-- a block's body: the block's signature with the body's parameters -/
  | body (decls : List DefDecl) (params : List ParamDecl)
deriving DecidableEq, Repr

/-- The data that the signature at an address is derived from. -/
structure SigData where
  app : SigApp
  holes : RowTable
  part : PartSig
deriving DecidableEq

/-- The signature that the data spells. -/
def SigData.signature (d : SigData) : Signature NativeOp :=
  match d.part with
  | .root => (d.app.withHoles d.holes).signature
  | .block decls => (d.app.withHoles d.holes).signature.withDefs decls
  | .body decls ps => ((d.app.withHoles d.holes).signature.withDefs decls).withParams ps

/-- The index of the body that an address inside a block's bodies' spine names: each `1` steps
along the spine, and `0` enters the body. Path arithmetic only: no walk of the program. -/
def bodyIndex : List Nat → Option Nat
  | 0 :: _ => some 0
  | 1 :: rest => (bodyIndex rest).map (· + 1)
  | _ => none

/-- The part of an address, as data, read off the root's declarations and the path: a one-level
case analysis of the root (decisions row 143), no traversal. -/
def partSigAt (p : NativeEff) (path : List Nat) : PartSig :=
  match p, path with
  | .defs decls _ _ _, 0 :: rest =>
    match (bodyIndex rest).bind fun k => decls[k]? with
    | some d => .body decls d.params
    | none => .root
  | .defs decls _ _ _, 1 :: _ => .block decls
  | .defs decls _ _ (.cons _ _), 2 :: _ => .block decls
  | _, _ => .root

/-- The data at an address of a sketch. -/
def sketchSigData (s : Sketch) (app : SigApp) (path : List Nat) : SigData :=
  ⟨app, s.holes, partSigAt s.program path⟩

/-- The rows of the data's sketch signature. -/
def SigData.allRows (d : SigData) : RowTable := d.app.rows ++ d.holes

/-- **A prefix extension, decided**: the same services, named types and part, and rows that
extend the old rows at their end. -/
def SigData.extendsB (a b : SigData) : Bool :=
  decide (a.app.services = b.app.services) && decide (a.app.types = b.app.types) &&
    decide (a.part = b.part) && a.allRows.isPrefixOf b.allRows


end Effect4.Program
