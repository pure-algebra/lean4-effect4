import OCaml5.Ml.Reflect
import OCaml5.Avatar.Part
import OCaml5.Avatar.Derived.Context

/-!
# OCaml5.Avatar.Context

**What it is.** The descriptions behind the generated block of `ocaml/avatar/deep_context.ml`,
the port of `src/Effect4/Machine/Context.lean` (seat F2).

**Depends on.** `OCaml5.Ml.Reflect`, `OCaml5.Avatar.Part`, `OCaml5.Avatar.Derived.Context`.

**Properties.**
* **Field and constructor order is the Lean order**, arity for arity — *tested* (`Check`).
* **The block is byte-identical to the one the avatar file carries** — *tested*
  (`ocaml/avatar/render-deep.sh`), executed.
-/

namespace OCaml5.Avatar

open OCaml5.Ml

/-! ## `src/Effect4/Machine/Context.lean` → `ocaml/avatar/deep_context.ml` (seat F2)

The first-order environment (M4a/M4b) and the machine's value alphabet. `Context`'s `keysNodup`
proof field is ERASED (F2-L2: a proof has no OCaml counterpart; `add`/`mergeEntries` keep the
invariant by construction). `Val` is generated as its own carrier `val_` (prefix `Cv`) so that
`encode`/`decode` and the hooks keep the Lean shape; `Deep_context.wire_of_val` is the projection
onto the avatar's wire alphabet, the W1-1 row. `Requirement` (`Row ServiceKey`) is the strictly
ascending key list; `ServiceProgram`/`UsesOnly`/`interpret` (an `Effects` free program) refuse. -/


namespace Context

def subst : Subst :=
  [("FiberId", Ty.int),
   ("ServiceKey", Ty.named "service_key"),
   ("ServiceName", Ty.int),
   ("ServiceTypeCode", Ty.int),
   ("Err", Ty.named "err"),
   ("Defect", Ty.named "defect"),
   ("Ann", Ty.unit),
   ("Val", Ty.named "val_"),
   ("Ctx", Ty.named "context"),
   ("Context", Ty.named "context"),
   ("Service", Ty.named "service"),
   ("Reference", Ty.named "reference"),
   ("Requirement", Ty.list (Ty.named "service_key")),
   ("CauseV", Ty.named "cause_v"), ("Cause", Ty.named "cause_v"),
   ("ExitV", Ty.named "exit_v"), ("Exit", Ty.named "exit_v"),
   ("ServiceKey.Carrier", Ty.named "val_")]

private def keyL : LTy := .nm "ServiceKey"
private def valL : LTy := .nm "Val"

def serviceKey : StructDesc where
  leanName := "ServiceKey"; site := "Context/Key.lean:79"; subst := subst
  fields := [{ leanName := "name", leanTy := .nm "ServiceName" },
             { leanName := "service", leanTy := .nm "ServiceTypeCode" }]
/-- `Service U` (`Context.lean:89`): the key and its carrier value, `Val` at `ValU`. -/
def service : StructDesc where
  leanName := "Service"; site := "Context.lean:89"; subst := subst
  fields := [{ leanName := "key", leanTy := keyL }, { leanName := "value", leanTy := valL }]
/-- `Context U` (`Context.lean:180`): the insertion-ordered entries; the proof field erased. -/
def context : StructDesc where
  leanName := "Context"; site := "Context.lean:180"; subst := subst
  fields := [{ leanName := "entries", leanTy := .lst (.nm "Service") },
             { leanName := "keysNodup", leanTy := .unit,
               kind := .erased "a proof (`(entries.map Service.key).Nodup`); kept by construction (F2-L2)" }]
/-- `Reference U` (`Context.lean:406`). -/
def reference : StructDesc where
  leanName := "Reference"; site := "Context.lean:406"; subst := subst
  fields := [{ leanName := "key", leanTy := keyL }, { leanName := "default", leanTy := valL }]
def err : InductiveDesc where
  leanName := "Err"; site := "Context.lean:772"; ctorPrefix := "Ce"; subst := subst
  ctors := [{ leanName := "boom" }, { leanName := "tag", args := [⟨"code", .nat, false⟩] }]
def defect : InductiveDesc where
  leanName := "Defect"; site := "Context.lean:781"; ctorPrefix := "Cx"; subst := subst
  ctors := [{ leanName := "notImplemented" }, { leanName := "asyncFiber" }, { leanName := "badName" },
            { leanName := "serviceNotFound", args := [⟨"key", keyL, false⟩] },
            { leanName := "unknownLayer", args := [⟨"index", .nat, false⟩] }]
/-- `Val` (`Context.lean:797`), fifteen constructors, prefix `Cv`. -/
def val : InductiveDesc where
  leanName := "Val"; site := "Context.lean:797"; ctorPrefix := "Cv"; subst := subst
  ctors := [{ leanName := "unit" }, { leanName := "nat", args := [⟨"n", .nat, false⟩] },
            { leanName := "bool", args := [⟨"b", .bool, false⟩] },
            { leanName := "fiber", args := [⟨"id", .nm "FiberId", false⟩] },
            { leanName := "fibers", args := [⟨"ids", .lst (.nm "FiberId"), false⟩] },
            { leanName := "scopeHandle", args := [⟨"scope", .nat, false⟩] },
            { leanName := "memoMap", args := [⟨"id", .nat, false⟩] },
            { leanName := "promise", args := [⟨"cell", .nat, false⟩] },
            { leanName := "pair", args := [⟨"first", valL, false⟩, ⟨"second", valL, false⟩] },
            { leanName := "exitOk", args := [⟨"value", valL, false⟩] },
            { leanName := "exitErr", args := [⟨"cause", .nm "CauseV", false⟩] },
            { leanName := "exitNil" },
            { leanName := "exitCons", args := [⟨"head", valL, false⟩, ⟨"tail", valL, false⟩] },
            { leanName := "ctxNil" },
            { leanName := "ctxCons", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩, ⟨"rest", valL, false⟩] }]
def contextUpdate : InductiveDesc where
  leanName := "ContextUpdate"; site := "Context.lean:1005"; ctorPrefix := "Cu"; subst := subst
  ctors := [{ leanName := "setTo", args := [⟨"context", .nm "Ctx", false⟩] },
            { leanName := "provide", args := [⟨"that", .nm "Ctx", false⟩] },
            { leanName := "provideService", args := [⟨"key", keyL, false⟩, ⟨"value", valL, false⟩] }]

def structs : List StructDesc := [serviceKey, service, context, reference]
def inductives : List InductiveDesc := [err, defect, val, contextUpdate]

def generated : List Decl :=
  [.comment ("Generated by OCaml5.Ml (`Render.lean`, seat W1). Do not edit; edit the"
      ++ " descriptions (`Ml.Deep.Context`, seat F2).\n   One declaration per `Effect4/Deep/Context.lean`"
      ++ " carrier (and `ServiceKey` of `Context/Key.lean`), same field and constructor order."),
   serviceKey.header, renameDecl "service_key" serviceKey.decl,
   err.header, renameDecl "err" err.decl,
   defect.header, renameDecl "defect" defect.decl,
   .comment "`CauseV`/`ExitV` (`Context.lean:829-832`) over this `Err`/`Defect`: the avatar's `cause`/`exitv` carry the wire's `int` error and `string` defect (W1-1); the aliases name the site.",
   .rawD "type cause_v = cause",
   .rawD "type exit_v = exitv",
   .comment "`Val`, `Service ValU` and `Context ValU` are one mutually recursive group in OCaml (`ctxCons` names a key and a value; `Context` holds services).",
   val.header, renameDecl "val_" val.decl,
   service.header, renameDecl "service" service.decl,
   context.header, renameDecl "context" context.decl,
   reference.header, renameDecl "reference" reference.decl,
   contextUpdate.header, renameDecl "context_update" contextUpdate.decl]


/-- The descriptions under the projection guard, in the order the report prints. -/
def all : List TypeDesc := [.struct serviceKey, .struct service, .struct context, .struct reference, .induct err, .induct defect, .induct val, .induct contextUpdate]

/-- `deep_context.ml` as a part of the avatar. -/
def part : Part :=
  { name := "context", file := "deep_context.ml", guarded := all, derived := Derived.Context.all,
    generated := generated }

end Context

end OCaml5.Avatar
