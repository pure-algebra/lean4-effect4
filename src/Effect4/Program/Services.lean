module

public import Effect4.Program.Eff
public import Effect4.Codegen.Refusal

/-!
# Program.Services — a block's services and the formation of its roles

`servicesOf` reads the definitions' roles without a target. `serviceFaultIn` checks those roles
under a profile of names. `anyName` checks the program domain alone. The TypeScript printer
supplies its own profile and keeps its refusal order (`src/Effect4/Codegen/Print.lean`).

This module imports only the program syntax and the refusal alphabet. It imports no target
syntax or printer. `NameProfile` is executable configuration, not canonical program content.
The view establishes neither program admission nor the meaning of a service method.
-/

@[expose] public section

set_option autoImplicit false

namespace Effect4.Program

/-- A service of a block: its name, its initial program's position, and its methods, each with
its name, its definition's position and its arity. -/
structure Service where
  name : String
  init : Nat
  methods : List (String × Nat × Nat)
deriving DecidableEq, Repr

/-- The method of service `s` that the definition at position `j` is, if it is one. -/
def methodAt (s : String) (defs : List DefDecl) (j : Nat) : Option (String × Nat × Nat) :=
  match defs[j]? with
  | some d =>
    match d.role with
    | .serviceMethod s' m n => if s' = s then some (m, j, n) else none
    | _ => none
  | none => none

/-- The methods of service `s` in a block, in block order. -/
def serviceMethods (s : String) (defs : List DefDecl) : List (String × Nat × Nat) :=
  (List.range defs.length).filterMap (methodAt s defs)

/-- The service whose initial program is the definition at position `i`, if it is one. -/
def serviceAt (defs : List DefDecl) (i : Nat) : Option Service :=
  match defs[i]? with
  | some d =>
    match d.role with
    | .serviceInit s => some ⟨s, i, serviceMethods s defs⟩
    | _ => none
  | none => none

/-- The services a block's roles declare, in the order of their initial programs. -/
def servicesOf (defs : List DefDecl) : List Service :=
  (List.range defs.length).filterMap (serviceAt defs)

/-- A method's arguments after the state: `arity` types read off the rest of its request. -/
def methodArgTys : Nat → Ty → Option (List Ty)
  | 0, _ => some []
  | 1, t => some [t]
  | n + 2, .prod a b => (methodArgTys (n + 1) b).map (a :: ·)
  | _ + 2, _ => none

/-- A method's arguments, from its definition's request and the service's state type. -/
def methodArgs (state : Ty) (d : DefDecl) (arity : Nat) : Option (List Ty) :=
  match arity, d.request with
  | 0, request => if request = state then some [] else none
  | n + 1, .prod first rest => if first = state then methodArgTys (n + 1) rest else none
  | _ + 1, _ => none

/-- Whether a definition is a method of a service that the block does not declare. -/
def strayMethod (names : List String) (d : DefDecl) : Bool :=
  match d.role with
  | .serviceMethod s _ _ => !names.contains s
  | _ => false

/-- The first name of a list that a later one repeats, if one does. -/
def repeatOf : List String → Option String
  | [] => none
  | n :: rest => if rest.contains n then some n else repeatOf rest

/-- The refusal of the first definition that is a method of a service the block does not
declare (`strayMethod`), by the definition and the service it names. -/
def strayOf (names : List String) : List DefDecl → Option PrintRefusal
  | [] => none
  | d :: ds =>
    match d.role with
    | .serviceMethod s _ _ => if names.contains s then strayOf names ds else some (.strayMethod d.name s)
    | _ => strayOf names ds

/-- **The names a target accepts beside a block's services**.
This executable configuration is not stored program syntax. -/
structure NameProfile where
  /-- a fault among the definitions' names, in a block with a service -/
  defNameFault : List DefDecl → Option String
  /-- the constants a service declares, which no two services may share -/
  serviceConsts : String → List String
  /-- a method name the target accepts -/
  method : String → Bool
  /-- whether a service's constants collide with the block's definitions or names -/
  collides : List DefDecl → String → Bool

/-- **The program domain's profile**: a service is named by its own name, and no name is a
target's business. -/
def anyName : NameProfile where
  defNameFault _ := none
  serviceConsts s := [s]
  method _ := true
  collides _ _ := false

/-- One service's fault under a profile: `serviceFaultOf` with its name checks read from the
profile. -/
def serviceFaultOfIn (p : NameProfile) (defs : List DefDecl) (sv : Service) : Option PrintRefusal :=
  match defs[sv.init]? with
  | none => some (.service sv.name)
  | some init =>
    if init.request ≠ .unit || !init.params.isEmpty then some (.service sv.name)
    else if !(sv.methods.map (·.1)).Nodup || sv.methods.isEmpty ||
        sv.methods.any (fun x => !p.method x.1) then some (.service sv.name)
    else if p.collides defs sv.name then
      some (.service sv.name)
    else sv.methods.findSome? fun (m, j, n) =>
      match defs[j]? with
      | some d =>
        if (methodArgs init.answer d n).isSome then none
        else some (.serviceMethod sv.name m)
      | none => some (.serviceMethod sv.name m)

/-- **A block's service fault under a profile**: `serviceFault` with its name checks read from
the profile. -/
def serviceFaultIn (p : NameProfile) (defs : List DefDecl) : Option PrintRefusal :=
  match p.defNameFault defs with
  | some n => some (.serviceName n)
  | none =>
  match repeatOf ((servicesOf defs).flatMap fun sv => p.serviceConsts sv.name) with
  | some n => some (.serviceName n)
  | none =>
  match strayOf ((servicesOf defs).map (·.name)) defs with
  | some why => some why
  | none => (servicesOf defs).findSome? (serviceFaultOfIn p defs)

end Effect4.Program
