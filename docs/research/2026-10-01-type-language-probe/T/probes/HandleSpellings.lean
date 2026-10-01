import Effect4.Codegen.Types
import Effect4.Schema.Bridge

/-!
# Seat T probe: what a rendered handle spelling cannot carry (tested on the tree's definitions)

Every Effect module type the corpus names as a type (`Queue.Dequeue<Job>`, `Stream.Stream<A>`,
`Duration.Duration`, `Redacted.Redacted<string>`, `Chunk.Chunk<A>`, `DateTime.Utc`, and TypeScript's
`null`/`undefined`) has, in today's `Ty`, only the opaque spelling `Ty.handle target` with the type
arguments rendered into `target` (`Ty.chunk`, `Program/Ty.lean:760-761`; `Ty.null`, `Ty.undefined`,
`Ty.duration`, `Ty.dateTime`, `:215-235`). Four consequences, each a `#guard` on the tree:
1. the printer's legacy grammar refuses an object type inside a handle (`Codegen/Types.lean:18-21`),
   so once records exist a handle over a record has no printed type;
2. instantiation does not reach a template parameter rendered into a handle (`Ty.lean:474-495`),
   so a generated module row cannot be polymorphic in a module type (DI-89's route);
3. subtyping through a rendered handle is string equality: no covariance (`Ty.sub`, `:437-460`);
4. `null` is a declaration named "null" at the Schema face (`Schema/Bridge.lean:47`), not rc.112's
   `Null` node (`Schema/Representation.lean:713`).
No theorem here; every check is a finite probe.
-/

open Effect4.Program Effect4.Codegen.Types

-- 1. legacy grammar: scalars and tuples inside a generic handle read; an object type does not
#guard (parseLegacy "Chunk.Chunk<number>").isSome
#guard (parseLegacy "Queue.Dequeue<readonly [number, string]>").isSome
#guard (parseLegacy "Queue.Dequeue<{ readonly id: number }>").isNone
#guard (parseLegacy "{ readonly id: number }").isNone
#guard (ofTy (.handle "Queue.Dequeue<{ readonly id: number }>")).isNone
#guard (ofTy (.handle "Queue.Dequeue<number>")).isSome

-- 2. a parameter rendered into a handle is text: instantiation leaves it, while a structural former substitutes
#guard Ty.chunk (.var 0) == .handle "Chunk.Chunk<A>"
#guard Ty.instantiate [(0, .nat)] (Ty.chunk (.var 0)) == .handle "Chunk.Chunk<A>"
#guard Ty.instantiate [(0, .nat)] (.list (.var 0)) == .list .nat
#guard Ty.instantiate [(0, .nat)] (.refOf (.var 0)) == .refOf .nat

-- 3. no covariance through a rendered handle; covariance through a structural former
#guard Ty.sub (Ty.chunk (.lit "x")) (Ty.chunk .string) == false
#guard Ty.sub (.list (.lit "x")) (.list .string) == true

-- 4. the Schema face of `null`: a declaration whose id is the spelling, not the `null` node
#guard (match Effect4.Schema.Bridge.schema Ty.null with
  | .declaration rep _ [] [] => rep.id == "null"
  | _ => false)
#guard (match Effect4.Schema.Bridge.schema Ty.null with
  | .null _ _ => false
  | _ => true)
