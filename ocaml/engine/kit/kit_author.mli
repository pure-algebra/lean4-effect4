(** Kit_author — write Eff programs in OCaml with names, through Lean's authoring surface
    (hand-written face over generated code).

    What it is: OCaml spellings of Lean's [Program.Authoring], lowered by LCNF into the api
    closure ([Effect4_gen.Api_gen], roots [Effect4.Program.Authoring.*]). A binder is an OCaml
    function, so a variable is an OCaml name:
    [let* todos = perform "Todos.add" (str "milk") in succeed (length todos)]. Each builder is one
    Lean function, and [build] is Lean's elaborator ([elaborateAt],
    [src/Effect4/Program/Authoring/Named.lean]). So a program written here is the program the
    same text in Lean elaborates to, and a name refuses here where it refuses in Lean. This
    module adds no authoring rule of its own: a new convenience lands in Lean's authoring module
    and is a root of the closure.
    Depends on: Eff_types, Effect4_gen.Api_gen (generated), Kit (the application and the
    checker).

    Behaviours it holds itself to:
    A1  Each builder is the Lean function its comment names; a binder's variable is a name minted
        for its scope ([minting]) and read through [minted].                by construction
    A2  A name resolves or [build] refuses it, with the address of the refusing node and the
        reason Lean gives ([Authoring.Refusal]).                             tested (T4)
    A3  A built program is the checker's to type: [build_checked] answers [Kit.check]'s answer.
                                                                               by construction *)

(** {1 Terms} *)

type term
(** A term under construction: Lean's [TermSrc], a function of the scope it is placed in. *)

val nat : int -> term
val str : string -> term
val bool : bool -> term
val unit : term

val atom : string -> term list -> term
(** An atom of the term language by its name ([Authoring.app]): ["add"], ["lt"], ["length"], … *)

val ( + ) : term -> term -> term
val ( - ) : term -> term -> term
(** Truncated at zero, as Lean's [Nat.sub] ([natSub]). *)

val ( * ) : term -> term -> term
val ( < ) : term -> term -> term
val ( = ) : term -> term -> term
val ( && ) : term -> term -> term
val ( || ) : term -> term -> term
val not : term -> term
val pair : term -> term -> term
val some : term -> term
val none : term
val nil : term
val cons : term -> term -> term
val length : term -> term
val append : term -> term -> term

(** {1 Programs} *)

type t
(** A program under construction: Lean's [Src NativeOp]. *)

val succeed : term -> t
val fail : term -> t
val sync : term -> t
val suspend : t -> t

val ( let* ) : t -> (term -> t) -> t
(** Run the first program, then the rest with its value bound ([bindWith]). *)

val ( >> ) : t -> t -> t
(** Run the first program, then the second, dropping the first one's value ([andThen]). *)

val perform : string -> term -> t
(** Call the host row of this spelling with the request ([Row.callNamed]). *)

val cell : term -> t
(** A new cell with this initial value ([Ref.make]); its value is the cell. *)

val get : term -> t
(** The value of the cell ([Ref.get]). *)

val set : term -> term -> t
(** Write the cell ([Ref.set]). *)

val if_ : term -> then_:t -> else_:t -> t
(** Choose by a boolean ([ifElse]). *)

val on_option : term -> none:t -> some:(term -> t) -> t
(** Choose by an option, binding the [some]'s value ([selectOptionWith]). *)

val loop :
  init:term -> test:(term -> term) -> step:(term -> term -> term) -> result:(term -> term) ->
  (term -> t) -> t
(** [loop ~init ~test ~step ~result body]: from the cursor [init], while [test c] holds run
    [body c] and move to [step c a], [a] the body's value; then answer [result c]
    ([loopWith], over [iterateWith]). *)

val catch : t -> (term -> t) -> t
(** Run the program; on a failure, run the handler with the failure's cause as a value
    ([catchWith]). *)

val on_exit : t -> (term -> t) -> t
(** Run the program, then the finalizer with its exit as a value; keep the program's exit unless
    the finalizer fails ([onExitWith]). *)

val exit_of : t -> t
(** The program's exit as a value ([exit]). *)

(** {1 Definitions} *)

type def
(** A definition: Lean's [DefSrc] of one request parameter. *)

val def : string -> request:Eff_types.Ty.t -> answer:Eff_types.Ty.t -> ?error:Eff_types.Ty.t -> (term -> t) -> def

val call : string -> term -> t
(** Invoke the definition of this name with the request ([Def.invoke]). *)

(** {1 Rows} *)

val row : string -> request:Eff_types.Ty.t -> answer:Eff_types.Ty.t -> ?error:Eff_types.Ty.t -> ?cite:string -> unit -> Eff_types.Row.t
(** A row the host answers, by its spelling and its three type columns ([Row.host]): asynchronous
    and externally registered, as the machine's reply admission demands. *)

(** {1 Building} *)

type refusal = Effect4_gen.Api_gen.effect4_program_authoring_refusal
(** Why elaboration refused, at the address where it did ([Authoring.Refusal]). *)

val refusal_text : refusal -> string

val build : ?app:Kit.app -> ?defs:def list -> t -> (Kit.program, refusal) result
(** The program of a main program and its definitions, its names resolved against the
    application's rows and the definitions ([elaborateAt]). *)

val build_checked :
  ?app:Kit.app -> ?defs:def list -> t ->
  (Kit.program * Eff_types.EffTy.t, [ `Name of refusal | `Type of Effect4_gen.Api_gen.type_refusal ]) result
(** The program and its type, or the name or the node it is refused at. *)
