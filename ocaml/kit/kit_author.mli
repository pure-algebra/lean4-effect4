(** Kit_author — write Eff programs in OCaml with names (hand-written).

    What it is: builders for [Eff_types] programs. A binder is an OCaml function, so a variable is
    an OCaml name: [let* todos = perform "Todos.add" (str "milk") in succeed (length todos)].
    Rows and definitions are named too, and [build] resolves the names. A program's variables are
    levels, the position from the outermost binder ([Term.var 0] is the first), so a bound
    variable is the same term at every depth below its binder, and a builder needs only the
    depth at which it is placed.
    Depends on: Eff_types, Kit (the application and the checker).

    Behaviours it holds itself to:
    A1  A builder places each binder's variable at the depth the program's typing reads it: the
        cursor of a loop, the answer of its body, the value a [let*] binds, the error a handler
        binds, the exit a finalizer binds, and a definition's request.        tested (T4)
    A2  A name resolves or [build] refuses it with the name and its kind; no name is guessed.
                                                                               tested (T4)
    A3  A built program is the checker's to type: [build_checked] answers [Kit.check]'s answer.
                                                                               by construction *)

(** {1 Terms} *)

type term = Eff_types.term

val nat : int -> term
val str : string -> term
val bool : bool -> term
val unit : term

val atom : string -> term list -> term
(** An atom of the term language by its name ([NativeAtom]): ["add"], ["lt"], ["length"], … *)

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
(** A program under construction: a function of where it is placed. *)

val succeed : term -> t
val fail : term -> t
val sync : term -> t
val suspend : t -> t

val ( let* ) : t -> (term -> t) -> t
(** Run the first program, then the rest with its value bound ([Eff.bind]). *)

val ( >> ) : t -> t -> t
(** Run the first program, then the second, dropping the first one's value. *)

val perform : string -> term -> t
(** Call the host row of this name with the request. *)

val cell : term -> t
(** A new cell with this initial value ([Ref.make]); its value is the cell. *)

val get : term -> t
(** The value of the cell ([Ref.get]). *)

val set : term -> term -> t
(** Write the cell ([Ref.set]). *)

val if_ : term -> then_:t -> else_:t -> t
(** Choose by a boolean ([Eff.select] at [Decision.bool]). *)

val on_option : term -> none:t -> some:(term -> t) -> t
(** Choose by an option, binding the [some]'s value ([Decision.option]). *)

val loop :
  init:term -> test:(term -> term) -> step:(term -> term -> term) -> result:(term -> term) ->
  (term -> t) -> t
(** [loop ~init ~test ~step ~result body]: from the cursor [init], while [test c] holds run
    [body c] and move to [step c a], [a] the body's value; then answer [result c]
    ([Eff.iterate]). *)

val catch : t -> (term -> t) -> t
(** Run the program; on a failure, run the handler with the failure's cause as a value
    ([Eff.catchCause], [Val.exitErr]). *)

val on_exit : t -> (term -> t) -> t
(** Run the program, then the finalizer with its exit as a value; keep the program's exit unless
    the finalizer fails ([Eff.onExit]). *)

val exit_of : t -> t
(** The program's exit as a value ([Eff.exit]). *)

(** {1 Definitions} *)

type def
(** A definition: a name, its request and answer types, and a body over its request. *)

val def : string -> request:Eff_types.ty -> answer:Eff_types.ty -> ?error:Eff_types.ty -> (term -> t) -> def

val call : string -> term -> t
(** Call the definition of this name with the request ([NativeOp.call]). *)

val program : def list -> t -> t
(** A program whose root block holds these definitions ([Eff.defs]); each may call any. *)

(** {1 Rows} *)

val row : string -> request:Eff_types.ty -> answer:Eff_types.ty -> ?error:Eff_types.ty -> ?cite:string -> unit -> Eff_types.row
(** A row the host answers, by its spelling and its three type columns ([Row.host]): asynchronous
    and externally registered, as the machine's reply admission demands. *)

(** {1 Building} *)

type refusal = Unbound_row of string | Unbound_def of string

val refusal_text : refusal -> string

val build : ?app:Kit.app -> t -> (Kit.program, refusal) result
(** The program, its names resolved against the application's rows and its definitions. *)

val build_checked :
  ?app:Kit.app -> t -> (Kit.program * Eff_types.eff_ty, [ `Name of refusal | `Type of Kit_gen.type_refusal ]) result
(** The program and its type, or the name or the node it is refused at. *)
