(* Typed_lint: rules 7 and 6 of ocaml/STANDARDS.md, read off OCaml's typed tree.

   What it is: a check over the .cmt files the compiler writes beside each module. A ppx runs
   before typing, so it cannot see the type a polymorphic comparison is used at; the typed tree
   records that type at every use. Dune runs the check over each hand library's .cmt files
   under the runtest alias (the rule beside each library stanza), so it reruns only for a
   library whose typed tree changed.

   Depends on: compiler-libs.common (Cmt_format, Typedtree, Tast_iterator, Envaux, Ctype,
   Printtyp) and the standard library. A unit's environment is rebuilt from the .cmi files on
   its recorded load path, which names directories relative to the build context's root, so
   [check] reads paths relative to the current directory and the caller runs it from that root.

   Behaviours:
   T1 Every use of a watched polymorphic comparison (=, <>, <, >, <=, >=, compare, min, max,
      Hashtbl.hash, List.mem, List.assoc and their kin, Array.mem, and the generic Hashtbl's
      keyed operations) at a type that is not int, char, bool or string after expanding
      abbreviations is a rule-7 finding, with its location and that type.
                                                        tested (test/red.expected)
   T2 A unit whose source file opens with "(* GENERATED" is skipped whole, and so is any
      .cmt that is not an implementation.             tested (test/red.expected)
   T3 With [~raises:true], each raise, raise_notrace, failwith or invalid_arg is a rule-6
      finding unless an enclosing binding's name ends in "_exn" or it sits in the body of a
      try or of a match with an exception case. A report: it decides no exit status.
                                                        tested (test/raise.expected)
   T4 An unreadable .cmt, an unreadable source, or an environment that cannot be rebuilt is a
      refusal; no finding is guessed in its place.    by construction; the absent .cmt is
                                                        tested (test/missing.expected) *)

type rule =
  | Compare (** rule 7: comparison by type *)
  | Raise (** rule 6: a function that raises ends in [_exn] *)

type finding =
  { rule : rule
  ; loc : Location.t
  ; operator : string
    (** the watched value's path, such as ["Stdlib.="]; for rule 6, followed by the
          constructor raised when the argument is one, as in ["Stdlib.raise Exit"] *)
  ; at : string (** rule 7: the compared type; rule 6: the enclosing binding *)
  }

type refusal =
  | Unreadable of string * string (** the .cmt, and why *)
  | No_source of string * string (** the source file, and why *)
  | Environment of string * string (** the location, and the module not found *)

(** [check ~raises cmt] is the findings of one .cmt in source order: rule 7's always, rule 6's
    when [raises]. A GENERATED unit and an interface have none. *)
val check : raises:bool -> string -> (finding list, refusal) result

(** One line: the location as the compiler prints it, the rule, the operator and its type or
    binding. *)
val render : finding -> string

val message : refusal -> string
