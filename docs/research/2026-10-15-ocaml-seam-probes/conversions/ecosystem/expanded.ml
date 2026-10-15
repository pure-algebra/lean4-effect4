[@@@ocaml.ppx.context
  {
    tool_name = "ppx_driver";
    include_dirs = [];
    load_path = [];
    open_modules = [];
    for_package = None;
    debug = false;
    use_threads = false;
    use_vmthreads = false;
    recursive_types = false;
    principal = false;
    transparent_modules = false;
    unboxed_types = false;
    unsafe_string = false;
    cookies = [("inline_tests", "enabled")]
  }]
let () =
  Ppx_module_timer_runtime.record_start Ppx_module_timer_runtime.__MODULE__
open Base
open Bin_prot.Std
open Typerep_lib.Std
let passed = ref 0
let check name holds =
  if not holds then failwith name;
  Int.incr passed;
  Stdlib.Printf.printf "PASS %s\n%!" name
module Request =
  struct
    type t = {
      count: int ;
      message: string }[@@deriving
                         (sexp, sexp_grammar, compare, hash, bin_io, typerep)]
    include
      struct
        [@@@ocaml.warning "-60"]
        let _ = fun (_ : t) -> ()
        let t_of_sexp =
          (let error_source__002_ = "ecosystem_probe.ml.Request.t" in
           fun x__003_ ->
             Sexplib0.Sexp_conv_record.record_of_sexp
               ~caller:error_source__002_
               ~fields:(Field
                          {
                            name = "count";
                            kind = Required;
                            conv = int_of_sexp;
                            rest =
                              (Field
                                 {
                                   name = "message";
                                   kind = Required;
                                   conv = string_of_sexp;
                                   rest = Empty
                                 })
                          })
               ~index_of_field:(function
                                | "count" -> 0
                                | "message" -> 1
                                | _ -> (-1)) ~allow_extra_fields:false
               ~create:(fun (count, (message, ())) ->
                          ({ count; message } : t)) x__003_ : Sexplib0.Sexp.t
                                                                -> t)
        let _ = t_of_sexp
        let sexp_of_t =
          (fun { count = count__005_; message = message__007_ } ->
             let bnds__004_ = ([] : _ Stdlib.List.t) in
             let bnds__004_ =
               let arg__008_ = sexp_of_string message__007_ in
               ((Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "message"; arg__008_])
                 :: bnds__004_ : _ Stdlib.List.t) in
             let bnds__004_ =
               let arg__006_ = sexp_of_int count__005_ in
               ((Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "count"; arg__006_])
                 :: bnds__004_ : _ Stdlib.List.t) in
             Sexplib0.Sexp.List bnds__004_ : t -> Sexplib0.Sexp.t)
        let _ = sexp_of_t
        let t_sexp_grammar : t Sexplib0.Sexp_grammar.t =
          {
            untyped =
              (Lazy
                 (lazy
                    (List
                       (Fields
                          {
                            allow_extra_fields = false;
                            fields =
                              [No_tag
                                 {
                                   name = "count";
                                   required = true;
                                   args =
                                     (Cons
                                        ((int_sexp_grammar.untyped), Empty))
                                 };
                              No_tag
                                {
                                  name = "message";
                                  required = true;
                                  args =
                                    (Cons
                                       ((string_sexp_grammar.untyped), Empty))
                                }]
                          }))))
          }
        let _ = t_sexp_grammar
        let compare =
          (fun a__009_ ->
             fun b__010_ ->
               if Stdlib.(==) a__009_ b__010_
               then 0
               else
                 (match compare_int a__009_.count b__010_.count with
                  | 0 -> compare_string a__009_.message b__010_.message
                  | n -> n) : t -> ((t)[@merlin.hide ]) -> int)
        let _ = compare
        let hash_fold_t :
          Ppx_hash_lib.Std.Hash.state -> t -> Ppx_hash_lib.Std.Hash.state =
          fun hsv ->
            fun arg ->
              let hsv = let hsv = hsv in hash_fold_int hsv arg.count in
              hash_fold_string hsv arg.message
        let _ = hash_fold_t
        let hash : t -> Ppx_hash_lib.Std.Hash.hash_value =
          let func arg =
            Ppx_hash_lib.Std.Hash.get_hash_value
              (let hsv = Ppx_hash_lib.Std.Hash.create () in
               hash_fold_t hsv arg) in
          fun x -> func x
        let _ = hash
        let bin_shape_t =
          let _group =
            Bin_prot.Shape.group
              (Bin_prot.Shape.Location.of_string "ecosystem_probe.ml:16:2")
              [((Bin_prot.Shape.Tid.of_string "t"), [],
                 (Bin_prot.Shape.record
                    [("count", bin_shape_int); ("message", bin_shape_string)]))] in
          (Bin_prot.Shape.top_app _group (Bin_prot.Shape.Tid.of_string "t"))
            []
        let _ = bin_shape_t
        let bin_size_t : t Bin_prot.Size.sizer =
          function
          | { count = v1; message = v2 } ->
              let size = 0 in
              let size = Bin_prot.Common.(+) size (bin_size_int v1) in
              Bin_prot.Common.(+) size (bin_size_string v2)
        let _ = bin_size_t
        let bin_write_t : t Bin_prot.Write.writer =
          fun buf ->
            fun ~pos ->
              function
              | { count = v1; message = v2 } ->
                  let pos = bin_write_int buf ~pos v1 in
                  bin_write_string buf ~pos v2
        let _ = bin_write_t
        let bin_writer_t =
          {
            Bin_prot.Type_class.size = bin_size_t;
            Bin_prot.Type_class.write = bin_write_t
          }
        let _ = bin_writer_t
        let __bin_read_t__ : (int -> t) Bin_prot.Read.reader =
          fun _buf ->
            fun ~pos_ref ->
              fun _vint ->
                Bin_prot.Common.raise_variant_wrong_type
                  "ecosystem_probe.ml.Request.t" (!pos_ref)
        let _ = __bin_read_t__
        let bin_read_t : t Bin_prot.Read.reader =
          fun buf ->
            fun ~pos_ref ->
              let v_count = bin_read_int buf ~pos_ref in
              let v_message = bin_read_string buf ~pos_ref in
              { count = v_count; message = v_message }
        let _ = bin_read_t
        let bin_reader_t =
          {
            Bin_prot.Type_class.read = bin_read_t;
            Bin_prot.Type_class.vtag_read = __bin_read_t__
          }
        let _ = bin_reader_t
        let bin_t =
          {
            Bin_prot.Type_class.writer = bin_writer_t;
            reader = bin_reader_t;
            shape = bin_shape_t
          }
        let _ = bin_t
        module Typename_of_t =
          (Typerep_lib.Std.Make_typename.Make0)(struct
                                                  type nonrec t = t
                                                  let name =
                                                    "ecosystem_probe.ml.Request.t"
                                                  let _ = name
                                                end)
        let typename_of_t = Typename_of_t.typename_of_t
        let _ = typename_of_t
        let typerep_of_t =
          let name_of_t = Typename_of_t.named in
          Typerep_lib.Std.Typerep.Named
            (name_of_t,
              (Some
                 (lazy
                    (let field0 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "count";
                           index = 0;
                           is_mutable = false;
                           rep = typerep_of_int;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.count)
                         } in
                     let field1 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "message";
                           index = 1;
                           is_mutable = false;
                           rep = typerep_of_string;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.message)
                         } in
                     let typename =
                       Typerep_lib.Std.Typerep.Named.typename_of_t name_of_t in
                     let has_double_array_tag =
                       Typerep_lib.Std.Typerep_obj.has_double_array_tag
                         {
                           count =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ());
                           message =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ())
                         } in
                     let fields =
                       [|(Typerep_lib.Std.Typerep.Record_internal.Field
                            field0);(Typerep_lib.Std.Typerep.Record_internal.Field
                                       field1)|] in
                     let create
                       { Typerep_lib.Std.Typerep.Record_internal.get = get }
                       =
                       let count = get field0
                       and message = get field1 in { count; message } in
                     Typerep_lib.Std.Typerep.Record
                       (Typerep_lib.Std.Typerep.Record.internal_use_only
                          {
                            Typerep_lib.Std.Typerep.Record_internal.typename
                              = typename;
                            Typerep_lib.Std.Typerep.Record_internal.has_double_array_tag
                              = has_double_array_tag;
                            Typerep_lib.Std.Typerep.Record_internal.fields =
                              fields;
                            Typerep_lib.Std.Typerep.Record_internal.create =
                              create
                          })))))
        let _ = typerep_of_t
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
    let type_id = Base.Type_equal.Id.create ~name:"request" sexp_of_t
  end
module Renamed =
  struct
    type t = {
      count: int ;
      label: string }[@@deriving (bin_io, typerep)]
    include
      struct
        [@@@ocaml.warning "-60"]
        let _ = fun (_ : t) -> ()
        let bin_shape_t =
          let _group =
            Bin_prot.Shape.group
              (Bin_prot.Shape.Location.of_string "ecosystem_probe.ml:22:2")
              [((Bin_prot.Shape.Tid.of_string "t"), [],
                 (Bin_prot.Shape.record
                    [("count", bin_shape_int); ("label", bin_shape_string)]))] in
          (Bin_prot.Shape.top_app _group (Bin_prot.Shape.Tid.of_string "t"))
            []
        let _ = bin_shape_t
        let bin_size_t : t Bin_prot.Size.sizer =
          function
          | { count = v1; label = v2 } ->
              let size = 0 in
              let size = Bin_prot.Common.(+) size (bin_size_int v1) in
              Bin_prot.Common.(+) size (bin_size_string v2)
        let _ = bin_size_t
        let bin_write_t : t Bin_prot.Write.writer =
          fun buf ->
            fun ~pos ->
              function
              | { count = v1; label = v2 } ->
                  let pos = bin_write_int buf ~pos v1 in
                  bin_write_string buf ~pos v2
        let _ = bin_write_t
        let bin_writer_t =
          {
            Bin_prot.Type_class.size = bin_size_t;
            Bin_prot.Type_class.write = bin_write_t
          }
        let _ = bin_writer_t
        let __bin_read_t__ : (int -> t) Bin_prot.Read.reader =
          fun _buf ->
            fun ~pos_ref ->
              fun _vint ->
                Bin_prot.Common.raise_variant_wrong_type
                  "ecosystem_probe.ml.Renamed.t" (!pos_ref)
        let _ = __bin_read_t__
        let bin_read_t : t Bin_prot.Read.reader =
          fun buf ->
            fun ~pos_ref ->
              let v_count = bin_read_int buf ~pos_ref in
              let v_label = bin_read_string buf ~pos_ref in
              { count = v_count; label = v_label }
        let _ = bin_read_t
        let bin_reader_t =
          {
            Bin_prot.Type_class.read = bin_read_t;
            Bin_prot.Type_class.vtag_read = __bin_read_t__
          }
        let _ = bin_reader_t
        let bin_t =
          {
            Bin_prot.Type_class.writer = bin_writer_t;
            reader = bin_reader_t;
            shape = bin_shape_t
          }
        let _ = bin_t
        module Typename_of_t =
          (Typerep_lib.Std.Make_typename.Make0)(struct
                                                  type nonrec t = t
                                                  let name =
                                                    "ecosystem_probe.ml.Renamed.t"
                                                  let _ = name
                                                end)
        let typename_of_t = Typename_of_t.typename_of_t
        let _ = typename_of_t
        let typerep_of_t =
          let name_of_t = Typename_of_t.named in
          Typerep_lib.Std.Typerep.Named
            (name_of_t,
              (Some
                 (lazy
                    (let field0 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "count";
                           index = 0;
                           is_mutable = false;
                           rep = typerep_of_int;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.count)
                         } in
                     let field1 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "label";
                           index = 1;
                           is_mutable = false;
                           rep = typerep_of_string;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.label)
                         } in
                     let typename =
                       Typerep_lib.Std.Typerep.Named.typename_of_t name_of_t in
                     let has_double_array_tag =
                       Typerep_lib.Std.Typerep_obj.has_double_array_tag
                         {
                           count =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ());
                           label =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ())
                         } in
                     let fields =
                       [|(Typerep_lib.Std.Typerep.Record_internal.Field
                            field0);(Typerep_lib.Std.Typerep.Record_internal.Field
                                       field1)|] in
                     let create
                       { Typerep_lib.Std.Typerep.Record_internal.get = get }
                       =
                       let count = get field0
                       and label = get field1 in { count; label } in
                     Typerep_lib.Std.Typerep.Record
                       (Typerep_lib.Std.Typerep.Record.internal_use_only
                          {
                            Typerep_lib.Std.Typerep.Record_internal.typename
                              = typename;
                            Typerep_lib.Std.Typerep.Record_internal.has_double_array_tag
                              = has_double_array_tag;
                            Typerep_lib.Std.Typerep.Record_internal.fields =
                              fields;
                            Typerep_lib.Std.Typerep.Record_internal.create =
                              create
                          })))))
        let _ = typerep_of_t
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
  end
module Same_fields =
  struct
    type t = {
      count: int ;
      message: string }[@@deriving typerep]
    include
      struct
        [@@@ocaml.warning "-60"]
        let _ = fun (_ : t) -> ()
        module Typename_of_t =
          (Typerep_lib.Std.Make_typename.Make0)(struct
                                                  type nonrec t = t
                                                  let name =
                                                    "ecosystem_probe.ml.Same_fields.t"
                                                  let _ = name
                                                end)
        let typename_of_t = Typename_of_t.typename_of_t
        let _ = typename_of_t
        let typerep_of_t =
          let name_of_t = Typename_of_t.named in
          Typerep_lib.Std.Typerep.Named
            (name_of_t,
              (Some
                 (lazy
                    (let field0 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "count";
                           index = 0;
                           is_mutable = false;
                           rep = typerep_of_int;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.count)
                         } in
                     let field1 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "message";
                           index = 1;
                           is_mutable = false;
                           rep = typerep_of_string;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.message)
                         } in
                     let typename =
                       Typerep_lib.Std.Typerep.Named.typename_of_t name_of_t in
                     let has_double_array_tag =
                       Typerep_lib.Std.Typerep_obj.has_double_array_tag
                         {
                           count =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ());
                           message =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ())
                         } in
                     let fields =
                       [|(Typerep_lib.Std.Typerep.Record_internal.Field
                            field0);(Typerep_lib.Std.Typerep.Record_internal.Field
                                       field1)|] in
                     let create
                       { Typerep_lib.Std.Typerep.Record_internal.get = get }
                       =
                       let count = get field0
                       and message = get field1 in { count; message } in
                     Typerep_lib.Std.Typerep.Record
                       (Typerep_lib.Std.Typerep.Record.internal_use_only
                          {
                            Typerep_lib.Std.Typerep.Record_internal.typename
                              = typename;
                            Typerep_lib.Std.Typerep.Record_internal.has_double_array_tag
                              = has_double_array_tag;
                            Typerep_lib.Std.Typerep.Record_internal.fields =
                              fields;
                            Typerep_lib.Std.Typerep.Record_internal.create =
                              create
                          })))))
        let _ = typerep_of_t
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
  end
module Request_alias =
  struct
    type t = Request.t[@@deriving (bin_io, typerep)]
    include
      struct
        [@@@ocaml.warning "-60"]
        let _ = fun (_ : t) -> ()
        let bin_shape_t =
          let _group =
            Bin_prot.Shape.group
              (Bin_prot.Shape.Location.of_string "ecosystem_probe.ml:30:2")
              [((Bin_prot.Shape.Tid.of_string "t"), [], Request.bin_shape_t)] in
          (Bin_prot.Shape.top_app _group (Bin_prot.Shape.Tid.of_string "t"))
            []
        let _ = bin_shape_t
        let bin_size_t : t Bin_prot.Size.sizer = Request.bin_size_t
        let _ = bin_size_t
        let bin_write_t : t Bin_prot.Write.writer = Request.bin_write_t
        let _ = bin_write_t
        let bin_writer_t =
          {
            Bin_prot.Type_class.size = bin_size_t;
            Bin_prot.Type_class.write = bin_write_t
          }
        let _ = bin_writer_t
        let __bin_read_t__ : (int -> t) Bin_prot.Read.reader =
          Request.__bin_read_t__
        let _ = __bin_read_t__
        let bin_read_t : t Bin_prot.Read.reader = Request.bin_read_t
        let _ = bin_read_t
        let bin_reader_t =
          {
            Bin_prot.Type_class.read = bin_read_t;
            Bin_prot.Type_class.vtag_read = __bin_read_t__
          }
        let _ = bin_reader_t
        let bin_t =
          {
            Bin_prot.Type_class.writer = bin_writer_t;
            reader = bin_reader_t;
            shape = bin_shape_t
          }
        let _ = bin_t
        module Typename_of_t =
          (Typerep_lib.Std.Make_typename.Make0)(struct
                                                  type nonrec t = t
                                                  let name =
                                                    "ecosystem_probe.ml.Request_alias.t"
                                                  let _ = name
                                                end)
        let typename_of_t = Typename_of_t.typename_of_t
        let _ = typename_of_t
        let typerep_of_t =
          let name_of_t = Typename_of_t.named in
          Typerep_lib.Std.Typerep.Named
            (name_of_t, (Some (lazy Request.typerep_of_t)))
        let _ = typerep_of_t
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
  end
module Service_key_view =
  struct
    type t = Eff_types.service_key = {
      name: int ;
      service: int }[@@deriving
                      (sexp, sexp_grammar, compare, hash, bin_io, typerep)]
    include
      struct
        [@@@ocaml.warning "-60"]
        let _ = fun (_ : t) -> ()
        let t_of_sexp =
          (let error_source__012_ = "ecosystem_probe.ml.Service_key_view.t" in
           fun x__013_ ->
             Sexplib0.Sexp_conv_record.record_of_sexp
               ~caller:error_source__012_
               ~fields:(Field
                          {
                            name = "name";
                            kind = Required;
                            conv = int_of_sexp;
                            rest =
                              (Field
                                 {
                                   name = "service";
                                   kind = Required;
                                   conv = int_of_sexp;
                                   rest = Empty
                                 })
                          })
               ~index_of_field:(function
                                | "name" -> 0
                                | "service" -> 1
                                | _ -> (-1)) ~allow_extra_fields:false
               ~create:(fun (name, (service, ())) -> ({ name; service } : t))
               x__013_ : Sexplib0.Sexp.t -> t)
        let _ = t_of_sexp
        let sexp_of_t =
          (fun { name = name__015_; service = service__017_ } ->
             let bnds__014_ = ([] : _ Stdlib.List.t) in
             let bnds__014_ =
               let arg__018_ = sexp_of_int service__017_ in
               ((Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "service"; arg__018_])
                 :: bnds__014_ : _ Stdlib.List.t) in
             let bnds__014_ =
               let arg__016_ = sexp_of_int name__015_ in
               ((Sexplib0.Sexp.List [Sexplib0.Sexp.Atom "name"; arg__016_])
                 :: bnds__014_ : _ Stdlib.List.t) in
             Sexplib0.Sexp.List bnds__014_ : t -> Sexplib0.Sexp.t)
        let _ = sexp_of_t
        let t_sexp_grammar : t Sexplib0.Sexp_grammar.t =
          {
            untyped =
              (Lazy
                 (lazy
                    (List
                       (Fields
                          {
                            allow_extra_fields = false;
                            fields =
                              [No_tag
                                 {
                                   name = "name";
                                   required = true;
                                   args =
                                     (Cons
                                        ((int_sexp_grammar.untyped), Empty))
                                 };
                              No_tag
                                {
                                  name = "service";
                                  required = true;
                                  args =
                                    (Cons ((int_sexp_grammar.untyped), Empty))
                                }]
                          }))))
          }
        let _ = t_sexp_grammar
        let compare =
          (fun a__019_ ->
             fun b__020_ ->
               if Stdlib.(==) a__019_ b__020_
               then 0
               else
                 (match compare_int a__019_.name b__020_.name with
                  | 0 -> compare_int a__019_.service b__020_.service
                  | n -> n) : t -> ((t)[@merlin.hide ]) -> int)
        let _ = compare
        let hash_fold_t :
          Ppx_hash_lib.Std.Hash.state -> t -> Ppx_hash_lib.Std.Hash.state =
          fun hsv ->
            fun arg ->
              let hsv = let hsv = hsv in hash_fold_int hsv arg.name in
              hash_fold_int hsv arg.service
        let _ = hash_fold_t
        let hash : t -> Ppx_hash_lib.Std.Hash.hash_value =
          let func arg =
            Ppx_hash_lib.Std.Hash.get_hash_value
              (let hsv = Ppx_hash_lib.Std.Hash.create () in
               hash_fold_t hsv arg) in
          fun x -> func x
        let _ = hash
        let bin_shape_t =
          let _group =
            Bin_prot.Shape.group
              (Bin_prot.Shape.Location.of_string "ecosystem_probe.ml:36:2")
              [((Bin_prot.Shape.Tid.of_string "t"), [],
                 (Bin_prot.Shape.record
                    [("name", bin_shape_int); ("service", bin_shape_int)]))] in
          (Bin_prot.Shape.top_app _group (Bin_prot.Shape.Tid.of_string "t"))
            []
        let _ = bin_shape_t
        let bin_size_t : t Bin_prot.Size.sizer =
          function
          | { name = v1; service = v2 } ->
              let size = 0 in
              let size = Bin_prot.Common.(+) size (bin_size_int v1) in
              Bin_prot.Common.(+) size (bin_size_int v2)
        let _ = bin_size_t
        let bin_write_t : t Bin_prot.Write.writer =
          fun buf ->
            fun ~pos ->
              function
              | { name = v1; service = v2 } ->
                  let pos = bin_write_int buf ~pos v1 in
                  bin_write_int buf ~pos v2
        let _ = bin_write_t
        let bin_writer_t =
          {
            Bin_prot.Type_class.size = bin_size_t;
            Bin_prot.Type_class.write = bin_write_t
          }
        let _ = bin_writer_t
        let __bin_read_t__ : (int -> t) Bin_prot.Read.reader =
          fun _buf ->
            fun ~pos_ref ->
              fun _vint ->
                Bin_prot.Common.raise_variant_wrong_type
                  "ecosystem_probe.ml.Service_key_view.t" (!pos_ref)
        let _ = __bin_read_t__
        let bin_read_t : t Bin_prot.Read.reader =
          fun buf ->
            fun ~pos_ref ->
              let v_name = bin_read_int buf ~pos_ref in
              let v_service = bin_read_int buf ~pos_ref in
              { name = v_name; service = v_service }
        let _ = bin_read_t
        let bin_reader_t =
          {
            Bin_prot.Type_class.read = bin_read_t;
            Bin_prot.Type_class.vtag_read = __bin_read_t__
          }
        let _ = bin_reader_t
        let bin_t =
          {
            Bin_prot.Type_class.writer = bin_writer_t;
            reader = bin_reader_t;
            shape = bin_shape_t
          }
        let _ = bin_t
        module Typename_of_t =
          (Typerep_lib.Std.Make_typename.Make0)(struct
                                                  type nonrec t = t
                                                  let name =
                                                    "ecosystem_probe.ml.Service_key_view.t"
                                                  let _ = name
                                                end)
        let typename_of_t = Typename_of_t.typename_of_t
        let _ = typename_of_t
        let typerep_of_t =
          let name_of_t = Typename_of_t.named in
          Typerep_lib.Std.Typerep.Named
            (name_of_t,
              (Some
                 (lazy
                    (let field0 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "name";
                           index = 0;
                           is_mutable = false;
                           rep = typerep_of_int;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.name)
                         } in
                     let field1 =
                       Typerep_lib.Std.Typerep.Field.internal_use_only
                         {
                           Typerep_lib.Std.Typerep.Field_internal.label =
                             "service";
                           index = 1;
                           is_mutable = false;
                           rep = typerep_of_int;
                           tyid = (Typerep_lib.Std.Typename.create ());
                           get = (fun t -> t.service)
                         } in
                     let typename =
                       Typerep_lib.Std.Typerep.Named.typename_of_t name_of_t in
                     let has_double_array_tag =
                       Typerep_lib.Std.Typerep_obj.has_double_array_tag
                         {
                           name =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ());
                           service =
                             (Typerep_lib.Std.Typerep_obj.double_array_value
                                ())
                         } in
                     let fields =
                       [|(Typerep_lib.Std.Typerep.Record_internal.Field
                            field0);(Typerep_lib.Std.Typerep.Record_internal.Field
                                       field1)|] in
                     let create
                       { Typerep_lib.Std.Typerep.Record_internal.get = get }
                       =
                       let name = get field0
                       and service = get field1 in { name; service } in
                     Typerep_lib.Std.Typerep.Record
                       (Typerep_lib.Std.Typerep.Record.internal_use_only
                          {
                            Typerep_lib.Std.Typerep.Record_internal.typename
                              = typename;
                            Typerep_lib.Std.Typerep.Record_internal.has_double_array_tag
                              = has_double_array_tag;
                            Typerep_lib.Std.Typerep.Record_internal.fields =
                              fields;
                            Typerep_lib.Std.Typerep.Record_internal.create =
                              create
                          })))))
        let _ = typerep_of_t
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
  end
module Asc =
  struct
    type t = int[@@deriving (sexp_of, compare)]
    include
      struct
        let _ = fun (_ : t) -> ()
        let sexp_of_t = (sexp_of_int : t -> Sexplib0.Sexp.t)
        let _ = sexp_of_t
        let compare = (compare_int : t -> ((t)[@merlin.hide ]) -> int)
        let _ = compare
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
    include
      (Comparator.Make)(struct
                          type nonrec t = t
                          let compare = compare
                          let sexp_of_t = sexp_of_t
                        end)
  end
module Desc =
  struct
    type t = int[@@deriving sexp_of]
    include
      struct
        let _ = fun (_ : t) -> ()
        let sexp_of_t = (sexp_of_int : t -> Sexplib0.Sexp.t)
        let _ = sexp_of_t
      end[@@ocaml.doc "@inline"][@@merlin.hide ]
    let compare a b = Int.compare b a
    include
      (Comparator.Make)(struct
                          type nonrec t = t
                          let compare = compare
                          let sexp_of_t = sexp_of_t
                        end)
  end
module type PAYLOAD  =
  sig
    type t
    val type_id : t Base.Type_equal.Id.t
    val sexp_of_t : t -> Sexp.t
    val bin_writer_t : t Bin_prot.Type_class.writer
    val bin_reader_t : t Bin_prot.Type_class.reader
  end
let inspect_binary (type a) ((module M)  : (module PAYLOAD with type t = a))
  (value : a) =
  let bytes = Bin_prot.Utils.bin_dump M.bin_writer_t value in
  let pos_ref = ref 0 in
  let decoded = M.bin_reader_t.read bytes ~pos_ref in
  ((M.sexp_of_t decoded), ((!pos_ref) = (Bigarray.Array1.dim bytes)))
let record_fields (type a) (repr : a Typerep.t) =
  match Typerep.head repr with
  | Typerep.Record record ->
      List.rev
        (Typerep.Record.fold record ~init:[]
           ~f:(fun acc ->
                 fun (Typerep.Record.Field f) -> (Typerep.Field.label f) ::
                   acc))
  | _ -> []
let count_field (type a) (repr : a Typerep.t) (value : a) =
  (match Typerep.head repr with
   | Typerep.Record record ->
       Typerep.Record.fold record ~init:(None : int option)
         ~f:(fun answer ->
               fun (Typerep.Record.Field f) ->
                 if String.equal (Typerep.Field.label f) "count"
                 then
                   match Typerep.head (Typerep.Field.traverse f) with
                   | Typerep.Int -> Some (Typerep.Field.get f value)
                   | _ -> answer
                 else answer)
   | _ -> None : int option)
let () =
  let original : Eff_types.service_key = { name = 11; service = 22 } in
  let view : Service_key_view.t = original in
  check "ppx_reexport_is_the_existing_generated_type"
    ((Service_key_view.compare original view) = 0);
  (let restored : Eff_types.service_key =
     Service_key_view.t_of_sexp (Service_key_view.sexp_of_t original) in
   check "ppx_reexport_converters_return_existing_generated_type"
     ((Int.equal restored.name 11) && (Int.equal restored.service 22));
   (let request = { Request.count = 42; message = "hello" } in
    let text_id = Base.Type_equal.Id.create ~name:"request" String.sexp_of_t in
    let recreated_id =
      Base.Type_equal.Id.create ~name:"request" Request.sexp_of_t in
    let map =
      Core.Univ_map.set Core.Univ_map.empty ~key:Request.type_id
        ~data:request in
    check "univ_map_recovers_same_typed_key"
      (Option.value_map (Core.Univ_map.find map Request.type_id)
         ~default:false ~f:(fun r -> (Request.compare request r) = 0));
    check "univ_map_rejects_same_text_wrong_type"
      (Option.is_none (Core.Univ_map.find map text_id));
    check "univ_map_rejects_recreated_same_type_key"
      (Option.is_none (Core.Univ_map.find map recreated_id));
    check "univ_map_detects_duplicate"
      (match Core.Univ_map.add map ~key:Request.type_id ~data:request with
       | `Duplicate -> true
       | `Ok _ -> false);
    check "type_id_same_key_witness"
      (Option.is_some
         (Base.Type_equal.Id.same_witness Request.type_id Request.type_id));
    check "type_id_different_key_no_witness"
      (Option.is_none
         (Base.Type_equal.Id.same_witness Request.type_id text_id));
    (let (observed, filled) = inspect_binary (module Request) request in
     check "first_class_module_keeps_matching_carrier_and_operations"
       ((Sexp.equal observed (Request.sexp_of_t request)) && filled);
     check "typerep_reflects_record_fields"
       (List.equal String.equal (record_fields Request.typerep_of_t)
          ["count"; "message"]);
     check "typerep_typed_field_accessor"
       (Option.equal Int.equal (count_field Request.typerep_of_t request)
          (Some 42));
     check "typerep_wrong_shape_has_no_count"
       (Option.is_none (count_field typerep_of_string "hello"));
     check "typerep_alias_has_same_type"
       (Typerep.same Request.typerep_of_t Request_alias.typerep_of_t);
     check "typerep_same_record_shape_is_not_same_type"
       (not (Typerep.same Request.typerep_of_t Same_fields.typerep_of_t));
     (let digest_a = Bin_prot.Shape.eval_to_digest_string Request.bin_shape_t in
      let digest_alias =
        Bin_prot.Shape.eval_to_digest_string Request_alias.bin_shape_t in
      let digest_renamed =
        Bin_prot.Shape.eval_to_digest_string Renamed.bin_shape_t in
      check "bin_shape_alias_same_digest"
        (String.equal digest_a digest_alias);
      check "bin_shape_detects_field_rename"
        (not (String.equal digest_a digest_renamed));
      (let bytes = Bin_prot.Utils.bin_dump Request.bin_writer_t request in
       let pos_ref = ref 0 in
       let renamed = Renamed.bin_read_t bytes ~pos_ref in
       check "bin_bytes_alone_do_not_enforce_shape"
         ((Int.equal renamed.count 42) &&
            (String.equal renamed.label "hello"));
       Stdlib.Printf.printf
         "OBS shape_request=%s shape_alias=%s shape_renamed=%s\n" digest_a
         digest_alias digest_renamed;
       (let negative = { Request.count = (-1); message = "not a natural" } in
        let negative_bytes =
          Bin_prot.Utils.bin_dump Request.bin_writer_t negative in
        let decoded_negative =
          Request.bin_read_t negative_bytes ~pos_ref:(ref 0) in
        check "bin_io_does_not_admit_program_natural"
          (Int.equal decoded_negative.count (-1));
        (let grammar : int Sexplib0.Sexp_grammar.t =
           (((int_sexp_grammar : int Sexplib0.Sexp_grammar.t))
           [@merlin.hide ]) in
         check "sexp_integer_grammar_has_no_native_bit_bound"
           (match grammar.untyped with
            | Sexplib0.Sexp_grammar.Integer -> true
            | _ -> false);
         (let huge = Sexp.Atom "18446744073709551616" in
          check "sexp_int_converter_still_refuses_overflow"
            (Result.is_error (Result.try_with (fun () -> Int.t_of_sexp huge)));
          check "compare_generated_on_concrete_record"
            ((Request.compare request request) = 0);
          check "hash_agrees_after_alias_roundtrip"
            (Int.equal (Request.hash request)
               (Request.hash (Request.t_of_sexp (Request.sexp_of_t request))));
          (let asc = Set.of_list (module Asc) [3; 1; 2] in
           let desc = Set.of_list (module Desc) [3; 1; 2] in
           check "comparator_witness_selects_ascending_order"
             (List.equal Int.equal (Set.to_list asc) [1; 2; 3]);
           check "comparator_witness_selects_descending_order"
             (List.equal Int.equal (Set.to_list desc) [3; 2; 1]);
           Stdlib.Printf.printf "MEASURE ecosystem_passed=%d\n%!" (!passed))))))))))
let () =
  Ppx_module_timer_runtime.record_until Ppx_module_timer_runtime.__MODULE__
