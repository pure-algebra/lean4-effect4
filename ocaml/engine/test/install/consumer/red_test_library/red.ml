(* red -- names a test library from outside ocaml/; its build must fail (the red control of plan
   E1). If the library ever installed, this would compile and check_install.sh would fail. *)
let () = Disk_test_support.require true "a test library named from an outside project"
