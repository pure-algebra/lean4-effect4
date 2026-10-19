#!/usr/bin/env bash
# packaging.sh -- can one compiled OCaml unit serve the public scope and the test lanes? (C5)
#
# What it is: three small dune workspaces built in WORK, each a finite question about who may
# name what. It prints one line per answer and exits 0 when every answer is the one recorded in
# receipt-w2-closure.md. Host-only evidence: dune 3.24.2 and OCaml 5.1.1 of the effect4 switch.
# Usage: packaging.sh WORK   (an empty scratch directory; nothing outside it is written)
#
#   P1 A dune private module is unbound from a test in another dune project of one workspace.
#   P2 A package-private library is not found from another project of one workspace, by either
#      name, and after `dune install` an outside client cannot name it either.
#   P3 In one project, a package-private library serves both scopes: a test in the project names
#      its hidden values and builds its sealed record, while an installed outside client sees
#      only the restricted public module, its sealed type abstract and its hidden values unbound.
set -uo pipefail
[ "$#" -eq 1 ] || { echo "usage: packaging.sh WORK" >&2; exit 2; }
work=$(cd "$1" && pwd)
dune() { opam exec --switch=effect4 -- dune "$@"; }
outside() { env -i PATH="$PATH" HOME="$HOME" TMPDIR="${TMPDIR:-/tmp}" OCAMLPATH="$1" \
  opam exec --switch=effect4 -- dune build --root "$2" "$3" 2>&1; }
failures=0
answers=0
expect() { # expect NAME TEXT OUTPUT: the output holds TEXT
  answers=$((answers + 1))
  if printf '%s' "$3" | grep -qF -- "$2"; then echo "PASS $1: $2"; else echo "FAIL $1: wanted $2"; printf '%s\n' "$3" | head -5; failures=$((failures + 1)); fi
}
closure='type built = { a : int }
type sig_app = { rows : int list }
let secret = 1
let pub = 2
let make a = { a }
let run b = b.a + secret
let width s = List.length s.rows'
api_mli='type built
type sig_app = Pg_closure.Closure.sig_app = { rows : int list }
val pub : int
val make : int -> built
val run : built -> int
val width : sig_app -> int'

# P1: a private module, named from another project of the workspace
d=$work/p1; mkdir -p "$d/gen" "$d/eng"
echo '(lang dune 3.0)' > "$d/dune-project"
printf '(lang dune 3.0)\n(package (name pg))\n' > "$d/gen/dune-project"
echo '(library (name pg) (public_name pg) (modules closure api) (private_modules closure))' > "$d/gen/dune"
printf '%s\n' "$closure" > "$d/gen/closure.ml"
echo 'include Closure' > "$d/gen/api.ml"
echo '(lang dune 3.0)' > "$d/eng/dune-project"
echo '(test (name t) (libraries pg))' > "$d/eng/dune"
echo 'let () = print_int Pg__Closure.secret' > "$d/eng/t.ml"
expect P1 "Unbound module Pg__Closure" "$(dune build --root "$d" 2>&1)"

# P2: a package-private library, from another project and from an installed outside client
d=$work/p2; mkdir -p "$d/gen" "$d/eng" "$d/out/a"
echo '(lang dune 3.0)' > "$d/dune-project"
printf '(lang dune 3.0)\n(package (name pg))\n' > "$d/gen/dune-project"
printf '(library (name pg_closure) (package pg) (modules closure))\n(library (name pg) (public_name pg) (modules api) (libraries pg_closure))\n' > "$d/gen/dune"
printf '%s\n' "$closure" > "$d/gen/closure.ml"
echo 'include Pg_closure.Closure' > "$d/gen/api.ml"
printf '%s\n' "$api_mli" > "$d/gen/api.mli"
echo '(lang dune 3.0)' > "$d/eng/dune-project"
echo 'let () = print_int Pg_closure.Closure.secret' > "$d/eng/t.ml"
echo '(test (name t) (libraries pg_closure))' > "$d/eng/dune"
expect P2 'Library "pg_closure" not found' "$(dune build --root "$d" 2>&1)"
echo '(test (name t) (libraries pg.__private__.pg_closure))' > "$d/eng/dune"
expect P2 'Library "pg.__private__.pg_closure" not found' "$(dune build --root "$d" 2>&1)"
rm -r "$d/eng"
dune build --root "$d" @install > /dev/null 2>&1
dune install --root "$d" --prefix "$d/prefix" > /dev/null 2>&1
echo '(lang dune 3.0)' > "$d/out/dune-project"
echo '(executable (name a) (libraries pg))' > "$d/out/a/dune"
echo 'let () = print_int (Pg_closure.Closure.secret + Pg.Api.pub)' > "$d/out/a/a.ml"
expect P2 "Unbound module Pg_closure" "$(outside "$d/prefix/lib" "$d/out" ./a/a.exe)"

# P3: one project; a package-private closure, a restricted public view, an in-project test
d=$work/p3; mkdir -p "$d/ws/gen" "$d/ws/eng" "$d/out/ok" "$d/out/red1" "$d/out/red2" "$d/out/red3"
printf '(lang dune 3.0)\n(package (name pg))\n' > "$d/ws/dune-project"
printf '(library (name pg_closure) (package pg) (modules closure))\n(library (name pg) (public_name pg) (modules api) (libraries pg_closure))\n' > "$d/ws/gen/dune"
printf '%s\n' "$closure" > "$d/ws/gen/closure.ml"
echo 'include Pg_closure.Closure' > "$d/ws/gen/api.ml"
printf '%s\n' "$api_mli" > "$d/ws/gen/api.mli"
echo '(test (name t) (libraries pg_closure pg))' > "$d/ws/eng/dune"
cat > "$d/ws/eng/t.ml" <<'EOF'
let () =
  let b = { Pg_closure.Closure.a = 5 } in
  Printf.printf "%d %d %d\n" (Pg_closure.Closure.run b) Pg_closure.Closure.secret
    (Pg.Api.width { Pg_closure.Closure.rows = [ 1; 2 ] })
EOF
expect P3 "6 1 2" "$(dune test --root "$d/ws" --force 2>&1)"
dune build --root "$d/ws" @install > /dev/null 2>&1
dune install --root "$d/ws" --prefix "$d/prefix" > /dev/null 2>&1
echo '(lang dune 3.0)' > "$d/out/dune-project"
for x in ok red1 red2 red3; do echo "(executable (name $x) (libraries pg))" > "$d/out/$x/dune"; done
echo 'let () = Printf.printf "%d %d %d\n" Pg.Api.pub (Pg.Api.run (Pg.Api.make 3)) (Pg.Api.width { Pg.Api.rows = [ 1; 2; 3 ] })' > "$d/out/ok/ok.ml"
echo 'let _ = Pg.Api.secret' > "$d/out/red1/red1.ml"
echo 'let _ = Pg_closure.Closure.secret' > "$d/out/red2/red2.ml"
echo 'let _ : Pg.Api.built = { a = 1 }' > "$d/out/red3/red3.ml"
outside "$d/prefix/lib" "$d/out" ./ok/ok.exe > /dev/null
expect P3 "2 4 3" "$("$d/out/_build/default/ok/ok.exe" 2>&1)"
expect P3 "Unbound value Pg.Api.secret" "$(outside "$d/prefix/lib" "$d/out" ./red1/red1.exe)"
expect P3 "Unbound module Pg_closure" "$(outside "$d/prefix/lib" "$d/out" ./red2/red2.exe)"
expect P3 "Unbound record field a" "$(outside "$d/prefix/lib" "$d/out" ./red3/red3.exe)"

[ "$failures" -eq 0 ] && echo "PASS packaging: $answers answers as recorded" || { echo "FAIL packaging: $failures of $answers"; exit 1; }
