#!/bin/sh
# Tool discovery for the effect4 opam switch. Explicit executable overrides win.
# No switch is installed or changed; missing required tools are named and refused.
effect4_toolchain() {
  if command -v opam >/dev/null 2>&1; then
    eval "$(opam env --switch="${EFFECT4_OPAM_SWITCH:-effect4}" --set-switch 2>/dev/null)"
  fi
  OCAMLC=${OCAMLC:-$(command -v ocamlc || true)}
  OCAMLOPT=${OCAMLOPT:-$(command -v ocamlopt || true)}
  OCAMLRUN=${OCAMLRUN:-$(command -v ocamlrun || true)}
  JSOO=${JSOO:-$(command -v js_of_ocaml || true)}
  NODE=${NODE:-$(command -v node || command -v node.exe || true)}
  case "$NODE" in
    *.exe)
      # WSL passes these per-run selectors to Windows Node only through WSLENV.
      WSLENV="${WSLENV:+$WSLENV:}EFFECT4_FAMILY:EFFECT4_PROGRAM:EFFECT4_TAPE:EFFECT4_CORPUS:EFFECT4_EFFECT_NODE_MODULES"
      export WSLENV ;;
  esac
  for effect4_tool in "$OCAMLC" "$OCAMLOPT" "$OCAMLRUN" "$JSOO" "$NODE"; do
    if [ -z "$effect4_tool" ] || ! command -v "$effect4_tool" >/dev/null 2>&1; then
      echo 'FAIL effect4 toolchain: need ocamlc, ocamlopt, ocamlrun, js_of_ocaml and node (switch effect4)' >&2
      return 1
    fi
  done
  export OCAMLC OCAMLOPT OCAMLRUN JSOO NODE
}

# Windows Node reached from WSL needs a Windows spelling of a filesystem argument.
effect4_node_path() {
  case "$NODE" in *.exe) wslpath -w "$1" ;; *) printf '%s' "$1" ;; esac
}
