#!/usr/bin/env bash
# Fail-closed replay harness for the finite Schema representation probes.
#
# Default mode is read-only CHECK mode. It runs every probe twice in fresh OS
# processes, refuses nondeterminism, and compares the fresh bytes with every
# retained file in observed/. Only an explicit --update may rewrite observed/.
set -euo pipefail

EXPECTED_BUN="1.3.14"
EXPECTED_NODE="v22.23.2"
EXPECTED_EFFECT_VERSION="4.0.0-rc.112"
EXPECTED_DIST_FILE_COUNT="1808"
EXPECTED_DIST_DIGEST="562fafd9320e4977f1beb9adf37d3ccda55c75034f37d45bfc4cebf7f9307fe5"

EXPECTED_PACKAGE_JSON="0ad20c73dfbe482996f046a0c1170b1a08d6fea7effeb6767fd247cdad53a56d"
EXPECTED_SCHEMA_REPRESENTATION="a0a7a1537cfe3a9159a80210e3de92342cc9e98651f0e8273a75ccdcccae69bc"
EXPECTED_SCHEMA_AST="7f7cb03664cad0f3bfa221f963ea55b1520afe1314c39054e85ad21f322275d8"
EXPECTED_SCHEMA="9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784"
EXPECTED_TO_REPRESENTATION="677449c734ac6373598a81207ba0573f86fb8bd2c9fb25d1369aa1e710d614a2"
EXPECTED_FROM_REPRESENTATION="0b95c360800d3c1dfe3e6c5683f79265fa7217494c8ce9cedb5c6dcbf936d82e"

HERE="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd -P)"
OBSERVED="$HERE/observed"
MODE="check"

usage() {
  cat <<'EOF'
usage: run-probes.sh [--update] <path-to-node_modules/effect>

Without --update, replay into a temporary directory and compare every output
byte-for-byte with observed/. With --update, replace the seven expected files
in observed/ after all package, runtime, and determinism gates pass.

The package path may instead be supplied as EFFECT_PACKAGE_DIR.
EOF
}

case "${1:-}" in
  --update)
    MODE="update"
    shift
    ;;
  --help|-h)
    usage
    exit 0
    ;;
  --*)
    echo "REFUSED: unknown option: $1" >&2
    usage >&2
    exit 2
    ;;
esac

if [ "$#" -gt 1 ]; then
  echo "REFUSED: expected at most one effect package path" >&2
  usage >&2
  exit 2
fi

EFFECT_INPUT="${1:-${EFFECT_PACKAGE_DIR:-}}"
if [ -z "$EFFECT_INPUT" ]; then
  usage >&2
  exit 2
fi
if [ ! -d "$EFFECT_INPUT" ]; then
  echo "REFUSED: effect package directory does not exist" >&2
  exit 1
fi
EFFECT_DIR="$(cd "$EFFECT_INPUT" && pwd -P)"

WORK="$(mktemp -d)"
cleanup() {
  rm -rf -- "$WORK"
}
trap cleanup EXIT HUP INT TERM

digest_of() {
  shasum -a 256 "$1" | cut -d' ' -f1
}

require_exact_runtime() {
  local command_name="$1"
  local expected="$2"
  local actual
  if ! command -v "$command_name" >/dev/null 2>&1; then
    echo "REFUSED: required runtime is unavailable: $command_name" >&2
    return 1
  fi
  actual="$($command_name --version)"
  if [ "$actual" != "$expected" ]; then
    echo "REFUSED: $command_name version $actual != pinned $expected" >&2
    return 1
  fi
  echo "PIN MATCHED: $command_name $actual"
}

gate_file() {
  local label="$1"
  local expected="$2"
  local path="$3"
  local actual
  if [ ! -f "$path" ]; then
    echo "REFUSED: missing pinned package file: $label" >&2
    return 1
  fi
  actual="$(digest_of "$path")"
  if [ "$actual" != "$expected" ]; then
    echo "REFUSED: $label digest $actual != pinned $expected" >&2
    return 1
  fi
  echo "PIN MATCHED: $label $actual"
}

gate_dist_tree() {
  local manifest="$WORK/dist.sha256"
  local actual_count
  local actual_digest
  if [ ! -d "$EFFECT_DIR/dist" ]; then
    echo "REFUSED: missing pinned package directory: dist" >&2
    return 1
  fi

  # The manifest names files relative to the package root and is sorted under
  # the C locale. Its digest is therefore independent of the checkout path.
  (
    cd "$EFFECT_DIR"
    find dist -type f -print | LC_ALL=C sort | while IFS= read -r relative; do
      printf '%s  %s\n' "$(digest_of "$relative")" "$relative"
    done
  ) > "$manifest"

  actual_count="$(wc -l < "$manifest" | tr -d '[:space:]')"
  actual_digest="$(digest_of "$manifest")"
  if [ "$actual_count" != "$EXPECTED_DIST_FILE_COUNT" ]; then
    echo "REFUSED: dist file count $actual_count != pinned $EXPECTED_DIST_FILE_COUNT" >&2
    return 1
  fi
  if [ "$actual_digest" != "$EXPECTED_DIST_DIGEST" ]; then
    echo "REFUSED: dist tree digest $actual_digest != pinned $EXPECTED_DIST_DIGEST" >&2
    return 1
  fi
  echo "PIN MATCHED: dist files $actual_count"
  echo "PIN MATCHED: dist tree $actual_digest"
}

require_exact_runtime bun "$EXPECTED_BUN"
require_exact_runtime node "$EXPECTED_NODE"

gate_file package.json "$EXPECTED_PACKAGE_JSON" "$EFFECT_DIR/package.json"
gate_file src/SchemaRepresentation.ts "$EXPECTED_SCHEMA_REPRESENTATION" \
  "$EFFECT_DIR/src/SchemaRepresentation.ts"
gate_file src/SchemaAST.ts "$EXPECTED_SCHEMA_AST" "$EFFECT_DIR/src/SchemaAST.ts"
gate_file src/Schema.ts "$EXPECTED_SCHEMA" "$EFFECT_DIR/src/Schema.ts"
gate_file src/internal/schema/toRepresentation.ts "$EXPECTED_TO_REPRESENTATION" \
  "$EFFECT_DIR/src/internal/schema/toRepresentation.ts"
gate_file src/internal/schema/fromRepresentation.ts "$EXPECTED_FROM_REPRESENTATION" \
  "$EFFECT_DIR/src/internal/schema/fromRepresentation.ts"
gate_dist_tree

ACTUAL_EFFECT_VERSION="$(node -e 'console.log(require(process.argv[1]).version)' \
  "$EFFECT_DIR/package.json")"
if [ "$ACTUAL_EFFECT_VERSION" != "$EXPECTED_EFFECT_VERSION" ]; then
  echo "REFUSED: effect version $ACTUAL_EFFECT_VERSION != pinned $EXPECTED_EFFECT_VERSION" >&2
  exit 1
fi
echo "PIN MATCHED: effect@$ACTUAL_EFFECT_VERSION"

mkdir -p "$WORK/node_modules" "$WORK/fresh"
ln -s "$EFFECT_DIR" "$WORK/node_modules/effect"
printf '{ "name": "schema-representation-probe", "private": true, "type": "module" }\n' \
  > "$WORK/package.json"
cp "$HERE"/probes/*.ts "$WORK/"

declare -a PROBES=(
  "p1-emission-order.ts     01-canonical-emission-order.observed.txt"
  "p2-numeric-domains.ts    02-numeric-domains.observed.txt"
  "p3-round-trip-census.ts  03-census-round-trip.observed.txt"
  "p4-annotation-pruning.ts 04-annotation-pruning.observed.txt"
  "p5-degenerate-shapes.ts  05-degenerate-shapes.observed.txt"
  "p6-vectors.ts            06-vectors.observed.json"
)

DETERMINISM="$WORK/determinism.txt"
: > "$DETERMINISM"
for entry in "${PROBES[@]}"; do
  # shellcheck disable=SC2086
  set -- $entry
  probe="$1"
  outfile="$2"
  first="$WORK/fresh/$outfile"
  second="$WORK/second-$outfile"
  (cd "$WORK" && bun run "$probe") > "$first" 2>&1
  (cd "$WORK" && bun run "$probe") > "$second" 2>&1
  if ! cmp -s "$first" "$second"; then
    echo "REFUSED: nondeterministic output from $probe" >&2
    diff -u "$first" "$second" >&2 || true
    exit 1
  fi
  echo "${probe%.ts}: two separate processes -> IDENTICAL output" >> "$DETERMINISM"
done

cat > "$WORK/fresh/00-capture-environment.txt" <<EOF
# replay environment (path- and time-independent)
bun                                  $EXPECTED_BUN
node                                 $EXPECTED_NODE
effect                               $EXPECTED_EFFECT_VERSION

# exact package closure
package.json                         $EXPECTED_PACKAGE_JSON
src/SchemaRepresentation.ts         $EXPECTED_SCHEMA_REPRESENTATION
src/SchemaAST.ts                     $EXPECTED_SCHEMA_AST
src/Schema.ts                        $EXPECTED_SCHEMA
src/internal/schema/toRepresentation.ts    $EXPECTED_TO_REPRESENTATION
src/internal/schema/fromRepresentation.ts  $EXPECTED_FROM_REPRESENTATION
dist regular files                  $EXPECTED_DIST_FILE_COUNT
dist path-independent tree digest   $EXPECTED_DIST_DIGEST

# determinism: each probe run twice in separate OS processes
$(cat "$DETERMINISM")
EOF

cat > "$WORK/expected-names.txt" <<'EOF'
00-capture-environment.txt
01-canonical-emission-order.observed.txt
02-numeric-domains.observed.txt
03-census-round-trip.observed.txt
04-annotation-pruning.observed.txt
05-degenerate-shapes.observed.txt
06-vectors.observed.json
EOF

if [ "$MODE" = "update" ]; then
  mkdir -p "$OBSERVED"
  while IFS= read -r name; do
    cp "$WORK/fresh/$name" "$OBSERVED/$name"
  done < "$WORK/expected-names.txt"
fi

if [ ! -d "$OBSERVED" ]; then
  echo "REFUSED: retained output directory is missing: observed" >&2
  exit 1
fi

find "$OBSERVED" -mindepth 1 -maxdepth 1 -print \
  | sed 's#^.*/##' | LC_ALL=C sort > "$WORK/actual-names.txt"
if ! cmp -s "$WORK/expected-names.txt" "$WORK/actual-names.txt"; then
  echo "REFUSED: retained output set has missing or extra entries" >&2
  diff -u "$WORK/expected-names.txt" "$WORK/actual-names.txt" >&2 || true
  exit 1
fi

drift=0
while IFS= read -r name; do
  if ! cmp -s "$WORK/fresh/$name" "$OBSERVED/$name"; then
    echo "DRIFT: observed/$name" >&2
    diff -u "$OBSERVED/$name" "$WORK/fresh/$name" >&2 || true
    drift=1
  fi
done < "$WORK/expected-names.txt"
if [ "$drift" -ne 0 ]; then
  echo "REFUSED: fresh probe bytes differ from retained outputs" >&2
  exit 1
fi

if [ "$MODE" = "update" ]; then
  echo "UPDATED: 7 deterministic outputs"
else
  echo "PASS: 7 retained outputs match fresh deterministic bytes"
fi
