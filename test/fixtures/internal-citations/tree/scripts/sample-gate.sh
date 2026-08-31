#!/usr/bin/env bash
# Synthetic fixture gate.
#
# Scanned trees include scripts/, so this file exists to prove that a shell
# script carrying only host-source citations is accepted:
# `SchemaRepresentation.ts:406` declares the closed union, `:436` the checks.
set -euo pipefail
printf 'PASS synthetic fixture gate\n'
