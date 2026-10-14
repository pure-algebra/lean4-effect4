#!/bin/bash
set -euo pipefail
lake build Test.Dogfood.Scenario.Todo.Cached Tools.RunChecks
lake env lean apps/todo/Check.lean
