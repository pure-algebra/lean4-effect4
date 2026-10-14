#!/bin/bash
if [ "${1-}" = --no-install ]; then
  exec /Users/pooks/.local/share/mise/shims/bun "$@"
fi
exec /Users/pooks/.local/share/mise/shims/bun --no-install "$@"
