#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
if rg -n '\b(sorry|axiom|admit)\b' --glob '*.lean' NewLang NewLang.lean; then
  echo 'Unexpected proof placeholder or added axiom in project Lean sources.' >&2
  exit 1
else
  status=$?
  if [ "$status" -ne 1 ]; then exit "$status"; fi
fi
lake build
check_file=$(mktemp --suffix=.lean)
trap 'rm -f "$check_file"' EXIT
cat > "$check_file" <<'LEAN'
import NewLang
#print axioms NewLang.F0.wellFormed_surviving_dependencies_live
#print axioms NewLang.F0.empty_wellFormed
LEAN
lake env lean "$check_file"
