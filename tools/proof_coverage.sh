#!/usr/bin/env bash
set -euo pipefail
guess_src() {
  if [ -d "src" ]; then echo "src"; elif [ -d "lean/src" ]; then echo "lean/src"; else echo ""; fi
}
SRC="$(guess_src)"
if [ -z "$SRC" ]; then
  echo "defs=0"
  echo "theorems=0"
  echo "sorry=999"
  echo "status=NO_SRC"
  exit 0
fi
TOTAL_DEFS=$(grep -R -E "^[[:space:]]*(def|noncomputable[[:space:]]+def|instance|abbrev)[[:space:]]+" -n "$SRC" | wc -l | tr -d ' ')
TOTAL_THMS=$(grep -R -E "^[[:space:]]*(theorem|lemma)[[:space:]]+" -n "$SRC" | wc -l | tr -d ' ')
SORRY_COUNT=$(grep -R "sorry" -n "$SRC" | wc -l | tr -d ' ')
echo "defs=${TOTAL_DEFS}"
echo "theorems=${TOTAL_THMS}"
echo "sorry=${SORRY_COUNT}"
if [ "$SORRY_COUNT" -eq 0 ]; then echo "status=SORRY_FREE"; else echo "status=INCOMPLETE"; fi