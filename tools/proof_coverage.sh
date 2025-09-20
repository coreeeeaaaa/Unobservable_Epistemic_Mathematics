#!/usr/bin/env bash
set -euo pipefail
guess_src() {
  if [ -d "lean/src" ]; then echo "lean/src"; elif [ -d "src" ]; then echo "src"; else echo ""; fi
}
SRC="$(guess_src)"
[ -n "$SRC" ] || { echo "defs=0"; echo "theorems=0"; echo "sorry=999"; echo "status=NO_SRC"; exit 0; }
TOTAL_DEFS=$(grep -R -E "^[[:space:]]*def[[:space:]]+" -n "$SRC" | wc -l | tr -d ' ')
TOTAL_THMS=$(grep -R -E "^[[:space:]]*(theorem|lemma)[[:space:]]+" -n "$SRC" | wc -l | tr -d ' ')
SORRY_COUNT=$(grep -R "sorry" -n "$SRC" | wc -l | tr -d ' ')
echo "defs=${TOTAL_DEFS}"
echo "theorems=${TOTAL_THMS}"
echo "sorry=${SORRY_COUNT}"
if [ "$SORRY_COUNT" -eq 0 ]; then echo "status=SORRY_FREE"; else echo "status=INCOMPLETE"; fi
