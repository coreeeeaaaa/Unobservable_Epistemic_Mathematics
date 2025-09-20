#!/usr/bin/env bash
set -euo pipefail
SRC="src"
[ -d "lean/src" ] && SRC="lean/src"
TOTAL_DEFS=$(grep -R -E "^[[:space:]]*def " -n ${SRC} | wc -l | tr -d ' ')
TOTAL_THMS=$(grep -R -E "^[[:space:]]*(theorem|lemma) " -n ${SRC} | wc -l | tr -d ' ')
SORRY_COUNT=$(grep -R "sorry" -n ${SRC} | wc -l | tr -d ' ')
echo "defs=${TOTAL_DEFS}"
echo "theorems=${TOTAL_THMS}"
echo "sorry=${SORRY_COUNT}"
if [ "$SORRY_COUNT" -gt 0 ]; then
  echo "status=INCOMPLETE"
else
  echo "status=SORRY_FREE"
fi
