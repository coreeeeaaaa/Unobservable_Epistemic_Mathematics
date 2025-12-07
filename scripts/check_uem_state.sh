#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

step() { printf '\n[%s] %s\n' "$1" "$2"; }

step "1/4" "Checking for sorry holes under formal/"
if rg --files-with-matches "sorry" "$ROOT/formal"; then
  echo "Found 'sorry' occurrences. Fill proofs before release." >&2
  exit 1
fi

step "2/4" "Running lake build UEM"
(cd "$ROOT/formal" && lake build UEM)

step "3/4" "Validating spec version linkage"
latest_spec="$(python - <<'PY'
from pathlib import Path
import re, sys

idx = Path("docs/spec/VERSION_INDEX.md")
if not idx.exists():
    sys.exit("docs/spec/VERSION_INDEX.md missing")
text = idx.read_text()
m = re.search(r"Latest.*?:.*?(docs/spec/[A-Za-z0-9_.\\-]+\\.md)", text)
if not m:
    sys.exit("Latest spec path not found in VERSION_INDEX.md")
print(m.group(1))
PY
)"

if [ ! -f "$ROOT/$latest_spec" ]; then
  echo "Latest spec path missing: $latest_spec" >&2
  exit 1
fi

if ! grep -q "$latest_spec" "$ROOT/README.md"; then
  echo "README missing link to latest spec ($latest_spec)" >&2
  exit 1
fi

legacy_spec="docs/spec/UEM_MATHEMATICAL_SYSTEM_SPEC_v3.0.md"
if [ ! -f "$ROOT/$legacy_spec" ]; then
  echo "Legacy spec pointer missing: $legacy_spec" >&2
  exit 1
fi

step "4/4" "All checks passed"
