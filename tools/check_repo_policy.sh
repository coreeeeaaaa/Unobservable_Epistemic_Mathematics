#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
cd "$repo_root"

# 1. Disallowed paths must not appear in the index or working tree.
prohibited_paths=(
  "design_docs"
  "agent_reports"
  "4_OPERATIONS"
  ".internal"
  "orchestrator_control"
  "systems"
  "CLAUDE.md"
  "GEMINI.md"
  "AGENTS.md"
)

violations=()

for path in "${prohibited_paths[@]}"; do
  if git ls-files -- "$path" >/dev/null 2>&1; then
    tracked=$(git ls-files -- "$path")
    if [[ -n "$tracked" ]]; then
      violations+=("tracked: $path")
    fi
  fi
  if [[ -e "$path" ]]; then
    violations+=("workspace: $path")
  fi
 done

if [[ ${#violations[@]} -gt 0 ]]; then
  echo "❌ Repository policy violation detected:"
  for v in "${violations[@]}"; do
    echo "  - $v"
  done
  exit 1
fi

# 2. Prevent accidental regression to placeholders or sample content.
pattern_violations=""
if command -v rg >/dev/null 2>&1; then
  pattern_violations=$(git diff --cached --name-only | while read -r file; do
    if [[ "$file" == *.lean || "$file" == *.md ]]; then
      if git diff --cached -- "$file" | rg -i "\\b(sample|placeholder|dummy code|todo|to-do)\\b" --context 0 >/dev/null; then
        echo "$file"
      fi
    fi
  done)
else
  echo "⚠️  ripgrep not found; skipping placeholder scan"
fi

if [[ -n "$pattern_violations" ]]; then
  echo "❌ Placeholder or sample language detected in staged changes:"
  echo "$pattern_violations"
  exit 1
fi

# 3. Ensure Lean project remains sorry-free when proof coverage is available.
if [[ -f tools/proof_coverage.sh ]]; then
  if command -v lake >/dev/null 2>&1; then
    tmp_report=$(mktemp)
    bash tools/proof_coverage.sh >"$tmp_report"
    status=$(grep '^status=' "$tmp_report" | cut -d= -f2)
    if [[ "$status" != "SORRY_FREE" ]]; then
      echo "❌ proof_coverage.sh reports status=$status"
      cat "$tmp_report"
      rm -f "$tmp_report"
      exit 1
    fi
    rm -f "$tmp_report"
  else
    echo "⚠️  lake not found; skipping coverage gate"
  fi
fi

echo "✅ Repository policy check passed."
