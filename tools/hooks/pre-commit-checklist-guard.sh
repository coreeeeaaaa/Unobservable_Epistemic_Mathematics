#!/usr/bin/env bash
set -euo pipefail

root_dir="$(git rev-parse --show-toplevel)"
checklists=("CHECKLIST.md" "CHECKLIST_ATOMIC.md")
errors=()

for file in "${checklists[@]}"; do
  # Detect staged deletion or rename
  status="$(git diff --cached --name-status -- "$file" || true)"
  if echo "$status" | grep -E "^D" >/dev/null 2>&1; then
    errors+=("• $file is staged for deletion. This file is protected.")
  fi
  if echo "$status" | grep -E "^R" >/dev/null 2>&1; then
    errors+=("• $file is staged for rename. Please keep the original path.")
  fi
  if [[ ! -f "$root_dir/$file" ]]; then
    errors+=("• $file is missing from the working tree.")
    continue
  fi
  line_count=$(wc -l < "$root_dir/$file")
  if [[ "$line_count" -lt 10 ]]; then
    errors+=("• $file currently has only $line_count lines. Was content truncated?")
  fi
  if [[ ! -s "$root_dir/$file" ]]; then
    errors+=("• $file is empty. Please restore its contents.")
  fi
  # Ensure file remains tracked
  if ! git ls-files -- "$file" >/dev/null 2>&1; then
    errors+=("• $file is not tracked by git. Add it back with 'git add $file'.")
  fi
  # Detect staged removal of execute bit, should always be regular file (no exec) - not necessary
  # Ensure staged diff does not remove entire content
  staged_removed_lines=$(git diff --cached -- "$file" | grep -c '^-' || true)
  staged_added_lines=$(git diff --cached -- "$file" | grep -c '^+' || true)
  if [[ "$staged_removed_lines" -gt 0 && "$staged_added_lines" -eq 0 ]]; then
    errors+=("• $file has staged removals with no additions. Check you are not wiping it.")
  fi

done

if [[ ${#errors[@]} -gt 0 ]]; then
  printf '\nChecklist guard blocked the commit for the following reasons:\n' >&2
  printf '%s\n' "${errors[@]}" >&2
  printf '\nRestore the files or run "git restore --staged <file>" to unstage the deletion.\n' >&2
  exit 1
fi

exit 0
