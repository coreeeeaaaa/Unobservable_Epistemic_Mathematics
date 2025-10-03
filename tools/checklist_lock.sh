#!/usr/bin/env bash
set -euo pipefail

usage() {
  cat <<'USAGE'
Usage: tools/checklist_lock.sh <lock|unlock|status>

  lock    Remove write permission from checklist files (makes them read-only).
  unlock  Restore write permission for the current user (required before editing).
  status  Show current permission bits for checklist files.
USAGE
}

if [[ $# -ne 1 ]]; then
  usage
  exit 1
fi

root_dir="$(git rev-parse --show-toplevel)"
checklists=("CHECKLIST.md" "CHECKLIST_ATOMIC.md")
command="$1"

case "$command" in
  lock)
    for file in "${checklists[@]}"; do
      chmod a-w "$root_dir/$file"
    done
    echo "Checklists locked (read-only)."
    ;;
  unlock)
    for file in "${checklists[@]}"; do
      chmod u+w "$root_dir/$file"
    done
    echo "Checklists unlocked (writable by current user)."
    ;;
  status)
    for file in "${checklists[@]}"; do
      ls -l "$root_dir/$file"
    done
    ;;
  *)
    usage
    exit 1
    ;;
esac
