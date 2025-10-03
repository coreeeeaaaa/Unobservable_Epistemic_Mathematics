#!/usr/bin/env bash
set -euo pipefail

repo_root=$(git rev-parse --show-toplevel)
internal_root="$repo_root/../INTERNAL/unobservable_mathematics"

mkdir -p "$internal_root"

move_if_exists() {
  local item="$1"
  if [[ -e "$repo_root/$item" ]]; then
    echo "[move] $item -> $internal_root/$item"
    mv "$repo_root/$item" "$internal_root/"
  fi
}

move_if_exists "design_docs"
move_if_exists "agent_reports"
move_if_exists "4_OPERATIONS"
move_if_exists ".internal"
move_if_exists "orchestrator_control"
move_if_exists "systems"
move_if_exists "CLAUDE.md"
move_if_exists "GEMINI.md"
move_if_exists "AGENTS.md"

echo "✔ Internal assets relocated to $internal_root"
