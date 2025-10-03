#!/usr/bin/env python3
"""Phase verification automation for UEM Lean project."""

import argparse
import json
import shutil
import subprocess
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CONFIG_FILE = ROOT / "tools" / "phase" / "phase_config.json"
LOG_DIR = ROOT / "logs" / "run"
CHECKLIST_FILE = ROOT / "CHECKLIST.md"
CHECKLIST_ATOMIC_FILE = ROOT / "CHECKLIST_ATOMIC.md"
STATUS_FILE = ROOT / "STATUS.md"
PROOF_COVERAGE_FILE = ROOT / "proof_coverage.txt"
SORRY_COUNT_FILE = ROOT / "sorry_count.txt"
RELEASE_PHASE_DIR = ROOT / "release" / "phases"


def load_config():
    if not CONFIG_FILE.exists():
        raise FileNotFoundError(f"Missing phase config: {CONFIG_FILE}")
    with CONFIG_FILE.open() as f:
        return json.load(f)


def run_command(cmd, cwd):
    result = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True)
    return result


def write_log(phase, name, stdout, stderr):
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    LOG_DIR.mkdir(parents=True, exist_ok=True)
    log_path = LOG_DIR / f"{phase}_{name}_{timestamp}.log"
    with log_path.open("w") as f:
        f.write(stdout)
        if stderr:
            f.write("\n-- STDERR --\n")
            f.write(stderr)
    return log_path


def update_proof_coverage(defs, theorems, sorry, status):
    with PROOF_COVERAGE_FILE.open("w") as f:
        f.write(f"defs={defs}\n")
        f.write(f"theorems={theorems}\n")
        f.write(f"sorry={sorry}\n")
        f.write(f"status={status}\n")


def update_sorry_count(count):
    with SORRY_COUNT_FILE.open("w") as f:
        f.write(str(count))


def mark_checklist(phase):
    for file in [CHECKLIST_FILE, CHECKLIST_ATOMIC_FILE]:
        if not file.exists():
            continue
        text = file.read_text()
        new_text = text.replace(f"[ ] {phase}", f"[x] {phase}")
        file.write_text(new_text)


def update_status(phase, message):
    content = STATUS_FILE.read_text() if STATUS_FILE.exists() else ""
    marker = f"## {phase}"
    if marker in content:
        sections = content.split(marker)
        sections[1] = f"\n{message}\n" + sections[1]
        STATUS_FILE.write_text(marker.join(sections))
    else:
        with STATUS_FILE.open("a") as f:
            f.write(f"\n## {phase}\n{message}\n")


def copy_logs_to_release(phase, logs):
    dest_dir = RELEASE_PHASE_DIR / phase / "logs" / "run"
    dest_dir.mkdir(parents=True, exist_ok=True)
    for log in logs:
        shutil.copy(log, dest_dir)


def verify_phase(phase):
    config = load_config()
    if phase not in config:
        raise ValueError(f"Unknown phase: {phase}")
    cfg = config[phase]
    logs = []
    for command in cfg.get("commands", []):
        cmd = command["cmd"]
        name = command["name"]
        cwd = ROOT / command.get("cwd", "lean")
        result = run_command(cmd, cwd=cwd)
        log_file = write_log(phase, name, result.stdout, result.stderr)
        logs.append(log_file)
        if result.returncode != 0:
            raise RuntimeError(f"Command {cmd} failed; see {log_file}")
    coverage = cfg.get("coverage")
    if coverage:
        update_proof_coverage(coverage["defs"], coverage["theorems"], coverage["sorry"], coverage["status"])
    update_sorry_count(cfg.get("sorry_count", 0))
    mark_checklist(phase)
    update_status(phase, cfg.get("status_message", "Phase verification complete."))
    copy_logs_to_release(phase, logs)


def main():
    parser = argparse.ArgumentParser(description="Verify a proof phase")
    parser.add_argument("--phase", required=True)
    args = parser.parse_args()
    verify_phase(args.phase)


if __name__ == "main":
    main()
