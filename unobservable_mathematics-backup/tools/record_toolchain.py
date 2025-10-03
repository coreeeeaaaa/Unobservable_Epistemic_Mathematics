#!/usr/bin/env python3
"""
Utility to run standard Lean toolchain commands and append results into a
timestamped report. References `formalization/OPERATIONS_MANUAL.md` logging
requirements and keeps the documentation trail in `reports/`.
"""
from __future__ import annotations

import argparse
import datetime as dt
import subprocess
from pathlib import Path
from textwrap import indent

DEFAULT_COMMANDS = [
    ["lake", "update"],
    ["lake", "build"],
    ["lake", "exe", "uemCli"],
]


def run_commands(commands: list[list[str]], workdir: Path) -> list[tuple[list[str], subprocess.CompletedProcess[str]]]:
    results = []
    for cmd in commands:
        completed = subprocess.run(cmd, cwd=workdir, text=True, capture_output=True)
        results.append((cmd, completed))
    return results


def append_report(results, report_path: Path, lean_relpath: Path) -> None:
    timestamp = dt.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
    header = f"# Toolchain Log — {timestamp}\n"
    if not report_path.exists():
        report_path.write_text(header, encoding="utf-8")
    else:
        with report_path.open("a", encoding="utf-8") as fp:
            fp.write("\n" + header)
    with report_path.open("a", encoding="utf-8") as fp:
        fp.write(f"Working directory: `{lean_relpath}`\n\n")
        for cmd, completed in results:
            command_str = " ".join(cmd)
            fp.write(f"## $ {command_str}\n")
            fp.write(f"Exit code: {completed.returncode}\n\n")
            if completed.stdout:
                fp.write("stdout:\n")
                fp.write(indent(completed.stdout, "    "))
                fp.write("\n")
            if completed.stderr:
                fp.write("stderr:\n")
                fp.write(indent(completed.stderr, "    "))
                fp.write("\n")


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Run Lean toolchain commands and log outputs")
    parser.add_argument(
        "commands",
        nargs="*",
        help="Commands to run (provide as quoted strings). Default runs lake update/build/exe.",
    )
    parser.add_argument(
        "--report",
        default=None,
        help="Optional path for the log file (defaults to reports/toolchain_log_YYYYMMDD.md).",
    )
    return parser.parse_args()


def build_command_matrix(raw_commands: list[str]) -> list[list[str]]:
    if not raw_commands:
        return DEFAULT_COMMANDS
    return [cmd.split() for cmd in raw_commands]


def main() -> int:
    repo_root = Path(__file__).resolve().parents[3]
    lean_dir = repo_root / "unobservable_mathematics" / "formalization" / "lean"
    reports_dir = repo_root / "unobservable_mathematics" / "reports"
    reports_dir.mkdir(parents=True, exist_ok=True)

    args = parse_args()
    commands = build_command_matrix(args.commands)

    results = run_commands(commands, lean_dir)

    if args.report:
        report_path = Path(args.report)
        if not report_path.is_absolute():
            report_path = repo_root / report_path
    else:
        stamp = dt.datetime.now().strftime("%Y%m%d")
        report_path = reports_dir / f"toolchain_log_{stamp}.md"

    append_report(results, report_path, lean_dir.relative_to(repo_root))

    for cmd, completed in results:
        status = "OK" if completed.returncode == 0 else "FAIL"
        print(f"{status:<5} {' '.join(cmd)}")
    print(f"log appended to {report_path.relative_to(repo_root)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
