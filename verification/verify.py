"""Build the proofs, compare to the challenge, and write verification logs."""

import argparse
import hashlib
import json
import os
import platform
from datetime import datetime, timezone
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_VERDICTS = (
    "Lean default kernel accepts the solution",
    "nanoda kernel accepts the solution",
    "Your solution is okay!",
)
INPUT_FILES = (
    ".github/workflows/comparator.yml",
    "comparator.json",
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "verification/verify.py",
)


def input_hashes():
    sources = [
        path
        for folder in ("FClikelean", "lean", "leanWithComparator", "verification")
        for path in (ROOT / folder).glob("*.lean")
    ]
    sources.extend(ROOT / name for name in INPUT_FILES)
    sources.append(ROOT / "Model.lean")
    return "".join(
        f"{hashlib.sha256(path.read_bytes()).hexdigest()}  {path.relative_to(ROOT)}\n"
        for path in sorted(sources)
    )


def run(output, filename, *command):
    log = output / filename
    print(f"Running {' '.join(command)}", flush=True)
    with log.open("w", encoding="utf-8") as stream:
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    if result.returncode:
        with log.open("rb") as stream:
            stream.seek(max(0, log.stat().st_size - 6000))
            print(stream.read().decode(errors="replace"))
        raise SystemExit(f"{filename} failed (exit {result.returncode}). See {log}")
    print(f"{filename} passed", flush=True)
    return log


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--trusted-local", action="store_true",
        help="Disable bubblewrap for a trusted local copy on a host without it.",
    )
    parser.add_argument(
        "--full-replay", action="store_true",
        help="Also replay the entire imported Lean environment, including Mathlib.",
    )
    parser.add_argument(
        "--output", type=Path, default=ROOT / "verification" / "results",
        help="New directory for logs and the verification receipt.",
    )
    args = parser.parse_args()
    commit = os.environ.get("GITHUB_SHA")
    if commit:
        actual_commit = subprocess.check_output(
            ("git", "rev-parse", "HEAD"), cwd=ROOT, text=True
        ).strip()
        if actual_commit != commit or args.trusted_local:
            raise SystemExit("CI requires the intended commit and the Comparator sandbox.")

    output = args.output.resolve()
    output.mkdir(parents=True)
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    hashes = input_hashes()
    (output / "inputs.sha256").write_text(hashes, encoding="utf-8")
    run(output, "build.log", "lake", "build")
    run(output, "statement.log", "lake", "env", "lean", "verification/Check.lean")
    command = ["lake", "env", "lake", "comparator"]
    if args.trusted_local:
        command.append("--inadvisably-no-sandbox")
    comparator = run(output, "comparator.log", *command)
    verdict = comparator.read_text(encoding="utf-8")
    if not all(message in verdict for message in REQUIRED_VERDICTS):
        raise SystemExit(f"Comparator did not report approval from both kernels. See {comparator}")

    if args.full_replay:
        run(output, "full-replay.log", "lake", "env", "leanchecker", "--fresh", "--verbose",
            config["solution_module"])
    if input_hashes() != hashes:
        raise SystemExit("Verification inputs changed during the run.")
    receipt = {
        "accepted": True,
        "checked_at_utc": datetime.now(timezone.utc).isoformat(timespec="seconds"),
        "platform": platform.system(),
        "github_commit": commit,
        "sandbox": "trusted local" if args.trusted_local else "bubblewrap",
        "comparator_kernels": ["Lean", "nanoda"],
        "fresh_lean_export_replay": True,
        "full_environment_replayed": args.full_replay,
        "theorems": config["theorem_names"],
        "definitions": config["definition_names"],
        "permitted_axioms": config["permitted_axioms"],
    }
    (output / "result.json").write_text(
        json.dumps(receipt, indent=2, ensure_ascii=False) + "\n", encoding="utf-8"
    )


if __name__ == "__main__":
    main()
