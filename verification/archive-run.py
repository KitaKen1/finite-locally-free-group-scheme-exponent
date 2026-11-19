"""Preserve a successful Lean verification run and its original GitHub artifacts."""

import argparse
import hashlib
import io
import json
from pathlib import Path
import re
import subprocess
import tempfile
from zipfile import ZipFile

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT_FILES = ("build.log", "statement.log", "comparator.log", "inputs.sha256", "result.json")
VERDICTS = (
    b"nanoda kernel accepts the solution",
    b"Lean default kernel accepts the solution",
    b"Your solution is okay!",
)


def get(repo, resource):
    return subprocess.check_output(("gh", "api", "--method", "GET", f"repos/{repo}/{resource}"))


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def verify_artifact(payload, digest, commit, config):
    if digest != f"sha256:{sha256(payload)}":
        raise SystemExit("Downloaded artifact does not match the GitHub SHA-256 digest.")
    with ZipFile(io.BytesIO(payload)) as archive:
        names = archive.namelist()
        if archive.testzip() is not None or any(names.count(name) != 1 for name in ARTIFACT_FILES):
            raise SystemExit("Artifact ZIP failed its integrity or required-file check.")
        files = {name: archive.read(name) for name in ARTIFACT_FILES}

    receipt = json.loads(files["result.json"])
    expected = {
        "accepted": True,
        "github_commit": commit,
        "sandbox": "bubblewrap",
        "comparator_kernels": ["Lean", "nanoda"],
        "fresh_lean_export_replay": True,
        "theorems": config["theorem_names"],
        "definitions": config["definition_names"],
        "permitted_axioms": config["permitted_axioms"],
    }
    if any(receipt.get(key) != value for key, value in expected.items()):
        raise SystemExit("Verification receipt differs from the expected commit or proof targets.")
    if not all(verdict in files["comparator.log"] for verdict in VERDICTS):
        raise SystemExit("Comparator log is missing a required kernel verdict.")
    return files


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo", required=True, help="OWNER/REPO")
    parser.add_argument("--run", type=int, required=True)
    parser.add_argument("--attempt", type=int, required=True)
    parser.add_argument("--expected-commit", required=True, help="Full SHA of the tested commit")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if not re.fullmatch(r"[\w.-]+/[\w.-]+", args.repo):
        parser.error("--repo must be OWNER/REPO")
    if not re.fullmatch(r"[0-9a-f]{40}", args.expected_commit):
        parser.error("--expected-commit must be a full SHA")
    if args.output.exists():
        parser.error("--output must be a new directory")

    run = f"actions/runs/{args.run}"
    attempt_path = f"{run}/attempts/{args.attempt}"
    attempt_data = get(args.repo, attempt_path)
    attempt = json.loads(attempt_data)
    if attempt["conclusion"] != "success" or attempt["run_attempt"] != args.attempt:
        raise SystemExit("The requested run attempt did not succeed.")
    if attempt["event"] != "pull_request" and attempt["head_sha"] != args.expected_commit:
        raise SystemExit("The run attempt is for a different commit.")

    artifacts = json.loads(get(args.repo, f"{run}/artifacts?per_page=100"))
    artifact_name = f"lean-verification-{args.run}-{args.attempt}"
    matches = [item for item in artifacts["artifacts"] if item["name"] == artifact_name]
    if artifacts["total_count"] > 100 or len(matches) != 1 or matches[0]["expired"]:
        raise SystemExit(f"Expected one available artifact named {artifact_name}.")
    artifact = matches[0]
    payload = get(args.repo, f'actions/artifacts/{artifact["id"]}/zip')
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    files = verify_artifact(payload, artifact.get("digest"), args.expected_commit, config)

    workflow_logs = get(args.repo, f"{attempt_path}/logs")
    with ZipFile(io.BytesIO(workflow_logs)) as archive:
        if archive.testzip() is not None:
            raise SystemExit("The workflow log ZIP failed its integrity check.")
    files.update({
        "attempt.json": attempt_data,
        "artifact.json": (json.dumps(artifact, indent=2) + "\n").encode(),
        "lean-verification.zip": payload,
        "workflow-logs.zip": workflow_logs,
    })
    checksums = "".join(f"{sha256(data)}  {name}\n" for name, data in sorted(files.items()))
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(dir=args.output.parent) as staging:
        archive_dir = Path(staging) / "archive"
        archive_dir.mkdir()
        for name, data in files.items():
            (archive_dir / name).write_bytes(data)
        (archive_dir / "SHA256SUMS").write_text(checksums, encoding="utf-8")
        archive_dir.rename(args.output)
    print(f"Archived {attempt['html_url']} to {args.output}")


if __name__ == "__main__":
    main()
