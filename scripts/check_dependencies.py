#!/usr/bin/env python3
"""Verify that the checked-out Mathlib dependency matches lake-manifest.json."""

from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from urllib.parse import urlparse

PROJECT_ROOT = Path(__file__).resolve().parents[1]
MANIFEST_PATH = PROJECT_ROOT / "lake-manifest.json"
EXPECTED_MATHLIB_URL = "https://github.com/leanprover-community/mathlib4.git"


def fail(message: str) -> "NoReturn":
    print(f"dependency check failed: {message}", file=sys.stderr)
    raise SystemExit(1)


def run_git(repository: Path, *args: str) -> str:
    try:
        completed = subprocess.run(
            ["git", "-C", str(repository), *args],
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except FileNotFoundError:
        fail("git is not installed")
    except subprocess.CalledProcessError as error:
        detail = error.stderr.strip() or error.stdout.strip()
        fail(f"git {' '.join(args)} failed in {repository}: {detail}")
    return completed.stdout.strip()


def normalize_git_url(url: str) -> str:
    value = url.strip().removesuffix("/").removesuffix(".git")
    if value.startswith("git@github.com:"):
        value = "https://github.com/" + value.removeprefix("git@github.com:")
    parsed = urlparse(value)
    if parsed.scheme in {"http", "https"}:
        host = parsed.netloc.lower()
        path = parsed.path.rstrip("/")
        return f"https://{host}{path}"
    return value


def main() -> None:
    try:
        manifest = json.loads(MANIFEST_PATH.read_text(encoding="utf-8"))
    except FileNotFoundError:
        fail(f"missing {MANIFEST_PATH.name}")
    except json.JSONDecodeError as error:
        fail(f"invalid {MANIFEST_PATH.name}: {error}")

    packages = manifest.get("packages")
    if not isinstance(packages, list):
        fail("lake-manifest.json has no package list")

    mathlib = next(
        (package for package in packages if package.get("name") == "mathlib"),
        None,
    )
    if mathlib is None:
        fail("mathlib is absent from lake-manifest.json")
    if mathlib.get("type") != "git":
        fail("mathlib is not pinned as a git dependency")

    manifest_url = mathlib.get("url")
    manifest_rev = mathlib.get("rev")
    if not isinstance(manifest_url, str) or not isinstance(manifest_rev, str):
        fail("mathlib URL or revision is missing from lake-manifest.json")
    if normalize_git_url(manifest_url) != normalize_git_url(EXPECTED_MATHLIB_URL):
        fail(f"unexpected Mathlib source URL: {manifest_url}")
    if len(manifest_rev) != 40 or any(c not in "0123456789abcdef" for c in manifest_rev.lower()):
        fail(f"Mathlib revision is not a full commit hash: {manifest_rev}")

    packages_dir = manifest.get("packagesDir", ".lake/packages")
    checkout = PROJECT_ROOT / packages_dir / "mathlib"
    if not checkout.is_dir():
        fail(f"Mathlib checkout is missing: {checkout}")

    actual_rev = run_git(checkout, "rev-parse", "HEAD")
    if actual_rev != manifest_rev:
        fail(f"Mathlib revision mismatch: expected {manifest_rev}, found {actual_rev}")

    remote_url = run_git(checkout, "remote", "get-url", "origin")
    if normalize_git_url(remote_url) != normalize_git_url(manifest_url):
        fail(f"Mathlib origin mismatch: expected {manifest_url}, found {remote_url}")

    status = run_git(checkout, "status", "--porcelain", "--untracked-files=all")
    if status:
        fail("Mathlib checkout contains local modifications or untracked files")

    print(f"Mathlib source: {manifest_url}")
    print(f"Mathlib revision: {actual_rev}")
    print("Mathlib checkout: clean")


if __name__ == "__main__":
    main()
