#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd -- "${SCRIPT_DIR}/.." && pwd)"

cd "${PROJECT_ROOT}"

lake build
python3 scripts/check_dependencies.py
lake env lean HumanVerification/Main.lean
lake env lean HumanVerification/Check.lean
python3 scripts/audit_project.py
