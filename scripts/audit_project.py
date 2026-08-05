#!/usr/bin/env python3
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_PARTS = {".git", ".lake"}

lean_files = sorted(
    path
    for path in ROOT.rglob("*.lean")
    if not EXCLUDED_PARTS.intersection(path.relative_to(ROOT).parts)
)

module_to_file = {
    ".".join(path.relative_to(ROOT).with_suffix("").parts): path
    for path in lean_files
}

import_re = re.compile(r"^\s*import\s+([^\s]+)", re.MULTILINE)
imports: dict[str, list[str]] = {}
unresolved: list[tuple[str, str]] = []

for module, path in module_to_file.items():
    dependencies = import_re.findall(path.read_text(encoding="utf-8"))
    imports[module] = [dep for dep in dependencies if dep in module_to_file]
    for dependency in dependencies:
        if dependency.startswith(("NRR.", "HumanVerification.")) and dependency not in module_to_file:
            unresolved.append((module, dependency))

state: dict[str, int] = {}
cycles: list[list[str]] = []


def visit(module: str, trail: list[str]) -> None:
    status = state.get(module, 0)
    if status == 1:
        start = trail.index(module)
        cycles.append(trail[start:] + [module])
        return
    if status == 2:
        return

    state[module] = 1
    for dependency in imports.get(module, []):
        visit(dependency, trail + [dependency])
    state[module] = 2


for module in module_to_file:
    visit(module, [module])

bypass_re = re.compile(
    r"\b(?:sorry|admit|implemented_by|unsafe)\b|^\s*axiom\b",
    re.MULTILINE,
)
bypass_hits = [
    path.relative_to(ROOT)
    for path in lean_files
    if bypass_re.search(path.read_text(encoding="utf-8"))
]

print(f"Lean sources: {len(lean_files)}")
print(f"Unresolved project imports: {len(unresolved)}")
print(f"Import cycles: {len(cycles)}")
print(f"Files with proof bypasses: {len(bypass_hits)}")

for module, dependency in unresolved[:20]:
    print("UNRESOLVED", module, dependency)
for cycle in cycles[:10]:
    print("CYCLE", " -> ".join(cycle))
for path in bypass_hits[:20]:
    print("BYPASS", path)

if unresolved or cycles or bypass_hits:
    sys.exit(1)
