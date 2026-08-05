# Verification

Pinned environment:

- Lean `v4.28.0`
- Mathlib commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`

Run from the repository root:

```bash
./scripts/verify.sh
```

The script performs:

```bash
lake build
python3 scripts/check_dependencies.py
lake env lean HumanVerification/Main.lean
lake env lean HumanVerification/Check.lean
python3 scripts/audit_project.py
```

`HumanVerification/Check.lean` contains definitional-equality checks for the public plane, area,
perimeter, and partition predicate. These checks fail if the public definitions cease to use the
intended Mathlib objects.

`check_dependencies.py` verifies that the Mathlib checkout comes from the official repository,
matches the exact commit in `lake-manifest.json`, and contains no local changes.

The source audit checks project imports, import cycles, and common proof bypasses. These checks
supplement, but do not replace, verification by the Lean kernel.
