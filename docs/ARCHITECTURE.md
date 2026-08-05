# Architecture

The project uses one main Lean library, `NRR`, plus the small `HumanVerification` library.

- `NRR/AAK/MainTheoremAffinePullback.lean` exports the existing Nandakumar-Ramana Rao theorem with
  the internal Cauchy perimeter.
- `NRR/OddSphereDegree/` contains the odd-degree sphere and algebraic-topology machinery required by
  the obstruction argument. These modules were moved from the former separate source tree.
- `HumanVerification/CauchyCrofton/` contains the proposed bridge from the internal Cauchy perimeter
  to the one-dimensional Hausdorff measure of a convex frontier.
- `HumanVerification/Main.lean` is the intended human-facing statement file.

All project module paths and code namespaces use `NRR`; there is no separate `HamSandwich` library.
