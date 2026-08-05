# Human verification

The complete public statement is contained in:

```text
HumanVerification/Main.lean
```

The file defines:

- the Euclidean plane;
- `ConvexFigure` as a compact convex set with nonempty interior;
- area using planar Lebesgue measure;
- perimeter using the one-dimensional Hausdorff measure of the frontier;
- convex partitions;
- the final equal-area/equal-perimeter theorem.

It imports the proof layer through:

```lean
import HumanVerification.EqualAreaEqualPerimeterPartitionWrapper
```

The adapter between the public `ConvexFigure` and the internal NRR convex-body representation is a
local `letI` inside the theorem proof. It is not a global declaration and is not part of the theorem
statement.

The file ends with:

```lean
#print axioms HumanVerification.equalAreaEqualPerimeterPartition
```

Verification commands:

```bash
lake build
lake env lean HumanVerification/Check.lean
```
