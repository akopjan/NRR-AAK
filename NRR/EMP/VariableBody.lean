import NRR.EMP.VariableBody.Phase1Interface
import NRR.EMP.VariableBody.Basic
import NRR.EMP.VariableBody.HalfspaceCoefficients
import NRR.EMP.VariableBody.IndicatorStability
import NRR.EMP.VariableBody.CellAreaContinuity
import NRR.EMP.VariableBody.AreaVector
import NRR.EMP.VariableBody.EqualAreaRelation
import NRR.EMP.VariableBody.CompactSiteFamily
import NRR.EMP.VariableBody.WeightBounds
import NRR.EMP.VariableBody.WeightBox
import NRR.EMP.VariableBody.ClosedGraph
import NRR.EMP.VariableBody.NormalizedWeightContinuity
import NRR.EMP.VariableBody.CanonicalCell
import NRR.EMP.VariableBody.CanonicalCellGraph
import NRR.EMP.VariableBody.CanonicalCellContinuity
import NRR.EMP.VariableBody.Children
import NRR.EMP.VariableBody.Partition

/-!
# `NRR.EMP.VariableBody` — variable-body equal-area power partitions

This public aggregator exposes the stable variable-body API for the Akopyan–Avvakumov–Karasev
power-partition development. All results are stated over a compact metric parameter space with a
continuous site family:

```
[MetricSpace X] [CompactSpace X]    sites : C(X, Config n)
```

The parent body varies in the Hausdorff subbody space `BodySpace K A` of a fixed planar parent
`K`. Over this compact family the development provides:

* continuity of each power-cell area (`continuous_cellArea`);
* the closed equal-area relation and the resulting continuity of the canonical normalized
  equal-area weight (`isClosed_isNormalizedEqualAreaWeight`, `weightBound`,
  `continuous_normalizedWeight_compactFamily`);
* continuity of the canonical cells and their packaging as subbodies
  (`continuous_canonicalCell`);
* the canonical children `child`, each lying in `BodySpace K (A / (n : ℝ))`, with continuous
  bodies, areas, and perimeters (`continuous_child`, `continuous_child_perimeter`);
* the pointwise equal-area partition exposed only as a dependent witness (`witness`), with no
  topology placed on `ConvexPartition`.

The continuity results hold on this compact family only; `Config n` itself is not claimed to be
compact. The proofs go through the equal-area existence and uniqueness cores reached via
`EMP.normalizedWeight`, and do not invoke `EMP.continuous_normalizedWeight_core`.
-/
