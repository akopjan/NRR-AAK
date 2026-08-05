import NRR.BodySpace.Basic
import NRR.BodySpace.Topology
import NRR.BodySpace.ConvexClosed
import NRR.BodySpace.Compactness
import NRR.BodySpace.BoundaryNull
import NRR.BodySpace.MembershipStability
import NRR.BodySpace.AreaContinuity
import NRR.BodySpace.PositiveArea
import NRR.BodySpace.SupportWidthContinuity
import NRR.BodySpace.PerimeterContinuity
import NRR.BodySpace.FullBody

/-!
# `NRR.BodySpace` — convex-body hyperspace

This aggregator re-exports the convex-body hyperspace API in dependency order.

Three body types are kept distinct:

* `NRR.Geometry.ConvexBody Plane` is the solid planar body type: compact, convex, with nonempty
  interior. Solid bodies alone are not closed under Hausdorff degeneration.
* `NRR.ConvexSubbody K` is the fixed-parent hyperspace of compact nonempty convex subsets of a
  solid body `K`. Its elements may be lower-dimensional, and the space is compact.
* `NRR.BodySpace K A` is the closed lower-area subspace `{C : ConvexSubbody K // A ≤ C.area}`.
  When `A > 0`, every element is solid and admits the continuous bridge
  `BodySpace.toGeometryConvexBody`.

The metric is Mathlib's Hausdorff distance on nonempty compact planar sets, transported through
`ConvexSubbody.toNonemptyCompacts`. The API includes continuity of area and Cauchy perimeter and
pointwise membership stability under Hausdorff convergence.
-/
