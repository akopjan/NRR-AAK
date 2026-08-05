import HumanVerification.Main

#check HumanVerification.ConvexFigure
#check HumanVerification.ConvexFigure.area
#check HumanVerification.ConvexFigure.perimeter
#check HumanVerification.IsConvexPartition
#check HumanVerification.equalAreaEqualPerimeterPartition

/-- The public plane is definitionally the standard two-dimensional Euclidean space. -/
example :
    HumanVerification.Plane = EuclideanSpace ℝ (Fin 2) := by
  rfl

/-- Public area is definitionally the standard Mathlib volume measure. -/
example (F : HumanVerification.ConvexFigure) :
    F.area = MeasureTheory.volume F.carrier := by
  rfl

/-- Public perimeter is definitionally one-dimensional Hausdorff measure of the frontier. -/
example (F : HumanVerification.ConvexFigure) :
    F.perimeter =
      (MeasureTheory.Measure.hausdorffMeasure (1 : ℝ) :
          MeasureTheory.Measure HumanVerification.Plane)
        (Set.frontier F.carrier) := by
  rfl

/-- The public partition predicate has the intended covering and disjoint-interior meaning. -/
example {n : ℕ}
    (F : HumanVerification.ConvexFigure)
    (pieces : Fin n → HumanVerification.ConvexFigure) :
    HumanVerification.IsConvexPartition F pieces ↔
      F.carrier = ⋃ i, (pieces i).carrier ∧
      ∀ i j, i ≠ j →
        Disjoint
          (Set.interior (pieces i).carrier)
          (Set.interior (pieces j).carrier) := by
  rfl

example (F : HumanVerification.ConvexFigure) (n : ℕ) (hn : 0 < n) :
    ∃ pieces : Fin n → HumanVerification.ConvexFigure,
      HumanVerification.IsConvexPartition F pieces ∧
      (∀ i j, (pieces i).area = (pieces j).area) ∧
      (∀ i j, (pieces i).perimeter = (pieces j).perimeter) :=
  HumanVerification.equalAreaEqualPerimeterPartition F n hn

#print axioms HumanVerification.equalAreaEqualPerimeterPartition
