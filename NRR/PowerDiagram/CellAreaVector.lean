import Mathlib
import NRR.ConvexBody
import NRR.PowerDiagram.BodyCells
import NRR.PowerDiagram.BodyCellPartition
import NRR.PowerDiagram.CellAreaContinuityWeights

/-!
# `NRR.PowerDiagram.CellAreaVector` — the restricted power‑cell area vector

Packaging the (fixed‑site) restricted power‑cell areas of a convex body `K` into a single
vector‑valued map

```
PowerDiagram.areaVec K s w = fun i => bodyCellArea K s w i : Fin n → ℝ.
```

The two headline facts, both with **fixed sites**:

* `continuous_areaVec_weights` — the vector `w ↦ areaVec K s w` is continuous in the weights.
* `sum_areaVec_eq_area` — under distinct sites its total mass is the body area `K.area`.

## Necessary nondegeneracy hypotheses

Both statements carry `hs : Function.Injective s`. This is **not** optional:

* Continuity specializes the fixed‑site component result
 `continuous_bodyCellArea_weights`, which is genuinely false when two sites coincide
 (the offending halfspace collapses to `{x | w i ≥ w j}`, producing a jump discontinuity of
 the area as `w i` crosses `w j`). Injectivity supplies the required `s j ≠ s i` for every
 `j ≠ i`.
* The total‑mass identity uses the almost‑disjoint covering of `K` by the restricted cells
 (`iUnion_bodyCellSet`, `bodyCellSet_inter_null`); the null‑overlap step needs distinct
 sites.

The total‑mass identity additionally needs at least one site (`[NeZero n]`): with no sites the
cells cover nothing while a convex body has positive area, so the `n = 0` claim is false.

Sites are held fixed throughout; nothing here assumes cells are nonempty, and no equal‑area
statement is proved.
-/

open NRR NRR.Geometry NRR.Geometry.ConvexBody MeasureTheory

namespace NRR.PowerDiagram

variable {n : ℕ}

/-- **Restricted power‑cell area vector.** With sites `s` and weights `w`, the `i`‑th component
is the restricted‑cell area `bodyCellArea K s w i`. -/
noncomputable def areaVec
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) : Fin n → ℝ :=
  fun i => bodyCellArea K s w i

/-- The `i`‑th component of `areaVec` is the restricted‑cell area. -/
@[simp] theorem areaVec_apply
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ) (i : Fin n) :
    areaVec K s w i = bodyCellArea K s w i := rfl

/-- **Fixed‑site weight‑continuity of the area vector.** With sites `s` fixed and pairwise
distinct (`hs`), the vector‑valued area map `w ↦ areaVec K s w` is continuous in the weights.
The injectivity hypothesis is necessary (see the module docstring). -/
theorem continuous_areaVec_weights
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (hs : Function.Injective s) :
    Continuous fun w : Fin n → ℝ => areaVec K s w := by
  refine continuous_pi fun i => ?_
  exact continuous_bodyCellArea_weights K s i (fun j hj => fun h => hj (hs h))

/-- **Total mass of the area vector.** For distinct sites (`hs`) and at least one site
(`[NeZero n]`), the areas of the restricted power cells sum to the body area `K.area`. -/
theorem sum_areaVec_eq_area [NeZero n]
    (K : Geometry.ConvexBody Plane) (s : Fin n → Plane) (w : Fin n → ℝ)
    (hs : Function.Injective s) :
    ∑ i, areaVec K s w i = K.area := by
  -- The area of a body is the Lebesgue measure of the body.
  have h_bodyArea : K.area = (volume (K : Set Plane)).toReal := rfl
  rw [ h_bodyArea, show K.carrier = ⋃ i, bodyCellSet K s w i from ?_ ];
  · convert ENNReal.toReal_sum ( fun i => ?_ ) |> Eq.symm using 1;
    · rw [ MeasureTheory.measure_iUnion₀ ];
      · rw [ tsum_fintype ];
      · exact fun i j hij => MeasureTheory.measure_mono_null ( fun x hx => by aesop ) ( bodyCellSet_inter_null K s w hs hij );
      · exact fun i => IsCompact.nullMeasurableSet ( bodyCellSet_isCompact K s w i );
    · exact fun _ => ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.measure_mono ( bodyCellSet_subset K s w i ) ) ( K.isCompact.measure_lt_top ) );
  · -- Apply the fact that the union of the body cells is equal to K.
    apply Eq.symm; exact iUnion_bodyCellSet K s w

end NRR.PowerDiagram