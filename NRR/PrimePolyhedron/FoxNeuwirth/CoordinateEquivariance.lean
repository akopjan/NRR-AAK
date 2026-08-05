import NRR.PrimePolyhedron.FoxNeuwirth.RefinedAffineMap

/-!
# Prime-equivariant coordinate maps
-/

namespace NRR
namespace FoxNeuwirthOrderComplex

variable {p : Nat}

/-- Prime-equivariance of a continuous full-coordinate map. -/
def IsEquivariantCoordinateMap
    (hp : Nat.Prime p)
    (F : RefinedAffineMap.ContinuousCoordinateMap p) : Prop :=
  ∀ (g : PrimeSymmetry hp) (x : Realization p), F (g • x) = g • F x

end FoxNeuwirthOrderComplex
end NRR
